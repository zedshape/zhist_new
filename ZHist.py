import numpy as np
import pandas as pd
import time
import scipy.stats as ss
from pyts.approximation import SymbolicAggregateApproximation

#rank based INT: https://github.com/edm1/rank-based-INT/blob/master/rank_based_inverse_normal_transformation.py
def rank_INT(series, c=3.0/8, stochastic=True):
    """ Perform rank-based inverse normal transformation on pandas series.
        If stochastic is True ties are given rank randomly, otherwise ties will
        share the same value. NaN values are ignored.
        Args:
            param1 (pandas.Series):   Series of values to transform
            param2 (Optional[float]): Constand parameter (Bloms constant)
            param3 (Optional[bool]):  Whether to randomise rank of ties
        
        Returns:
            pandas.Series
    """

    # Check input
    assert(isinstance(series, pd.Series))
    assert(isinstance(c, float))
    assert(isinstance(stochastic, bool))

    # Set seed
    np.random.seed(123)

    # Take original series indexes
    orig_idx = series.index

    # Drop NaNs
    series = series.loc[~pd.isnull(series)]

    # Get ranks
    if stochastic == True:
        # Shuffle by index
        series = series.loc[np.random.permutation(series.index)]
        # Get rank, ties are determined by their position in the series (hence
        # why we randomised the series)
        rank = ss.rankdata(series, method="ordinal")
    else:
        # Get rank, ties are averaged
        rank = ss.rankdata(series, method="average")

    # Convert numpy array back to series
    rank = pd.Series(rank, index=series.index)

    # Convert rank to normal distribution
    transformed = rank.apply(rank_to_normal, c=c, n=len(rank))
    
    return transformed[orig_idx]

def rank_to_normal(rank, c, n):
    # Standard quantile function
    x = (rank - c) / (n - 2*c + 1)
    return ss.norm.ppf(x)

#create monthly divided interval chunk

def PAA_HIST(dists, normal_term, date_enabled=False):
    dists_new = []
    movable = False
    for idx, elem in enumerate(dists):
        if idx == 0:
            dists_new.append(elem)
        else:
            old_idx = idx-1

            dist_old = dists[old_idx]['dist']
            dist_new = elem['dist']
            date_old = dists[old_idx]['date']
            date_new = elem['date']
            #### DATETIME OPTION ####
            if date_enabled == True:
                diff_date = (date_new - date_old).days
            else:
                diff_date = (date_new - date_old)
            
            diff = (dist_new - dist_old) / diff_date

            #dist_ongoing = dist_old
            #print("old:", date_old, dist_old, "new:", date_new, dist_new, "diff:", diff_date)

            while True:
                if movable == True:
                    movedate = normal_term - movable_date
                    # what if this move date is bigger than diff date?
                    diff_date = diff_date - movedate
                    if diff_date >= 0:
                        #print(movedate, diff_date)
                        dist_old = dist_old + diff*(movedate)
                        date_old = date_old + movedate
                        dists_new.append({'date': date_old, 'dist': dist_old})
                        #print(date_old, dist_old, diff_date)
                        movable = False
                    else:
                        movedate = diff_date + movedate
                        diff_date = movedate
                        break
                elif diff_date >= normal_term:
                    dist_old = dist_old + diff*(normal_term)
                    diff_date = diff_date - normal_term
                    date_old = date_old+normal_term
                    dists_new.append({'date': date_old, 'dist': dist_old})
                    #print(date_old, dist_old, diff_date)
                else:
                    if diff_date != 0:
                        #we need to move some day to next
                        #print("movable")
                        movable = True
                        movable_date = diff_date
                    break
    if movable == True:
        #print("movable", diff_date)
        #print(date_old, dist_old, diff_date)
        dist_old = dist_old + diff*(diff_date)
        date_old = date_old+diff_date
        dists_new.append({'date': date_old, 'dist': dist_old})
        #print(date_old, dist_old, diff_date)
        #print((date_new - date_old).days, diff, diff*diff_date)
    return dists_new

class ZHist:
    def __init__(self, data, drop_cols, distance="chi2", minTrend = 300, 
                 normal_term = 300, n_bins = 3, minimal_trend_gradient = 0,
                 matrix_cols = [], remove_events = [],
                 removeMatrix = False, removeTrend = True, isStandardized=False):
        self.data = data
        self.minTrend = minTrend
        self.removeMatrix = removeMatrix
        self.removeTrend = removeTrend
        self.minimal_trend_gradient = minimal_trend_gradient
        self.isStandardized = isStandardized
        self.repair_intervals = []
        self.normal_intervals = []
        self.remove_events = remove_events
        self.matrix_cols = matrix_cols
        # it will be for every chassi
        self.timeavgs = {} # average
        self.indices = {} # data indices in the dataframe, corresponding to specific car
        self.histogram_columns = {} # data structure for one dimensional columns
        self.uniqueIdx = self.data["no"].unique() # unique cars
        self.normal_term = normal_term
        self.n_bins = n_bins
        # copy part of data in need (without time, date, count ...)
        self.data_simplified = data.drop(drop_cols, axis=1)
        
        # create multiindex for components of the same histogram value
        self.repairs = self.data[self.data["status"]==1]["no"].unique()
        self.times = self.data["time"].reset_index(drop=True)
        
        if distance == "chi2":
            self.distance = self.distance_chi2
        
        for i in self.data_simplified.columns:
            if i[0] not in self.histogram_columns:
                self.histogram_columns[i[0]] = []
            self.histogram_columns[i[0]].append(i[1])

    def distance_chi2(self, val, avg):
        dist = (((val - avg)**2 / (val + avg)).sum())/2
        if (range(1,len(val)+1)*val).sum() > (range(1,len(avg)+1)*avg).sum():
            return dist
        return -dist
    
    def generateIntervals(self):
        final = {}
        final_trend = {}
        
        print("interval creation started")
        
        # Counter for checking the algorithm running time
        aa = time.perf_counter()

        # for each histogram column (e.g., ambient temp)
        for cur in self.histogram_columns:            
            hist_dists = []
            #isax = False
            print("current:", cur)

            # and for each chassi (unique car #)
            for idx in self.uniqueIdx:
                # we remove any na value (anyway that time will be imputed later on with our linearity assumption)
                # one bad thing here is we also lose some available information if only part of it was NA

                # need to change later on
                a = self.data_simplified[cur][self.indices[idx]].dropna()

                # We 'normalize' the real histogram value as well summing up to one to take a distance from central point
                a = a.div(a.sum(axis=1), axis=0)

                # Here we save distances from central point with their dates to create intervals
                dists = []
                for idx2, val in a.iterrows():
                    dists.append({"date": self.data['date'][idx2],
                                  "dist": self.distance(val, self.timeavgs[cur])})

                # run PAA_hist function to change the distance array into monthly-based
                new_dists = PAA_HIST(dists, self.normal_term)

                # The dictionary will be converted into python dataframe
                df_new_dists = pd.DataFrame(new_dists)

                # And will have its own chassi number at the front
                df_new_dists['no'] = idx

                # we append it to the list
                hist_dists.append(df_new_dists)

            # after tracersing all chassi (for one histogram variable)
            # we make one single dataframe and reset its index
            hist_df = pd.concat(hist_dists)
            hist_df = hist_df.reset_index(drop=True)

            # Using the whole value (regardless of the chassi numbers) we apply inverse normal transformation to
            # correct the distribution to the normal shape
            # hist_norm = rank_INT(hist_df['dist'])
            hist_norm = (hist_df['dist'] - np.mean(hist_df['dist']))/np.std(hist_df['dist'])

            # And we finally apply SAX, to convert distances into the numbers
            sax = SymbolicAggregateApproximation(n_bins=self.n_bins, strategy='normal')
            X_sax = sax.fit_transform([hist_norm])
            # print(hist_norm)
            # print(X_sax)

            # We attach this alphabet to the dataframe
            hist_df['alphabet'] = X_sax[0]

            ### Those big lines are used to merge the same alphabets into one entry
            for idx in self.uniqueIdx:
                if idx not in final:
                    final[idx] = []
                    final_trend[idx] = []

                a = hist_df[hist_df['no']==idx]
                min_date = a['date'].min()
                first = True
                for idx2, val in a.iterrows():
                    new_date = val['date']
                    if first == True:
                        #keep old date to create continuous alphabet
                        old_date = val['date']
                        old_date_trend = val['date']
                        old_alphabet = val['alphabet']
                        first = False
                        old_state = '#'
                    else:
                        ### TREND CONTROL
                        if val['dist'] - a['dist'][idx2-1] > self.minimal_trend_gradient:
                            new_state = 'i'
                        elif val['dist'] - a['dist'][idx2-1] < -self.minimal_trend_gradient:
                            new_state = 'd'
                        else:
                            new_state = 's'
                        if old_state == '#':
                            old_state = new_state

                        if val['alphabet'] != old_alphabet:
                            #stop collecting

                            event = ((cur, old_alphabet), (old_date - min_date), (new_date-min_date))
                            final[idx].append(event)
                            #update old alphabet and old date
                            old_alphabet = val['alphabet']
                            old_date = new_date
                            #print(event)

                        #TREND CONTROL
                        if new_state != old_state:
                            event = ((cur, old_state), (old_date_trend - min_date), (new_date-min_date))
                            final_trend[idx].append(event)
                            old_state = new_state
                            old_date_trend = new_date


                #last step: create intervals
                event = ((cur, old_alphabet), (old_date - min_date), (new_date-min_date))
                final[idx].append(event)
                event = ((cur, old_state), (old_date_trend - min_date), (new_date-min_date))
                final_trend[idx].append(event)
        bb = time.perf_counter()
        print("interval creation is done:", bb-aa)
        
        print("interval separation started")
        aa = time.perf_counter()
        for idx in final:
            if idx in self.repairs:
                self.repair_intervals.append(final[idx]+final_trend[idx])
            else:
                self.normal_intervals.append(final[idx]+final_trend[idx])
        bb = time.perf_counter()
        print("interval separation is done:", bb-aa)
    
    def removeNormal(self, intervals, letter):
        copied = []
        for v1 in intervals:
            tmparr = []
            copied.append(tmparr)
            for v2 in v1:
                #print(copied[i1][i2][0][1])
                if (v2[0][1] not in letter) and (self.removeMatrix == False or (self.removeMatrix == True and v2[0][0] not in self.matrix_cols)):
                    if self.removeTrend == False:
                        if (v2[0][1] in ['i','d'] and v2[2] - v2[1] >= self.minTrend):
                            tmparr.append(v2)
                    if self.removeTrend == True:
                        if (v2[0][1] not in ['i','d','s','#']):
                            tmparr.append(v2)

        return copied

    def getWeightedAverage(self):
        aa = time.perf_counter()

        #### Time information acquisition
        # here we substract the current time value by the previous one to get absolute time points
        for idx in self.uniqueIdx:
            self.indices[idx] = (self.data['no']==idx) # separate row numbers having the same car number
            
        for idx in self.uniqueIdx:
            currentidx = self.indices[idx] # again for each chassi
                # Here we multiply the absolute time points to each corresponding histogram to weight them.
            if self.isStandardized == True:
                self.data_simplified[currentidx] = self.data_simplified[currentidx].multiply(self.times[idx], axis=0)


        self.timeavgs = self.data_simplified.sum(axis=0).groupby(level=0).transform(lambda x: (x / x.sum()))

        bb = time.perf_counter()
        print("getWeightedAverage:", bb-aa)
    
    def fit(self):
        self.getWeightedAverage()
        self.generateIntervals()
        self.repair_intervals_removed = self.removeNormal(self.repair_intervals, self.remove_events)
        self.normal_intervals_removed = self.removeNormal(self.normal_intervals, self.remove_events)