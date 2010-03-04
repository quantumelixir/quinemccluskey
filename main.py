import sys, os
from optparse import OptionParser
from random import random
import psyco
psyco.full()

#Implement the Quine-McCluskey algorithm

def dash(a, i) :
    """Dash position i in the bitstring a"""
    return a[0:i] + '-' + a[i + 1:]

def decToBin(n, l):
    """Convert decimal integer to binary string padding with additional
    zeros to length l, if necessary"""
    bStr = ''
    if n < 0: raise ValueError, "must be a positive integer"
    if n == 0: return '0'*l
    while n > 0:
        bStr = str(n % 2) + bStr
        n = n >> 1
    return '0'*(l - len(bStr)) + bStr

def genBitStrings(m, d, l) :
    """Convert the minterms from decimals to a list of binary strings"""
    table = []
    for i in m + d :
        table += [decToBin(i, l)]
    return table

def flatten(l, valid=(list,tuple)) :
    """Flattens a list"""
    ret = []
    for i in l :
        if isinstance(i, valid) :
            ret += flatten(i)
        else :
            ret += [i]
    return ret

def uniq(alist) :
    """Return only the unique elements of the list"""
    set = {}
    map(set.__setitem__, alist, [])
    return set.keys()

def printGroups(groups, l) :
    """Neatly print the implicants in groups"""
    print 'START'
    print '-'*(l+5)
    for i in range(len(groups)) :
        for j in groups[i] :
            print j
        print '-'*(l+5)
    print 'END'

def printChart(chart, mterms) :
    """Print the PrimeImplicants vs Minterm Chart"""
    print '----'*len(mterms)
    for i in mterms :
        print '%3d' % i,
    print '\n', '----'*len(mterms)
    for i in chart :
        for j in i :
            print '%3d' % j,
        print
    print '----'*len(mterms)

def isAdjacent(a, b) :
    """Test if the two bitstrings a and b differ by one bit.
    Return 0 if they don't or a dashed bitstring if they do"""
    t, p = 0, -1
    for i in range(len(a)) :
        if (a[i] != b[i]) :
            if (b[i] == '-' or a[i] == '-') :
                return 0
            elif t == 0 :
                p = i
                t = t + 1
            elif t == 1 :
                return 0
    if p != -1 :
        return dash(a, p)
    return 0

def groupByOnes(table, inp) :
    """Group the implicants by the number of ones they contain"""
    groups = [[] for i in range(inp + 1)]
    for i in table :
        groups[i.count('1')] += [i]
    return groups

def minimizer(groups, l) :
    """Reduce iteratively the set of implicants to obtain the prime
    implicants"""

    inv = [[0 for j in groups[i]] for i in range(len(groups))]
    redns, newgroups = 0, [[] for i in range(l + 1)]

    for i in range(len(groups) - 1) :
        for j in range(len(groups[i])) :
            #Take care of corner case type 1
            if len(groups[i + 1]) == 0 :
                newgroups[groups[i][j].count('1')] += [groups[i][j]]
            else :
                for k in range(len(groups[i + 1])) :
                    r = isAdjacent(groups[i][j], groups[i + 1][k])
                    if r :
                        inv[i][j] = inv[i + 1][k] = 1
                    if r and r not in newgroups[r.count('1')] :
                        newgroups[r.count('1')] += [r]
                        redns = redns + 1

        #Take care of corner case type 2
        if len(groups[-2]) == 0 and len(groups[-1]) != 0 :
            for m in groups[-1] :
                newgroups[m.count('1')] += [m]

        for m in range(i) :
            for j in range(len(inv[m])) :
                if inv[m][j] == 0 :
                    r = groups[m][j]
                    if r and r not in newgroups[r.count('1')] :
                        newgroups[r.count('1')] += [r]

    if redns == 0 :
        return newgroups
    else :
        return minimizer(newgroups, l)

def isCovered(pI, mterm, l) :
    """Checks if a prime implicant can be covered by a minterm"""
    mterm = decToBin(mterm, l)
    for i in range(len(pI)) :
        if (pI[i] == '0' or pI[i] == '1') and pI[i] != mterm[i] :
            return 0
    return 1

def updateChart(chart, ind) :
    """Reflect changes on including prime implicants in final solution"""
    zeroed = 0
    for i in range(len(chart[ind])) :
        if chart[ind][i] == 1 :
            for j in range(len(chart)) :
                if chart[j][i] == 1 :
                    zeroed = zeroed + 1
                chart[j][i] = 0
    return zeroed

def makeChart(primeI, mterms, l) :
    """Make a chart of Prime Implicants vs Minterms"""
    return [[isCovered(primeI[i], mterms[j], l) for j in range(len(mterms))] for i in range(len(primeI))] 

def selectEssentialPI(chart, primeI, mterms, l) :
    """Selects the Essential prime Implicants"""
    colsums = map(sum, zip(*chart))
    indices = uniq([zip(*chart)[i].index(1) for i in range(len(colsums)) if colsums[i] == 1])
    return [primeI[i] for i in indices]

def selectGreedyCoveringPI(chart, primeI, mterms, l) :
    """Select a set of 'covering' prime implicants (including the essential
    prime implicants) in a greedy manner"""

    indices, greedy = [], 0
    colsums = map(sum, zip(*chart))
    total = sum(colsums)

    while total > 0 :
        if 1 in colsums :
            olen = len(indices)
            indices += uniq([zip(*chart)[i].index(1) for i in range(len(colsums)) if colsums[i] == 1])
            for i in indices[olen:] :
                total = total - updateChart(chart, i)
        else :
            greedy = 1
            rowsums = map(sum, chart)
            indices += [rowsums.index(max(rowsums))]
            total -= updateChart(chart, indices[-1])

        colsums = map(sum, zip(*chart))
        total = sum(colsums)

    if not greedy :
        print 'Covering implicants consist only of essential prime implicants.'

    return [primeI[i] for i in indices]

def evaluateInput(case, implicants) :
    for i in implicants :
        assert(len(case) == len(i))
        out = 1
        for j in range(len(i)) :
            if i[j] != '-' and ((i[j] == '0' and case[j] == '1') or (i[j] == '1' and case[j] == '0')) :
                out = 0
        if out == 1 :
            return 1
    return 0

def validateCPI(coveringPI, mterms, l) :
    m = genBitStrings(mterms, [], l)
    for i in m :
        if not evaluateInput(i, coveringPI) :
            return 0
    return 1

def logicExpression(implicants) :
    """Substitute implicants with logic expressions"""
    symbols, exp = 'ABCDEFGHIJKLMNOPQRSTUVWXYZ', []
    for i in implicants :
        if i == '-' * len(i) :
            return '1'
        s = ''
        for j in range(len(i)) :
            if i[j] == '1' :
                s += symbols[j]
            elif i[j] == '0' :
                s += symbols[j] + "'"
        exp += [s]
    return ' + '.join(exp)

def mycallback(option, opt, value, parser):
    """For parsing the multiple integer values for an option"""
    setattr(parser.values, option.dest, map(int, value.split(',')))

def myfloatcallback(option, opt, value, parser):
    """For parsing the single integer and multiple floating point values for an option"""
    setattr(parser.values, option.dest, map(int, [value.split(',')[0]]) + map(float, value.split(',')[1:]) )

def generateTestCase(n, mwt = 0.33, dwt = 0.33) :
    """Generate test cases for an n variable input boolean logic expression
    with weights for choosing minterms and dterms randomly"""
    m, d = [], []
    for i in range(2**n) :
        r = random()
        if r < mwt :
            m += [i]
        elif r < mwt + dwt :
            d += [i]
    return m, d

#main
if __name__ == '__main__' :

    desc = """Implements the Quine-McCluskey algorithm (in python) to minimize boolean logic expressions. Currently only supports multiple inputs and single output function minimization. Author: Chidambaram Annamalai [Sat Aug 01, 2009]"""

    parser = OptionParser(description=desc)
    parser.add_option('-i', '--inputvars',
        help='Number of input variables', type='int', dest='inp')
    parser.add_option('-o', '--outputfunctions',
        help='Number of output functions. Defaults to 1. Function currently not implemented',
        type='int', dest='out', default=1)
    parser.add_option('-m', '--minterms', help='Specify a list of minterms. Example: 1,3,5,6',
        type='string', dest='mterms', action='callback', callback=mycallback)
    parser.add_option('-d', '--dontcareterms', help='Specify a list of dont care terms. Example: 2,4,7',
        type='string', dest='dterms', action='callback', callback=mycallback, default=[])
    parser.add_option('-g', '--generatetestcase',
        help='Randomly generate a test case with given number of input variables,'
        'weights(sum < 1) for choosing mterms and dterms. Example: 5,0.33,0.1',
        type='string', dest='gen', action='callback', callback=myfloatcallback, default=[])
    parser.add_option('-q', '--quiet', help='Suppress intermediate output', dest='quiet', default=False, action='store_true')
    parser.add_option('-c', '--check', help='Check final expression', dest='check', default=False, action='store_true')
    (opts, args) = parser.parse_args()

    inp, out, mterms, dterms, gen, quiet, check = opts.inp, opts.out, opts.mterms, opts.dterms, opts.gen, opts.quiet, opts.check

    if gen :
        if mterms or dterms or inp :
            print '-g cannot be used with any other option'
            sys.exit()
        elif len(gen) != 3 :
            print '-g requires 3 arguments. See help'
            sys.exit()
    elif not all([inp, mterms]) :
        print 'Options -i, -m are mandatory when not using -g'
        sys.exit()

    if gen :
        inp, mwt, dwt = gen
        mterms, dterms = generateTestCase(inp, mwt, dwt)

    print 'Input Variables:', inp, '\nOutput Functions:', out
    print 'Minterms:', mterms, '\nDont Care Terms:', dterms

    table = genBitStrings(mterms, dterms, inp)
    groups = groupByOnes(table, inp)
    primeImplicants = flatten(minimizer(groups, inp))
    if not quiet :
        print 'Prime Implicants:', primeImplicants

    chart = makeChart(primeImplicants, mterms, inp)
    if not quiet :
        print '\nPrimeImplicants vs Minterm Chart'
        printChart(chart, mterms)

    print 'Essential Prime Implicants:', selectEssentialPI(chart, primeImplicants, mterms, inp)
    cover = selectGreedyCoveringPI(chart, primeImplicants, mterms, inp)
    print 'Covering Prime Implicants :', cover

    #Try expressing the cover in Symbols A,B,C...
    if len(cover[0]) <= 26 :
        print 'Minimized Logic Expression:', logicExpression(cover)

    #Check if the expression produces logic True for all minterms
    if check :
        if validateCPI(cover, mterms, inp) :
            print 'Validation: Logic expression produces correct result.'
