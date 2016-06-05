#! /usr/bin/env python

##################################################################################
#
#   The Reverse Mathematics Zoo
#   by Damir Dzhafarov
#   - Version 1.0 started August, 2010
#   - Version 2.0 started August, 2013
#   Revised by Eric Astor
#   - Version 3.0 - 29 May 2016
#   - Version 4.0 - started 30 May 2016
#   Documentation and support: http://rmzoo.uconn.edu
#
##################################################################################

from __future__ import print_function

import sys
from copy import copy
from collections import defaultdict

def eprint(*args, **kwargs):
    print(*args, file=sys.stderr, **kwargs)

Date = '30 May 2016'
Version = '4.0'

Error = False
def warning(s):
    global Error
    Error = True
    eprint(s)

def error(s):    # Just quit
    warning(s)
    quit()

# Data structures
from rmBitmasks import *

_FORM_COLOR = {Form.none: "white",
               Form.Pi11: "pink",
              Form.rPi12: "cyan"}
_CONS_COLOR = {Form.none: "white",
               Form.Pi11: "pink",
  Form.rPi12 | Form.Pi11: "cyan"}
    
##################################################################################
#
#   GET OPTIONS
#
##################################################################################
    
eprint('\nRM Zoo (v{0})'.format(Version))

from optparse import OptionParser, OptionGroup

parser = OptionParser('Usage: %prog [options] database', version='%prog ' + Version + ' (' + Date + ')')

parser.set_defaults(implications=False,nonimplications=False,omega=False,onlyprimary=False,weak=False,strong=False,showform=False,conservation=False)

parser.add_option('-i', action='store_true', dest='implications',
    help='Display implications between principles.')
parser.add_option('-n', action='store_true', dest='nonimplications',
    help='Display non-implications between principles.')
parser.add_option('-w', action='store_true', dest='weak',
    help='Display weakest non-redundant open implications.')
parser.add_option('-s', action='store_true', dest='strong',
    help='Display strongest non-redundant open implications.')
parser.add_option('-t', dest='reducibility', default='RCA',
    help='Display facts relative to REDUCIBILITY-implications.')
parser.add_option('-o', action='store_const', dest='reducibility', const='w',
    help='Display only facts that hold in omega models.')
parser.add_option('-p', action='store_true', dest='onlyprimary',
    help='Display only facts about primary principles.')
    
parser.add_option('-f', action='store_true', dest='showform',
    help='Indicate syntactic forms of principles.')
parser.add_option('-c', action='store_true', dest='conservation',
    help='Display known conservation results.')
    
parser.add_option('-r', dest='restrict_string', metavar='CLASS',
    help='Resrict to only the principles in CLASS.')
parser.add_option('-q', dest='query_string', metavar='FACT',
    help='Show whether FACT is known, and if so, its justification.')


(options, args) = parser.parse_args()

import os

Implications = options.implications
NonImplications = options.nonimplications
Weak = options.weak
Strong = options.strong
Reducibility = Reduction.fromString(options.reducibility)
OnlyPrimary = options.onlyprimary
ShowForm = options.showform
Conservation = options.conservation
Restrict = options.restrict_string
if Restrict:
    rSet = set()
    for p in Restrict.split():
        splitP = p.split('+')
        setP = set(splitP)
        p = '+'.join(sorted(setP))
        
        rSet.add(p)
        rSet.update(splitP)
    Restrict = rSet
Query = options.query_string
    
# Give errors if bad options chosen

if not Implications and not NonImplications and not OnlyPrimary and not Restrict and not Weak and not Strong and not ShowForm and not Conservation and not Query:
    parser.error('Error: No options selected.')
if OnlyPrimary:
    if not Implications and not NonImplications and not Weak and not Strong and not ShowForm and not Conservation:
        parser.error('Error: Option -p only works if one of -i, -n, -w, -s, -f, or -c is selected.')
if Restrict:
    if not Implications and not NonImplications and not Weak and not Strong and not ShowForm and not Conservation:
        parser.error('Error: Option -r only works if one of -i, -n, -w, -s, -f, or -c is selected.')
if Query:
    if Implications or NonImplications or Weak or Strong or ShowForm or Conservation or Restrict or OnlyPrimary:
        parser.error('Error: Option -q does not work with any other option.')

if len(args) > 1:
    parser.error('Too many arguments.')
if len(args) < 1:
    parser.error('No database file specified.')
databaseFile = args[0]
    
##################################################################################
#
#   IMPORT AND ORGANIZE DATA
#
##################################################################################

eprint('Importing and organizing data...')

def printOp(op):
    if op[1] == 'nc':
        return 'n{0}c'.format(op[0])
    else:
        return '{0}{1}'.format(*op)

justMarker = '*@'
def printJust(a):
    a = a.replace('@','    ')
    a = a.replace('*','\n')
    return a

class VersionError(Exception):
    def __init__(self, targetVersion, actualVersion):
        self.targetVersion = targetVersion
        self.actualVersion = actualVersion
    def __str__(self):
        return 'Version mismatch: found v{0}, targeting v{1}'.format(actualVersion, targetVersion)

if sys.version_info < (3,):
    import cPickle as pickle
else:
    import pickle
with open(databaseFile, 'rb') as f:
    fileVersion = pickle.load(f)
    if fileVersion != Version:
        raise VersionError(fileVersion, Version)
    database = pickle.load(f)

principles = database['principles']
implies, notImplies = database['implication']
conservative, nonConservative = database['conservation']
form = database['form']
primary, primaryIndex = database['primary']
justify = database['justify']
   
##################################################################################
#
#   IF RESTRICT OR QUERY: VALIDATE CLASS
#
##################################################################################

if Restrict:
    
    for a in Restrict:  # Give warnings if CLASS is not a subset of principles
        if a not in principles:
            error('Error: '+a+' is not in the database.')

##################################################################################
#
#   IF QUERY: GIVE ANSWER
#
##################################################################################

from pyparsing import *

name = Word( alphas+"_+^{}\\$", alphanums+"_+^{}$\\")

_reductionName = NoMatch()
for r in Reduction:
    if r != Reduction.none:
        _reductionName |= Literal(r.name)
reductionName = Optional(_reductionName, default=Reduction.RCA.name)

reduction = (reductionName + Literal("->")) | (Literal("<=") + Optional(Suppress(Literal("_")) + _reductionName, default=Reduction.RCA.name)).setParseAction(lambda s,l,t: [t[1], "->"])
nonReduction = reductionName + Literal("-|>")
equivalence = reductionName + Literal("<->")

_formName = NoMatch()
for f in Form:
    if f != Form.none:
        _formName |= Literal(f.name)
formName = _formName

conservation = formName + Literal("c")
nonConservation = (Literal("n") + formName + Literal("c")).setParseAction(lambda s,l,t: [t[1], "nc"])

operator = reduction | nonReduction | equivalence | conservation | nonConservation

query = name + Group(operator) + name + StringEnd()
            
if Query:
    Query = query.parseString(Query)
    
    a = '+'.join(sorted(set(Query[0].split('+'))))
    op = tuple(Query[1])
    b = '+'.join(sorted(set(Query[2].split('+'))))
    
    if a not in principles:
        error('Error: {0} is not in the database.'.format(a))
    if b not in principles:
        error('Error: {0} is not in the database.'.format(b))
    if (a,op,b) not in justify:
        error('Error: {0} {1} {2} is not a known fact.'.format(a, printOp(op), b))
    else:
        print('Justification for the fact {0} {1} {2}:'.format(a, printOp(op), b))
        print(printJust(justify[(a, op, b)]))
        eprint('\nFinished.')

##################################################################################
#
#   IF RESTRICT: DELETE PRINCIPLES NOT IN CLASS
#
##################################################################################

if Restrict:
    principles &= Restrict
    
##################################################################################
#
#   IF DIAGRAM: REMOVE REDUNDANT IMPLICATIONS AND NON-IMPLICATIONS 
#
##################################################################################

if Implications or NonImplications or Weak or Strong:

    eprint('Removing redundant facts for clarity...')
    
    # Create print versions of functions
    
    simpleImplies = defaultdict(bool)
    printImplies = defaultdict(bool)
    
    simpleNotImplies = defaultdict(bool)
    printNotImplies = defaultdict(bool)
    
    equivalent = defaultdict(bool)
    
    simpleConservative = defaultdict(noForm)
    printConservative = defaultdict(noForm)
    
    printWeakOpen = defaultdict(bool)
    printStrongOpen = defaultdict(bool)
    
    for a in principles:
        for b in principles:
            if a == b: # Remove self-relations to not confuse DOT reader
                continue
            
            simpleImplies[(a,b)] = Reduction.isPresent(Reducibility, implies[(a,b)])
            printImplies[(a,b)] = simpleImplies[(a,b)]
            
            simpleNotImplies[(a,b)] = Reduction.isPresent(Reducibility, notImplies[(a,b)])
            printNotImplies[(a,b)] = simpleNotImplies[(a,b)]
            
            if simpleImplies[(a,b)] and simpleImplies[(b,a)]:
                equivalent[(a,b)] = True
                equivalent[(b,a)] = True
            
            simpleConservative[(a,b)] = conservative[(a,b)]
            printConservative[(a,b)] = simpleConservative[(a,b)]
            
    # Assign primaries and make them unique
    
    for a in sorted(principles):
        currentPrimary = a
        currentIndex = len(primaryIndex)
        for b in principles:
            if equivalent[(a,b)] and b in primary:
                if primaryIndex.index(b) < currentIndex:
                    if currentPrimary in primary:
                        primary.remove(currentPrimary)
                    currentPrimary = b
                    currentIndex = primaryIndex.index(b)
                else:
                    primary.remove(b)
        if currentPrimary not in primary:
            primary.add(currentPrimary)
            primaryIndex.append(currentPrimary)
    
    for a in principles: # Remove facts involving non-primary principles
        if a not in primary:
            for b in principles:
                printImplies[(a,b)] = False
                printImplies[(b,a)] = False
                
                printNotImplies[(a,b)] = False
                printNotImplies[(b,a)] = False
                
                printConservative[(a,b)] = Form.none

    # Remove redundant implications
            
    for a in primary:
        for b in primary:
            for c in primary: # Remove implications obtained by transitivity
                if simpleImplies[(b,a)] and simpleImplies[(a,c)]:
                    printImplies[(b,c)] = False

    # Remove redundant non-implications

    for a in primary:
        for b in primary:
            if b == a: continue
            for c in primary:
                if c == a or c == b: continue
                
                if simpleNotImplies[(a,c)] and simpleImplies[(b,c)]: # If a -|> c, but b -> c, then a -|> b.
                    printNotImplies[(a,b)] = False
                if simpleImplies[(c,a)] and simpleNotImplies[(c,b)]: # If c -> a, but c -|> b, then a -|> b.
                    printNotImplies[(a,b)] = False
                
    # Remove redundant conservation facts

    for a in primary:  # Remove conservation results obtained by transitivity
        for b in primary:
            if b == a: continue
            for c in primary:
                if c == a or c == b: continue
                
                if simpleImplies[(a,b)]:
                    printConservative[(b,c)] &= ~simpleConservative[(a,c)]
                if simpleImplies[(b,c)]:
                    printConservative[(a,b)] &= ~simpleConservative[(a,c)]
    
    # Generate open implications

    for a in primary:
        for b in primary:
            if b == a: continue
            
            if not simpleImplies[(a,b)] and not simpleNotImplies[(a,b)]:
                printWeakOpen[(a,b)] = True
                printStrongOpen[(a,b)] = True

    for a in primary:
        for b in primary:
            if b == a: continue
            for c in primary:
                if c == a or c == b: continue
                
                if simpleImplies[(c,a)] and not simpleImplies[(c,b)] and not simpleNotImplies[(c,b)]: # c -> a, c ? b
                    printWeakOpen[(a,b)] = False
                if simpleImplies[(c,a)] and not simpleImplies[(b,a)] and not simpleNotImplies[(b,a)]: # c -> a, b ? a
                    printWeakOpen[(b,c)] = False
                
                if simpleImplies[(a,c)] and not simpleImplies[(c,b)] and not simpleNotImplies[(c,b)]: # a -> c, c ? b
                    printStrongOpen[(a,b)] = False
                if simpleImplies[(a,c)] and not simpleImplies[(b,a)] and not simpleNotImplies[(b,a)]: # a -> c, b ? a
                    printStrongOpen[(b,c)] = False
 
##################################################################################
#
#   IF DIAGRAM: PRINT OUT THE DOT FILE
#
##################################################################################   

if Implications or NonImplications or Weak or Strong or ShowForm or Conservation:

    eprint('Printing DOT file...')

    print("""//
// RM Zoo (v""" + Version + """)
//

digraph G {

graph [
    rankdir = TB        // put stronger principles higher up
  ranksep = 1.5
      ]

//
// Node Styles
//

node [shape=none,color=white];

//
// Data
//""")

    if Implications:
        
        for a in primary:
            for b in primary:
                if printImplies[(a,b)]:
                    style = ''
                    if printNotImplies[(b,a)] and not NonImplications:
                        style = ' [color = "black:white:black"]'
                    print('" {0} " -> " {1} "{2}'.format(a,b,style))
                        
    if NonImplications:
        
        for a in primary:
            for b in primary:
                if printNotImplies[(a,b)]:
                        print('" {0} " -> " {1} " [color = "red"]'.format(a,b))
    
    if not OnlyPrimary:
        for a in primary:
            for b in principles:
                if equivalent[(a,b)]:
                    print('" {0} " -> " {1} "  [dir = both]'.format(a,b))
                    
    if Weak:
        for a in primary:
            for b in primary:
                if printWeakOpen[(a,b)]:
                    print('" {0} " -> " {1} "  [color = "green"]'.format(a,b))
                
    if Strong:
        for a in primary:
            for b in primary:
                if printStrongOpen[(a,b)]:
                    print('" {0} " -> " {1} "  [color = "orange"]'.format(a,b))
        
    if ShowForm:
        for a in principles:
            if a in form:
                if form[a] != Form.none:
                    print('" {0} " [shape=box, style=filled, fillcolor={1}]'.format(a, _FORM_COLOR[form[a]]))
                
    
    if Conservation:
        for a in primary:
            for b in primary:
                if a == b: continue
                
                if printConservative[(a,b)] != Form.none:
                    print('" {0} " -> " {1} "  [color = "{2}"]'.format(a,b, _CONS_COLOR[printConservative[(a,b)]]))

    print('}')
    eprint('Finished.')
