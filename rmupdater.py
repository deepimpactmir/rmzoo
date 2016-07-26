#! /usr/bin/env python

##################################################################################
#
#   The Reverse Mathematics Zoo Updater
#   by Damir Dzhafarov
#   - Version 1.0 started August, 2010
#   - Version 2.0 started August, 2013
#   Revised by Eric Astor
#   - Version 3.0 - 29 May 2016
#   - Version 4.0 - started 30 May 2016
#   - Version 4.1 - optimizations & refactoring, started 2 July 2016
#   - Version 4.2 - new forms and reasoning, started 12 July 2016
#   - Version 4.3 - changed internal representations, started 21 July 2016
#   - Version 4.4 - moved to a shelf database, started 25 July 2016
#   Documentation and support: http://rmzoo.uconn.edu
#
##################################################################################

from __future__ import print_function

import sys
import time
from io import open
from collections import defaultdict

from version_guard import lru_cache, closingWrapper

import shelve

def eprint(*args, **kwargs):
    print(*args, file=sys.stderr, **kwargs)

Error = False
def warning(s):
    global Error
    Error = True
    eprint(s)

def error(s):    # Throw exception
    raise Exception(s)

Date = u'25 July 2016'
Version = u'4.4'

from rmBitmasks import *
from renderJustification import *

principles = set([u'RCA'])
principlesList = []

def addPrinciple(a):
    setA = set(a.split(u'+'))
    a = u'+'.join(sorted(setA))
    principles.add(a)
    principles.update(setA)
    return a

implies = defaultdict(noReduction)
notImplies = defaultdict(noReduction)

def addReduction(a,reduction,b):
    implies[(a,b)] |= Reduction.weaker(reduction)

def addNonReduction(a,reduction,b):
    notImplies[(a,b)] |= Reduction.stronger(reduction)

conservative = defaultdict(noForm)
nonConservative = defaultdict(noForm)

def addConservative(a,frm,b):
    conservative[(a,b)] |= Form.stronger(frm)

def addNonConservative(a,frm,b):
    nonConservative[(a,b)] |= Form.weaker(frm)

form = defaultdict(noForm)

primary = set()
primaryIndex = []

def addForm(a, frm):
    form[a] |= Form.weaker(frm)

def addPrimary(a):
    primary.add(a)
    primaryIndex.append(a)

justify = {}
justComplexity = {}

def addJustification(fact, jst, cplx):
    try:
        if cplx >= justComplexity[fact]:
            return False
    except KeyError:
        pass
    justify[fact] = jst
    justComplexity[fact] = cplx
    return True

def unoptimizedJustification(fact, jst, cplx):
    if fact in justify:
        return False
    else:
        justify[fact] = jst
        return True

def addUnjustified(a, op, b):
    error(u'The fact "{0}" is not justified.'.format(printFact(a, op, b)))

def addFact(a, op, b, jst, cplx):
    fact = (a, op, b)
    if not addJustification(fact, jst, cplx):
        return False
    
    if op[1] == u'->': # reduction
        r = op[0]
        addReduction(a, r, b)
        for x in Reduction.list(Reduction.weaker(r)):
            if x == r: continue
            
            addJustification((a, (x, op[1]), b),
                             (fact,), 1 + cplx)
            if Reduction.isPresent(x, notImplies[(a,b)]):
                error(u'The following facts are contradictory.\n\n' + 
                        printJustification((a,(x,u'->'),b), justify) + u'\n\n' + 
                        printJustification((a,(x,u'-|>'),b), justify))
    elif op[1] == u'-|>': # non-reduction
        r = op[0]
        addNonReduction(a, r, b)
        for x in Reduction.list(Reduction.stronger(r)):
            if x == r: continue
            
            addJustification((a, (x, op[1]), b),
                             (fact,), 1 + cplx)
            if Reduction.isPresent(x, implies[(a,b)]):
                error(u'The following facts are contradictory.\n\n' + 
                        printJustification((a,(x,u'->'),b), justify) + u'\n\n' + 
                        printJustification((a,(x,u'-|>'),b), justify))
    elif op[1] == u'<->': # equivalence
        addJustification((b, op, a), jst, cplx)
        
        r = op[0]
        addFact(a, (op[0], u'->'), b,
                (fact,), 1 + cplx)
        addFact(b, (op[0], u'->'), a,
                (fact,), 1 + cplx)
    elif op[1] == u'c': # conservation
        frm = op[0]
        addConservative(a, frm, b)
        for x in Form.list(Form.stronger(frm)):
            if x == frm: continue
            
            addJustification((a, (x, op[1]), b),
                             (fact,), 1 + cplx)
            if Reduction.isPresent(x, nonConservative[(a,b)]):
                error(u'The following facts are contradictory.\n\n' + 
                        printJustification((a,(x,u'c'),b), justify) + u'\n\n' + 
                        printJustification((a,(x,u'nc'),b), justify))
    elif op[1] == u'nc': # non-conservation
        frm = op[0]
        addNonConservative(a, frm, b)
        for x in Form.list(Form.weaker(frm)):
            if x == frm: continue
            
            addJustification((a, (x, op[1]), b),
                             (fact,), 1 + cplx)
            if Reduction.isPresent(x, conservative[(a,b)]):
                error(u'The following facts are contradictory.\n\n' + 
                        printJustification((a,(x,u'c'),b), justify) + u'\n\n' + 
                        printJustification((a,(x,u'nc'),b), justify))
    else:
        error(u'Unrecognized operator {0}'.format(op))
    
    return True

def standardizePrinciple(a):
    return u'+'.join(sorted(set(a.split(u'+'))))
def standardizeFact(a, op, b):
    a = standardizePrinciple(a)
    if op != u'form':
        b = standardizePrinciple(b)
        if op[1] == u'<=':
            op = (op[0], u'->')
            a,b = b,a
        elif op[1] == u'</=':
            op = (op[0], u'-|>')
            a,b = b,a
    return a, op, b

from pyparsing import *
def parseDatabase(databaseString, quiet=False):
    start = time.clock()
    if not quiet: eprint(u'Parsing results...')
    # Name parsed strings
    name = Word( alphas+"_+^{}\\$", alphanums+"_+^{}$\\").setParseAction(lambda s,l,t: addPrinciple(t[0]))
    
    parenth = Literal('"')
    justification = QuotedString('"""',multiline=True) | quotedString.setParseAction(removeQuotes)
    
    _reductionName = NoMatch()
    for r in Reduction:
        if r != Reduction.none:
            _reductionName |= Literal(r.name)
    _reductionType = _reductionName.setParseAction(lambda s,l,t: [Reduction.fromString(t[0])])
    reductionType = Optional(_reductionType, default=Reduction.RCA)
    postfixReductionType = Optional(Suppress(Literal("_")) + _reductionType, default=Reduction.RCA)
    
    implication = (reductionType + Literal("->")) | (Literal("=>") + postfixReductionType).setParseAction(lambda s,l,t: [t[1], "->"])
    nonImplication = (reductionType + Literal("-|>")) | (Literal("=/>") + postfixReductionType).setParseAction(lambda s,l,t: [t[1], "-|>"])
    equivalence = (reductionType + Literal("<->")) | (Literal("<=>") + postfixReductionType).setParseAction(lambda s,l,t: [t[1], "<->"])
    
    reduction = (Literal("<=") + postfixReductionType).setParseAction(lambda s,l,t: [t[1], "<="])
    nonReduction = (Literal("</=") + postfixReductionType).setParseAction(lambda s,l,t: [t[1], "</="])
    
    _formName = NoMatch()
    for f in Form:
        if f != Form.none:
            _formName |= Literal(f.name)
    formType = _formName.setParseAction(lambda s,l,t: [Form.fromString(t[0])])
    
    conservation = formType + Literal("c")
    nonConservation = (Literal("n") + formType + Literal("c")).setParseAction(lambda s,l,t: [t[1], "nc"])
    
    operator = implication | nonImplication | reduction | nonReduction | equivalence | conservation | nonConservation
    
    # Database lines
    unjustified = (name + Group(operator) + name + ~justification).setParseAction(lambda s,l,t: addUnjustified(*standardizeFact(t[0], tuple(t[1]), t[2])))
    
    def _addFactParseAction(s,l,t):
        a,op,b = standardizeFact(t[0], tuple(t[1]), t[2])
        addFact(a, op, b, t[3], 1)
    fact = (name + Group(operator) + name + justification).setParseAction(_addFactParseAction)

    formDef = (name + Literal("form") + formType).setParseAction(lambda s,l,t: addForm(t[0], t[2]))
    primary = (name + Literal("is primary")).setParseAction(lambda s,l,t: addPrimary(t[0]))
    
    comments = Suppress(Literal( "#" ) + SkipTo(LineEnd()))
    
    # Represent and parse database file
    entry = fact | formDef | primary | unjustified | comments
    database = ZeroOrMore( entry ) + StringEnd()
    
    database.parseString(databaseString)
    
    global principlesList
    principlesList = sorted(principles)
    
    if not quiet: eprint(u'Principles found: {0:,d}'.format(len(principlesList)))
    if not quiet: eprint(u'Elapsed: {0:.6f} s\n'.format(time.clock() - start))

# No inputs; affects '->' and 'c'.
def addTrivialFacts():
    for a in principlesList:
        for r in Reduction:
            addFact(a, (r, u'->'), a, u'', 1)
            addFact(a, (r, u'<->'), a, u'', 1)
        for f in Form:
            addFact(a, (f, u'c'), a, u'', 1)
        if a != u'RCA':
            for r in Reduction:
                addFact(a, (r, u'->'), u'RCA', u'', 1)

# No inputs; affects '->'
def weakenConjunctions():
    for a in principlesList:
        splitA = a.split(u'+')
        if len(splitA) == 1: continue # a is not a conjunction
        setA = set(splitA)
        
        for b in principlesList:
            if a == b: continue
            
            splitB = b.split(u'+')
            if len(splitB) >= len(splitA): continue # b cannot be a strict subset of a
            setB = set(splitB)
            
            if setB <= setA:
                for r in Reduction:
                    addFact(a, (r, u'->'), b, u'', 1)

# Uses '->', affects '->'
def reductionConjunction(): # Conjunctions follow from their conjuncts
    r = False
    for b in principlesList:
        splitB = b.split(u'+')
        if len(splitB) == 1: continue # b is not a conjunction
        setB = set(splitB)
        
        for a in principlesList:
            if a == b: continue
            
            conj = ~0
            for x in splitB:
                conj &= implies[(a,x)]
            if conj == Reduction.none: continue
            
            for x in Reduction.list(conj):
                aImpConjuncts = tuple([(a, (x, u'->'), t) for t in splitB])
                r |= addFact(a, (x, u'->'), b,
                             aImpConjuncts, sum(justComplexity[aImpX] for aImpX in aImpConjuncts))
    return r

# Complete (current) transitive closure of array, using Floyd-Warshall
def transitiveClosure(cls, array, opName): # Take the transitive closure
    r = False
    for c in principlesList:
        for a in principlesList:
            if a == c: continue
            
            acRelation = array[(a,c)]
            if acRelation == cls.none: continue
            
            for b in principlesList:
                if b == a or b == c: continue
                
                transitive = acRelation & array[(c,b)]
                if transitive == cls.none: continue
                
                for x in cls.list(transitive):
                    op = (x, opName)
                    aOpC = (a, op, c)
                    cOpB = (c, op, b)
                    
                    r |= addFact(a, op, b,
                                 (aOpC, cOpB), 1 + justComplexity[aOpC] + justComplexity[cOpB])
    return r

# Uses '->' and 'c', affects 'c'
def liftConservation(): # Lift conservation facts over known implications
    r = False
    for c in principlesList:
        for a in principlesList:
            if a == c:
                # If b implies a, then a is conservative over b
                for b in principlesList:
                    if b == a: continue
                    
                    if Reduction.isPresent(Reduction.RCA, implies[(b,a)]):
                        for x in Form:
                            bImpA = (b, (Reduction.RCA, u'->'), a)
                            
                            r |= addFact(a, (x, u'c'), b,
                                         (bImpA,), 1 + justComplexity[bImpA])
                continue
            
            # If c is conservative over b, and c implies a, then a is conservative over b.
            if Reduction.isPresent(Reduction.RCA, implies[(c,a)]):
                cImpA = (c, (Reduction.RCA, u'->'), a)
                cplxCImpA = justComplexity[cImpA]
                
                for b in principlesList:
                    if b == a or b == c: continue
                    
                    cbConservative = conservative[(c,b)]
                    if cbConservative != Form.none:
                        for x in Form.list(cbConservative):
                            cConsB = (c, (x, u'c'), b)
                            
                            r |= addFact(a, (x, u'c'), b,
                                         (cConsB, cImpA), 1 + justComplexity[cConsB] + cplxCImpA)
            
            # If a is conservative over c, and b implies c, then a is conservative over b.
            acConservative = conservative[(a,c)]
            if acConservative != Form.none:
                acConservativeForms = Form.list(acConservative)
                aConsCForms = [(a, (x, u'c'), c) for x in acConservativeForms]
                cplxAConsC = [justComplexity[aConsC] for aConsC in aConsCForms]
                acLoop = list(zip(acConservativeForms, aConsCForms, cplxAConsC))
                
                for b in principlesList:
                    if b == a or b == c: continue
                    
                    if Reduction.isPresent(Reduction.RCA, implies[(b,c)]):
                        for x,aConsC,cplxAC in acLoop:
                            bImpC = (b, (Reduction.RCA, u'->'), c)
                            
                            r |= addFact(a, (x, u'c'), b,
                                         (aConsC, bImpC), 1 + cplxAC + justComplexity[bImpC])
    return r

# Uses '->' and 'c', affects '->'
def implementPositiveConservation(): # Apply known conservation facts to implications
    r = False
    for c in principlesList:
        for a in principlesList:
            if a == c: continue
            
            caConservative = conservative[(c,a)]
            if caConservative == Form.none: continue
            for b in principlesList:
                if b == a: continue
                if b == c:
                    # If b is (form)-conservative over a and b is a (form) statement, then a implies b.
                    frms = form[b] & caConservative
                    if frms != Form.none:
                        for x in Form.list(frms):
                            bConsA = (b, (x, u'c'), a)
                            r |= addFact(a, (Reduction.RCA, u'->'), b,
                                         (bConsA, (b, u'form', x)), 2 + justComplexity[bConsA])
                    continue
                
                # If c is (form)-conservative over a, c implies b, and b is a (form) statement, then a implies b.
                frms = form[b] & caConservative
                if frms != Form.none and Reduction.isPresent(Reduction.RCA, implies[(c,b)]):
                    for x in Form.list(frms):
                        cImpB = (c, (Reduction.RCA, u'->'), b)
                        cConsA = (c, (x, u'c'), a)
                        r |= addFact(a, (Reduction.RCA, u'->'), b,
                                     (cImpB, cConsA, (b, u'form', x)), 2 + justComplexity[cImpB] + justComplexity[cConsA])
    return r

# Uses '->', affects ONLY justify
def extractEquivalences(): # Convert bi-implications to equivalences
    r = False
    for a in principlesList:
        for b in principlesList:
            if b == a: continue
            
            equiv = implies[(a,b)] & implies[(b,a)]
            if equiv == Reduction.none: continue
            
            for x in Reduction.list(equiv):
                aImpB = (a, (x, u'->'), b)
                bImpA = (b, (x, u'->'), a)
                r |= addFact(a, (x, u'<->'), b,
                             (aImpB, bImpA), 1 + justComplexity[aImpB] + justComplexity[bImpA])
    return r

# Uses '-|>' and '->', affects '-|>'
def conjunctionSplit(): # Split non-implications over conjunctions
    r = False
    for b in principlesList:
        splitB = b.split(u'+')
        setB = set(splitB)
        for c in principlesList:
            if b == c: continue
            
            splitC = c.split(u'+')
            setC = set(splitC)
            
            setBC = setB | setC
            bc = u'+'.join(sorted(setBC))
            if bc not in principles: continue
            
            for a in principlesList:
                splitImp = notImplies[(a,bc)] & implies[(a,c)]
                if splitImp == Reduction.none: continue
                
                # If a does not imply b+c, but a implies c, then a does not imply b.
                for x in Reduction.list(splitImp):
                    aNImpBC = (a, (x, u'-|>'), bc)
                    aImpC = (a, (x, u'->'), c)
                    r |= addFact(a, (x, u'-|>'), b,
                                 (aNImpBC, aImpC), 1 + justComplexity[aNImpBC] + justComplexity[aImpC])
    return r

# Uses '->' and '-|>', affects '-|>'
def nonImplicationClosure(): # "transitive" non-implications
    r = False
    for c in principlesList:
        for a in principlesList:
            if a == c: continue
            
            # If c implies a, but c does not imply b, then a does not imply b
            cImpliesA = implies[(c,a)]
            if cImpliesA != Reduction.none:
                for b in principlesList:
                    if b == a or b == c: continue
                    
                    abClosure = cImpliesA & notImplies[(c,b)]
                    if abClosure != Reduction.none:
                        for x in Reduction.list(abClosure):
                            cImpA = (c, (x, u'->'), a)
                            cNImpB = (c, (x, u'-|>'), b)
                            
                            r |= addFact(a, (x, u'-|>'), b,
                                         (cImpA, cNImpB), 1 + justComplexity[cImpA] + justComplexity[cNImpB])
            
            # If a does not imply c, but b implies c, then a does not imply b
            aNotImpliesC = notImplies[(a,c)]
            if aNotImpliesC != Reduction.none:
                for b in principlesList:
                    if b == a or b == c: continue
                    
                    abClosure = aNotImpliesC & implies[(b,c)]
                    if abClosure != Reduction.none:
                        for x in Reduction.list(abClosure):
                            aNImpC = (a, (x, u'-|>'), c)
                            bImpC = (b, (x, u'->'), c)
                            
                            r |= addFact(a, (x, u'-|>'), b,
                                         (aNImpC, bImpC), 1 + justComplexity[aNImpC] + justComplexity[bImpC])
    return r

# Uses '-|>' and 'c', affects '-|>'
def implementNegativeConservation(): # Apply known conservation facts to non-implications
    r = False
    for c in principlesList:
        for b in principlesList:
            if b == c: continue
            
            formB = form[b]
            if formB == Form.none: continue
            if Reduction.isPresent(Reduction.RCA, notImplies[(c,b)]): # c does not imply b
                for a in principlesList:
                    if a == b or a == c: continue
                    
                    # If c does not imply b, b is (form), and a is (form)-conversative over c, then a does not imply b.
                    frms = form[b] & conservative[(a,c)]
                    for x in Form.list(frms):
                        cImpB = (c, (Reduction.RCA, u'-|>'), b)
                        aConsC = (a, (x, u'c'), c)
                        r |= addFact(a, (Reduction.RCA, u'-|>'), b,
                                     (cImpB, aConsC, (b, u'form', x)), 2 + justComplexity[cImpB] + justComplexity[aConsC])
    return r

# Uses '->' and '-|>', affects 'nc'
def extractNonConservation(): # Transfer non-implications to non-conservation facts
    r = False
    for c in principlesList:
        cForm = form[c]
        if cForm == Form.none: continue
        cForms = Form.list(cForm)
        for a in principlesList:
            if a == c:
                for b in principlesList:
                    if b == a: continue
                    
                    # If b does not imply a, and a is (form), then a is not (form)-conservative over b.
                    if Reduction.isPresent(Reduction.RCA, notImplies[(b,a)]):
                        bNImpA = (b, (Reduction.RCA, u'-|>'), a)
                        for x in cForms:
                            r |= addFact(a, (x, u'nc'), b,
                                         (bNImpA, (a, u'form', x)), 2 + justComplexity[bNImpA])
                continue
            # If a implies c, but b does not imply c, and c is (form), then a is not (form)-conservative over b.
            if Reduction.isPresent(Reduction.RCA, implies[(a,c)]):
                aImpC = (a, (Reduction.RCA, u'->'), c)
                for b in principlesList:
                    if b == a or b == c: continue
                    
                    if Reduction.isPresent(Reduction.RCA, notImplies[(b,c)]):
                        bNImpC = (b, (Reduction.RCA, u'-|>'), c)
                        for x in cForms:
                            r |= addFact(a, (x, u'nc'), b,
                                         (aImpC, bNImpC, (c, u'form', x)), 2 + justComplexity[aImpC] + justComplexity[bNImpC])
    return r

# Uses 'nc' and '->', affects 'nc'
def liftNonConservation(): # Lift non-conservation facts over known implications
    r = False
    for c in principlesList:
        for a in principlesList:
            if a == c: continue
            
            # If a implies c, and c is not conservative over b, then a is not conservative over b.
            if Reduction.isPresent(Reduction.RCA, implies[(a,c)]):
                aImpC = (a, (Reduction.RCA, u'->'), c)
                cplxAImpC = justComplexity[aImpC]
                
                for b in principlesList:
                    if b == a or b == c: continue
                    
                    cbNonConservative = nonConservative[(c,b)]
                    if cbNonConservative != Form.none:
                        for x in Form.list(cbNonConservative):
                            cNConsB = (c, (x, u'nc'), b)
                            
                            r |= addFact(a, (x, u'nc'), b,
                                         (aImpC, cNConsB), 1 + cplxAImpC + justComplexity[cNConsB])
            
            # If a is not conservative over c, and c implies b, then a is not conservative over b.
            acNonConservative = nonConservative[(a,c)]
            if acNonConservative != Form.none:
                acNonConservativeForms = Form.list(acNonConservative)
                aNConsCForms = [(a, (x, u'nc'), c) for x in acNonConservativeForms]
                cplxANConsC = [justComplexity[aNConsC] for aNConsC in aNConsCForms]
                acLoop = list(zip(acNonConservativeForms, aNConsCForms, cplxANConsC))
                
                for b in principlesList:
                    if b == a or b == c: continue
                
                    if Reduction.isPresent(Reduction.RCA, implies[(c,b)]):
                        for x,aNConsC,cplxAC in acLoop:
                            cImpB = (c, (Reduction.RCA, u'->'), b)
                            
                            r |= addFact(a, (x, u'nc'), b,
                                         (aNConsC, cImpB), 1 + cplxAC + justComplexity[cImpB])
    return r

# Uses 'c' and 'nc', affects 'nc'
def conservationConflict():
    r = False
    for c in principlesList:
        for a in principlesList:
            if a == c: continue
            
            acNonConservative = nonConservative[(a,c)]
            for b in principlesList:
                if b == a or b == c: continue
                
                # If a is not conservative over c, but b is conservative over c, then a is not conservative over b.
                conflict = acNonConservative & conservative[(b,c)]
                if conflict == Form.none: continue
                for x in Form.list(conflict):
                    aNConsC = (a, (x, u'nc'), c)
                    bConsC = (b, (x, u'c'), c)
                    
                    r |= addFact(a, (x, u'nc'), b,
                                 (aNConsC, bConsC), 1 + justComplexity[aNConsC] + justComplexity[bConsC])
    return r

# Uses 'nc', affects '-|>'
def extractNonImplication(): # Transfer non-conservation facts to non-implications
    r = False
    for a in principlesList:
        for b in principlesList:
            if b == a: continue
            
            # If b is not conservative over a, then a does not imply b.
            baNonConservative = nonConservative[(b,a)]
            if baNonConservative == Form.none: continue
            for x in Form.list(baNonConservative):
                bNConsA = (b, (x, u'nc'), a)
                r |= addFact(a, (Reduction.RCA, u'-|>'), b,
                             (bNConsA,), 1 + justComplexity[bNConsA])
    return r

def deriveInferences(quiet=False):
    start = time.clock()
    if not quiet: eprint(u'Adding trivial facts...')
    addTrivialFacts()
    if not quiet: eprint(u'Weakening conjunctions...')
    weakenConjunctions()
    if not quiet: eprint(u'Elapsed: {0:.6f} s\n'.format(time.clock() - start))
    
    start = time.clock()
    if not quiet: eprint(u'Looping over implications and conservation facts:')
    i,c = True,True # implies updated and conservative updated
    n = 0
    while i or c:
        n += 1
        
        io = i
        co = c
        i,c = False,False
        
        if io:
            if not quiet: eprint(u'Reducing implications over conjunctions...')
            i |= reductionConjunction() # Uses '->', affects '->'
            
            if not quiet: eprint(u'Finding transitive implications...')
            i |= transitiveClosure(Reduction, implies, u'->') # Uses '->', affects '->'
        if co:
            if not quiet: eprint(u'Finding transitive conservation facts...')
            c |= transitiveClosure(Form, conservative, u'c') # Uses 'c', affects 'c'
        
        if not quiet: eprint(u'Lifting conservation facts over known implications...')
        c |= liftConservation() # Uses '->' and 'c', affects 'c'
        
        if not quiet: eprint(u'Applying known conservation facts...')
        i |= implementPositiveConservation() # Uses '->' and 'c', affects '->'
    if not quiet: eprint(u'Finished with implications and conservation facts.')
    if not quiet: eprint(u'Elapsed: {0:.6f} s (with {1} repeats)\n'.format(time.clock() - start, n))
    
    start = time.clock()
    if not quiet: eprint(u'Extracting equivalences...')
    extractEquivalences()
    if not quiet: eprint(u'Elapsed: {0:.6f} s\n'.format(time.clock() - start))
    
    start = time.clock()
    if not quiet: eprint(u'Looping over non-implications and conservation facts:')
    ni,nc = True,True # notImplies updated and nonConservative updated
    n = 0
    while ni or nc:
        n += 1
        
        nio = ni
        nco = nc
        ni,nc = False,False
        
        if nio:
            if not quiet: eprint(u'Splitting over conjunctions...')
            ni |= conjunctionSplit() # Uses '-|>' and '->', affects '-|>'
            
            if not quiet: eprint(u'Closing over implications...')
            ni |= nonImplicationClosure() # Uses '->' and '-|>', affects '-|>'
            
            if not quiet: eprint(u'Applying known conservation facts to non-implications...')
            ni |= implementNegativeConservation() # Uses '-|>' and 'c', affects '-|>'
            
            if not quiet: eprint(u'Extracting non-conservation facts...')
            nc |= extractNonConservation() # Uses '->' and '-|>', affects 'nc'
        
        if nco:
            if not quiet: eprint(u'Lifting non-conservation facts over implications...')
            nc |= liftNonConservation() # Uses 'nc' and '->', affects 'nc'
            
            if not quiet: eprint(u'Lifting non-conservation facts over conservations...')
            nc |= conservationConflict() # Uses 'c' and 'nc', affects 'nc'
            
            if not quiet: eprint(u'Extracting non-implications...')
            ni |= extractNonImplication() # Uses 'nc', affects '-|>'
    if not quiet: eprint(u'Finished with non-implications and non-conservation facts.')
    if not quiet: eprint(u'Elapsed: {0:.6f} s (with {1} repeats)\n'.format(time.clock() - start, n))

def getDatabase():
    return {'version': Version,
            'principles': principles,
            'implication': (implies, notImplies),
            'conservation': (conservative, nonConservative),
            'form': form,
            'primary': (primary, primaryIndex),
            'justify': justify}

def setDatabase(shelf):
    if shelf['version'] != Version:
        raise VersionError(shelf['version'], Version)
    
    global principles, principlesList
    principles = shelf['principles']
    principlesList = sorted(principles)
    
    global implies, notImplies
    implies, notImplies = shelf['implication']
    
    global conservative, nonConservative
    conservative, nonConservative = shelf['conservation']
    
    global form
    form = shelf['form']
    
    global primary, primaryIndex
    primary, primaryIndex = shelf['primary']
    
    global justify
    justify = shelf['justify']

def dumpDatabase(shelfTitle, quiet=False):
    if not quiet: eprint(u'Facts known: {0:,d}\n'.format(len(justify)))
    
    start = time.clock()
    if not quiet: eprint(u'Dumping updated database to binary file...')
    with closingWrapper(shelve.open(shelfTitle, flag='n', protocol=2)) as shelf:
        shelf['version'] = Version
        shelf['principles'] = principles
        shelf['primary'] = (primary, primaryIndex)
        shelf['form'] = form
        shelf['implication'] = (implies, notImplies)
        shelf['conservation'] = (conservative, nonConservative)
        shelf['justify'] = justify
    if not quiet: eprint(u'Elapsed: {0:.6f} s\n'.format(time.clock() - start))

def loadDatabase(shelfFile, quiet=False):
    with closingWrapper(shelve.open(shelfFile, flag='r', protocol=2)) as shelf:
        setDatabase(shelf)

from optparse import OptionParser, OptionGroup
def main():
    absoluteStart = time.clock()
    eprint(u'\nRM Zoo (v{0})\n'.format(Version))
    
    parser = OptionParser(u'Usage: %prog [options] results [database_title]', version=u'%prog {0} ({1})'.format(Version, Date))
    
    parser.set_defaults(quiet=False, verbose=False)
    
    parser.add_option('-q', action='store_true', dest='quiet',
        help = u'Suppress progress/timing indicators.')
    parser.add_option('-v', action='store_true', dest='verbose',
        help = u'Report additional execution information.')
    
    (options, args) = parser.parse_args()
    if len(args)>2:
        parser.error(u'Too many arguments provided.')
    if len(args)<1:
        parser.error(u'No results file specified.')
    
    if options.quiet and options.verbose:
        parser.error(u'Options -q and -v are incompatible.')
    
    import os
    resultsFile = args[0]
    if len(args) > 1:
        shelfTitle = args[1]
    else:
        eprint(u'No database title specified; defaulting to "database".')
        shelfTitle = 'database'
    
    if not os.path.exists(resultsFile):
        parser.error(u'Results file "{0}" does not exist.'.format(resultsFile))
    
    with open(resultsFile, encoding='utf-8') as f:
        parseDatabase(f.read(), options.quiet)
    deriveInferences(options.quiet)
    dumpDatabase(shelfTitle, options.quiet)
    if not options.quiet: eprint(u'Total elapsed time: {0:.6f} s'.format(time.clock() - absoluteStart))
    
    if options.verbose:
        eprint(u'\nCache report: ')
        eprint(u'\tReduction.strongest: {0}'.format(Reduction.strongest.cache_info()))
        eprint(u'\tReduction.list: {0}'.format(Reduction.list.cache_info()))
        eprint(u'\tForm.strongest: {0}'.format(Form.strongest.cache_info()))
        eprint(u'\tForm.list: {0}'.format(Form.list.cache_info()))
        eprint(u'\tprintOp: {0}'.format(printOp.cache_info()))

if __name__ == '__main__':
    main()