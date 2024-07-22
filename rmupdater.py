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
#   - Version 5.0 - clean implementation of inference rules, started 1 August 2016
#   - Version 5.1 - reverted from shelf database for cross-platform compatibility, started 16 August 2016
#   Documentation and support: http://rmzoo.uconn.edu
#
##################################################################################

from __future__ import print_function

import itertools
import sys
import time
import os

from io import open
from collections import defaultdict
from typing import Any, DefaultDict, Tuple, List, Set, Type

import zlib
import pickle

from pyparsing import (
    Word,
    alphas,
    alphanums,
    Literal,
    NoMatch,
    Optional,
    Group,
    ZeroOrMore,
    StringEnd,
    SkipTo,
    LineEnd,
    quotedString,
    QuotedString,
    removeQuotes,
    Suppress,
)

from rmBitmasks import Form, Reduction, noForm, noReduction
from renderJustification import printFact, printJustification

from optparse import OptionParser


Date: str = "16 August 2016"
Version: str = "5.1"
DatabaseVersion: str = "5.1"

timekeeper = time.perf_counter

RCAprinciple: str = "RCA"

principlesList: List[str] = [RCAprinciple]
principles: Set[str] = set(principlesList)


def eprint(*args: Any, **kwargs: Any) -> None:
    print(*args, file=sys.stderr, **kwargs)


def addPrinciple(a: str) -> str:
    setA = set(a.split("+"))
    a = "+".join(sorted(setA))
    principles.add(a)
    principles.update(setA)
    return a


conjunction: dict[Tuple[str, str], str] = {}


def joinPrinciples(a: str, b: str) -> str:
    try:
        return conjunction[a, b]
    except KeyError:
        p = "+".join(sorted(set(a.split("+")) | set(b.split("+"))))
        if p not in principles:
            p = None
        conjunction[a, b] = p
        conjunction[b, a] = p
        return p


equivalent: DefaultDict[Tuple[str, str], Reduction] = defaultdict(noReduction)
implies: DefaultDict[Tuple[str, str], Reduction] = defaultdict(noReduction)
notImplies: DefaultDict[Tuple[str, str], Reduction] = defaultdict(noReduction)


def addEquivalent(a: str, reduction: Reduction, b: str) -> None:
    equivalent[a, b] |= Reduction.weaker(reduction)


def addReduction(a: str, reduction: Reduction, b: str) -> None:
    implies[a, b] |= Reduction.weaker(reduction)


def addNonReduction(a: str, reduction: Reduction, b: str) -> None:
    notImplies[a, b] |= Reduction.stronger(reduction)


conservative: DefaultDict[Tuple[str, str], Form] = defaultdict(noForm)
nonConservative: DefaultDict[Tuple[str, str], Form] = defaultdict(noForm)


def addConservative(a: str, frm: Form, b: str) -> None:
    conservative[a, b] |= Form.stronger(frm)


def addNonConservative(a: str, frm: Form, b: str) -> None:
    nonConservative[a, b] |= Form.weaker(frm)


form: DefaultDict[str, Form] = defaultdict(noForm)

primary: Set[str] = set()
primaryIndex: List[str] = []


def addForm(a: str, frm: Form) -> None:
    form[a] |= Form.weaker(frm)


def addPrimary(a: str) -> None:
    primary.add(a)
    primaryIndex.append(a)


justify: dict[Tuple[str, Tuple[Any, str], str], Any] = {}
justComplexity: dict[Tuple[str, Tuple[Any, str], str], int] = {}


def updateJustification(
    fact: Tuple[str, Tuple[Any, str], str], jst: Any, cplx: int
) -> bool:
    try:
        if cplx >= justComplexity[fact]:
            return False
    except KeyError:
        pass
    justify[fact] = jst
    justComplexity[fact] = cplx
    return True


class UnjustifiedFactError(Exception):
    def __init__(self, a: str, op: Tuple[Any, str], b: str):
        super().__init__(f'The fact "{printFact(a, op, b)}" is not justified.')


def addUnjustified(a: str, op: Tuple[Any, str], b: str) -> None:
    raise UnjustifiedFactError(a, op, b)


class ContradictionError(Exception):
    def __init__(
        self,
        fact1: Tuple[str, Tuple[Any, str], str],
        fact2: Tuple[str, Tuple[Any, str], str],
    ):
        super().__init__(
            "The following facts are contradictory:\n\n"
            + printJustification(fact1, justify)
            + "\n\n"
            + printJustification(fact2, justify)
        )


def addFact(a: str, op: Tuple[Any, str], b: str, jst: Any, cplx: int) -> bool:
    fact = (a, op, b)
    if not updateJustification(fact, jst, cplx):
        return False
    opCtx, opCore = op

    ref = (fact,)
    refCplx = 1 + cplx

    if opCore == "<->":
        updateJustification((b, op, a), jst, cplx)

        for x in Reduction.list(Reduction.weaker(opCtx)):
            newOp = (x, "<->")

            addEquivalent(a, x, b)
            updateJustification((a, newOp, b), ref, refCplx)

            addEquivalent(b, x, a)
            updateJustification((b, newOp, a), ref, refCplx)

        impliesOp = (opCtx, "->")
        addFact(a, impliesOp, b, (fact,), refCplx)
        addFact(b, impliesOp, a, (fact,), refCplx)
    elif opCore == "->":
        for x in Reduction.list(Reduction.weaker(opCtx)):
            addReduction(a, x, b)
            updateJustification((a, (x, "->"), b), ref, refCplx)

            if Reduction.isPresent(x, notImplies[a, b]):
                raise ContradictionError((a, (x, "->"), b), (a, (x, "-|>"), b))

            if x == Reduction.RCA:
                if x == opCtx:
                    newRef = ref
                    newRefCplx = refCplx
                else:
                    newRef = ((a, (x, "->"), b),)
                    newRefCplx = 1 + refCplx

                for f in Form:
                    if f != Form.none:
                        addFact(b, (f, "c"), a, newRef, newRefCplx)

        ab = joinPrinciples(a, b)
        if ab is not None:
            addFact(a, (opCtx, "<->"), ab, ref, refCplx)
    elif opCore == "-|>":
        for x in Reduction.list(Reduction.stronger(opCtx)):
            addNonReduction(a, x, b)
            updateJustification((a, (x, "-|>"), b), ref, refCplx)

            if Reduction.isPresent(x, implies[a, b]):
                raise ContradictionError((a, (x, "-|>"), b), (a, (x, "->"), b))

            if x == Reduction.RCA:
                if x == opCtx:
                    newFact = fact
                    newCplx = 1 + refCplx
                else:
                    newFact = (a, (x, "-|>"), b)
                    newCplx = 2 + refCplx

                for f in Form.list(form[b]):
                    addFact(b, (f, "nc"), a, (newFact, (b, "form", f)), newCplx)
    elif opCore == "c":
        for f in Form.list(Form.stronger(opCtx)):
            newFact = (a, (f, "c"), b)

            addConservative(a, f, b)
            updateJustification(newFact, ref, refCplx)

            if Form.isPresent(f, nonConservative[a, b]):
                raise ContradictionError((a, (f, "c"), b), (a, (f, "nc"), b))

            if Form.isPresent(f, form[a]):
                if f == opCtx:
                    newCplx = 1 + refCplx
                else:
                    newCplx = 2 + refCplx

                addFact(b, (Reduction.RCA, "->"), a, (newFact, (a, "form", f)), newCplx)
    elif opCore == "nc":
        for f in Form.list(Form.weaker(opCtx)):
            addNonConservative(a, f, b)
            updateJustification((a, (f, "nc"), b), ref, refCplx)

            if Form.isPresent(f, conservative[a, b]):
                raise ContradictionError((a, (f, "nc"), b), (a, (f, "c"), b))

        addFact(b, (Reduction.RCA, "-|>"), a, ref, refCplx)
    else:
        raise ValueError(f"Unrecognized operator: {opCore}")

    return True


def standardizePrinciple(a: str) -> str:
    return "+".join(sorted(set(a.split("+"))))


def standardizeFact(
    a: str, op: Tuple[Any, str], b: str
) -> Tuple[str, Tuple[Any, str], str]:
    a = standardizePrinciple(a)
    if op != "form":
        b = standardizePrinciple(b)
        if op[1] == "<=":
            op = (op[0], "->")
            a, b = b, a
        elif op[1] == "</=":
            op = (op[0], "-|>")
            a, b = b, a
    return a, op, b


def parseResults(resultsString, quiet=False):
    start = timekeeper()
    if not quiet:
        eprint("Parsing results...")
    # Name parsed strings
    name = Word(alphas + "_+^{}\\$", alphanums + "_+^{}$\\").setParseAction(
        lambda s, l, t: addPrinciple(t[0])
    )

    justification = QuotedString('"""', multiline=True) | quotedString.setParseAction(
        removeQuotes
    )

    _reductionName = NoMatch()
    for r in Reduction:
        if r != Reduction.none:
            _reductionName |= Literal(r.name)
    for r in Reduction.alias:
        if r != "":
            _reductionName |= Literal(r)
    _reductionType = _reductionName.setParseAction(
        lambda s, l, t: [Reduction.fromString(t[0])]
    )
    reductionType = Optional(_reductionType, default=Reduction.RCA)
    postfixReductionType = Optional(
        Suppress(Literal("_")) + _reductionType, default=Reduction.RCA
    )

    implication = (reductionType + Literal("->")) | (
        Literal("=>") + postfixReductionType
    ).setParseAction(lambda s, l, t: [t[1], "->"])
    nonImplication = (reductionType + Literal("-|>")) | (
        Literal("=/>") + postfixReductionType
    ).setParseAction(lambda s, l, t: [t[1], "-|>"])
    equivalence = (reductionType + Literal("<->")) | (
        Literal("<=>") + postfixReductionType
    ).setParseAction(lambda s, l, t: [t[1], "<->"])

    reduction = (Literal("<=") + postfixReductionType).setParseAction(
        lambda s, l, t: [t[1], "<="]
    )
    nonReduction = (Literal("</=") + postfixReductionType).setParseAction(
        lambda s, l, t: [t[1], "</="]
    )

    _formName = NoMatch()
    for f in Form:
        if f != Form.none:
            _formName |= Literal(f.name)
    formType = _formName.setParseAction(lambda s, l, t: [Form.fromString(t[0])])

    conservation = formType + Literal("c")
    nonConservation = (Literal("n") + formType + Literal("c")).setParseAction(
        lambda s, l, t: [t[1], "nc"]
    )

    operator = (
        implication
        | nonImplication
        | reduction
        | nonReduction
        | equivalence
        | conservation
        | nonConservation
    )

    # Results file lines
    unjustified = (name + Group(operator) + name + ~justification).setParseAction(
        lambda s, l, t: addUnjustified(*standardizeFact(t[0], tuple(t[1]), t[2]))
    )

    factsToAdd = []

    def _addFactParseAction(s, l, t):
        a, op, b = standardizeFact(t[0], tuple(t[1]), t[2])
        factsToAdd.append(((a, op, b), t[3]))

    fact = (name + Group(operator) + name + justification).setParseAction(
        _addFactParseAction
    )

    formDef = (name + Literal("form") + formType).setParseAction(
        lambda s, l, t: addForm(t[0], t[2])
    )
    primary = (name + Literal("is primary")).setParseAction(
        lambda s, l, t: addPrimary(t[0])
    )

    comments = Suppress(Literal("#") + SkipTo(LineEnd()))

    # Represent and parse results file
    entry = fact | formDef | primary | unjustified | comments
    results = ZeroOrMore(entry) + StringEnd()

    results.parseString(resultsString)

    global principlesList
    principlesList = sorted(principles)

    for (a, op, b), jst in factsToAdd:
        addFact(a, op, b, jst, 1)

    if not quiet:
        eprint("Principles found: {0:,d}".format(len(principlesList)))
    if not quiet:
        eprint("Elapsed: {0:.6f} s\n".format(timekeeper() - start))


# General fact; uses nothing, affects '<->', '->', and 'c'
def addReflexivities():
    for a in principlesList:
        for x in Reduction:
            if x == Reduction.none:
                continue

            # (a X-> a)
            addFact(a, (x, "->"), a, "reflexivity", 1)

            # (a X<-> a)
            addFact(a, (x, "<->"), a, "reflexivity", 1)

        for f in Form:
            if f == Form.none:
                continue

            # (a Fc a)
            addFact(a, (f, "c"), a, "reflexivity", 1)


# General fact; uses nothing, affects '->'
def addRCABottom():
    # (a X-> RCA)
    for a in principlesList:
        for x in Reduction:
            if x == Reduction.none:
                continue

            addFact(a, (x, "->"), RCAprinciple, "", 1)


# General fact; uses nothing, affects '->'
def definitionOfConjunction():
    # IF (a == b+...), THEN (a X-> b).
    for a in principlesList:
        splitA = set(a.split("+"))
        if len(splitA) == 1:
            continue

        for b in principlesList:
            if b == a:
                continue

            splitB = set(b.split("+"))
            if splitB <= splitA:
                for x in Reduction:
                    if x == Reduction.none:
                        continue

                    addFact(a, (x, "->"), b, "", 1)


# Uses '->', affects '<->'
def definitionOfEquivalence():
    # a X<-> b
    # WHEN
    #    (a X-> b) AND (b X-> a)

    r = False
    for a, b in itertools.combinations(principlesList, 2):
        equiv = implies[a, b] & implies[b, a]

        if equiv != Reduction.none:
            for x in Reduction.list(equiv):
                imp = (x, "->")
                aImpB = (a, imp, b)
                bImpA = (b, imp, a)

                r |= addFact(
                    a,
                    (x, "<->"),
                    b,
                    (aImpB, bImpA),
                    1 + justComplexity[aImpB] + justComplexity[bImpA],
                )
    return r


# Uses array, affects array
def transitiveClosure(
    array: DefaultDict[Any, Reduction], opName: str, clsCtx: Type[Reduction]
) -> bool:
    # Complete (current) transitive closure of array, using Floyd-Warshall

    r = False
    for c in principlesList:
        for a in principlesList:
            if a == c:
                continue

            acRelation = array[a, c]
            if acRelation == clsCtx.none:
                continue

            for b in principlesList:
                if b in (a, c):
                    continue

                transitive = acRelation & array[c, b]
                if transitive == clsCtx.none:
                    continue

                for x in clsCtx.list(transitive):
                    op = (x, opName)
                    aOpC = (a, op, c)
                    cOpB = (c, op, b)

                    r |= addFact(
                        a,
                        op,
                        b,
                        (aOpC, cOpB),
                        1 + justComplexity[aOpC] + justComplexity[cOpB],
                    )
    return r


# Uses '->', affects '->'
def unifyOverConjunctions():
    # a X-> b
    # WHEN
    #    (b == c+d) AND (a X-> c) AND (a X-> d) "Definition of conjunction"

    r = False
    for b in principlesList:
        splitB = b.split("+")
        if len(splitB) == 1:
            continue  # b is not a conjunction

        for a in principlesList:
            aImpliesAll = ~Reduction.none
            for p in splitB:
                aImpliesAll &= implies[a, p]
            if aImpliesAll == Reduction.none:
                continue

            for x in Reduction.list(aImpliesAll):
                aImpConjuncts = tuple([(a, (x, "->"), t) for t in splitB])
                r |= addFact(
                    a,
                    (x, "->"),
                    b,
                    aImpConjuncts,
                    1 + sum(justComplexity[aImpX] for aImpX in aImpConjuncts),
                )
    return r


# REDUNDANT
# Uses 'c' and '->', affects '->'
def definitionOfConservation():
    # a RCA-> b
    # WHEN
    #    (c Fc a) AND (c RCA-> b) AND (b has form F) "Definition of conservation"

    r = False
    for c in principlesList:
        for b in principlesList:
            if b == c:
                continue

            if Reduction.isPresent(Reduction.RCA, implies[c, b]):
                formB = form[b]
                if formB == Form.none:
                    continue

                cImpB = (c, (Reduction.RCA, "->"), b)
                refCplxCB = 2 + justComplexity[cImpB]

                for a in principlesList:
                    if a in (b, c):
                        continue

                    frms = formB & conservative[c, a]
                    if frms == Form.none:
                        continue

                    for f in Form.list(frms):
                        cConsA = (c, (f, "c"), a)

                        r |= addFact(
                            a,
                            (Reduction.RCA, "->"),
                            b,
                            (cConsA, cImpB, (b, "form", f)),
                            refCplxCB + justComplexity[cConsA],
                        )
    return r


# Uses posArray and negArray, affects negArray
def contrapositiveTransitivity(posArray, posOpName, negArray, negOpName, clsCtx):
    r = False
    for c in principlesList:
        for a in principlesList:
            if a == c:
                continue

            # a nop b
            # WHEN
            #    (c op a) AND (c nop b)
            caRelation = posArray[c, a]
            if caRelation != clsCtx.none:
                for b in principlesList:
                    if b == a or b == c:
                        continue

                    contexts = caRelation & negArray[c, b]
                    if contexts == clsCtx.none:
                        continue

                    for ctx in clsCtx.list(contexts):
                        nop = (ctx, negOpName)

                        cOpA = (c, (ctx, posOpName), a)
                        cNOpB = (c, nop, b)

                        r |= addFact(
                            a,
                            nop,
                            b,
                            (cOpA, cNOpB),
                            1 + justComplexity[cOpA] + justComplexity[cNOpB],
                        )

            # a nop b
            # WHEN
            #    (a nop c) AND (b op c)
            acNRelation = negArray[a, c]
            if acNRelation != clsCtx.none:
                for b in principlesList:
                    if b == a or b == c:
                        continue

                    contexts = acNRelation & posArray[b, c]
                    if contexts == clsCtx.none:
                        continue

                    for ctx in clsCtx.list(contexts):
                        nop = (ctx, negOpName)

                        aNOpC = (a, nop, c)
                        bOpC = (b, (ctx, posOpName), c)

                        r |= addFact(
                            a,
                            nop,
                            b,
                            (aNOpC, bOpC),
                            1 + justComplexity[aNOpC] + justComplexity[bOpC],
                        )
    return r


# Uses '->' and '-|>', affects '-|>'
def contrapositiveConjunction():
    # a X-|> b
    # WHEN
    #    (a X-> c) AND (a X-|> b+c)

    r = False
    for c in principlesList:
        for b in principlesList:
            if b == c:
                continue

            bc = joinPrinciples(b, c)
            if bc is None:
                continue

            for a in principlesList:
                if a == b:
                    continue

                if a == c:  # Special-case
                    reds = notImplies[a, bc]
                    if reds == Reduction.none:
                        continue

                    for x in Reduction.list(reds):
                        notImp = (x, "-|>")

                        aNotImpBC = (a, notImp, bc)

                        r |= addFact(
                            a, notImp, b, (aNotImpBC,), 1 + justComplexity[aNotImpBC]
                        )
                else:
                    reds = implies[a, c] & notImplies[a, bc]
                    if reds == Reduction.none:
                        continue

                    for x in Reduction.list(reds):
                        notImp = (x, "-|>")

                        aImpC = (a, (x, "->"), c)
                        aNotImpBC = (a, notImp, bc)

                        r |= addFact(
                            a,
                            notImp,
                            b,
                            (aImpC, aNotImpBC),
                            1 + justComplexity[aImpC] + justComplexity[aNotImpBC],
                        )
    return r


# REDUNDANT
# Uses 'c' and '-|>', affects '-|>'
def contrapositiveConservation():
    # a RCA-|> b
    # WHEN
    #    (a Fc c) AND (c RCA-|> b) AND (b has form F)
    notImp = (Reduction.RCA, "-|>")

    r = False
    for c in principlesList:
        for b in principlesList:
            if b == c:
                continue

            if Reduction.isPresent(Reduction.RCA, notImplies[c, b]):
                formB = form[b]
                if formB == Form.none:
                    continue

                cNotImpB = (c, notImp, b)
                refCplxCB = 2 + justComplexity[cNotImpB]

                for a in principlesList:
                    if a == b or a == c:
                        continue

                    frms = conservative[a, c] & formB
                    if frms == Form.none:
                        continue

                    for f in Form.list(frms):
                        aConsC = (a, (f, "c"), c)

                        r |= addFact(
                            a,
                            notImp,
                            b,
                            (aConsC, cNotImpB, (b, "form", f)),
                            justComplexity[aConsC] + refCplxCB,
                        )
    return r


# REDUNDANT
# Uses 'c' and '->', affects 'c'
def liftConservation():
    r = False
    for c in principlesList:
        # a Fc b
        # WHEN
        #    (c RCA-> a) AND (c Fc b) [aka "Weaker principles prove less"]
        for a in principlesList:
            if a == c:
                continue

            if Reduction.isPresent(Reduction.RCA, implies[c, a]):
                cImpA = (c, (Reduction.RCA, "->"), a)
                refCplxCA = 1 + justComplexity[cImpA]

                for b in principlesList:
                    if b in (a, c):
                        continue

                    for f in Form.list(conservative[c, b]):
                        fc = (f, "c")
                        cConsB = (c, fc, b)

                        r |= addFact(
                            a,
                            fc,
                            b,
                            (cImpA, cConsB),
                            refCplxCA + justComplexity[cConsB],
                        )

        # a Fc b
        # WHEN
        #    (a Fc c) AND (b RCA-> c) [aka "Stronger principles prove more"]
        for b in principlesList:
            if b == c:
                continue

            if Reduction.isPresent(Reduction.RCA, implies[b, c]):
                bImpC = (b, (Reduction.RCA, "->"), c)
                refCplxBC = 1 + justComplexity[bImpC]

                for a in principlesList:
                    if a in (b, c):
                        continue

                    for f in Form.list(conservative[a, c]):
                        fc = (f, "c")
                        aConsC = (a, fc, c)

                        r |= addFact(
                            a,
                            fc,
                            b,
                            (aConsC, bImpC),
                            justComplexity[aConsC] + refCplxBC,
                        )
    return r


# REDUNDANT
# Uses '->' and '-|>', affects 'nc'
def definitionOfNonConservation():
    # a nFc b
    # WHEN
    #    (a RCA-> c) AND (b RCA-|> c) AND (c has form F)
    r = False
    for c in principlesList:
        formC = form[c]
        if formC == Form.none:
            continue
        cForms = Form.list(formC)

        for a in principlesList:
            if a == c:
                continue

            if Reduction.isPresent(Reduction.RCA, implies[a, c]):
                aImpC = (a, (Reduction.RCA, "->"), c)
                refCplxAC = 2 + justComplexity[aImpC]

                for b in principlesList:
                    if b == a or b == c:
                        continue

                    if Reduction.isPresent(Reduction.RCA, notImplies[b, c]):
                        bNotImpC = (b, (Reduction.RCA, "-|>"), c)

                        cplx = refCplxAC + justComplexity[bNotImpC]

                        for f in cForms:
                            r |= addFact(
                                a, (f, "nc"), b, (aImpC, bNotImpC, (c, "form", f)), cplx
                            )
    return r


# REDUNDANT
# Uses 'nc' and '->', affects 'nc'
def liftNonConservation():
    imp = (Reduction.RCA, "->")

    r = False
    for c in principlesList:
        # a nFc b
        # WHEN
        #    (a nFc c) AND (c RCA-> b) [aka "Weaker principles prove less (contrapositive)"]
        for b in principlesList:
            if b == c:
                continue

            if Reduction.isPresent(Reduction.RCA, implies[c, b]):
                cImpB = (c, imp, b)
                refCplxCB = 1 + justComplexity[cImpB]

                for a in principlesList:
                    if a == b or a == c:
                        continue

                    for f in Form.list(nonConservative[a, c]):
                        nFc = (f, "nc")
                        aNonConsC = (a, nFc, c)

                        r |= addFact(
                            a,
                            nFc,
                            b,
                            (aNonConsC, cImpB),
                            justComplexity[aNonConsC] + refCplxCB,
                        )

        # a nFc b
        # WHEN
        #    (a RCA-> c) AND (c nFc b) [aka "Stronger principles prove more (contrapositive)"]
        for a in principlesList:
            if a == c:
                continue

            if Reduction.isPresent(Reduction.RCA, implies[a, c]):
                aImpC = (a, imp, c)
                refCplxAC = 1 + justComplexity[aImpC]

                for b in principlesList:
                    if b == a or b == c:
                        continue

                    for f in Form.list(nonConservative[c, b]):
                        nFc = (f, "nc")
                        cNonConsB = (c, (f, "nc"), b)

                        r |= addFact(
                            a,
                            nFc,
                            b,
                            (aImpC, cNonConsB),
                            refCplxAC + justComplexity[cNonConsB],
                        )
    return r


def deriveInferences(quiet=False, verbose=False):
    start = timekeeper()
    if not quiet:
        eprint("Adding reflexivity facts..")
    addReflexivities()
    if not quiet:
        eprint("Making RCA trivial..")
    addRCABottom()
    if not quiet:
        eprint("Recording conjunctions...")
    definitionOfConjunction()
    if not quiet:
        eprint("Elapsed: {0:.6f} s\n".format(timekeeper() - start))

    start = timekeeper()
    if not quiet:
        eprint("Deriving positive facts:")
    n = 0
    eUpdated, iUpdated, cUpdated = True, True, True
    while eUpdated or iUpdated or cUpdated:
        n += 1
        eChanged, iChanged, cChanged = False, False, False

        if iUpdated or iChanged:
            if not quiet:
                eprint("\tExtracting equivalences...")
            eChanged |= definitionOfEquivalence()  # Uses '->', affects '<->'
        if eUpdated or eChanged:
            if not quiet:
                eprint("\tTaking the transitive closure of equivalence...")
            eChanged |= transitiveClosure(
                equivalent, "<->", Reduction
            )  # Uses '<->', affects '<->'

        if iUpdated or iChanged:
            if not quiet:
                eprint("\tTaking the transitive closure of implication...")
            iChanged |= transitiveClosure(
                implies, "->", Reduction
            )  # Uses '->', affects '->'
            if not quiet:
                eprint("\tReverse-engineering implications of conjunctions...")
            iChanged |= unifyOverConjunctions()  # Uses '->', affects '->'
        if (cUpdated or cChanged) or (iUpdated or iChanged):
            if not quiet:
                eprint("\tImplementing conservativity for implication...")
            iChanged |= definitionOfConservation()  # Uses 'c' and '->', affects '->'

        if cUpdated or cChanged:
            if not quiet:
                eprint("\tTaking the transitive closure of conservation facts...")
            cChanged |= transitiveClosure(
                conservative, "c", Form
            )  # Uses 'c', affects 'c'
        if (cUpdated or cChanged) or (iUpdated or iChanged):
            if not quiet:
                eprint("\tLifting conservation facts over implications...")
            cChanged |= liftConservation()  # Uses 'c' and '->', affects 'c'

        if verbose:
            eprint("\t\tDuring iteration {0}:".format(n))
            if eChanged:
                eprint("\t\t\tEquivalences updated.")
            if iChanged:
                eprint("\t\t\tImplications updated.")
            if cChanged:
                eprint("\t\t\tConservation facts updated.")
            if not eChanged and not iChanged and not cChanged:
                eprint("\t\t\tNothing updated.")

        eUpdated = eChanged
        iUpdated = iChanged
        cUpdated = cChanged
    if not quiet:
        eprint("Finished with positive facts.")
        eprint(
            "Elapsed: {0:.6f} s (with {1} repeats)\n".format(timekeeper() - start, n)
        )

    start = timekeeper()
    if not quiet:
        eprint("Deriving negative facts:")
    n = 0
    niUpdated, ncUpdated = True, True
    while niUpdated or ncUpdated:
        n += 1
        niChanged, ncChanged = False, False

        if niUpdated or niChanged:
            if not quiet:
                eprint("\tApplying transivitity to non-implications...")
            niChanged |= contrapositiveTransitivity(
                implies, "->", notImplies, "-|>", Reduction
            )  # Uses '->' and '-|>', affects '-|>'
            if not quiet:
                eprint("\tSplitting non-implications over conjunctions...")
            niChanged |= (
                contrapositiveConjunction()
            )  # Uses '->' and '-|>', affects '-|>'
            if not quiet:
                eprint("\tImplementing conservativity for non-implication...")
            niChanged |= (
                contrapositiveConservation()
            )  # Uses 'c' and '-|>', affects '-|>'

        if ncUpdated or ncChanged:
            if not quiet:
                eprint("\tApplying transivitity to non-conservation facts...")
            ncChanged |= contrapositiveTransitivity(
                conservative, "c", nonConservative, "nc", Form
            )  # Uses 'c' and 'nc', affects 'nc'
        if niUpdated or niChanged:
            if not quiet:
                eprint("\tExtracting non-conservation facts from non-implications...")
            ncChanged |= (
                definitionOfNonConservation()
            )  # Uses '->' and '-|>', affects 'nc'
        if ncUpdated or ncChanged:
            if not quiet:
                eprint("\tLifting non-conservation facts over implications...")
            ncChanged |= liftNonConservation()  # Uses 'nc' and '->', affects 'nc'

        if verbose:
            eprint("\t\tDuring iteration {0}:".format(n))
            if niChanged:
                eprint("\t\t\tNon-implications updated.")
            if ncChanged:
                eprint("\t\t\tNon-conservation facts updated.")
            if not niChanged and not ncChanged:
                eprint("\t\t\tNothing updated.")

        niUpdated = niChanged
        ncUpdated = ncChanged
    if not quiet:
        eprint("Finished with negative facts.")
        eprint(
            "Elapsed: {0:.6f} s (with {1} repeats)\n".format(timekeeper() - start, n)
        )


def getDatabase():
    return {
        "version": DatabaseVersion,
        "principles": principles,
        "implication": (implies, notImplies),
        "conservation": (conservative, nonConservative),
        "form": form,
        "primary": (primary, primaryIndex),
        "justify": justify,
    }


def setDatabase(database):
    global principles, principlesList
    principles = database["principles"]
    principlesList = sorted(principles)

    global implies, notImplies
    implies, notImplies = database["implication"]

    global conservative, nonConservative
    conservative, nonConservative = database["conservation"]

    global form
    form = database["form"]

    global primary, primaryIndex
    primary, primaryIndex = database["primary"]

    global justify
    justify = database["justify"]

    global justComplexity
    justComplexity = {}

    def rebuildComplexity(fact):
        try:
            return justComplexity[fact]
        except KeyError:
            r = 1

            a, op, b = fact
            if op != "form":
                jst = justify[fact]
                if not isinstance(jst, str):
                    r += sum(rebuildComplexity(f) for f in jst)

            justComplexity[fact] = r
            return r

    for fact in justify:
        rebuildComplexity(fact)


def dumpDatabase(databaseName, quiet=False):
    if not quiet:
        eprint("Facts known: {0:,d}\n".format(len(justify)))

    start = timekeeper()
    if not quiet:
        eprint("Dumping updated database to binary file...")
    with open(databaseName, mode="wb") as databaseFile:
        pickledDatabase = pickle.dumps(getDatabase(), protocol=2)
        compressedDatabase = zlib.compress(pickledDatabase)
        databaseFile.write(compressedDatabase)

    if not quiet:
        eprint("Elapsed: {0:.6f} s\n".format(timekeeper() - start))


def loadDatabase(databaseName, quiet=False):
    with open(databaseName, mode="rb") as databaseFile:
        compressedDatabase = databaseFile.read()
        pickledDatabase = zlib.decompress(compressedDatabase)
        setDatabase(pickle.loads(pickledDatabase))


def main():
    absoluteStart = timekeeper()
    eprint("\nRM Zoo (v{0})\n".format(Version))

    parser = OptionParser(
        "Usage: %prog [options] results [database_title]",
        version="%prog {0} ({1})".format(Version, Date),
    )

    parser.set_defaults(quiet=False, verbose=False)

    parser.add_option(
        "-q",
        action="store_true",
        dest="quiet",
        help="Suppress progress/timing indicators.",
    )
    parser.add_option(
        "-v",
        action="store_true",
        dest="verbose",
        help="Report additional execution information.",
    )

    (options, args) = parser.parse_args()
    if len(args) > 2:
        parser.error("Too many arguments provided.")
    if len(args) < 1:
        parser.error("No results file specified.")

    if options.quiet and options.verbose:
        parser.error("Options -q and -v are incompatible.")

    resultsFile = args[0]
    if len(args) > 1:
        databaseTitle = args[1]
    else:
        eprint('No database title specified; defaulting to "database".')
        databaseTitle = "database.dat"

    if os.path.splitext(databaseTitle)[1] == "":
        databaseName = databaseTitle + os.extsep + "dat"
    else:
        databaseName = databaseTitle

    if not os.path.exists(resultsFile):
        parser.error('Results file "{0}" does not exist.'.format(resultsFile))

    with open(resultsFile, encoding="utf-8") as f:
        parseResults(f.read(), options.quiet)
    deriveInferences(quiet=options.quiet, verbose=options.verbose)
    dumpDatabase(databaseName, options.quiet)
    if not options.quiet:
        eprint("Total elapsed time: {0:.6f} s".format(timekeeper() - absoluteStart))

    if options.verbose:
        try:
            report = []
            report.append("\tReduction.list: {0}".format(Reduction.list.cache_info()))
            report.append("\tForm.list: {0}".format(Form.list.cache_info()))
            eprint("\nCache report: ")
            eprint("\n".join(report))
        except AttributeError:
            pass


if __name__ == "__main__":
    main()
