from __future__ import print_function, unicode_literals

from rmBitmasks import Reduction

from version_guard import lru_cache, isString

_justLineMarker = "*"
_justIndentMarker = "@"
justMarker = _justLineMarker + _justIndentMarker
_justIndented = justMarker + _justIndentMarker
_justFormat = justMarker + "{0}: "


def indentJust(jst):
    return jst.replace(justMarker, _justIndented)


@lru_cache(maxsize=1024)
def printOp(op):
    if isString(op):
        return op

    opCtx, opCore = op
    try:
        opCtx = opCtx.name
    except AttributeError:
        pass

    if opCore == "nc":
        return "n{0}c".format(opCtx)
    elif opCore in ("=>", "=/>", "<=", "</=", "<=>"):
        return "{1}_{0}".format(opCtx, opCore)
    else:
        return "{0}{1}".format(opCtx, opCore)


def printFact(a, op, b):
    if op == "form":
        b = b.name
    elif op[0] in (
        Reduction.sW,
        Reduction.W,
        Reduction.gW,
        Reduction.sc,
        Reduction.c,
    ):  # Reducibility fact, not implication fact
        if op[1] == "->":
            op = (op[0], "<=")
            a, b = b, a
        elif op[1] == "-|>":
            op = (op[0], "</=")
            a, b = b, a
        elif op[1] == "<->":
            op = (op[0], "<=>")
    return "{0} {1} {2}".format(a, printOp(op), b)


printedJustify = {}


def printJustification(fact, justify, formatted=True):
    a, op, b = fact

    r = ""
    try:
        r = printedJustify[fact]
    except KeyError:
        if op == "form":
            r = justMarker + printFact(*fact)
        else:
            try:
                jst = justify[fact]
            except KeyError:
                raise Exception(
                    'ERROR: Referenced fact "{0}" not justified!'.format(
                        printFact(*fact)
                    )
                )

            if isString(jst):
                r = _justFormat.format(printFact(*fact)) + jst
            else:
                r = _justFormat.format(printFact(*fact)) + "".join(
                    (
                        _justIndented + f
                        if isString(f)
                        else indentJust(printJustification(f, justify, formatted=False))
                    )
                    for f in jst
                )
        printedJustify[fact] = r

    if formatted:
        return r.replace(_justLineMarker, "\n").replace(_justIndentMarker, "    ")
    else:
        return r
