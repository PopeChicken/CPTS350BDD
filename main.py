import collections
import importlib
collections.abc = importlib.import_module('collections.abc')

from pyeda.inter import *
from functools import *
import operator

# gets the bits for the parameter n
def bitsFor(n, width=5):
    return [(n >> i) & 1 for i in range(width)]

# Return expr that is true iff the binary vector 'varsList' equals integer value
def cubeEq(varsList, value):
    bits = bitsFor(value, len(varsList))
    lits = []
    for v, b in zip(varsList, bits):
        if b:
            lits.append(v)
        else:
            lits.append(~v)
    return reduce(operator.and_, lits)

# making the relations for varsA and varsB
def makeRelation(varsA, varsB, offsets):
    terms = []
    for a in range(32):
        aCube = cubeEq(varsA, a)
        for off in offsets:
            b = (a + off) % 32
            bCube = cubeEq(varsB, b)
            terms.append(aCube & bCube)
    return reduce(operator.or_, terms)

def rrTests(RRExpr, xVar, yVar, xBits, yBits):
    # build the variable assignments for x = xBits
    bitsX = bitsFor(xBits)
    assignX = {}

    # paris each var with the binaryBits and makes a check a map to the truth value
    for i, bits in zip(xVar, bitsX):
        assignX[i] = bool(bits)

    # build the variable assignments for y = yBits
    bitsY = bitsFor(yBits)
    assignY = {}

    # paris each var with the binaryBits and makes a check a map to the truth value
    for i, bits in zip(yVar, bitsY):
        assignY[i] = bool(bits)

    # merge both assignments
    assignments = {**assignX, **assignY}

    # returns true or false
    return RRExpr.restrict(assignments).is_one()

def evenPrimeTests(expr, bits, var):
    # get the binary for the number we are testing
    binaryBits = bitsFor(bits)

    assignment = {}

    # paris each var with the binaryBits and makes a check a map to the truth value
    for i, bits in zip(var, binaryBits):
        assignment[i] = bool(bits)


    return expr.restrict(assignment).is_one()

def main():
    # number of bits to represent 0..31
    x = exprvars('x', 5)
    y = exprvars('y', 5)
    z = exprvars('z', 5)

    # building even/prime
    RRExpr = makeRelation(x, y, offsets=[3, 8])

    evenSet = [0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26, 28, 30]

    # getting the evenExpr
    evenTerms = []
    for i in evenSet:
        evenTerms.append(cubeEq(x, i))
    evenExpr = reduce(operator.or_, evenTerms)

    primeSet = {3, 5, 7, 11, 13, 17, 19, 23, 29, 31}

    # getting the primeBDD
    primeTerms = []
    for i in primeSet:
        primeTerms.append(cubeEq(x, i))
    primeExpr = reduce(operator.or_, primeTerms)
    primeBDD = expr2bdd(primeExpr)

    print("Tests for 3.1")
    print("RR(27,3):", rrTests(RRExpr, x, y, 27, 3))
    print("RR(16,20):", rrTests(RRExpr, x, y, 16, 20))
    print("EVEN(14):", evenPrimeTests(evenExpr, 14, x))
    print("EVEN(13):", evenPrimeTests(evenExpr, 13, x))
    print("PRIME(7):", evenPrimeTests(primeExpr, 7, x))
    print("PRIME(2):", evenPrimeTests(primeExpr, 14, x))

    RR2Expr = makeRelation(x, z, offsets=[6, 11, 16])
    print('\nTests for 3.2')
    print("RR2(27,6):", rrTests(RR2Expr, x, z, 27, 6))
    print("RR2(27,9):", rrTests(RR2Expr, x, z, 27, 9))

    # getting RR2 set up for statement A
    baseOffsets = {6, 11, 16}
    changed = True
    while changed:
        changed = False
        newOffsets = set(baseOffsets)
        for i in baseOffsets:
            for j in baseOffsets:
                s = (i + j) % 32
                if s not in newOffsets:
                    newOffsets.add(s)
                    changed = True
        baseOffsets = newOffsets

    RR2starExpr = makeRelation(x, z, offsets=sorted(list(baseOffsets)))
    RR2starBDD = expr2bdd(RR2starExpr)

    # evaluation of statement A
    evenZTerms = []    
    # making EVEN(u)
    for i in range(32):
        if i % 2 == 0:
            evenZTerms.append(cubeEq(z, i))
    evenZExpr = reduce(operator.or_, evenZTerms)
    evenZBDD = expr2bdd(evenZExpr)

    # truth value of EVEN (v) ∧ RR2star(u, v)
    conjBDD = RR2starBDD & evenZBDD

    # making for the ∃v. (EVEN (v) ∧ RR2star(u, v)))
    for i in z:
        existsEvenReachable = conjBDD.smoothing([expr2bdd(i)])

    # finally checking the whole line
    counterExample = primeBDD & ~existsEvenReachable

    StatementA = counterExample.is_zero()
    print('\nStatementA (for each prime u, exists even v reachable in positive even steps):', StatementA)


if __name__ == "__main__":
    main()