import sys
import fileinput

def biconditionalElimination(s):
    if type(s) is str:
        return s
    elif type(s) is list and s[0] == "iff":
        return(["and",
                ["if",
                 biconditionalElimination(s[1]),
                 biconditionalElimination(s[2])],
                ["if",
                 biconditionalElimination(s[2]),
                 biconditionalElimination(s[1])]])
    else:
        return([s[0]] + [biconditionalElimination(i) for i in s[1:]])

def implicationElimination(s):
    if type(s) is str:
        return s
    elif type(s) is list and s[0] == "if":
        return(["or",
                ["not",
                 implicationElimination(s[1])],
                implicationElimination(s[2])])
    else:
        return([s[0]] + [implicationElimination(i) for i in s[1:]])

def doubleNegationElimination(s):
    if type(s) is str:
        return s
    elif type(s) is list and s[0] == "not" and type(s[1]) is list and s[1][0] == "not":
        return(doubleNegationElimination(s[1][1]))
    else:
        return([s[0]] + [doubleNegationElimination(i) for i in s[1:]])

def demorgan(s):
    revision = demorgan1(s)
    if revision == s:
        return s
    else:
        return demorgan(revision)
    
def demorgan1(s):
    if type(s) is str:
        return s
    elif type(s) is list and s[0] == "not" and type(s[1]) is list and s[1][0] == "and":
        return(["or"] + [demorgan(["not", i]) for i in s[1][1:]])
    elif type(s) is list and s[0] == "not" and type(s[1]) is list and s[1][0] == "or":
        return(["and"] + [demorgan(["not", i]) for i in s[1][1:]])
    else:
        return ([s[0]] + [demorgan(i) for i in s[1:]])

def binaryize(s): # ensures all connectives are binary (and / or)
    if type(s) is str:
        return s
    elif type(s) is list and s[0] == "and" and len(s) > 3: # too long
        return(["and", s[1], binaryize(["and"] + s[2:])])
    elif type(s) is list and s[0] == "or" and len(s) > 3: # too long
        return(["or", s[1], binaryize(["or"] + s[2:])])
    else:
        return([s[0]] + [binaryize(i) for i in s[1:]])
    
def distributivity(s, tup):
    revision = distributivity1(s, tup)
    if revision == s:
        return s
    else:
        return distributivity(revision, tup)
    
def distributivity1(s, tup): # only works on binary connectives
    if type(s) is str:
        return s
    elif type(s) is list and s[0] == tup[0] and type(s[1]) is list and s[1][0] == tup[1]:
        # distribute s[2] over s[1]
        return([tup[1]] + [distributivity([tup[0], i, s[2]], tup) for i in s[1][1:]])
    elif type(s) is list and s[0] == tup[0] and type(s[2]) is list and s[2][0] == tup[1]:
        # distribute s[1] over s[2]
        return([tup[1]] + [distributivity([tup[0], i, s[1]], tup) for i in s[2][1:]])
    else:
        return ([s[0]] + [distributivity(i, tup) for i in s[1:]])

def andAssociativity(s):
    revision = andAssociativity1(s)
    if revision == s:
        return s
    else:
        return andAssociativity(revision)
    
def andAssociativity1(s):
    if type(s) is str:
        return s
    elif type(s) is list and s[0] == "and":
        result = ["and"]
        # iterate through conjuncts looking for "and" lists
        for i in s[1:]:
            if type(i) is list and i[0] == "and":
                result = result + i[1:]
            else:
                result.append(i)
        return result
    else:
        return([s[0]] + [andAssociativity1(i) for i in s[1:]])

def orAssociativity(s):
    revision = orAssociativity1(s)
    if revision == s:
        return s
    else:
        return orAssociativity(revision)

def orAssociativity1(s):
    if type(s) is str:
        return s
    elif type(s) is list and s[0] == "or":
        result = ["or"]
        # iterate through disjuncts looking for "or" lists
        for i in s[1:]:
            if type(i) is list and i[0] == "or":
                result = result + i[1:]
            else:
                result.append(i)
        return result
    else:
        return([s[0]] + [orAssociativity1(i) for i in s[1:]])


def removeDuplicateLiterals(s):
    if type(s) is str:
        return s
    if s[0] == "not":
        return s
    if s[0] == "and":
        return(["and"] + [removeDuplicateLiterals(i) for i in s[1:]])
    if s[0] == "or":
        remains = []
        for l in s[1:]:
            if l not in remains:
                remains.append(l)
        if len(remains) == 1:
            return remains[0]
        else:
            return(["or"] + remains)

def removeDuplicateClauses(s):
    if type(s) is str:
        return s
    if s[0] == "not":
        return s
    if s[0] == "or":
        return s
    if s[0] == "and": #conjunction of clauses
        remains = []
        for c in s[1:]:
            if unique(c, remains):
                remains.append(c)
        if len(remains) == 1:
            return remains[0]
        else:
            return(["and"] + remains)

def unique(c, remains):
    for p in remains:
        if type(c) is str or type(p) is str:
            if c == p:
                return False
        elif len(c) == len(p):
            if len([i for i in c[1:] if i not in p[1:]]) == 0:
                return False
    return True
        

def cnf(s, tup):
    s = biconditionalElimination(s)
    s = implicationElimination(s)
    s = demorgan(s)
    s = doubleNegationElimination(s)
    s = binaryize(s)
    s = distributivity(s, tup)
    s = andAssociativity(s)
    s = orAssociativity(s)
    s = removeDuplicateLiterals(s)
    s = removeDuplicateClauses(s)
    return s

# formula = ['and', 's', ['if', 'r', ['not', ['or', 'p', 'q']]]]

# formula = ['and', 's', ['or', 'r', ['not', ['not', ['or', 'p', 'q']]]]]

# formula = ['and', 's', ['if', 'r', ['not', ['or', 'p', 'q']]]]

# formula = ['or', 's', ['and', 'p', 'q']]

to_dnf_or_cnf = input("Convert to (D)NF or (C)NF? ").upper()

tup = ('or', 'and')

if to_dnf_or_cnf == 'D':
    tup = ('and', 'or')
elif to_dnf_or_cnf != 'C':
    print("Incorrect input. Please input either 'C' or 'D'")
    exit()

formula = [['or', 's', ['and', 'r', ['or', 'p', 'q']]], ]

formula_in_cnf = [cnf(l, tup) for l in formula]

print(formula_in_cnf[0])

