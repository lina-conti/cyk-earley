#! /usr/bin/python
# -*- encoding: utf8 -*-

# -----
# TP Implementation of the Earley algorithm (with pred function)
#
# 1) Familiarize yourself with the code.
# 2) Implement the incomplete functions (those containing the keyword "pass").
# 3) Make a copy of the file and modify the code to return (and display in a readable way)
#    a syntax tree when the analysis is successful (feel free to modify the existing classes for this)
#
# You are of course allowed to define auxiliary functions or add methods to classes,
# but all your code must be carefully commented:
# - the role or return value of each function must be specified, as well as how it works
# - any variable creation must be accompanied by a comment on its role/meaning.
#
# This TP (in the form of two executable files: one for parsing and one for printing the derivation tree) should be submitted on Moodle before Tuesday 21 December 23:59
# -----



class Symbol:
    # field name: String
    # (no methods)

    def __init__(self, name):
        # name: String

        self.name = name

    def __str__(self):
        return self.name


class Rule:
    # field lhs: Symbol
    # field rhs: list of Symbol
    # (no methods)

    def __init__(self, lhs, rhs):
        # lhs: Symbol
        # rhs: list of Symbol

        self.lhs = lhs
        self.rhs = rhs

    def __str__(self):
        return str(self.lhs) + " --> [" + ",".join([str(s) for s in self.rhs]) + "]"


class Grammar:
    # field symbols: list of Symbol
    # field axiom: Symbol
    # field rules: list of Rule
    # field nonTerminals: set of Symbol
    # field name: String
    # method createNewSymbol: String -> Symbol
    # method isNonTerminal: Symbol -> Boolean

    def __init__(self, symbols, axiom, rules, name):
        # symbols: list of Symbol
        # axiom: Symbol
        # rules: list of Rule
        # name: String

        self.symbols = symbols
        self.axiom = axiom
        self.rules = rules
        self.name = name

        self.nonTerminals = set()
        for rule in rules:
            self.nonTerminals.add(rule.lhs)

    # Returns a new symbol (with a new name build from the argument)
    def createNewSymbol(self, symbolName):
        # symbolName: String

        name = symbolName

        ok = False
        while (ok == False):
            ok = True
            for s in self.symbols:
                if s.name == name:
                    ok = False
                    continue

            if ok == False:
                name = name + "'"

        return Symbol(name)

    def isNonTerminal(self, symbol):
        # symbol: Symbol

        return symbol in self.nonTerminals

    def __str__(self):
        return "{" + \
               "symbols = [" + ",".join([str(s) for s in self.symbols]) + "] " + \
               "axiom = " + str(self.axiom) + " " + \
               "rules = [" + ", ".join(str(r) for r in self.rules) + "]" + \
               "}"


class Item:
    # field lhs: Symbol
    # field bd (before dot): list of Symbol
    # field ad (after dot): list of Symbol
    # field i: Integer

    def __init__(self, i, lhs, bd, ad):  # [i,lhs --> bd•ad]
        self.lhs = lhs
        self.bd = bd
        self.ad = ad
        self.i = i

    def __str__(self):
        return "[%d,%s --> %s • %s]" % \
               (self.i, str(self.lhs), ",".join([str(s) for s in self.bd]), ",".join([str(s) for s in self.ad]))

    def __eq__(self, other):
        return self.i == other.i and \
               self.lhs == other.lhs and self.bd == other.bd and self.ad == other.ad

class TableCell:
    # field c: list of Item
    # method cAppend: add Item to table cell


    c = []  # cell

    def __init__(self):
        self.c = []

    def __str__(self):
        return "{" + ", ".join([str(item) for item in self.c]) + "}"

    # Adds an item at the end of the t (+ prints some log), argument reason indicates the name of operations:"init","pred","scan","comp"
    # Argument print_log indicates whether to print log information or not
    def cAppend(self, item, print_log, reason=None):
        if reason != None:
            reasonStr =  reason + ": "
        else:
            reasonStr = ""

        if item not in self.c:
            self.c.append(item)
            if print_log:
                print(reasonStr+ str(item) )

    # Returns the item in position i of the TableCell
    def cGet(self, i):
        return self.c[i]

    # Returns the number of items in the TableCell
    def cLen(self):
        return len(self.c)

# ------------------------

# Creation and initialisation of the table T for the word w and the grammar gr
def init(g, w, print_log):
    # g: Grammar
    # w: word
    # print_log: boolean that indicates whether to print log information or not

    #T is a dictionary
    T = {}

    # makes T a dictionary with keys in len(w) and empty TableCells (ordered sets) as values
    for j in range(len(w) + 1):
        T[j] = TableCell()

    # foreach S -> α in P, add (S -> .α, 0) to T[0]
    for r in g.rules:
        if str(r.lhs) == str(g.axiom):
            T.get(0).cAppend(Item(0, r.lhs, [], r.rhs), print_log, "init, add to cell " + str(0))

    return T


# Insert in the table any new items resulting from the pred operation for the iterm it
def pred(g, it, T, j, print_log):
    # g: Grammar
    # it: Item (A -> α . β, i)
    # T: table
    # j : index
    # print_log: boolean that indicates whether to print log information or not

    # foreach β1 -> γ in P, add (β1 -> .γ, j) to T[j]
    for r in g.rules:
        if str(r.lhs) == str(it.ad[0]):
            T.get(j).cAppend(Item(j, r.lhs, [], r.rhs), print_log, "pred, add to cell " + str(j))


# Insert in the table any new items resulting from the scan operation for the item it
def scan(it, T, j, w, print_log):
    # it: Item (A -> α . β, i)
    # T: table
    # j: index
    # w: word
    # print_log: boolean that indicates whether to print log information or not

    # if β1 = uj then add (A -> αβ1•β2:|β|, i) to T[j +1]
    if str(it.ad[0]) == str(w[j]):
        T.get(j+1).cAppend(Item(it.i, it.lhs, it.bd + [it.ad[0]], it.ad[1:]), print_log, "scan, add to cell " + str(j+1))


# Insert in the table any possible new items resulting from the comp operation for the item it
def comp(it,T,j, print_log):
    # it: Item (A -> α . β, i)
    # T: table
    # j: index
    # print_log: boolean that indicates whether to print log information or not

    k_prime = 0 # k_prime loops through T[i]
    while k_prime < T.get(it.i).cLen():
        # it_prime: Item (i', A′ -> α′•β′) in T[i][k′]
        it_prime = T.get(it.i).cGet(k_prime)
        # if β′1 =A then add((A′ -> α′β′1•β′2:|β′|, i′) to T[j]
        if it_prime.ad: # to avoid index out of range
            if str(it_prime.ad[0]) == str(it.lhs):
                T.get(j).cAppend(Item(it_prime.i, it_prime.lhs, it_prime.bd + [it_prime.ad[0]], it_prime.ad[1:]), print_log, "comp, add to cell " + str(j))
        k_prime += 1


# Return True if the analysis is successful, otherwise False
def table_complete(g, w, T):
    # g: Grammar
    # w: word
    # T: table

    # for all items in T[|u|]
    for i in range(T.get(len(w)).cLen()):
        it = T.get(len(w)).cGet(i)
        # if the item is of form (S -> α•, 0) then the analysis is successful
        if (it.i == 0) and (str(it.lhs) == str(g.axiom)) and (not it.ad):
            return True
    return False


# Parse the word w for the grammar g return the parsing table at the end of the algorithm
def parse_earley(g, w, print_log):
    # g: Grammar
    # w: word
    # print_log: boolean that indicates whether to print log information or not


    # Initialisation
    T = init(g,w, print_log)

    # Top-down analysis
    for j in range(len(w) + 1): # j loops through T
        if print_log:
            print("j = " +str(j))
        k = 0  # k loops through T[j]
        while k < T.get(j).cLen():
            item = T.get(j).cGet(k)    # we will be working with the item in T[j][k]: (A -> α•β,i)
            if item.ad == []:   # if β = ε
                # comp?
                comp(item, T, j, print_log)
            elif g.isNonTerminal(item.ad[0]): # if β1 ∈ N
                # pred?
                pred(g, item, T, j, print_log)
            elif j < len(w):
                # scan?
                scan(item, T, j, w, print_log)
            k += 1


    if table_complete(g, w, T):
        print("Success")
    else:
        print("Failed parsing")

    return T

# --------------
# Definition of the symbols
symS = Symbol("S")
symA = Symbol("A")
symTerminalA = Symbol("a")
symTerminalB = Symbol("b")

# Definition of a grammar
g1 = Grammar(
    # All symbols
    [symS, symA, symTerminalA, symTerminalB],

    # Axiom
    symS,

    # List of rules
    [
        Rule(symS, [symA, symS]),  # S --> AS
        Rule(symS, [symTerminalB]),  # S --> b
        Rule(symA, [symTerminalA]),  # A --> a
    ],

    # name
    "g1"
)

# Definition of a grammar
g2 = Grammar(
    # All symbols
    [symS, symA, symTerminalA, symTerminalB],

    # Axiom
    symS,

    # List of rules
    [
        Rule(symS, [symA, symS]),  # S --> AS
        Rule(symS, [symTerminalB]),  # S --> b
        Rule(symA, [symA]),  # A --> A
        Rule(symA, [symTerminalA]),  # A --> a
    ],

    # name
    "g2"
)

# for w in words:
#	execute(w, g2)

# Definition of a grammar
g3 = Grammar(
    # All symbols
    [symS, symA, symTerminalA, symTerminalB],

    # Axiom
    symS,

    # List of rules
    [
        Rule(symS, [symA, symS]),  # S --> AS
        Rule(symS, [symA]),  # S --> A
        Rule(symA, [symS]),  # A --> S
        Rule(symS, [symTerminalB]),  # S --> b
        Rule(symS, [symTerminalB, symTerminalB]),  # S --> bb
        Rule(symA, []),  # A --> [epsilon]
        Rule(symA, [symTerminalA]),  # A --> a
    ],

    # name
    "g3"
)

# --------------
words = ["aab", "b", "aaaaab", "abab"]

print("GRAMMAR 1:")
print(g1)
print()
for word in words:
    print("Is the word " + word + " generated by g1?")
    parse_earley(g1, word, False)
    print()


print("GRAMMAR 2:")
print(g2)
print()
for word in words:
    print("Is the word " + word + " generated by g2?")
    parse_earley(g2, word, False)
    print()



print("GRAMMAR 3:")
print(g3)
print()
for word in words:
    print("Is the word " + word + " generated by g3?")
    parse_earley(g3, word, False)
    print()



"""
# ------------------------ my tests ------------------------------

# Definition of a grammar
gt = Grammar(
    # All symbols
    [symS, symA, symTerminalA, symTerminalB],

    # Axiom
    symS,

    # List of rules
    [
        Rule(symS, [symA, symS]),  # S --> AS
        Rule(symS, [symTerminalB]),  # S --> b
        Rule(symA, [symTerminalA]),  # A --> a
    ],

    # name
    "gt"
)

print("GRAMMAR TEST:")
print(gt)
print()
parse_earley(gt, "ab")

# ------------------------ my tests ------------------------------
"""
