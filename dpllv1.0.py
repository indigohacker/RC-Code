##
# Authors: Raghav Prasad, Krishna Datta
#

import random
import time
import copy


# A clause consists of a set of symbols, each of which is negated
# or not. A clause where
# clause.symbols = {"a": 1, "b": -1, "c": 1}
# corresponds to the statement: a OR (NOT b) OR c .
class Clause:
    def __init__(self):
        self.symbols = {}
        pass

    def from_str(self, s):
        s = s.split()
        for token in s:
            if token[0] == "-":
                sign = -1
                symbol = token[1:]
            else:
                sign = 1
                symbol = token
            self.symbols[symbol] = sign

    def __str__(self):
        tokens = []
        for symbol,sign in self.symbols.items():
            token = ""
            if sign == -1:
                token += "-"
            token += symbol
            tokens.append(token)
        return " ".join(tokens)

# A SAT instance consists of a set of CNF clauses. All clauses
# must be satisfied in order for the SAT instance to be satisfied.
class SatInstance:
    def __init__(self):
        pass

    def from_str(self, s):
        self.symbols = set()
        self.clauses = []
        for line in s.splitlines():
            clause = Clause()
            clause.from_str(line)
            self.clauses.append(clause)
            for symbol in clause.symbols:
                self.symbols.add(symbol)
        # self.symbols = sorted(self.symbols)

    def __str__(self):
        s = ""
        for clause in self.clauses:
            s += str(clause)
            s += "\n"
        return s

    def is_satisfied(self, assignment):
        for clause in self.clauses:
            flag = False
            for symbol in clause.symbols:
                if(symbol in assignment and clause.symbols[symbol] == assignment[symbol][0]):
                    flag = True
                    break
            if(flag != True):
                return False
        return True

def bcp(assign_record,decision_level,clauses,implication_stack):
    last_signed_symbol = None
    last_signed_clause = Clause()
    while(True):
        unit_flag = False
        for clause in clauses:
            symbols = clause.symbols
            # to how many symbols left unsigned
            count = 0
            unsigned_symbol = 0
            value = 1
            satisfied_flag = False
            for symbol in symbols:
                if (assign_record[symbol][0] == symbols[symbol]):
                    satisfied_flag = True
                    break
                if (assign_record[symbol][0] == 0):
                    count += 1
                    unsigned_symbol = symbol
                    value = symbols[symbol]
            if (not satisfied_flag and count == 0):
                new_clause = Clause()
                for symbol in last_signed_clause.symbols:
                    if(symbol != last_signed_symbol):
                        if(symbol not in new_clause.symbols):
                            new_clause.symbols[symbol] = -last_signed_clause.symbols[symbol]
                for symbol in clause.symbols:# current conflict clause
                    if(symbol != last_signed_symbol):
                        if(symbol not in new_clause.symbols):
                            new_clause.symbols[symbol] = -clause.symbols[symbol]
                return new_clause,True
            if (satisfied_flag == True):
                continue
            if (count == 1):
                unit_flag = True
                # make implication
                if (decision_level not in implication_stack):
                    implication_stack[decision_level] = {unsigned_symbol: value}
                else:
                    implication_stack[decision_level][unsigned_symbol] = value
                # update record
                last_signed_clause = copy.deepcopy(clause)
                last_signed_symbol = unsigned_symbol

                assign_record[unsigned_symbol][0] = value
                assign_record[unsigned_symbol][2] = decision_level
        if (not unit_flag):
            break
    return  None,False

# check the proper decision level to roll back
def conflict_analysis(decision_level, decision_stack, implication_stack, assign_record, new_clause):
    level = []
    for symbol in new_clause.symbols:
        if symbol not in new_clause.symbols:
            level.append(assign_record[symbol][2])
    level = sorted(level)
    if(len(level) >= 2):
        back_level = level[-2]
        while (decision_level > back_level):
            if (decision_level in implication_stack):
                for symbol in implication_stack[decision_level]:
                    assign_record[symbol] = (0, 1, 0)
                del implication_stack[decision_level]

            assign_record[decision_stack[decision_level][0]] = (0, 1, 0)
            del decision_stack[decision_level]
            decision_level -= 1
        return back_level

    else:
        back_level = decision_level
        while (back_level >= 0):
            pass
            if (back_level in implication_stack):
                for symbol in implication_stack[back_level]:
                    assign_record[symbol][0] = 0
                del implication_stack[back_level]
            (symbol, value) = decision_stack[back_level]
            if (assign_record[symbol][1] != 1):
                assign_record[symbol] = (0, 1, 0)
                del decision_stack[back_level]
                back_level -= 1
                continue
            else:
                decision_stack[back_level] = (symbol, -value)
                assign_record[symbol][:-1] = (-value, 0)
                break
        return back_level

def decide(assign_record):
    for symbol in assign_record:
        if(assign_record[symbol][0] == 0):
            return False # not assigned yet
    return True # all assigned

def jeroslow_wang(literal, clauses):
    jw_val = 0
    for clause in clauses:
        if literal in clause.symbols:
            jw_val += 2**(-1*len(clause.symbols))

    return jw_val


def DPLL(symbols, clauses):
    assign_record = {}
    literal_record = {}

    for symbol in symbols:
        assign_record[symbol] = [0,1,0]
    for clause in clauses:
        for symbol in clause.symbols:
            value = clause.symbols[symbol]
            if ((symbol, value) not in literal_record):
                literal_record[(symbol, value)] = 0
            literal_record[(symbol, value)] += 1

    literal_mheap = []
    for literal in literal_record:
        literal_mheap.append((literal[0], literal[1], literal_record[literal], jeroslow_wang(literal, clauses)))
    literal_mheap = sorted(literal_mheap, key=lambda x:x[-1], reverse = True)

    decision_stack = {}
    decision_level = 0

    implication_stack = {}
    while(not decide(assign_record)):
        for item in literal_mheap:
            if(assign_record[item[0]][0] == 0):
                decision_stack[decision_level] = (item[0],item[1])
                assign_record[item[0]][0] = item[1]
                assign_record[item[0]][2] = decision_level
                break

        while(True):
            new_clause, conflict = bcp(assign_record,decision_level,clauses,implication_stack)
            if(not conflict):
                break

            clauses.append(new_clause)
            beta = conflict_analysis(decision_level, decision_stack, implication_stack, assign_record, new_clause)
            if(beta < 0):
                print("Not SAT")
                return {}
            decision_level = beta
        decision_level += 1
    return assign_record



with open("input.txt", "r") as input_file:
    instance_strs = input_file.read()

instance_strs = instance_strs.split("\n\n")

with open("output_assignment.txt", "w") as output_file:
    count = 0
    for instance_str in instance_strs:
        instance = SatInstance()
        instance.from_str(instance_str)
        if instance_str.strip() == "":
            continue
        instance = SatInstance()
        instance.from_str(instance_str)
        # use DPLL to give the assignment
        assignment = DPLL(instance.symbols, instance.clauses)
        #print(sorted(assignment, key = lambda x:int(x[0])))
        
        print(instance.is_satisfied(assignment)) # to test whether it works
        for symbol_index, (symbol,(sign,valid,level)) in enumerate(assignment.items()):
            if symbol_index != 0:
                output_file.write(" ")
            token = ""
            if sign == -1:
                token += "-"
            token += symbol
            output_file.write(token)
        output_file.write("\n")
        count += 1
        # print(count)  
        # print(time.strftime("%Y-%m-%d %A %X", time.localtime()))

















