def is_satisfiable(cnf_formula):
	clauses = cnf_formula
	symbols = list(set([literal[-1] for clause in clauses for literal in clause]))
	model = {}

	return dpll(clauses, symbols, model)

def dpll(clauses, symbols, model):
	clauses = apply_model(clauses, model)

	if len(clauses) == 0:
		return True

	number_of_false_clauses_in_model = len([clause for clause in clauses if len(clause) == 0])
	
	if number_of_false_clauses_in_model > 0:
		return False

	pure_symbols = find_pure_symbols(symbols, clauses, model)

	# print("Pure_symbols: ", pure_symbols)

	if len(pure_symbols) > 0:
		for pure_symbol in pure_symbols:
			model.update({pure_symbol:pure_symbols[pure_symbol]})
		symbols = [symbol for symbol in symbols if not symbol in pure_symbols.keys()]

		return dpll(clauses, symbols, model)

	unit_clauses = find_unit_clauses(clauses, model)

	if len(unit_clauses) > 0:
		for unit_clause in unit_clauses:
			model.update({unit_clause:unit_clauses[unit_clause]})
		symbols = symbols = [symbol for symbol in symbols if not symbol in unit_clauses.keys()]

		return dpll(clauses, symbols, model)

	first_symbol = symbols[0]
	remaining = symbols.remove(symbols[0])

	return dpll(clauses, remaining, model.update({first_symbol:True})) or dpll(clauses, remaining, model.update({first_symbol:False}))


def find_pure_symbols(symbols, clauses, model):
	# apply_model(clauses, model)

	pure_symbols = {}
	for symbol in symbols:
		lit1 = '!'+symbol
		lit2 = symbol
		for clause in clauses:
			if not symbol in pure_symbols.keys():
				if lit1 in clause:
					pure_symbols.update({symbol:False})
				elif lit2 in clause:
					pure_symbols.update({symbol:True})

			else:
				if (lit1 in clause and pure_symbols[symbol]) or (lit2 in clause and not pure_symbols[symbol]):
					del pure_symbols[symbol]
					break

	return pure_symbols

def find_unit_clauses(clauses, model):
	# clauses = apply_model(clauses, model)
	unit_clauses = {clause[0][-1]:(True if len(clause[0]) == 1 else False) for clause in clauses if len(clause) == 1}

	return unit_clauses

def apply_model(clauses, model):
	clauses_to_be_removed = []
	for clause in clauses:
		literals_to_be_removed = []
		for literal in clause:
			if len(literal) == 2:
				atom = literal[1]

				if atom in model.keys() and not model[atom]:
					clauses_to_be_removed.append(clause)
					break
				elif atom in model.keys() and model[atom]:
					literals_to_be_removed.append(literal)

			else:
				atom = literal

				if atom in model.keys() and model[atom]:
					clauses_to_be_removed.append(clause)
					break
				elif atom in model.keys() and not model[atom]:
					literals_to_be_removed.append(literal)

		for x in literals_to_be_removed:
			clause.remove(x)

	for x in clauses_to_be_removed:
		clauses.remove(x)

	return clauses

cnf_formula = [['p',], ['!p',]]

print(is_satisfiable(cnf_formula))
