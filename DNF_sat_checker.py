model = {}

def is_satisfiable(dnf_formula):
	global model

	for clause in dnf_formula:
		is_clause_satisfiable = True
		for literal in clause:
			if len(literal) == 2:
				atom = literal[1]
				if atom in model.keys() and model[atom]:
					is_clause_satisfiable = False
					model.clear()
					break
				elif not atom in model.keys():
					model.update({atom:False})

			else:
				atom = literal
				if atom in model.keys() and not model[atom]:
					is_clause_satisfiable = False
					model.clear()
					break
				elif not atom in model.keys():
					model.update({atom:True})

		if is_clause_satisfiable:
			return True

	return False

print(is_satisfiable([['p', '!p', 'q'], ['r', 's']]))
