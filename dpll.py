model = {}
is_conflict = False

def dpll(clauses):
	global model
	global is_conflict
	clauses = apply_model(clauses, model)
	local_model = {}
	is_conflict = False
	level = 0
	if not bcp(clauses, local_model, level):
		print("Unsatisfiable")
		return False

	while True:
		print("model: ", model)
		clauses = apply_model(clauses, model)
		level+=1
		if not decide(clauses, level):
			print("Satisfiable")
			return True

		while(not bcp(clauses, local_model, level)):
			backtrack_level = analyze_conflict()
			level = backtrack_level
			if backtrack_level<0:
				print("Unsatisfiable")
				return False
			backtrack(backtrack_level)
			clauses = apply_model(clauses, model)


def bcp(clauses, local_model, level):
	global is_conflict
	clauses = apply_model(clauses, local_model)
	print("is_conflict: ", is_conflict)
	if is_conflict:
		return False

	print("clauses", clauses)
	unit_clauses = find_unit_clauses(clauses)
	if len(unit_clauses) == 0:
		model.update(local_model)
		print("true returned")
		return True
	
	local_model.update({list(unit_clauses.keys())[0]:(unit_clauses[list(unit_clauses.keys())[0]], level)})
	print("local_model ", local_model)
	return bcp(clauses, local_model, level) 

def resolve(clause1, clause2, literal):
	pass

def analyze_conflict():
	pass

def jw(clauses):
	jw_dict = {}
	for clause in clauses:
		for literal in clause:
			if literal[-1] in model.keys():
				break
			if not (literal in jw_dict.keys()):
				jw_dict.update({literal:0})
			jw_dict[literal] += 2**(-1*len(clause))

	if len(jw_dict) is 0:
		return None

	import operator
	sorted_x = sorted(jw_dict.items(), key=operator.itemgetter(1))
	return sorted_x[-1][0]


def decide(clauses, level):
	global model
	literal = jw(clauses)
	if literal is None:
		return False
	# print("before: ",model)
	model.update({literal[-1]:(True if len(literal) == 1 else False, level)})
	# print("after: ", model)
	return True

def backtrack(backtrack_level):
	global model

	for key, value in model:
		if(value[1]>backtrack_level):
			del model[key]


def find_unit_clauses(clauses):
	unit_clauses = {clause[-1]:(True if len(clause[0]) == 1 else False) for clause in clauses if len(clause) == 1}

	return unit_clauses

def apply_model(clauses, model):
	global is_conflict
	clauses_to_be_removed = []
	for clause in clauses:
		literals_to_be_removed = []
		for literal in clause:
			if len(literal) == 2:
				atom = literal[1]

				if atom in model.keys() and not model[atom][0]:
					clauses_to_be_removed.append(clause)
					break
				elif atom in model.keys() and model[atom][0]:
					literals_to_be_removed.append(literal)

			else:
				atom = literal

				if atom in model.keys() and model[atom][0]:
					clauses_to_be_removed.append(clause)
					break
				elif atom in model.keys() and not model[atom][0]:
					literals_to_be_removed.append(literal)

		for x in literals_to_be_removed:
			print("len(clause) ", len(clause))
			if len(clause) == 1:
				is_conflict = True
			clause.remove(x)

	for x in clauses_to_be_removed:
		clauses.remove(x)

	return clauses

cnf_formula = [['!q'], ['p', '!p']]

# dpll(cnf_formula)

print(jw(cnf_formula))