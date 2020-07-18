from valid_symbols_dictionary import symbols_dict

formula = "(s>(r.(p+q)))"
# formula = "(s.(r+(!(!(p+q)))))"

prefix_formula = None

formula_backup = formula

def check_balanced_parantheses(formula):
	bracket = ['(', ')', '{', '}', '[', ']']
	for x in formula:
		if x not in bracket:
			formula = formula.replace(x, '')


	brackets = ['()', '{}', '[]']

	while any(x in formula for x in brackets):
		for br in brackets:
			formula = formula.replace(br, '')

	return not formula

def check_subformula_validity(subformula):
	global formula

	if subformula[1:len(subformula)-1].find('(') == -1:
		subformula_wo_parentheses = subformula[1:len(subformula)-1]
		binary_ops = list(symbols_dict.keys())
		binary_ops.remove('!')

		if any(x in subformula for x in binary_ops):
			if (len(subformula_wo_parentheses) == 3) and (not subformula_wo_parentheses[0] in symbols_dict.keys()) and (not subformula_wo_parentheses[2] in symbols_dict.keys()) and (subformula_wo_parentheses[1] in binary_ops):
				convert_formula_to_prefix(subformula_wo_parentheses, 'b')
				formula = formula.replace(subformula, 'X')
				return True
			return False

		elif '!' in subformula:
			if (len(subformula_wo_parentheses) == 2) and (not subformula_wo_parentheses[1] in symbols_dict.keys()) and (subformula_wo_parentheses[0] == '!'):
				convert_formula_to_prefix(subformula_wo_parentheses, 'u')
				formula = formula.replace(subformula, 'X')
				return True
			return False
		
		# print("Formula so far: ", formula)
		return False

def check_formula_validity():
	global formula

	if formula[0] != '(' or formula[-1] != ')':
		return False

	while '(' in formula:
		innermost_open_bracket_index = len(formula) - formula[::-1].find('(') - 1
		innermost_close_bracket_index = formula.find(')', innermost_open_bracket_index)
		if not check_subformula_validity(formula[innermost_open_bracket_index:innermost_close_bracket_index+1]):
			return False

	return True


def convert_formula_to_prefix(subformula, operator_type):
	global prefix_formula

	li = []
	if operator_type is 'b':
		operator = subformula[1]
		li.insert(0, symbols_dict[operator])
		if not subformula[0] is 'X':
			li.append(subformula[0])
		else:
			li.append(prefix_formula)

		if not subformula[2] is 'X':
			li.append(subformula[2])
		else:
			li.append(prefix_formula)

	else:
		operator = subformula[0]
		li.insert(0, symbols_dict[operator])
		if not subformula[1] is 'X':
			li.append(subformula[1])
		else:
			li.append(prefix_formula)

	prefix_formula = li


print(check_balanced_parantheses(formula) and check_formula_validity())

prefix_formula = [prefix_formula, ]
print(prefix_formula)








