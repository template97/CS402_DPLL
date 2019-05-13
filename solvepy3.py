import sys
import numpy as np
import operator

VAR_NUM = 0
CLS_NUM = 0
MAX_ITER = 20
default_file = "./uf20-91.tar/uf20-01.cnf"

_input = [] # pure input formula
P_NONE = 0
P_POS = 1
P_NEG = 1 << 1
P_NOT = 1 << 2

def main():
	get_input()
	FA = _input

	(result, new_FA, new_A) = DPLL(FA, [], 0)

	if not result:
		print("s UNSATISFIABLE")
	else: 
		print("s SATISFIABLE")
		print(new_A)

def DPLL(FA, A, lev):
	global VAR_NUM, CLS_NUM
	db = False
	if(db): print("\nDPLL start", A, "\n",FA)

	FA_temp = []

	new_FA = FA[:]
	new_A = A[:]
	while(FA_temp != new_FA):
		#print(new_A)
		FA_temp = new_FA[:]
		pure = []
		(pure, count) = variable_count(new_FA, new_A)			# count variable appearing

		(result, new_FA, new_A) = pure_literal_elimination(new_FA, new_A, pure)	# eiliminate pure literal
		if not result:
			if(db): print("wrong 1")
			return (False, new_FA, new_A)
		elif(new_FA == []):
			if(db): print("good 1")
			return (True, new_FA, new_A)
		#print(new_A, new_FA)

		(result, new_FA, new_A) = unit_propagation(new_FA, new_A)			# threat unit clause
		if not result:
			if(db): print("wrong 2")
			return (False, FA, A)
		elif(new_FA == []):
			if(db): print("good 2")
			return (True, new_FA, new_A)

	if(db): print("\nafter propagation", new_A, "\n", new_FA)
	return select_and_branch(new_FA, new_A, count, lev)

def select_and_branch(_FA, _A, count, lev):
	global VAR_NUM, CLS_NUM
	db = False

	print(lev, end = ' ')
	#if(db): print("select and branch", A)
	#count_sorted = sorted(count.items, key = abs(operator.itemgetter(1)), reverse = True)
	
	for (var, cnt) in sorted(count.items(), key =lambda x:abs(x[1])):#, reverse = True):
		if (var != 0) and (var not in _A) and ((-1 * var) not in _A):
			
			FA = _FA[:]
			A = _A[:]
			new_FA = []
			new_A = []
			#print(lev, var, "- 1 ", A)
			(result, new_FA, new_A) = add_and_check(FA, A, var)
			if result:
				(new_result, new_FA, new_A) = DPLL(new_FA, new_A, lev + 1)
				if new_result:
					if(db and cnt > 0): print("select : ", var, "succeed")
					if(db): print("good 3")
					return (new_result, new_FA, new_A)
			
			FA = _FA[:]
			A = _A[:]
			new_FA = []
			new_A = []
			#print(lev,var, "- 2 ", A)
			(result, new_FA, new_A) = add_and_check(FA, A, (-1 * var))
			if result:
				(new_result, new_FA, new_A) = DPLL(new_FA, new_A, lev +1)
				if new_result:
					if(db and cnt <= 0): print("select : ", (-1 *var), "succeed")
					if(db): print("good 4")
					return (new_result, new_FA, new_A)
	if(db): print("wrong 4")
	return (False, FA, A)


def variable_count(FA, A):
	global VAR_NUM, CLS_NUM, P_NEG, P_POS, P_NONE, P_NOT
	db = False

	pure = [P_NONE for j in range(VAR_NUM + 1)]	
	count = dict() #0 for j in range(VAR_NUM + 1)]

	for j in range(VAR_NUM + 1):
		count[j] = 0

	for clause in FA:
		for var in clause:
			abs_val = abs(var)
		
			if(pure[abs_val] == P_NONE):
				if(var > 0):
					pure[abs_val] = P_POS
				else:
					pure[abs_val] = P_NEG
			elif( (pure[abs_val] == P_POS and var < 0) or (pure[abs_val] == P_NEG and var > 0)):
				pure[abs_val] = P_NOT

			if(var < 0):
				count[abs_val] -= 1
			else:
				count[abs_val] += 1
	return (pure, count)

def pure_literal_elimination(FA, A, pure):
	global VAR_NUM, CLS_NUM , P_NONE, P_POS, P_NEG, P_NOT
	db = False

	#if(db): print("\npure check")
	
	result = True
	new_FA = FA[:]
	new_A = A[:]
	for var in range(1, VAR_NUM+1):
		if(pure[var] == P_POS):
			if(db): print(var, "is pure")
			(result, new_FA, new_A) = add_and_check(new_FA, new_A, var)
			return (result, new_FA, new_A)
		
		if(pure[var] == P_NEG):
			if(db): print((-1 * var), "is pure")
			(result, new_FA, new_A) = add_and_check(new_FA, new_A, (-1 * var))
			return (result, new_FA, new_A)

	return (result, new_FA, new_A)

def unit_propagation(FA, A):
	global VAR_NUM, CLS_NUM
	db = False

	#if(db): print("\nunit propagation")
	new_FA = FA[:]
	new_A = A[:]
	result = True

	for clause in FA:
		if len(clause) == 1:
			if(db): print(clause, "is unit clause")#" of ", FA)
			(result, new_FA, new_A) = add_and_check(FA, A, clause[0])
			return (result, new_FA, new_A)

	return (result, new_FA, new_A)

def apply_A_by_guess(_FA, _A):
	global VAR_NUM, CLS_NUM, default_file

	db = False

	new_FA = []
	FA = _FA[:]
	A = _A[:]
	if(db): print("apply_A_by_guess", FA, A)

	
	for _clause in FA:
		clause = _clause[:]
		remove_var = []
		clause_SAT = False

		for var in clause:
			if var in A: # the clause is true !
				clause_SAT = True
				break
			if (-1 * var) in A:
				remove_var.append(var)

		if(not clause_SAT):
			for var in remove_var:
				clause.remove(var)
			if clause == []:
				if(db): print("apply fail")#, FA)
				return (False, FA, A)
				#print("s UNSATISFIABLE")
				#exit(0)
			else:
				new_FA.append(clause[:])

	# FA = new_FA
	#if(db): print()
	return (True, new_FA, A)
	#if new_FA == []:
		#print("s SATISFIABLE")
		#print(A)
		#exit(0)

def add_and_check(_FA, _A, num):
	global VAR_NUM, CLS_NUM
	db = False

	FA = _FA[:]
	A = _A[:]
	if(db): print("add_and_check", A, num)


	A.append(num)
	A = list(set(A))

	temp = []
	for i in A:
		temp.append(abs(i))
	temp = list(set(temp))

	if(db): print(A, temp)
	if( len(A) > len(temp)):
		return (False, FA, A)
		#print("s UNSATISFIABLE")
		#exit(0)
	else:
		return apply_A_by_guess(FA, A)


def get_input():
	global VAR_NUM, CLS_NUM, default_file, _input

	db = False
	if len(sys.argv) == 1:
		file_name = default_file
		#if(db): print("wrong input #0")
		#exit(-1)
	else:
		file_name = sys.argv[1]

	phase = 0
	cls_cnt = 0

	with open(file_name, 'r') as f:

		for buf in f:
			if( buf[0] == 'c'):
				if(phase != 0):
					if(db): print("wrong input #1")
					exit(-1)
				if(db): print(buf)
			
			elif( buf[0] == 'p' ):
				if( phase != 0 ):
					if(db): print("wrong input #2")
					exit(-1)
				args = buf.split()
				VAR_NUM = int(args[2])
				CLS_NUM = int(args[3])

				phase += 1
				if(db): print(buf)
			else:
				if(phase < 1):
					if(db): print("wrong input #3")
					exit(-1)
				phase += 1
				cls_cnt += 1
				args = buf.split()
				try:
					tmp = []
					for arg in args:
						val = int(arg)
						if(val == 0):
							break
						abs_val = abs(val)
						if(abs_val > VAR_NUM):
							if(db): print("wrong input #5")
							exit(-1)
						tmp.append(val)
		
					_input.append(tmp)
					if(db): print(tmp)
				except ValueError:
					if(db): print("wrong input #4")
					exit(-1)
				if(cls_cnt == CLS_NUM):
					break

	if(db): print("complete input sequence")
	if(db): print(_input)
	# input end 

if __name__ == '__main__':
	main()
