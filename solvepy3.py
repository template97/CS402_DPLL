import sys
import numpy as np
import operator

VAR_NUM = 0
CLS_NUM = 0
MAX_ITER = 1000
default_path = "./uf20-91.tar/"

# pure input formula
P_NONE = 0
P_POS = 1
P_NEG = 1 << 1
P_NOT = 1 << 2

def main(num):
	global VAR_NUM, CLS_NUM


	_input = []
	FA = []
	(VAR_NUM, CLS_NUM, _input) = get_input(num)

	FA = _input[:]

	(result, __FA, __A) = DPLL(FA, [], 0)

	if not result:
		print("s UNSATISFIABLE")
	else: 
		print("s SATISFIABLE")
		print(__A)

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
		count = []
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

	#print(_A)
	if(db): print(lev, end = ' ')
	#if(db): print("select and branch", A)
	max_cnt = 0
	min_cnt = 0
	selected_var = 0
	selected_cnt = 0
	#print(count)
	#print(_FA)
	
	for (_var, _cnt) in count.items():
		if( _var not in _A and (-1 * _var) not in _A and _var != 0):
			#print(_var, end = ' ')
			if(_cnt >= max_cnt):
				max_cnt = _cnt
				if(max_cnt >= abs(min_cnt)):
					selected_var = _var
					selected_cnt = _cnt

			if(_cnt <= min_cnt):
				min_cnt = _cnt
				if(abs(min_cnt) > max_cnt):
					selected_var = _var
					selected_cnt = _cnt

	#count_sorted = sorted(count.items, key = abs(operator.itemgetter(1)), reverse = True)
	
	if( selected_cnt >= 0 ):
		var = selected_var
	elif( selected_cnt < 0):
		var = selected_var * -1

	FA = _FA[:]
	A = _A[:]
	new_FA = []
	new_A = []
	(result, new_FA, new_A) = add_and_check(FA, A, var)
	if result:
		if(db): print("[", var, "]")
		(new_result, new_FA, new_A) = DPLL(new_FA, new_A, lev + 1)
		if new_result:
			if(db): print("select : ", var, "succeed")
			if(db): print("good 3")
			return (new_result, new_FA, new_A)

	FA = _FA[:]
	A = _A[:]
	new_FA = []
	new_A = []
	#print(lev,var, "- 2 ", A)
	(result, new_FA, new_A) = add_and_check(FA, A, (-1 * var))
	if result:
		if(db): print("[", (-1 * var), "]")
		(new_result, new_FA, new_A) = DPLL(new_FA, new_A, lev +1)
		if new_result:
			if(db): print("select : ", (-1 *var), "succeed")
			if(db): print("good 4")
			return (new_result, new_FA, new_A)

			
	if(db): print("wrong :", lev, "[", var, "]")
	return (False, FA, A)


def variable_count(FA, A):
	global VAR_NUM, CLS_NUM, P_NEG, P_POS, P_NONE, P_NOT
	db = False

	_pure = [P_NONE for j in range(VAR_NUM + 1)]	
	_count = dict() #0 for j in range(VAR_NUM + 1)]

	for j in range(VAR_NUM + 1):
		_count[j] = 0

	for clause in FA:
		for var in clause:
			abs_val = abs(var)

			if(_pure[abs_val] == P_NONE):
				if(var > 0):
					_pure[abs_val] = P_POS
				else:
					_pure[abs_val] = P_NEG
			elif( (_pure[abs_val] == P_POS and var < 0) or (_pure[abs_val] == P_NEG and var > 0)):
				_pure[abs_val] = P_NOT

			if(var < 0):
				_count[abs_val] -= 1
			else:
				_count[abs_val] += 1
	return (_pure, _count)

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


def get_input(num):
	global VAR_NUM, CLS_NUM, default_file, _input

	db = False
	if num == 0: # input exist
		file_name = sys.argv[1]
	else:
		file_name = default_path + "uf20-0" + str(num) + ".cnf"
	#print(file_name)
	phase = 0
	cls_cnt = 0

	_inp = []
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
				v_num = int(args[2])
				c_num = int(args[3])

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
						if(abs_val > v_num):
							if(db): print("wrong input #5")
							exit(-1)
						tmp.append(val)
		
					_inp.append(tmp)
					if(db): print(tmp)
				except ValueError:
					if(db): print("wrong input #4")
					exit(-1)
				if(cls_cnt == c_num):
					break

	if(db): print("complete input sequence")
	if(db): print(_inp)
	#print(v_num, c_num)
	return (v_num, c_num, _inp)
	# input end 

if __name__ == '__main__':	
	if len(sys.argv) != 1:
		main(0)
	else:
		for i in range(1,1000):
			print(i, end = ' ')
			main(i)
