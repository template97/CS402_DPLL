import sys
import numpy as np
import operator
import time
import copy

VAR_NUM = 0
CLS_NUM = 0
MAX_ITER = 1000
default_path = "../testcases/uuf100-430.tar/"
default_format = "uuf100-0"
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

	#FA = copy.deepcopy(_input)
	FA = _input

	(result, __FA, __A) = DPLL(FA, [], 0)

	if not result:
		print("s UNSATISFIABLE@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@")
	else: 
		print("s SATISFIABLE")
		for a in __A:
			print(a, end = ' ')


def DPLL(FA, A, lev):
	global VAR_NUM, CLS_NUM
	db = True
	# print("\nDPLL start", A, "\n",FA, "\n")

	if FA == []:
		return (True, FA, A)

	FA_temp = []
	A_temp = []

	new_FA = copy.deepcopy(FA)
	new_A = A[:]

	at_least = True
	while(at_least or A_temp != new_A): #FA_temp != new_FA):
		#FA_temp = copy.deepcopy(new_FA)
		A_temp = new_A[:]
		pure = []
		count = []
		(pure, count) = variable_count(new_FA, new_A)			# count variable appearing

		(result, new_FA, new_A) = pure_literal_elimination(new_FA, new_A, pure)	# eiliminate pure literal
		if not result:
			# if(db): print("wrong 1")
			return (False, new_FA, new_A)
		elif(new_FA == []):
			# if(db): print("good 1")
			return (True, new_FA, new_A)



		(result, new_FA, new_A) = unit_propagation(new_FA, new_A)			# threat unit clause
		if not result:
			# if(db): print("wrong 2")
			return (False, new_FA, new_A)
		elif(new_FA == []):
			# if(db): print("good 2")
			return (True, new_FA, new_A)

		if not is_res_ok(new_FA):
			#print("resolution fail")#, new_FA)
			return (False, new_FA, new_A)

		at_least = False

	# if(db): print("\nafter propagation", new_A, "\n", new_FA)
	
	#_FA = new_FA[:]
	#_A = new_A[:]

	# if not is_res_ok(new_FA):
	# 	print("resolution fail2")#, new_FA)
	# 	return (False, new_FA, new_A)
	return select_and_branch(new_FA, new_A, count, lev)


def is_res_ok(FA): # check completeness
	global VAR_NUM, CLS_NUM

	new_FA = copy.deepcopy(FA)

	
	res = True
	while(True):
		if len(new_FA) == 1:
			return True
		if not res:
			return True

		res = False
		exist = [-1 for j in range(VAR_NUM * 2 + 2)]

		i = 0
		for clause in new_FA:
			if clause == []:
				return False
			for var in clause:
				if exist[VAR_NUM + 1 + (-1 * var)] != -1:
					resolution(clause, new_FA[exist[VAR_NUM + 1 + (-1 * var)]], var, new_FA)
					res = True
					break
				exist[VAR_NUM + 1 + var] = i
			if res:
				break
			i += 1

	return True

def resolution(cls1, cls2, var, FA):
	#n = exist[VAR_NUM + 1 + (-1 * var)]


	cls1.remove(var)
	cls2.remove(-1 * var)

	#__cls = cls2
	_cls = cls2[:]
	for v in _cls:
		if v not in cls1:
			cls1.append(v)
	#cls1.extend(_cls)
	FA.remove(cls2)


def select_and_branch(FA, A, count, lev):
	global VAR_NUM, CLS_NUM
	# db = False
	# if(db): 
	
	#print(len(A), end = ' ')

	# print(_FA, _A)
	max_cnt = 0
	min_cnt = 0
	selected_var = 0
	selected_cnt = 0
	
	for (_var, _cnt) in count.items():
		if( _var not in A and (-1 * _var) not in A and _var != 0):
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
	
	if( selected_cnt >= 0 ):
		var = selected_var * -1
	elif( selected_cnt < 0):
		var = selected_var #* -1

	# FA = copy.deepcopy(_FA)
	# A = _A[:]
	new_FA = []
	new_A = []
	(result, new_FA, new_A) = add_and_check(FA, A, var)
	if result:
		(new_result, new_FA, new_A) = DPLL(new_FA, new_A, lev + 1)
		if new_result:
			# if(db): print("good 3")
			return (new_result, new_FA, new_A)

	# FA = copy.deepcopy(_FA)
	# A = _A[:]
	new_FA = []
	new_A = []
	(result, new_FA, new_A) = add_and_check(FA, A, (-1 * var))
	if result:
		(new_result, new_FA, new_A) = DPLL(new_FA, new_A, lev +1)
		if new_result:
			# if(db): print("good 4")
			return (new_result, new_FA, new_A)

			
	# if(db): print("wrong :", lev, "[", var, "]")
	return (False, FA, A)


def variable_count(FA, A):
	global VAR_NUM, CLS_NUM, P_NEG, P_POS, P_NONE, P_NOT
	# db = False

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
	# db = False

	result = True
	new_FA = copy.deepcopy(FA)
	new_A = A[:]
	for var in range(1, VAR_NUM+1):
		if(pure[var] == P_POS):
			# if(db): print(var, "is pure")
			(result, new_FA, new_A) = add_and_check(new_FA, new_A, var)
			return (result, new_FA, new_A)
		
		if(pure[var] == P_NEG):
			# if(db): print((-1 * var), "is pure")
			(result, new_FA, new_A) = add_and_check(new_FA, new_A, (-1 * var))
			return (result, new_FA, new_A)

	return (result, new_FA, new_A)

def unit_propagation(new_FA, new_A):
	global VAR_NUM, CLS_NUM
	# db = False

	# new_FA = copy.deepcopy(FA)
	# new_A = A[:]
	result = True

	for clause in new_FA:
		if len(clause) == 1:
			# if(db): print(clause, "is unit clause", " of ", A)
			(result, new_FA, new_A) = add_and_check(new_FA, new_A, clause[0])
			return (result, new_FA, new_A)

	return (result, new_FA, new_A)

def apply_A_by_guess(_FA, _A):
	global VAR_NUM, CLS_NUM, default_file

	# db = False

	new_FA = []
	FA = copy.deepcopy(_FA)
	A = _A[:]
	# if(db): print("apply_A_by_guess", FA, A)

	
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
				# if(db): print("apply fail")#, FA)
				return (False, FA, A)
			else:
				new_FA.append(clause[:])

	return (True, new_FA, A)

def add_and_check(_FA, _A, num):
	global VAR_NUM, CLS_NUM
	db = False

	#FA = _FA[:]	
	# if(db): print("add_and_check", A, num)

	if num in _A:
		print("error")
		exit(-1)
	elif (-1 * num) in _A:
		print(num, _A)
		return (False, _FA, _A)
	else:
		A = _A[:]
		A.append(num)
		# print("add and check:",num, _FA)
		return apply_A_by_guess(_FA, A)
	
	#A = list(set(A))

	# temp = []
	# for i in A:
	# 	temp.append(abs(i))
	# temp = list(set(temp))

	# # if(db): print(A, temp)
	# if( len(A) > len(temp)):
	# 	return (False, FA, A)
	# else:
	# 	return 


def get_input(num):
	global VAR_NUM, CLS_NUM, default_file, _input

	# db = False
	if num == 0: # input exist
		file_name = sys.argv[1]
	else:
		file_name = default_path + default_format + str(num) + ".cnf"
	phase = 0
	cls_cnt = 0

	_inp = []
	with open(file_name, 'r') as f:

		for buf in f:
			if( buf[0] == 'c'):
				if(phase != 0):
					# if(db): print("wrong input #1")
					exit(-1)
				# if(db): print(buf)
			
			elif( buf[0] == 'p' ):
				if( phase != 0 ):
					# if(db): print("wrong input #2")
					exit(-1)
				args = buf.split()
				v_num = int(args[2])
				c_num = int(args[3])

				phase += 1
				# if(db): print(buf)
			else:
				if(phase < 1):
					# if(db): print("wrong input #3")
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
							# if(db): print("wrong input #5")
							exit(-1)
						tmp.append(val)
		
					_inp.append(tmp)
					# if(db): print(tmp)
				except ValueError:
					# if(db): print("wrong input #4")
					exit(-1)
				if(cls_cnt == c_num):
					break

	# if(db): print("complete input sequence")
	# if(db): print(_inp)
	return (v_num, c_num, _inp)
	
if __name__ == '__main__':	
	if len(sys.argv) != 1:
		main(0)
	else:
		for i in range(1, 6):
			print(i, end = ': ')
			startTime = time.time()
			main(i)
			endTime = time.time() - startTime
			print("\ntime:", endTime)
			print("")				
