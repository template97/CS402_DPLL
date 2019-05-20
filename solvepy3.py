''' KAIST 2019 Spring 
	CS 402 Introduction to Logic for Computer Science
	DPLL project
	20160400 Juhyeong Yu 
	template97@kaist.ac.kr '''

import sys
import numpy as np
import operator
import time
import copy

VAR_NUM = 0
CLS_NUM = 0
# default_path = "../testcases/uf20-91.tar/"
# default_format = "uf20-0"
default_path = "../testcases/uf100-430.tar/"#uf20-91.tar/"
default_format = "uf100-0"#uf20-0"
# pure input formula
P_NONE = 0
P_POS = 1
P_NEG = 1 << 1
P_NOT = 1 << 2

def init_and_start(num):
	global VAR_NUM, CLS_NUM, VSIDS, var_select

	_input = []
	FA = []
	(VAR_NUM, CLS_NUM, _input, _count) = get_input(num)
	VSIDS = np.zeros(VAR_NUM + 1)
	#FA = copy.deepcopy(_input)
	FA = _input
	var_select = sorted(_count.items(), key=lambda x: x[1])

	(result, __FA, __A) = DPLL(FA, [], 0)

	if not result:
		print("s UNSATISFIABLE")
		return False
	else: 
		print("s SATISFIABLE")
		print("v", end = ' ')
		for a in __A:
			print(a, end = ' ')
		print("")
		return True
		
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
	_count = dict()
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

				for j in range(v_num + 1):
					_count[j] = 0
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
		
						if(val < 0):
							_count[abs_val] -= 1
						else:
							_count[abs_val] += 1
					_inp.append(tmp)
					# if(db): print(tmp)
				except ValueError:
					# if(db): print("wrong input #4")
					exit(-1)
				if(cls_cnt == c_num):
					break

	# if(db): print("complete input sequence")
	# if(db): print(_inp)
	return (v_num, c_num, _inp, _count)

def DPLL(FA, A, lev):
	global VAR_NUM, CLS_NUM, VSIDS
	db = True
	# print("\nDPLL start", A, "\n",FA, "\n")
	#print(lev, end = ' ')
	if FA == []:
		return (True, FA, A)

	new_FA = FA #copy.deepcopy(FA)
	new_A = A #A[:]

	(result, new_FA, new_A) = unit_propagation(new_FA, new_A)			# threat unit clause
	if not result:
		# if(db): print("wrong 2")
		return (False, new_FA, new_A)
	elif(new_FA == []):
		# if(db): print("good 2")
		return (True, new_FA, new_A)
	# if not is_res_ok(new_FA):
	# 	print("resolution fail2")#, new_FA)
	# 	return (False, new_FA, new_A)
	return select_and_branch(new_FA, new_A, lev)

def unit_propagation(new_FA, new_A):
	global VAR_NUM, CLS_NUM
	# db = False

	# new_FA = copy.deepcopy(FA)
	# new_A = A[:]
	result = True
	check = True
	while(check):
		check = False
		for clause in new_FA:
			if len(clause) == 1:
				# if(db): print(clause, "is unit clause")#, " of ", A)
				check = True
				(result, new_FA, new_A) = add_and_check(new_FA, new_A, clause[0])
				if not result:
					return (result, new_FA, new_A)
				break;
	return (result, new_FA, new_A)

def select_and_branch(FA, A, lev):
	global VAR_NUM, CLS_NUM, VSIDS,var_select
	# db = False
	# if(db): 
	
	#print(lev, end = ' ')
	# print(_FA, _A)

	#print(VSIDS, A)
	while(True):
		#print(np.amax(VSIDS), end = ' ')
		if np.amax(VSIDS) == 0:
			#print(var_select)
			for var, __ in var_select:
				if var not in A and (var * -1) not in A:
					break
			break
		else:
			a = np.where(VSIDS == np.amax(VSIDS)) 
			var = a[0][0]
			if var not in A and (var * -1) not in A:
				break
			else:
				VSIDS[var] = 0
	var *= -1
	(result, new_FA, new_A) = add_and_check(FA, A, var)
	if result:
		(new_result, new_FA, new_A) = DPLL(new_FA, new_A, lev + 1)
		if new_result:
			# if(db): print("good 3")
			return (new_result, new_FA, new_A)

	(result, new_FA, new_A) = add_and_check(FA, A, (-1 * var))
	if result:
		(new_result, new_FA, new_A) = DPLL(new_FA, new_A, lev +1)
		if new_result:
			# if(db): print("good 4")
			return (new_result, new_FA, new_A)
	# if(db): print("wrong :", lev, "[", var, "]")
	return (False, FA, A)

def add_and_check(_FA, _A, num):
	global VAR_NUM, CLS_NUM
	db = False

	#FA = _FA[:]	
	# if(db): print("add_and_check", A, num)

	if num in _A:
		print("error", num, _A)
		exit(-1)
	elif (-1 * num) in _A:
		#print(num, _A)
		return (False, _FA, _A)
	else:
		A = _A[:]
		A.append(num)
		# print("add and check:",num, _FA)
		return apply_A(_FA, A, num)

def apply_A(_FA, _A, _var):
	global VAR_NUM, CLS_NUM, VSIDS

	# db = False

	new_FA = []
	FA = _FA #copy.deepcopy(_FA)
	A = _A #[:]
	# if(db):print("apply_A", FA, A)

	failed = False
	var_cls = np.array([False for j in range(VAR_NUM + 1)])

	for _clause in FA:
		clause = _clause[:]
		remove_var = []

		if _var in clause or (-1 * _var) in clause:
			for v in clause:
				var_cls[abs(v)] = True

		if not failed:
			if _var in clause:
				__ = True
			elif (-1 * _var) in clause:
				clause.remove(-1 * _var)
				if clause == []:
					failed = True					
				else:
					new_FA.append(clause)
			else:
				new_FA.append(clause)

	if failed:
		var_cls[abs(_var)] = False
		VSIDS[var_cls] += 1
		VSIDS *= 0.95
		#rint(VSIDS)
		return (False, FA, A)
	else:
		return (True, new_FA, A)

'''
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
	new_FA = FA #copy.deepcopy(FA)
	new_A = A #[:]
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
'''	

if __name__ == '__main__':	
	if len(sys.argv) != 1:
		init_and_start(0)
	else:
		start = time.time()
		sat = 0
		unsat = 0
		for i in range(1, 1001):
			#print(i, end = ': ')
			startTime = time.time()

			if init_and_start(i):
				sat += 1
			else:
				unsat += 1

			endTime = time.time() - startTime
			#print("time: %.5f" % endTime)
			#print("")				
		end = time.time() - start
		#print("\nTotal time: %.5f   SAT: %d UNSAT: %d" % (end, sat, unsat))
		#print("")				

