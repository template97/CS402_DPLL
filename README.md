# CS402_DPLL
2019 Spring KAIST CS402 DPLL project

- Deadline
May 20 midight

- What to submit
1. source code
2. summary (1~2 page)

- Input format
https://www.satcompetition.org/2009/format-benchmarks2009.html

c
c start with comments
c
c 
p cnf 5 3
1 -5 4 0
-1 5 3 4 0
-3 -4 0

python2 solvepy2.py "testn.cnf" --- when solvepy2.py is found,
python3 solvepy3.py "testn.cnf" --- when solvepy3.py is found.

- Output format
<unsat>
s UNSATISFIABLE

<sat>
s SATISFIABLE
v 2 5 -7 0


- Test cases
https://www.cs.ubc.ca/~hoos/SATLIB/benchm.html
http://people.sc.fsu.edu/~jburkardt/data/cnf/cnf.html
