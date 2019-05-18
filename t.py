import numpy as np

y = np.zeros(5)

x = y

if(np.amax(x) == 0):
	print("#")
(a) = np.where(x == np.amax(x) ) 
print(a[0][0])

