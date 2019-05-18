import numpy as np

y = [2,3,1,3,0]

x = np.array(y)

(a) = np.where(x == np.amax(x) ) 
print(a[0][0])

