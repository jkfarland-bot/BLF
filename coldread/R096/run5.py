import sys; sys.argv=['x','5']
exec(open('analyze.py').read().replace("for n in range(1,nmax+1):","for n in [5]:"))
