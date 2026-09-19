"""Exact Pearson-polynomial construction, with numerical root diagnostics only."""
from fractions import Fraction as F
from functools import reduce
from math import gcd, sqrt

def add(a,b):
    return [(a[i] if i<len(a) else F(0))+(b[i] if i<len(b) else F(0)) for i in range(max(len(a),len(b)))]
def mul(a,b):
    r=[F(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):r[i+j]+=x*y
    return r
def scale(a,b):return [x*b for x in a]
def poly(k,l,r):
    N=[2*k**3,-3*k*l,r,2*k]
    D=[4*k*k,-3*l,F(0),F(-2)]
    A=[k*k,-l,F(0),F(-2)]
    P=add(scale(mul(N,N),6),scale(mul(A,mul(D,D)),-1))
    den=1
    for p in P: den=den*p.denominator//gcd(den,p.denominator)
    P=[int(p*den) for p in P]
    gc=reduce(gcd,P)
    return [p//gc for p in P]
def evaluate(P,x):
    result=0
    for c in reversed(P):result=result*x+c
    return result
def params(p,k,l,r,m2):
    c=(r*p*p+2*k**3+2*k*p**3-3*k*l*p)/(p*(4*k*k-2*p**3-3*l*p))
    s=k/p-3*c
    delta=sqrt(s*s+4*p)
    m0=(s-delta)/2;m1=(s+delta)/2
    pi=-m0/delta
    v0=m2-p+c*m0;v1=m2-p+c*m1
    orient=delta**8+18*delta**4*(v1-v0)**2-135*(v1-v0)**4
    return pi,m0,m1,v0,v1,orient
def scan(k,l,r,m2):
    import numpy as np
    P=poly(F(k),F(l),F(r))
    print('target k,l,r,m2',k,l,r,m2,'polynomial ascending',P)
    for z in sorted(np.roots(list(reversed(P))),key=lambda z:z.real):
        if abs(z.imag)<1e-7 and z.real>0:
            p=float(z.real)
            print('p=',p,'params=',params(p,float(k),float(l),float(r),float(m2)))
if __name__=='__main__':
    scan(F(3,2),F(-5,4),F(-10),F(5,2))
    scan(F(6),F(10),F(-40),F(4))
