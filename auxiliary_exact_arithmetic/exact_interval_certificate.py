"""Rational interval certificate for the algebraic Gaussian-mixture alias.

Every verification below uses fractions.Fraction; decimal output is display only.
"""
from fractions import Fraction as F
from dataclasses import dataclass
from itertools import permutations
from math import comb, ceil
from exact_gaussian_alias import poly, evaluate

@dataclass(frozen=True)
class I:
    lo:F
    hi:F
    def __init__(self,lo,hi=None):
        object.__setattr__(self,'lo',F(lo));object.__setattr__(self,'hi',F(lo if hi is None else hi))
        assert self.lo<=self.hi
    def __add__(self,b):
        b=conv(b);return I(self.lo+b.lo,self.hi+b.hi)
    __radd__=__add__
    def __neg__(self):return I(-self.hi,-self.lo)
    def __sub__(self,b):return self+-conv(b)
    def __rsub__(self,b):return conv(b)+-self
    def __mul__(self,b):
        b=conv(b);a=[self.lo*b.lo,self.lo*b.hi,self.hi*b.lo,self.hi*b.hi];return I(min(a),max(a))
    __rmul__=__mul__
    def __truediv__(self,b):
        b=conv(b);assert b.lo*b.hi>0;return self*I(1/b.hi,1/b.lo)
    def __rtruediv__(self,b):return conv(b)/self
    def __pow__(self,n):
        assert isinstance(n,int) and n>=0
        if n==0:return I(1)
        if self.lo>=0:return I(self.lo**n,self.hi**n)
        if self.hi<=0:return (-self)**n if n%2==0 else -((-self)**n)
        return I(0,max(-self.lo,self.hi)**n) if n%2==0 else I(self.lo**n,self.hi**n)
    def show(self):return (float(self.lo),float(self.hi))
    def inside(self,a,b):return F(a)<self.lo and self.hi<F(b)
def conv(x):return x if isinstance(x,I) else I(x)
def horner(coeff,x):
    ans=I(0)
    for c in reversed(coeff):ans=ans*x+c
    return ans

def determinant(mat):
    n=len(mat);result=I(0)
    for order in permutations(range(n)):
        inv=sum(order[i]>order[j] for i in range(n) for j in range(i+1,n))
        term=I(-1 if inv%2 else 1)
        for i,j in enumerate(order):term=term*mat[i][j]
        result=result+term
    return result

def normal_moment(k,mu,var):
    # Gaussian raw moments, with exact integer coefficients.
    if k==0:return I(1)
    if k==1:return mu
    return mu*normal_moment(k-1,mu,var)+(k-1)*var*normal_moment(k-2,mu,var)

def jacobian(pi,mu0,mu1,v0,v1):
    rows=[]
    for k in range(1,6):
        rows.append([
            normal_moment(k,mu1,v1)-normal_moment(k,mu0,v0),
            (1-pi)*k*normal_moment(k-1,mu0,v0),
            pi*k*normal_moment(k-1,mu1,v1),
            (1-pi)*comb(k,2)*normal_moment(k-2,mu0,v0) if k>=2 else I(0),
            pi*comb(k,2)*normal_moment(k-2,mu1,v1) if k>=2 else I(0),
        ])
    return rows

def verify():
    P=poly(F(3,2),F(-5,4),F(-10))
    p=I(F(634,1000),F(635,1000))
    left=evaluate(P,p.lo);right=evaluate(P,p.hi)
    assert F(8,10)<left<1 and -14<right<-13
    dP=horner([i*P[i] for i in range(1,len(P))],p)
    assert dP.inside(-14652,-14447)
    print('P(left),P(right)',float(left),float(right),'dP',dP.show())
    c=(24*p**3-80*p**2+45*p+54)/(2*p*(36-8*p**3+15*p))
    s=3/(2*p)-3*c
    delta2=s*s+4*p
    delta=I(F(1738,1000),F(1748,1000))
    assert delta.lo**2<delta2.lo and delta.hi**2>delta2.hi
    mu0=(s-delta)/2;mu1=(s+delta)/2
    pi=-mu0/delta
    v0=F(5,2)-p+c*mu0;v1=F(5,2)-p+c*mu1
    orientation=delta2**4+18*delta2**2*(v1-v0)**2-135*(v1-v0)**4
    for name,interval in [('c',c),('s',s),('delta2',delta2),('pi',pi),('mu0',mu0),('mu1',mu1),('v0',v0),('v1',v1),('orientation',orientation)]:print(name,interval.show())
    assert pi.inside(F(69,100),F(72,100))
    # A strict margin keeps the corrected weight in (0.69, 0.72).
    assert pi.inside(F(696,1000),F(710,1000))
    assert mu0.inside(F(-125,100),F(-120,100))
    assert mu1.inside(F(49,100),F(54,100))
    assert v0.inside(F(57,100),F(65,100))
    assert v1.inside(F(235,100),F(244,100))
    assert orientation.inside(-840,-671)
    detJ=-(pi**2)*((1-pi)**2)*delta*orientation
    assert detJ.inside(47,68)
    J=jacobian(pi,mu0,mu1,v0,v1)
    inverse_bound=F(0)
    row_bounds=[]
    for i in range(5):
        row_bound=F(0)
        for j in range(5):
            # Inverse entry i,j uses cofactor j,i.
            minor=[[J[r][c] for c in range(5) if c!=i] for r in range(5) if r!=j]
            cofactor=determinant(minor)
            row_bound+=max(abs(cofactor.lo),abs(cofactor.hi))/detJ.lo
        inverse_bound=max(inverse_bound,row_bound)
        row_bounds.append(ceil(row_bound))
        assert row_bound<ceil(row_bound)
    print('detJ interval',detJ.show(),'inverse infinity norm upper bound',float(inverse_bound))
    print('Certified integer upper bounds for inverse row sums:',row_bounds)
    assert inverse_bound<122
    print('All root-isolation, strict parameter, and regularity certificates passed.')

if __name__=='__main__':verify()
