#!/usr/bin/env python3
"""Exact checks for Hardinian diagonal formulas, r=2,3.

The finite checks are not the asymptotic proof; see main.pdf (source: main.tex).
All counts are Python arbitrary-precision integers. Optional diagnostics use
SymPy exact algebra and mpmath only for *displaying* asymptotic ratios.
"""
from __future__ import annotations
import argparse
import itertools
import json
from math import comb
from pathlib import Path

ROOT = Path(__file__).resolve().parent

def d_table(N: int) -> list[list[int]]:
    """D[u][v] = sum_{j=u}^{v-1} binom(u+v,j), 0<=u<v<=N."""
    if N < 0:
        return []
    D = [[0]*(N+1) for _ in range(N+1)]
    for s in range(1, 2*N):
        prefix = [0]
        term = 1
        for j in range(s+1):
            prefix.append(prefix[-1] + term)
            if j < s:
                term = term*(s-j)//(j+1)
        for u in range(max(0, s-N), (s-1)//2+1):
            v = s-u
            D[u][v] = prefix[v]-prefix[u]
    return D

def count_all(max_n: int) -> list[dict[str,int]]:
    """All H2/H3 through max_n, O(max_n^3) integer arithmetic operations."""
    if max_n < 1:
        raise ValueError('max_n must be positive')
    D = d_table(max_n-2)
    h2 = h3 = 0
    rows = [{'n':1, 'H2':0, 'H3':0}]
    for N in range(max_n-1):
        h2 += sum(D[u][N]**2 for u in range(N))
        for u in range(N):
            for v in range(u+1,N):
                a = (D[u][v] << N) - (D[u][N] << v) + (D[v][N] << u)
                assert a >= 0, (u,v,N,a)
                h3 += a*a
        rows.append({'n':N+2,'H2':h2,'H3':h3})
    return rows

def brute_arrays(n: int, r: int) -> int:
    """Independent row-major enumeration from the original array definition."""
    endpoint = n-r-1
    if endpoint < 0:
        return 0
    a = [0]*(n*n)
    def visit(p: int) -> int:
        if p == n*n:
            return 1
        i,j = divmod(p,n)
        lo,hi = max(0,max(i,j)-r), min(max(i,j), endpoint)
        for k in ([p-n] if i else []) + ([p-1] if j else []) + ([p-n-1] if i and j else []):
            lo=max(lo,a[k]); hi=min(hi,a[k]+1)
        if p == 0:
            lo=hi=0
        if p == n*n-1:
            lo=max(lo,endpoint); hi=min(hi,endpoint)
        ans=0
        for value in range(lo,hi+1):
            a[p]=value
            ans += visit(p+1)
        return ans
    return visit(0)

def determinant(a: list[list[int]]) -> int:
    """Bareiss exact determinant, with pivoting."""
    n=len(a)
    if n==0: return 1
    a=[row[:] for row in a]
    previous=1; sign=1
    for k in range(n-1):
        if a[k][k]==0:
            p=next((p for p in range(k+1,n) if a[p][k]),None)
            if p is None: return 0
            a[k],a[p]=a[p],a[k]; sign=-sign
        pivot=a[k][k]
        for i in range(k+1,n):
            for j in range(k+1,n):
                numerator=a[i][j]*pivot-a[i][k]*a[k][j]
                assert numerator % previous == 0
                a[i][j]=numerator//previous
        for i in range(k+1,n): a[i][k]=0
        previous=pivot
    return sign*a[-1][-1]

def source_minor_count(n: int,r: int) -> int:
    """The source's complementary-minor formula, independently evaluated."""
    m=n-1
    if m<r: return 0
    choices=list(itertools.combinations(range(m),m-r))
    return sum(determinant([[comb(i+j,i) for j in J] for i in I])
               for I in choices for J in choices)

# Transcribed from the primary OEIS b-files on 2026-10-13.
# https://oeis.org/A253217/b253217.txt ; https://oeis.org/A252998/b252998.txt
PUBLISHED_H2 = [0,0,1,19,268,3568,47698,649712,9023385,127419681,
1823918697,26398702645,385582981615,5674890516295,84060883775765,
1252066289632643,18738613233957420,281620474177057788,4248088188086420832,
64290523406324922880,975830464322173456704,14850742002311881225488,
226547336492483013279388,3463477599521304894420136,53055002867950934581755010,
814196129458535463283681310,12515761528347361046998694850,
192688236724840975842818003334,2970798117955713392918707254876,
45863453850514034083843279513972,708918500049411660274524809057602,
10970490185056084630098708463002352,169950961711323001987462092191799193,
2635480579545620444838374961705089785,40907977518723916972214026491065029589,
635541529816904196745529070625664313213,9882013075470916243344848275529466770265]
PUBLISHED_H3 = [0,0,0,1,69,3072,122833,4915726,204051186,8849413857,
399736867216,18698541563923,900653139548828,44458651801451163,
2240500172425946056,114922424191743943701,5985232324581998309113,
315879022416448194306768,16866530575466182807473867,
909949468518210982067804594,49546225698236313520912253881,
2720166754877070803387321887120,150460342868943700305640582398675,
8378936691714574760295136083583638]
H3_SENTINELS = {
100:17779844553147826201147879141171055026265191641014538135523012154496634924006847149861200035209313561668608432842282034365163007330813905397408377725654172887000688209448,
101:1103802584589437781045076406872026078220543296822598582920181014806614016860180076542127304060086084322848776922330428318995330096930707527321711480626935590309182600607991}

def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-n',type=int,default=201)
    args=parser.parse_args()
    if not 101 <= args.max_n <= 500:
        parser.error('--max-n must lie in 101..500 for the supplied checks')
    rows=count_all(args.max_n)
    for n,val in enumerate(PUBLISHED_H2,1): assert rows[n-1]['H2']==val,(n,'OEIS H2')
    for n,val in enumerate(PUBLISHED_H3,1): assert rows[n-1]['H3']==val,(n,'OEIS H3')
    for n,val in H3_SENTINELS.items(): assert rows[n-1]['H3']==val,(n,'OEIS H3 sentinel')
    direct=[]
    for n in range(1,7):
        for r in (2,3):
            value=brute_arrays(n,r)
            assert value==rows[n-1][f'H{r}'],(n,r,'array definition')
            direct.append({'n':n,'r':r,'count':value})
    for n in range(3,9):
        for r in (2,3):
            assert source_minor_count(n,r)==rows[n-1][f'H{r}'],(n,r,'source minors')
    report={'max_n':args.max_n,'published_H2_prefix_matched':37,
            'published_H3_prefix_matched':24,'published_H3_sentinels_matched':[100,101],
            'original_array_definition_checked_through_n':6,
            'complementary_minor_formula_checked_through_n':8,
            'all_exact_checks_passed':True,'direct_enumeration':direct,'rows':rows}
    try:
        import sympy as sp
        q=sp.symbols('q'); moments=[1/(1-q)]
        for k in range(4): moments.append(sp.simplify(q*sp.diff(moments[-1],q)))
        z2=sp.factor(sp.det(sp.Matrix([[moments[i+j] for j in range(2)] for i in range(2)])))
        z3=sp.factor(sp.det(sp.Matrix([[moments[i+j] for j in range(3)] for i in range(3)])))
        assert sp.simplify(z2-q/(1-q)**4)==0
        assert sp.simplify(z3-4*q**3/(1-q)**9)==0
        report['weighted_Vandermonde_sums']={'r2':str(z2),'r3':str(z3)}
        import mpmath as mp
        mp.mp.dps=40
        ratios=[]
        for n in (20,50,100,201):
            if n>args.max_n: continue
            row=rows[n-1]
            ratios.append({'n':n,
                'H2_div_conjectured_leading_term':str(mp.mpf(row['H2'])*324*mp.pi*n/mp.mpf(16)**n),
                'H3_div_conjectured_leading_term':str(mp.mpf(row['H3'])*78732*mp.pi*n**3/mp.mpf(64)**n)})
        report['floating_diagnostics_not_proof']=ratios
    except ImportError:
        report['optional_symbolic_and_decimal_checks']='Skipped: sympy/mpmath unavailable'
    (ROOT/'hardinian_results.json').write_text(json.dumps(report,indent=2),encoding='utf-8')
    print('All Hardinian exact checks passed.')
    for row in report.get('floating_diagnostics_not_proof',[]): print(row)

if __name__=='__main__': main()
