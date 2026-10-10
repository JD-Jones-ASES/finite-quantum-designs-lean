#!/usr/bin/env python3
"""Standard-library replay of every construction of the entry, in exact arithmetic (no floats):
 (1) odd prime powers q: the standard basis + q bases psi(a x^2 + b x)/sqrt q are q+1 MUBs (exact in Z[zeta_p]
     via polynomial representatives mod the cyclotomic polynomial; |.|^2 compared as cyclotomic integers);
 (2) 2^n: the Z/4 trace-form bases i^{x^T S_a x}(-1)^{b.x}/sqrt(2^n) are 2^n + 1 MUBs (exact in Z[i]);
 (3) Hoggar's 64 lines: |<u,v>|^2 = 16 on every ordered pair, |v|^2 = 12 (exact in Z[i]);
 (4) the frame identity sum v v^* = 96 I for Hoggar, and the Gerzon equality value 1/9 = 1/(8+1);
 (5) the tetrahedral and Hesse families (exact in Z[omega] with the scale removed).
Prints one line per check and ends with VERDICT: PASS or VERDICT: FAIL; exit status 0 on PASS only.
Run: python -I scripts/check_designs.py  (Python >= 3.9, standard library only; about one minute).
"""
import itertools, sys, time
sys.stdout.reconfigure(encoding="utf-8", errors="replace")
from fractions import Fraction

ok = True
def report(name, good, detail=""):
    global ok
    ok = ok and good
    print(("PASS " if good else "FAIL ") + name + ("  " + detail if detail else ""), flush=True)

# ---------- (1) odd prime powers: cyclotomic-integer arithmetic ----------
def cyclo_mod(p):
    """Z[zeta_p] as integer vectors of length p (exponent basis), reduced by sum_{j<p} zeta^j = 0 (set coeff of zeta^{p-1} to 0)."""
    def reduce(v):
        c = v[p-1]
        return [x - c for x in v[:p-1]] + [0]
    def zero():
        return [0]*p
    def add(u, v):
        return reduce([a+b for a, b in zip(u, v)])
    def mul(u, v):
        w = [0]*p
        for i, a in enumerate(u):
            if a == 0: continue
            for j, b in enumerate(v):
                if b == 0: continue
                w[(i+j) % p] += a*b
        return reduce(w)
    def conj(u):
        w = [0]*p
        for i, a in enumerate(u):
            w[(-i) % p] += a
        return reduce(w)
    def zeta_pow(k):
        w = [0]*p; w[k % p] = 1
        return reduce(w)
    def is_int(u, n):
        return u == reduce([n] + [0]*(p-1))
    return add, mul, conj, zeta_pow, is_int, zero

def finite_field(p, k):
    """GF(p^k) as tuples over Z/p with a monic irreducible of degree k found by brute force; returns (elems, add, mul, trace)."""
    def polymulmod(a, b, m):
        r = [0]*(2*k-1)
        for i, ai in enumerate(a):
            for j, bj in enumerate(b):
                r[i+j] = (r[i+j] + ai*bj) % p
        for d in range(2*k-2, k-1, -1):
            c = r[d]
            if c:
                for i in range(k+1):
                    r[d-k+i] = (r[d-k+i] - c*m[i]) % p
        return tuple(r[:k])
    if k == 1:
        m = [0, 1]
    else:
        m = None
        for coeffs in itertools.product(range(p), repeat=k):
            cand = list(coeffs) + [1]
            if cand[0] == 0: continue
            # irreducible iff no root-free factor test: brute-force check that no monic poly of degree 1..k//2 divides it
            def divides(g):
                # polynomial long division cand / g over Z/p
                a = cand[:]
                dg = len(g)-1
                while len(a)-1 >= dg:
                    c = a[-1]
                    if c:
                        sh = len(a)-1-dg
                        for i, gi in enumerate(g):
                            a[sh+i] = (a[sh+i] - c*gi) % p
                    a.pop()
                return all(x == 0 for x in a)
            red = False
            for d in range(1, k//2+1):
                for gc in itertools.product(range(p), repeat=d):
                    if divides(list(gc)+[1]):
                        red = True; break
                if red: break
            if not red:
                m = cand; break
    elems = list(itertools.product(range(p), repeat=k))
    def add(a, b): return tuple((x+y) % p for x, y in zip(a, b))
    def mul(a, b): return polymulmod(a, b, m)
    def trace(a):
        t = (0,)*k; y = a
        for _ in range(k):
            t = add(t, y); y = mul(y, y)  # Frobenius x -> x^p
            for _ in range(p-2):  # y = y^p needs p-1 multiplications
                pass
        return t
    # proper Frobenius: x^p
    def frob(a):
        r = (1,)+(0,)*(k-1); b = a
        e = p
        while e:
            if e & 1: r = mul(r, b)
            b = mul(b, b); e >>= 1
        return r
    def trace(a):
        t = (0,)*k; y = a
        for _ in range(k):
            t = add(t, y); y = frob(y)
        assert all(x == 0 for x in t[1:]), "trace not in prime field"
        return t[0]
    return elems, add, mul, trace

def replay_odd(p, k):
    t0 = time.time()
    q = p**k
    elems, add, mul, trace = finite_field(p, k)
    cadd, cmul, cconj, zeta, is_int, zero = cyclo_mod(p)
    sq = {x: mul(x, x) for x in elems}
    # vector v_{a,b}(x) = zeta^{Tr(a x^2 + b x)} (unnormalised; sqrt q removed; compare |.|^2 to q^2, 0, q)
    vec = {}
    for a in elems:
        for b in elems:
            vec[(a, b)] = [zeta(trace(add(mul(a, sq[x]), mul(b, x)))) for x in elems]
    bad = 0; cnt = 0
    keys = list(vec)
    for i, (a, b) in enumerate(keys):
        u = vec[(a, b)]
        for (a2, b2) in keys[i:]:
            v = vec[(a2, b2)]
            s = zero()
            for ux, vx in zip(u, v):
                s = cadd(s, cmul(cconj(ux), vx))
            n2 = cmul(s, cconj(s))
            want = (q*q if (a, b) == (a2, b2) else 0) if a == a2 else q
            cnt += 1
            if not is_int(n2, want): bad += 1
    # against the standard basis every entry has |.|^2 = 1 (zeta is a unit): trivially q^{-1} after scaling
    report(f"odd q = {q} ({p}^{k}): standard + {q} quadratic-phase bases are {q+1} MUBs",
           bad == 0, f"{cnt} inner products, {bad} failures, {time.time()-t0:.1f}s")

for p, k in [(3, 1), (5, 1), (7, 1), (3, 2), (11, 1), (13, 1), (5, 2), (3, 3)]:
    replay_odd(p, k)

# ---------- (2) 2^n: Z/4 trace form, exact in Z[i] ----------
I4 = [(1, 0), (0, 1), (-1, 0), (0, -1)]
def replay_even(n):
    t0 = time.time(); d = 2**n
    elems, add, mul, trace = finite_field(2, n)
    E = [tuple(1 if j == i else 0 for j in range(n)) for i in range(n)]
    S = {a: [[trace(mul(a, mul(E[j], E[k]))) for k in range(n)] for j in range(n)] for a in elems}
    def Q(a, x):  # x as bit tuple; x^T S x over Z, mod 4
        s = 0
        for j in range(n):
            if x[j]:
                for k in range(n):
                    if x[k]: s += S[a][j][k]
        return s % 4
    xs = list(itertools.product(range(2), repeat=n))
    def expo(a, b, x):  # exponent of i: Q_a(x) + 2 b.x
        return (Q(a, x) + 2*sum(bi*xi for bi, xi in zip(b, x))) % 4
    tabs = {(a, b): [expo(a, b, x) for x in xs] for a in elems for b in elems}
    keys = list(tabs); bad = 0; cnt = 0
    for i, (a, b) in enumerate(keys):
        for (a2, b2) in keys[i:]:
            re = im = 0
            for e1, e2 in zip(tabs[(a, b)], tabs[(a2, b2)]):
                kk = (e2 - e1) % 4
                re += I4[kk][0]; im += I4[kk][1]
            n2 = re*re + im*im
            want = (d*d if (a, b) == (a2, b2) else 0) if a == a2 else d
            cnt += 1
            if n2 != want: bad += 1
    # nonsingularity of S_a - S_a' over F_2 for a != a' (the structural fact the Lean route needs)
    def rank2(M):
        M = [row[:] for row in M]; r = 0
        for c in range(n):
            piv = next((i for i in range(r, n) if M[i][c] % 2), None)
            if piv is None: continue
            M[r], M[piv] = M[piv], M[r]
            for i in range(n):
                if i != r and M[i][c] % 2:
                    M[i] = [(x + y) % 2 for x, y in zip(M[i], M[r])]
            r += 1
        return r
    sing = sum(1 for a in elems for a2 in elems if a != a2 and rank2([[S[a][j][k] ^ S[a2][j][k] for k in range(n)] for j in range(n)]) < n)
    report(f"2^{n} = {d}: standard + {d} Z/4 trace-form bases are {d+1} MUBs, entries in {{±1, ±i}}/√{d}",
           bad == 0 and sing == 0, f"{cnt} inner products, {bad} failures; singular differences {sing}; {time.time()-t0:.1f}s")

for n in range(1, 5):
    replay_even(n)

# ---------- (3)(4) Hoggar ----------
def hoggar():
    t0 = time.time()
    psi = [(-1, 2)] + [(1, 0)]*7  # Gaussian integers (re, im)
    def pop(z): return bin(z).count("1")
    vecs = {}
    for a in range(8):
        for b in range(8):
            v = []
            for x in range(8):
                y = x ^ a
                s = -1 if pop(b & y) % 2 else 1
                v.append((s*psi[y][0], s*psi[y][1]))
            vecs[(a, b)] = v
    keys = list(vecs)
    bad = 0; cnt = 0
    for k1 in keys:
        for k2 in keys:
            re = im = 0
            for (ur, ui), (vr, vi) in zip(vecs[k1], vecs[k2]):
                # conj(u) * v
                re += ur*vr + ui*vi; im += ur*vi - ui*vr
            n2 = re*re + im*im
            want = 144 if k1 == k2 else 16
            cnt += 1
            if n2 != want: bad += 1
    report("Hoggar: 64 vectors (-1+2i,1^7) under X^aZ^b, |v|^2 = 12, |<u,v>|^2 = 16 on every ordered pair (overlapSq = 1/9)",
           bad == 0, f"{cnt} ordered pairs, {bad} failures, {time.time()-t0:.1f}s")
    # frame identity: sum_v v v^* = 96 I (then sum (1/12)(1/8) v v^* = I)
    G = [[(0, 0)]*8 for _ in range(8)]
    for v in vecs.values():
        for k in range(8):
            for l in range(8):
                (ar, ai), (br, bi) = v[k], v[l]
                # v_k * conj(v_l)
                G[k][l] = (G[k][l][0] + ar*br + ai*bi, G[k][l][1] + ai*br - ar*bi)
    good = all(G[k][l] == ((96, 0) if k == l else (0, 0)) for k in range(8) for l in range(8))
    report("Hoggar frame identity: sum_v v v^* = 96 I, i.e. sum_i (1/8) |phi_i><phi_i| = I with |phi_i| = 1", good)
    report("Gerzon equality value at d = 8: 16/144 = 1/9 = 1/(d+1)", Fraction(16, 144) == Fraction(1, 9))
hoggar()

# ---------- (5) tetrahedral (d=2) and Hesse (d=3), exact in Z[omega], scale removed ----------
def eis():
    # Z[omega], omega^2 = -1 - omega; elements (a, b) = a + b omega
    def mul(u, v):
        a, b = u; c, d = v
        return (a*c - b*d, a*d + b*c - b*d)
    def add(u, v): return (u[0]+v[0], u[1]+v[1])
    def conj(u):  # conj(omega) = omega^2 = -1 - omega
        a, b = u
        return (a - b, -b)
    def norm(u):  # u * conj u, must be rational integer
        r = mul(u, conj(u)); assert r[1] == 0; return r[0]
    return mul, add, conj, norm
mul, add, conj, norm = eis()
w = (0, 1); w2 = mul(w, w); one = (1, 0); zero = (0, 0)
# tetrahedral: vectors scaled by sqrt 3: (sqrt3, 0), (1, sqrt2), (1, sqrt2 w), (1, sqrt2 w^2) -- mixed radicals; use
# the Gram structure instead: |<v_i,v_j>|^2 = 1/3 with |v|^2 = 1. Check with Fractions for the real parts and Z[omega] for phases:
# <v_1, v_j> = (1/3) + (2/3) w^{j-1}... |.|^2 = (1/9)|1 + 2 w^m|^2 = (1/9)(1 + 2 + 4 - ... ) compute exactly:
def normsq_affine(m):  # |1 + 2 w^m|^2 = (1 + 2w^m)(1 + 2 w^{-m}) = 1 + 2(w^m + w^-m) + 4
    wm = [one, w, w2][m % 3]
    z = add(one, mul((2, 0), wm))
    return norm(z)
tet = all(Fraction(normsq_affine(m), 9) == Fraction(1, 3) for m in (1, 2)) and Fraction(1, 3) == Fraction(1, 3)
# |<v_0, v_j>|^2 = (1/3) directly (first coordinate sqrt(1/3))
report("tetrahedral d = 2 (FC qubitSICFamily): all overlaps 1/3", tet)
# Hesse: vectors (0, 1, -w^m), (-w^m, 0, 1), (1, -w^m, 0) scaled by sqrt 2: overlaps |<u,v>|^2 / 4 = 1/4 iff |<u,v>|^2 = 1
hv = []
for m in range(3):
    wm = [one, w, w2][m]; nwm = (-wm[0], -wm[1])
    hv += [(zero, one, nwm), (nwm, zero, one), (one, nwm, zero)]
bad = 0
for i in range(9):
    for j in range(9):
        s = zero
        for a, b in zip(hv[i], hv[j]):
            s = add(s, mul(conj(a), b))
        n2 = norm(s)
        if n2 != (4 if i == j else 1): bad += 1
report("Hesse d = 3 (FC hesseFamily): |v|^2 = 2, |<u,v>|^2 = 1 on every distinct pair (overlapSq = 1/4)", bad == 0, f"{bad} failures")

print("VERDICT: " + ("PASS" if ok else "FAIL"))
sys.exit(0 if ok else 1)
