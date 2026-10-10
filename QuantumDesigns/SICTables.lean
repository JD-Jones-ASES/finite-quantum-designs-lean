module

/-!
# The Hoggar overlaps, kernel-checked

The 64 vectors `v_{a,b}(x) = (−1)^{b·(x ⊕ a)} ψ(x ⊕ a)` in `ℤ[i]⁸` (`a, b, x < 8`, `⊕` the bitwise exclusive or,
`b·y` the parity of `b &&& y`), with the fiducial `ψ = (−1 + 2i, 1, 1, 1, 1, 1, 1, 1)`, each Gaussian integer stored
as its real and imaginary parts. The vector with index `i < 64` is `v_{i / 8, i % 8}`. The integer inner product
`⟨u, v⟩ = Σ_x conj(u x) v x` has real part `Σ (ur vr + ui vi)` and imaginary part `Σ (ur vi − ui vr)`;
`hg_overlaps` checks, by kernel evaluation, that its squared modulus is `144` on the diagonal and `16` off it, and
that the diagonal value is the real number `12`. No imports.
-/

@[expose] public section

namespace QuantumDesigns

/-- The sign `(−1)^{popcount y}` for `y < 8`. -/
def hg_sgn (y : Nat) : Int :=
  if (y &&& 1) ^^^ ((y >>> 1) &&& 1) ^^^ ((y >>> 2) &&& 1) = 0 then 1 else -1

/-- Real part of the fiducial `(−1 + 2i, 1, …, 1)`. -/
def hg_fr (y : Nat) : Int := if y = 0 then -1 else 1

/-- Imaginary part of the fiducial. -/
def hg_fi (y : Nat) : Int := if y = 0 then 2 else 0

/-- Real part of coordinate `x` of the vector with index `i`. -/
def hg_vr (i x : Nat) : Int := hg_sgn ((i % 8) &&& (x ^^^ (i / 8))) * hg_fr (x ^^^ (i / 8))

/-- Imaginary part of coordinate `x` of the vector with index `i`. -/
def hg_vi (i x : Nat) : Int := hg_sgn ((i % 8) &&& (x ^^^ (i / 8))) * hg_fi (x ^^^ (i / 8))

/-- One term of the real part of the inner product. -/
def hg_tr (i j x : Nat) : Int := hg_vr i x * hg_vr j x + hg_vi i x * hg_vi j x

/-- One term of the imaginary part of the inner product. -/
def hg_ti (i j x : Nat) : Int := hg_vr i x * hg_vi j x - hg_vi i x * hg_vr j x

/-- Real part of the integer inner product. -/
def hg_ipRe (i j : Nat) : Int :=
  hg_tr i j 0 + hg_tr i j 1 + hg_tr i j 2 + hg_tr i j 3 + hg_tr i j 4 + hg_tr i j 5 + hg_tr i j 6 + hg_tr i j 7

/-- Imaginary part of the integer inner product. -/
def hg_ipIm (i j : Nat) : Int :=
  hg_ti i j 0 + hg_ti i j 1 + hg_ti i j 2 + hg_ti i j 3 + hg_ti i j 4 + hg_ti i j 5 + hg_ti i j 6 + hg_ti i j 7

/-- The diagonal inner products are `12`. -/
theorem hg_diag : ∀ i, i < 64 → hg_ipRe i i = 12 ∧ hg_ipIm i i = 0 := by decide +kernel

/-- The squared moduli of the off-diagonal inner products are `16`. -/
theorem hg_overlaps : ∀ i, i < 64 → ∀ j, j < 64 → i ≠ j →
    hg_ipRe i j * hg_ipRe i j + hg_ipIm i j * hg_ipIm i j = 16 := by decide +kernel

end QuantumDesigns
