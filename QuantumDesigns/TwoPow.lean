module

public import QuantumDesigns.Defs

/-!
# Complete sets of mutually unbiased bases in dimension `2ⁿ`

Lane **twopow** (the stretch; kill criterion in ARCH.md). Let `K = GaloisField 2 n` (`Fintype.ofFinite`;
`GaloisField.card 2 n (hn : n ≠ 0) : Nat.card K = 2 ^ n`), `V = Fin n → ZMod 2` with a basis
`β : Basis (Fin n) (ZMod 2) K` (`Module.finBasis`; `Module.finrank (ZMod 2) K = n` from the cardinality, or
`GaloisField.finrank`). For `a : K` let `B_a (x, y) = Algebra.trace (ZMod 2) K (a * β x * β y)`, a symmetric bilinear
form on `V` with Gram matrix `S_a : Matrix (Fin n) (Fin n) (ZMod 2)`, `S_a j k = trace (a β_j β_k)`. The map
`a ↦ S_a` is additive, and `S_a` is nonsingular for `a ≠ 0`: the trace form of a finite separable extension is
nondegenerate (`Algebra.traceForm_nondegenerate (ZMod 2) K`, `IsSeparable`/`IsGalois` of `GaloisField`), and
`x ↦ a x` is a bijection.

**The ℤ/4 lift.** For `x : Fin n → ZMod 2` write `x̃ : Fin n → ℤ` with entries `0, 1` (`ZMod.val`) and
`Q_a(x) = Σ_{j,k} S̃_a j k · x̃ j · x̃ k ∈ ℤ` (the symmetric `0/1` lift of `S_a`, `S̃ = ZMod.val ∘ S`). Entries of the
basis `a`, column `b : V`, row `x : V`: `(√2ⁿ)⁻¹ · i^{Q_a(x)} · (−1)^{b · x}` with `b · x = Σ_j b̃_j x̃_j ∈ ℤ`
(powers of `Complex.I` with integer exponents, `zpow`, or `i^{(Q mod 4)}`). The key identity, over ℤ then mod 4:
`Q_a(x + y) = Q_a(x) + Q_a(y) + 2 B̃_a(x, y) − 4 (…)` where `x + y` in `V` is the xor, `(x + y)~ = x̃ + ỹ − 2 x̃ ỹ`
coordinatewise, so `Q_a(x + y) ≡ Q_a(x) + Q_a(y) + 2 Σ_{j,k} S̃ j k x̃ j ỹ k (mod 4)`, every other term carrying a factor
`4` (the cross terms `−2 x̃_j ỹ_j` enter `Q` with coefficient `2 S̃ … · (x̃_k + ỹ_k)`, hence `≡ 0 mod 4` once
multiplied out: check by expanding `(u − 2w)ᵀ S (u − 2w)` with `u = x̃ + ỹ`, `w = x̃ ỹ`). Then, as in the odd case, with `f = Q_a − Q_{a'}` (NOT `Q_{a−a'}`: the `0/1` lift of a difference is not the difference of
lifts on the diagonal, mod 4; the identity that holds is `f(x ⊕ t) ≡ f(x) + f(t) + 2 xᵀ(S_a − S_{a'}) t (mod 4)`, which
follows from the one above applied to `Q_a` and `Q_{a'}`): `‖Σ_x i^{f(x)} (−1)^{c·x}‖² = Σ_t i^{f(t)} (−1)^{c·t}
Σ_y (−1)^{ỹᵀ(S̃_a − S̃_{a'}) t̃}` and the inner sum is `2ⁿ · [(S_a − S_{a'}) t = 0]`, which for `a ≠ a'` forces `t = 0`; so
the squared norm is `2ⁿ`, and the entry of the relative unitary has squared norm `2ⁿ / 4ⁿ = 1/2ⁿ`. Unitarity of each basis is the case `a = a'` (`Σ_y (−1)^{c·y} = 2ⁿ [c = 0]`).
The desk's exact replay (`bench/rt-069-finite-quantum-designs/lanes/desk/replay.py`) confirms the construction for
`n ≤ 4`, including nonsingularity of every difference `S_a − S_{a'}`.

If the identity in ℤ/4 is awkward, an equivalent route is to work in `ZMod 4` from the start with `x̃ : Fin n → ZMod 4`
taking values in `{0, 1}` (`ZMod.castHom`? no: lift by `ZMod.val`), and the character `k ↦ Complex.I ^ k.val` on
`ZMod 4` (`ZMod.stdAddChar` at `N = 4` is this character up to the choice of root).
-/

@[expose] public section

namespace QuantumDesigns

theorem hasCompleteMUBs_two_pow_internal (n : ℕ) (hn : 1 ≤ n) : HasCompleteMUBs (2 ^ n) := sorry

end QuantumDesigns
