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
noncomputable section

namespace QuantumDesigns

open Complex Matrix Finset

/-! ## Signs, powers of `i`, and the `0/1` lift -/

/-- The sign character `v ↦ (-1)^v` of `ZMod 2`. -/
def tp_sgn (v : ZMod 2) : ℂ := if v = 0 then 1 else -1

theorem tp_zmod2_cases (v : ZMod 2) : v = 0 ∨ v = 1 := by
  revert v; decide

theorem tp_sgn_zero : tp_sgn 0 = 1 := by simp [tp_sgn]

theorem tp_sgn_one : tp_sgn 1 = -1 := by simp [tp_sgn]

theorem tp_sgn_add (u v : ZMod 2) : tp_sgn (u + v) = tp_sgn u * tp_sgn v := by
  rcases tp_zmod2_cases u with rfl | rfl <;> rcases tp_zmod2_cases v with rfl | rfl
  · simp [tp_sgn_zero]
  · simp [tp_sgn_zero]
  · simp [tp_sgn_zero]
  · rw [show (1 + 1 : ZMod 2) = 0 by decide, tp_sgn_zero, tp_sgn_one]; ring

theorem tp_star_sgn (v : ZMod 2) : star (tp_sgn v) = tp_sgn v := by
  unfold tp_sgn; split_ifs <;> simp

theorem tp_norm_sgn (v : ZMod 2) : ‖tp_sgn v‖ = 1 := by
  unfold tp_sgn; split_ifs <;> simp

/-- Integer powers of `i`. -/
def tp_om (m : ℤ) : ℂ := I ^ m

theorem tp_om_add (a b : ℤ) : tp_om (a + b) = tp_om a * tp_om b :=
  zpow_add₀ I_ne_zero a b

theorem tp_om_four_mul (m : ℤ) : tp_om (4 * m) = 1 := by
  rw [tp_om, _root_.zpow_mul, show (I ^ (4 : ℤ)) = I ^ (4 : ℕ) from zpow_ofNat I 4, I_pow_four, _root_.one_zpow]

theorem tp_om_two_mul (m : ℤ) : tp_om (2 * m) = tp_sgn (m : ZMod 2) := by
  rw [tp_om, _root_.zpow_mul, show (I ^ (2 : ℤ)) = I ^ (2 : ℕ) from zpow_ofNat I 2, I_sq, tp_sgn]
  split_ifs with h
  · exact (ZMod.intCast_eq_zero_iff_even.1 h).neg_one_zpow
  · exact (Int.not_even_iff_odd.1 (fun he => h (ZMod.intCast_eq_zero_iff_even.2 he))).neg_one_zpow

theorem tp_norm_om (m : ℤ) : ‖tp_om m‖ = 1 := by
  rw [tp_om, norm_zpow, norm_I, _root_.one_zpow]

theorem tp_star_mul_self {z : ℂ} (hz : ‖z‖ = 1) : star z * z = 1 := by
  have h := Complex.conj_mul' z
  rw [hz] at h
  simpa using h

/-- The `0/1` lift of `ZMod 2` to `ℤ`. -/
def tp_u (v : ZMod 2) : ℤ := (v.val : ℤ)

theorem tp_u_add (a b : ZMod 2) : tp_u (a + b) = tp_u a + tp_u b - 2 * tp_u a * tp_u b := by
  revert a b; decide

theorem tp_u_cast (v : ZMod 2) : ((tp_u v : ℤ) : ZMod 2) = v := by
  simp [tp_u]

/-! ## The quadratic form and its ℤ/4 identity -/

/-- The `ℤ`-valued quadratic form `x̃ᵀ S̃ x̃` of the `0/1` lifts. -/
def tp_Q {n : ℕ} (S : Matrix (Fin n) (Fin n) (ZMod 2)) (x : Fin n → ZMod 2) : ℤ :=
  ∑ j, ∑ k, tp_u (S j k) * tp_u (x j) * tp_u (x k)

/-- The `ℤ`-valued bilinear form `x̃ᵀ S̃ t̃` of the `0/1` lifts. -/
def tp_P {n : ℕ} (S : Matrix (Fin n) (Fin n) (ZMod 2)) (x t : Fin n → ZMod 2) : ℤ :=
  ∑ j, ∑ k, tp_u (S j k) * tp_u (x j) * tp_u (t k)

theorem tp_antisym_sum {n : ℕ} (s T : Fin n → Fin n → ℤ) (hs : ∀ j k, s j k = s k j)
    (hT : ∀ j k, T j k = - T k j) : ∑ j, ∑ k, s j k * T j k = 0 := by
  have h : ∑ j, ∑ k, s j k * T j k = ∑ j, ∑ k, s k j * T k j := Finset.sum_comm
  have h2 : ∑ j, ∑ k, s k j * T k j = - ∑ j, ∑ k, s j k * T j k := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hs k j, hT k j]; ring
  linarith

theorem tp_Q_add {n : ℕ} (S : Matrix (Fin n) (Fin n) (ZMod 2)) (hS : S.IsSymm)
    (x t : Fin n → ZMod 2) :
    ∃ m : ℤ, tp_Q S (x + t) = tp_Q S x + tp_Q S t + 2 * tp_P S x t + 4 * m := by
  set s : Fin n → Fin n → ℤ := fun j k => tp_u (S j k) with hs_def
  set a : Fin n → ℤ := fun j => tp_u (x j) with ha
  set b : Fin n → ℤ := fun j => tp_u (t j) with hb
  refine ⟨∑ j, ∑ k, s j k * (a j * b j * (a k * b k) - a j * b j * (a k + b k)), ?_⟩
  have key := tp_antisym_sum s
    (fun j k => b j * a k - a j * b k + 2 * (a j * b j) * (a k + b k)
      - 2 * (a j + b j) * (a k * b k))
    (fun j k => by simp only [hs_def]; rw [hS.apply j k]) (fun j k => by ring)
  rw [← sub_eq_zero, ← key]
  simp only [tp_Q, tp_P, Pi.add_apply, tp_u_add, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  simp only [hs_def, ha, hb]
  ring

theorem tp_P_cast {n : ℕ} (S : Matrix (Fin n) (Fin n) (ZMod 2)) (x t : Fin n → ZMod 2) :
    ((tp_P S x t : ℤ) : ZMod 2) = x ⬝ᵥ (S *ᵥ t) := by
  simp only [tp_P, dotProduct, mulVec, Int.cast_sum, Int.cast_mul, tp_u_cast, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem tp_om_Q_add {n : ℕ} (S : Matrix (Fin n) (Fin n) (ZMod 2)) (hS : S.IsSymm)
    (x t : Fin n → ZMod 2) :
    tp_om (tp_Q S (x + t)) = tp_om (tp_Q S x) * tp_om (tp_Q S t) * tp_sgn (x ⬝ᵥ (S *ᵥ t)) := by
  obtain ⟨m, hm⟩ := tp_Q_add S hS x t
  rw [hm, tp_om_add, tp_om_four_mul, tp_om_add, tp_om_add, tp_om_two_mul, tp_P_cast, mul_one]

/-! ## Character sums over `(ZMod 2)ⁿ` -/

theorem tp_sum_sgn {n : ℕ} (w : Fin n → ZMod 2) :
    ∑ x : Fin n → ZMod 2, tp_sgn (x ⬝ᵥ w) =
      if w = 0 then (Fintype.card (Fin n → ZMod 2) : ℂ) else 0 := by
  split_ifs with hw
  · subst hw; simp [tp_sgn_zero]
  · obtain ⟨j, hj⟩ : ∃ j, w j ≠ 0 := by
      by_contra h; push_neg at h; exact hw (funext h)
    have hj1 : w j = 1 := (tp_zmod2_cases (w j)).resolve_left hj
    set y0 : Fin n → ZMod 2 := Pi.single j 1
    have hy : y0 ⬝ᵥ w = 1 := by simp [y0, single_dotProduct, hj1]
    have h1 : ∑ x : Fin n → ZMod 2, tp_sgn ((x + y0) ⬝ᵥ w) = ∑ x, tp_sgn (x ⬝ᵥ w) :=
      Fintype.sum_equiv (Equiv.addRight y0) _ _ (fun x => rfl)
    simp only [add_dotProduct, hy, tp_sgn_add, tp_sgn_one, ← Finset.sum_mul] at h1
    have h2 : (2 : ℂ) * ∑ x : Fin n → ZMod 2, tp_sgn (x ⬝ᵥ w) = 0 := by linear_combination -h1
    simpa using h2

theorem tp_normSq_sum {n : ℕ} (D : Matrix (Fin n) (Fin n) (ZMod 2))
    (hD : ∀ t, D *ᵥ t = 0 → t = 0) (g : (Fin n → ZMod 2) → ℂ)
    (hg1 : ∀ x, star (g x) * g x = 1)
    (hg : ∀ x t, g (x + t) = g x * g t * tp_sgn (x ⬝ᵥ (D *ᵥ t))) :
    star (∑ x, g x) * ∑ x, g x = (Fintype.card (Fin n → ZMod 2) : ℂ) := by
  have h0 : g 0 = 1 := by
    have h := hg 0 0
    simp only [add_zero, zero_dotProduct, tp_sgn_zero, mul_one] at h
    have hne : g 0 ≠ 0 := fun h' => by simpa [h'] using hg1 0
    have : g 0 * 1 = g 0 * g 0 := by rw [mul_one]; exact h
    exact (mul_left_cancel₀ hne this).symm
  calc star (∑ x, g x) * ∑ x, g x = ∑ x, ∑ y, star (g x) * g y := by
        rw [star_sum, Finset.sum_mul_sum]
    _ = ∑ x, ∑ t, star (g x) * g (x + t) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        exact (Fintype.sum_equiv (Equiv.addLeft x) _ _ (fun t => rfl)).symm
    _ = ∑ x, ∑ t, g t * tp_sgn (x ⬝ᵥ (D *ᵥ t)) := by
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun t _ => ?_
        rw [hg, ← mul_assoc, ← mul_assoc, hg1, one_mul]
    _ = ∑ t, g t * ∑ x, tp_sgn (x ⬝ᵥ (D *ᵥ t)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [Finset.mul_sum]
    _ = ∑ t : Fin n → ZMod 2, if t = 0 then (Fintype.card (Fin n → ZMod 2) : ℂ) else 0 := by
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [tp_sum_sgn]
        by_cases ht : t = 0
        · subst ht; simp [h0]
        · rw [if_neg (fun h => ht (hD t h)), if_neg ht, mul_zero]
    _ = (Fintype.card (Fin n → ZMod 2) : ℂ) := by simp

theorem hasCompleteMUBs_two_pow_internal (n : ℕ) (hn : 1 ≤ n) : HasCompleteMUBs (2 ^ n) := sorry

end QuantumDesigns
