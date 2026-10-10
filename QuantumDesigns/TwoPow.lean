module

public import QuantumDesigns.Defs

/-!
# Complete sets of mutually unbiased bases in dimension `2ⁿ`

Write `V = Fin n → ZMod 2` and lift `ZMod 2` to `ℤ` by `v ↦ v.val ∈ {0, 1}` (`tp_u`). For a symmetric
`S : Matrix (Fin n) (Fin n) (ZMod 2)` put `Q_S(x) = Σ_{j,k} S̃ j k · x̃ j · x̃ k ∈ ℤ` (`tp_Q`) and let the basis
attached to `S` have, in row `x` and column `b` (both enumerated by `Fin (2 ^ n)`), the entry
`i^{Q_S(x)} (−1)^{b·x} / √2ⁿ` (`tp_mat`).

**The ℤ/4 identity** (`tp_Q_add`, `tp_om_Q_add`). Coordinatewise `(x + y)~ = x̃ + ỹ − 2 x̃ ỹ`; expanding and using the
symmetry of `S̃`, every term other than `Q_S(x) + Q_S(y) + 2 x̃ᵀ S̃ ỹ` carries a factor `4`, so
`i^{Q_S(x + y)} = i^{Q_S(x)} i^{Q_S(y)} (−1)^{xᵀ S y}`.

**The character sums.** `Σ_x (−1)^{x·w} = 2ⁿ [w = 0]` (`tp_sum_sgn`) gives unitarity of every basis. For two
symmetric `S, S'` and `g(x) = conj(i^{Q_S(x)}) i^{Q_{S'}(x)} (−1)^{c·x}`, the identity gives
`g(x + t) = g(x) g(t) (−1)^{xᵀ (S − S') t}`, hence `|Σ_x g(x)|² = Σ_t g(t) Σ_x (−1)^{xᵀ(S − S')t} = 2ⁿ` when `S − S'`
is nonsingular (`tp_normSq_sum`); every entry of the relative unitary then has squared modulus `2ⁿ / 4ⁿ = 1/2ⁿ`
(`tp_unbiased`). With the standard basis this proves `tp_mubs_of_symmetric_spread`: `2ⁿ` symmetric binary matrices
with nonsingular pairwise differences give `2ⁿ + 1` mutually unbiased bases.

**The family.** Let `K = GaloisField 2 n` with a basis `β` over `ZMod 2` (`GaloisField.finrank`) and
`S_a j k = Algebra.trace (ZMod 2) K (a β_j β_k)` for `a : K`. Each `S_a` is symmetric, `S_a − S_{a'} = S_{a − a'}`,
and `S_c t = 0` with `c ≠ 0` forces `t = 0`: the linear form `z ↦ tr(c y z)`, `y = Σ t_k β_k`, vanishes on the basis,
so `c y = 0` by nondegeneracy of the trace form of the separable extension `K / ZMod 2`
(`traceForm_nondegenerate`), hence `y = 0` and `t = 0` (`tp_exists_spread`).
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
  · obtain ⟨j, hj⟩ : ∃ j, w j ≠ 0 := Function.ne_iff.1 hw
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
        · have hDt : D *ᵥ t ≠ 0 := fun h => ht (hD t h)
          simp only [hDt, ht, ↓reduceIte, mul_zero]
    _ = (Fintype.card (Fin n → ZMod 2) : ℂ) := by simp

/-! ## The bases -/

theorem tp_card_V (n : ℕ) : Fintype.card (Fin n → ZMod 2) = 2 ^ n := by simp

/-- An enumeration of `(ZMod 2)ⁿ` by `Fin (2 ^ n)`. -/
def tp_e (n : ℕ) : Fin (2 ^ n) ≃ (Fin n → ZMod 2) :=
  (Fintype.equivFinOfCardEq (tp_card_V n)).symm

/-- The basis attached to `S`: row `x`, column `b`, entry `i^{Q(x)} (-1)^{b·x} / √2ⁿ`. -/
def tp_mat {n : ℕ} (S : Matrix (Fin n) (Fin n) (ZMod 2)) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  fun i j => (((Real.sqrt (2 ^ n : ℝ))⁻¹ : ℝ) : ℂ) *
    (tp_om (tp_Q S (tp_e n i)) * tp_sgn (tp_e n j ⬝ᵥ tp_e n i))

theorem tp_c_sq (n : ℕ) :
    (((Real.sqrt (2 ^ n : ℝ))⁻¹ : ℝ) : ℂ) * (((Real.sqrt (2 ^ n : ℝ))⁻¹ : ℝ) : ℂ) =
      (((2 : ℝ) ^ n)⁻¹ : ℝ) := by
  rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (by positivity)]

theorem tp_gram {n : ℕ} (S S' : Matrix (Fin n) (Fin n) (ZMod 2)) (i j : Fin (2 ^ n)) :
    (star (tp_mat S) * tp_mat S') i j = ((((2 : ℝ) ^ n)⁻¹ : ℝ) : ℂ) *
      ∑ x : Fin n → ZMod 2, star (tp_om (tp_Q S x)) * tp_om (tp_Q S' x) *
        tp_sgn (x ⬝ᵥ (tp_e n i + tp_e n j)) := by
  rw [Matrix.mul_apply, Finset.mul_sum]
  refine Fintype.sum_equiv (tp_e n) _ _ (fun k => ?_)
  simp only [Matrix.star_apply, tp_mat, star_mul', tp_star_sgn]
  rw [← tp_c_sq n, show star ((((Real.sqrt (2 ^ n : ℝ))⁻¹ : ℝ) : ℂ)) =
      (((Real.sqrt (2 ^ n : ℝ))⁻¹ : ℝ) : ℂ) from Complex.conj_ofReal _, dotProduct_add,
    tp_sgn_add, dotProduct_comm (tp_e n k) (tp_e n i), dotProduct_comm (tp_e n k) (tp_e n j)]
  ring

theorem tp_add_eq_sub {n : ℕ} (y z : Fin n → ZMod 2) : y + z = y - z :=
  funext fun k => by
    simp only [Pi.add_apply, Pi.sub_apply, sub_eq_add_neg, ZMod.neg_eq_self_mod_two]

theorem tp_mat_unitary {n : ℕ} (S : Matrix (Fin n) (Fin n) (ZMod 2)) :
    tp_mat S ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  rw [tp_gram]
  have h1 : ∀ x : Fin n → ZMod 2, star (tp_om (tp_Q S x)) * tp_om (tp_Q S x) = 1 :=
    fun x => tp_star_mul_self (tp_norm_om _)
  simp only [h1, one_mul, tp_sum_sgn, tp_card_V, Matrix.one_apply]
  have hij : tp_e n i + tp_e n j = 0 ↔ i = j := by
    rw [tp_add_eq_sub, sub_eq_zero, (tp_e n).injective.eq_iff]
  by_cases h : i = j
  · subst h
    simp only [hij.2 rfl, ↓reduceIte]
    push_cast
    exact inv_mul_cancel₀ (pow_ne_zero n (two_ne_zero' ℂ))
  · have h' : tp_e n i + tp_e n j ≠ 0 := mt hij.1 h
    simp only [h', h, ↓reduceIte, mul_zero]

theorem tp_norm_entry {n : ℕ} (S : Matrix (Fin n) (Fin n) (ZMod 2)) (i j : Fin (2 ^ n)) :
    ‖tp_mat S i j‖ ^ 2 = ((2 ^ n : ℕ) : ℝ)⁻¹ := by
  simp only [tp_mat, norm_mul, tp_norm_om, tp_norm_sgn, mul_one, Complex.norm_real,
    Real.norm_eq_abs]
  rw [abs_of_nonneg (by positivity), inv_pow, Real.sq_sqrt (by positivity)]
  push_cast
  rfl

theorem tp_unbiased {n : ℕ} (S S' : Matrix (Fin n) (Fin n) (ZMod 2)) (hS : S.IsSymm)
    (hS' : S'.IsSymm) (hD : ∀ t, (S - S') *ᵥ t = 0 → t = 0) (i j : Fin (2 ^ n)) :
    ‖(star (tp_mat S) * tp_mat S') i j‖ ^ 2 = ((2 ^ n : ℕ) : ℝ)⁻¹ := by
  rw [tp_gram]
  set c := tp_e n i + tp_e n j
  set g : (Fin n → ZMod 2) → ℂ :=
    fun x => star (tp_om (tp_Q S x)) * tp_om (tp_Q S' x) * tp_sgn (x ⬝ᵥ c) with hg_def
  have hg1 : ∀ x, star (g x) * g x = 1 := fun x =>
    tp_star_mul_self (by simp only [hg_def, norm_mul, norm_star, tp_norm_om, tp_norm_sgn, mul_one])
  have hg : ∀ x t, g (x + t) = g x * g t * tp_sgn (x ⬝ᵥ ((S - S') *ᵥ t)) := by
    intro x t
    have hd : x ⬝ᵥ ((S - S') *ᵥ t) = x ⬝ᵥ (S *ᵥ t) + x ⬝ᵥ (S' *ᵥ t) := by
      rw [sub_mulVec, dotProduct_sub, sub_eq_add_neg, ZMod.neg_eq_self_mod_two]
    simp only [hg_def, tp_om_Q_add S hS, tp_om_Q_add S' hS', add_dotProduct, tp_sgn_add,
      star_mul', tp_star_sgn, hd]
    ring
  have hN := tp_normSq_sum (S - S') hD g hg1 hg
  rw [tp_card_V] at hN
  have hN' : ‖∑ x, g x‖ ^ 2 = (2 : ℝ) ^ n := by
    have h3 := Complex.conj_mul' (∑ x, g x)
    have h2 : ((‖∑ x, g x‖ ^ 2 : ℝ) : ℂ) = (((2 : ℝ) ^ n : ℝ) : ℂ) := by
      rw [Complex.ofReal_pow, ← h3]
      exact hN.trans (by push_cast; ring)
    exact_mod_cast h2
  rw [norm_mul, mul_pow, hN', Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  push_cast
  have h2n : (2 : ℝ) ^ n ≠ 0 := by positivity
  field_simp

/-- **The combinatorial core.** A family of `2ⁿ` symmetric binary `n × n` matrices whose pairwise
differences are nonsingular gives, with the standard basis, a complete set of `2ⁿ + 1` mutually
unbiased bases in dimension `2ⁿ`. -/
theorem tp_mubs_of_symmetric_spread (n : ℕ) (S : Fin (2 ^ n) → Matrix (Fin n) (Fin n) (ZMod 2))
    (hsym : ∀ a, (S a).IsSymm)
    (hspread : ∀ a a', a ≠ a' → ∀ t, (S a - S a') *ᵥ t = 0 → t = 0) :
    HasCompleteMUBs (2 ^ n) := by
  refine ⟨Fin.cases 1 (fun a => ⟨tp_mat (S a), tp_mat_unitary _⟩), ?_⟩
  intro m m' hne
  rcases Fin.eq_zero_or_eq_succ m with rfl | ⟨a, rfl⟩ <;>
    rcases Fin.eq_zero_or_eq_succ m' with rfl | ⟨a', rfl⟩
  · exact absurd rfl hne
  · intro i j
    simp only [Fin.cases_zero, Fin.cases_succ, relativeUnitary, OneMemClass.coe_one, star_one,
      one_mul]
    exact tp_norm_entry _ i j
  · intro i j
    simp only [Fin.cases_zero, Fin.cases_succ, relativeUnitary, OneMemClass.coe_one, mul_one,
      Matrix.star_apply, norm_star]
    exact tp_norm_entry _ j i
  · intro i j
    simp only [Fin.cases_succ, relativeUnitary]
    exact tp_unbiased _ _ (hsym a) (hsym a')
      (hspread a a' (fun h => hne (by rw [h]))) i j

/-! ## The family from `GaloisField 2 n` -/

/-- The trace forms `(x, y) ↦ tr(a x y)` of `GaloisField 2 n` in a basis are symmetric, and the
difference of two of them is nonsingular. -/
theorem tp_exists_spread (n : ℕ) (hn : 1 ≤ n) :
    ∃ S : Fin (2 ^ n) → Matrix (Fin n) (Fin n) (ZMod 2),
      (∀ a, (S a).IsSymm) ∧ ∀ a a', a ≠ a' → ∀ t, (S a - S a') *ᵥ t = 0 → t = 0 := by
  classical
  let _ : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  have hn0 : n ≠ 0 := by omega
  have hcard : Fintype.card (GaloisField 2 n) = 2 ^ n := by
    rw [← Nat.card_eq_fintype_card]; exact GaloisField.card 2 n hn0
  let e : Fin (2 ^ n) ≃ GaloisField 2 n := (Fintype.equivFinOfCardEq hcard).symm
  let β : Module.Basis (Fin n) (ZMod 2) (GaloisField 2 n) :=
    Module.finBasisOfFinrankEq (ZMod 2) (GaloisField 2 n) (GaloisField.finrank 2 hn0)
  let T : GaloisField 2 n → Matrix (Fin n) (Fin n) (ZMod 2) :=
    fun a j k => Algebra.trace (ZMod 2) (GaloisField 2 n) (a * β j * β k)
  refine ⟨fun a => T (e a), fun a => ?_, fun a a' hne t ht => ?_⟩
  · refine Matrix.IsSymm.ext fun j k => ?_
    show Algebra.trace (ZMod 2) (GaloisField 2 n) (e a * β k * β j) =
      Algebra.trace (ZMod 2) (GaloisField 2 n) (e a * β j * β k)
    rw [mul_right_comm]
  · have hc : e a - e a' ≠ 0 := sub_ne_zero.2 (e.injective.ne hne)
    have hT : T (e a) - T (e a') = T (e a - e a') := by
      ext j k
      show T (e a) j k - T (e a') j k = T (e a - e a') j k
      simp only [T, sub_mul]
      exact (map_sub _ _ _).symm
    simp only at ht
    rw [hT] at ht
    set c := e a - e a'
    set y : GaloisField 2 n := ∑ k, t k • β k with hy_def
    have hy : ∀ j, Algebra.trace (ZMod 2) (GaloisField 2 n) (c * y * β j) = 0 := by
      intro j
      have h := congrFun ht j
      simp only [mulVec, dotProduct, T, Pi.zero_apply] at h
      rw [← h, hy_def, Finset.mul_sum, Finset.sum_mul, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [show c * (t k • β k) * β j = t k • (c * β j * β k) by
        simp only [Algebra.smul_def]; ring, map_smul, smul_eq_mul, mul_comm]
    have hL : Algebra.traceForm (ZMod 2) (GaloisField 2 n) (c * y) = 0 :=
      β.ext (fun j => by rw [Algebra.traceForm_apply, hy j, LinearMap.zero_apply])
    have hcy : c * y = 0 :=
      (traceForm_nondegenerate (ZMod 2) (GaloisField 2 n)).1 (c * y)
        (fun z => by rw [hL, LinearMap.zero_apply])
    have hy0 : y = 0 := (mul_eq_zero.1 hcy).resolve_left hc
    calc t = β.equivFun (β.equivFun.symm t) := (β.equivFun.apply_symm_apply t).symm
      _ = 0 := by rw [Module.Basis.equivFun_symm_apply, ← hy_def, hy0, map_zero]

theorem hasCompleteMUBs_two_pow_internal (n : ℕ) (hn : 1 ≤ n) : HasCompleteMUBs (2 ^ n) := by
  obtain ⟨S, hsym, hspread⟩ := tp_exists_spread n hn
  exact tp_mubs_of_symmetric_spread n S hsym hspread

end QuantumDesigns
