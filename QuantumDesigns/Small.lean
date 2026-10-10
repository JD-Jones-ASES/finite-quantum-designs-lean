module

public import QuantumDesigns.Defs
public import QuantumDesigns.SmallTables

/-!
# Explicit complete sets in dimensions 2, 4 and 8, kernel-checked

Every entry of the `d` non-standard bases is `c · i^E` with `E ∈ {0, 1, 2, 3}` and `‖c‖² = 1/d`: for `d = 2`,
`c = (√2)⁻¹`; for `d = 4`, `c = 1/2`; for `d = 8`, `c = (1 + i)/4` (`‖c‖² = 2/16 = 1/8`). The exponent tables
`E_a(x, b) = Q_a(x) + 2 b·x mod 4` (the trace form of `𝔽_{2ⁿ}` in the polynomial basis) and their Gaussian-integer
check live in the Mathlib-free leaf `QuantumDesigns.SmallTables` (`decide +kernel`).

The soundness lemma `sm_hasMUBs` turns the integer verdict into the statement over `ℂ`:
`(c i^E)^* (c i^{E'}) = ‖c‖² i^{3E + E'}` and `Σ_x i^{k_x} = (re : ℂ) + (im : ℂ) I` with `re`, `im` the summed real
and imaginary parts of the powers of `i`; inside a basis this gives `star M * M = 1`, across bases
`‖·‖² = ‖c‖⁴ (re² + im²) = d / d² = 1/d`, and against the standard basis every entry has `‖c i^E‖² = 1/d`.
-/

@[expose] public section

namespace QuantumDesigns

open Complex Finset

theorem sm_all_spec {n : ℕ} {p : ℕ → Bool} (h : sm_all n p = true) : ∀ i < n, p i = true := by
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
    have h' : (sm_all n p && p n) = true := h
    rw [Bool.and_eq_true] at h'
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · exact ih h'.1 i hi
    · exact h'.2

theorem sm_sumRe_eq (g : ℕ → ℕ) (n : ℕ) : sm_sumRe g n = ∑ i ∈ range n, sm_re (g i) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show sm_sumRe g n + sm_re (g n) = _
    rw [Finset.sum_range_succ, ih]

theorem sm_sumIm_eq (g : ℕ → ℕ) (n : ℕ) : sm_sumIm g n = ∑ i ∈ range n, sm_im (g i) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show sm_sumIm g n + sm_im (g n) = _
    rw [Finset.sum_range_succ, ih]

theorem sm_I_pow (k : ℕ) : I ^ k = ((sm_re k : ℤ) : ℂ) + ((sm_im k : ℤ) : ℂ) * I := by
  have hk : I ^ k = I ^ (k % 4) := by
    conv_lhs => rw [← Nat.div_add_mod k 4, pow_add, pow_mul, I_pow_four, one_pow, one_mul]
  rw [hk]
  unfold sm_re sm_im
  have : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by omega
  rcases this with h | h | h | h <;> simp [h, I_sq, I_pow_three]

theorem sm_star_I_pow (e : ℕ) : star (I ^ e) = I ^ (3 * e) := by
  rw [star_pow, pow_mul, I_pow_three, Complex.star_def, conj_I]

theorem sm_sum_I_pow (g : ℕ → ℕ) (d : ℕ) :
    ∑ x : Fin d, I ^ g x = ((sm_sumRe g d : ℤ) : ℂ) + ((sm_sumIm g d : ℤ) : ℂ) * I := by
  rw [Fin.sum_univ_eq_sum_range (fun x => I ^ g x) d, sm_sumRe_eq, sm_sumIm_eq]
  simp_rw [sm_I_pow]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul]
  push_cast
  rfl

/-- The matrix of basis `a`: entry `c · i^{E_a(b, x)}` in row `x`, column `b`. -/
def sm_M (tab : List (List (List ℕ))) (c : ℂ) (d a : ℕ) : Matrix (Fin d) (Fin d) ℂ :=
  fun x b => c * I ^ sm_E tab a b x

theorem sm_relEntry (tab : List (List (List ℕ))) (c : ℂ) (d a a' : ℕ) (b b' : Fin d) :
    (star (sm_M tab c d a) * sm_M tab c d a') b b' =
      (Complex.normSq c : ℂ) * (((sm_sumRe (fun x => 3 * sm_E tab a b x + sm_E tab a' b' x) d : ℤ) : ℂ)
        + ((sm_sumIm (fun x => 3 * sm_E tab a b x + sm_E tab a' b' x) d : ℤ) : ℂ) * I) := by
  rw [← sm_sum_I_pow, Matrix.mul_apply, Finset.mul_sum, normSq_eq_conj_mul_self]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [Matrix.star_apply, sm_M, star_mul', sm_star_I_pow, pow_add, Complex.star_def]
  ring

theorem sm_unitary (tab : List (List (List ℕ))) (c : ℂ) (d : ℕ) (hd : 0 < d)
    (hc : Complex.normSq c = (d : ℝ)⁻¹) (hchk : sm_check tab d = true) (a : ℕ) (ha : a < d) :
    sm_M tab c d a ∈ Matrix.unitaryGroup (Fin d) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext b b'
  have h := sm_all_spec (sm_all_spec (sm_all_spec (sm_all_spec hchk a ha) b b.2) a ha) b' b'.2
  rw [sm_relEntry, hc]
  unfold sm_pairOK at h
  simp only [ite_true] at h
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  by_cases hbb : b = b'
  · subst hbb
    simp only [ite_true, Bool.and_eq_true, beq_iff_eq] at h
    rw [h.1, h.2, Matrix.one_apply_eq]
    push_cast
    simp only [zero_mul, add_zero]
    field_simp
  · have hv : (b : ℕ) ≠ b' := fun e => hbb (Fin.ext e)
    simp only [hv, ite_false, Bool.and_eq_true, beq_iff_eq] at h
    rw [h.1, h.2, Matrix.one_apply_ne hbb]
    simp

theorem sm_cross (tab : List (List (List ℕ))) (c : ℂ) (d : ℕ) (hd : 0 < d)
    (hc : Complex.normSq c = (d : ℝ)⁻¹) (hchk : sm_check tab d = true) (a a' : ℕ) (ha : a < d)
    (ha' : a' < d) (haa : a ≠ a') (b b' : Fin d) :
    ‖(star (sm_M tab c d a) * sm_M tab c d a') b b'‖ ^ 2 = (d : ℝ)⁻¹ := by
  have h := sm_all_spec (sm_all_spec (sm_all_spec (sm_all_spec hchk a ha) b b.2) a' ha') b' b'.2
  unfold sm_pairOK at h
  simp only [haa, ite_false, beq_iff_eq] at h
  rw [sm_relEntry, hc, Complex.sq_norm, Complex.normSq_mul]
  set re := sm_sumRe (fun x => 3 * sm_E tab a b x + sm_E tab a' b' x) d
  set im := sm_sumIm (fun x => 3 * sm_E tab a b x + sm_E tab a' b' x) d
  have h2 : ((re : ℝ) ^ 2 + (im : ℝ) ^ 2) = d := by
    have : ((re * re + im * im : ℤ) : ℝ) = ((d : ℤ) : ℝ) := by rw [h]
    push_cast at this
    nlinarith [this]
  have e1 : (((re : ℤ) : ℂ) + ((im : ℤ) : ℂ) * I) = ((re : ℝ) : ℂ) + ((im : ℝ) : ℂ) * I := by
    push_cast; rfl
  rw [e1, normSq_add_mul_I, h2, normSq_ofReal]
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  field_simp

theorem sm_entry_normSq (tab : List (List (List ℕ))) (c : ℂ) (d a : ℕ)
    (hc : Complex.normSq c = (d : ℝ)⁻¹) (x b : Fin d) : ‖sm_M tab c d a x b‖ ^ 2 = (d : ℝ)⁻¹ := by
  simp only [sm_M, norm_mul, norm_pow, Complex.norm_I, one_pow, mul_one]
  rw [Complex.sq_norm, hc]

/-- The generic construction: a table passing `sm_check` with `‖c‖² = 1/d` gives `d + 1` mutually unbiased bases. -/
theorem sm_hasMUBs (tab : List (List (List ℕ))) (c : ℂ) (d : ℕ) (hd : 0 < d)
    (hc : Complex.normSq c = (d : ℝ)⁻¹) (hchk : sm_check tab d = true) : HasMUBs d (d + 1) := by
  let U : Fin d → UMat d := fun a => ⟨sm_M tab c d a, sm_unitary tab c d hd hc hchk a a.2⟩
  refine ⟨Fin.cons 1 U, ?_⟩
  intro m n hmn
  induction m using Fin.cases with
  | zero =>
    induction n using Fin.cases with
    | zero => exact absurd rfl hmn
    | succ a' =>
      intro i j
      simp only [Fin.cons_zero, Fin.cons_succ, relativeUnitary, U]
      rw [show ((1 : UMat d) : Matrix (Fin d) (Fin d) ℂ) = 1 from rfl, star_one, one_mul]
      exact sm_entry_normSq tab c d a' hc i j
  | succ a =>
    induction n using Fin.cases with
    | zero =>
      intro i j
      simp only [Fin.cons_zero, Fin.cons_succ, relativeUnitary, U]
      rw [show ((1 : UMat d) : Matrix (Fin d) (Fin d) ℂ) = 1 from rfl, mul_one, Matrix.star_apply, norm_star]
      exact sm_entry_normSq tab c d a hc j i
    | succ a' =>
      intro i j
      have haa : (a : ℕ) ≠ a' := fun e => hmn (by rw [Fin.ext e])
      simp only [Fin.cons_succ, relativeUnitary, U]
      exact sm_cross tab c d hd hc hchk a a' a.2 a'.2 haa i j

theorem hasMUBs_two_three : HasMUBs 2 3 :=
  sm_hasMUBs sm_tab2 ((Real.sqrt 2 : ℂ))⁻¹ 2 (by norm_num)
    (by rw [map_inv₀, normSq_ofReal, Real.mul_self_sqrt (by norm_num)]; norm_num) sm_tab2_ok

theorem hasMUBs_four_five : HasMUBs 4 5 :=
  sm_hasMUBs sm_tab4 (1 / 2) 4 (by norm_num)
    (by rw [map_div₀, map_one, show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, normSq_ofReal]; norm_num) sm_tab4_ok

theorem hasMUBs_eight_nine : HasMUBs 8 9 :=
  sm_hasMUBs sm_tab8 ((1 + I) / 4) 8 (by norm_num)
    (by
      rw [map_div₀, show (1 + I : ℂ) = ((1 : ℝ) : ℂ) + ((1 : ℝ) : ℂ) * I by simp, normSq_add_mul_I,
        show (4 : ℂ) = ((4 : ℝ) : ℂ) by norm_num, normSq_ofReal]
      norm_num) sm_tab8_ok

end QuantumDesigns
