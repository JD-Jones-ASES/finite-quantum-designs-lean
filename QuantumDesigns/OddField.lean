module

public import QuantumDesigns.Defs

/-!
# Complete sets of mutually unbiased bases over a finite field of odd characteristic

Fix a finite field `F` with `ringChar F ≠ 2`, `q = Fintype.card F`, a nontrivial additive
character `ψ : AddChar F ℂ` (`AddChar.FiniteField.primitiveChar_to_Complex` with `..._isPrimitive`, or any `ψ ≠ 1`:
over a field a nontrivial character is primitive, `AddChar.IsPrimitive.of_ne_one`), and an equivalence
`e : F ≃ Fin q` (`Fintype.equivFin`).

**`quadSum_normSq`.** With `S = Σ_x ψ(c x² + e x)`: `‖S‖² = S * conj S`; `conj (ψ y) = ψ (−y)`
(`AddChar.map_neg_eq_conj`); reindex the inner sum by `x = y + t` (`Equiv.addRight`); `c(y+t)² + e(y+t) − c y² − e y
= c t² + e t + 2 c t y`; so `‖S‖² = Σ_t ψ(c t² + e t) Σ_y ψ((2 c t) y) = Σ_t ψ(c t² + e t) · (if 2 c t = 0 then q else 0)`
(`AddChar.sum_mulShift`); `2 c t = 0 ↔ t = 0` since `2 ≠ 0` (`ringChar F ≠ 2`: `Ring.two_ne_zero`) and `c ≠ 0`; the
`t = 0` term is `ψ 0 = 1`, so `‖S‖² = q`. No Gauss sums, no quadratic characters.

**The bases.** For `a : F`, `M a : Matrix (Fin q) (Fin q) ℂ`, `M a i j = (√q)⁻¹ * ψ (a * x ^ 2 + y * x)` with
`x = e.symm i` (row) and `y = e.symm j` (column). Unitarity: `(M a)^* (M a) = 1` entrywise is
`(1/q) Σ_x ψ((y' − y) x) = δ` (`sum_mulShift`). Unbiasedness against the standard basis `1`: every entry has
`‖·‖² = 1/q` (`AddChar.norm_apply`). Between `M a` and `M a'`, `a ≠ a'`: the `(j, j')` entry of `(M a)^* (M a')` is
`(1/q) Σ_x ψ((a' − a) x² + (y' − y) x)`, of squared norm `q / q² = 1/q` by `quadSum_normSq`. The family
`Fin (q + 1) → UMat q` is `Fin.cons 1 (fun a => ⟨M (e.symm a), _⟩)`; `IsMUBFamily` by cases on `Fin.cons`
(`Fin.cases`), using `IsUnbiased.symm` (prove it locally: `relativeUnitary V U = star (relativeUnitary U V)`).
-/

@[expose] public section

namespace QuantumDesigns

open ComplexConjugate

/-- Conjugate times value of an additive character is the character at the difference. -/
theorem of_conj_mul_apply {F : Type} [Field F] (ψ : AddChar F ℂ) [Finite F] (A B : F) :
    conj (ψ A) * ψ B = ψ (B - A) := by
  rw [← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul, neg_add_eq_sub]

theorem quadSum_normSq_internal (F : Type) [Field F] [Fintype F] (h2 : ringChar F ≠ 2)
    (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) (c e : F) (hc : c ≠ 0) :
    ‖∑ x : F, ψ (c * x ^ 2 + e * x)‖ ^ (2 : ℕ) = Fintype.card F := by
  classical
  have hprim : ψ.IsPrimitive := AddChar.IsPrimitive.of_ne_one hψ
  have h2' : (2 : F) ≠ 0 := Ring.two_ne_zero h2
  set f : F → F := fun x => c * x ^ 2 + e * x with hf
  have key : conj (∑ x : F, ψ (f x)) * ∑ x : F, ψ (f x) = (Fintype.card F : ℂ) := by
    rw [map_sum, Finset.sum_mul_sum]
    simp_rw [of_conj_mul_apply]
    have h3 : ∀ x : F, ∑ y : F, ψ (f y - f x)
        = ∑ t : F, ψ (c * t ^ 2 + e * t) * ψ (x * (2 * c * t)) := by
      intro x
      refine (Fintype.sum_equiv (Equiv.addLeft x) _ _ (fun t => ?_)).symm
      rw [← AddChar.map_add_eq_mul]
      congr 1
      simp only [hf, Equiv.coe_addLeft]
      ring
    simp_rw [h3]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, AddChar.sum_mulShift _ hprim]
    rw [Finset.sum_eq_single (0 : F)]
    · simp
    · intro t _ ht
      have : 2 * c * t ≠ 0 := mul_ne_zero (mul_ne_zero h2' hc) ht
      simp [this]
    · simp
  have h := RCLike.conj_mul (∑ x : F, ψ (f x))
  rw [key] at h
  have h' : (((‖∑ x : F, ψ (f x)‖ ^ (2 : ℕ) : ℝ)) : ℂ) = (((Fintype.card F : ℕ) : ℝ) : ℂ) := by
    rw [Complex.ofReal_natCast, Complex.ofReal_pow]; exact h.symm
  exact Complex.ofReal_injective h'

/-- The rescaled phase matrix of slope `a`. -/
noncomputable def of_M {F : Type} [Field F] [Fintype F] (ψ : AddChar F ℂ)
    (e : F ≃ Fin (Fintype.card F)) (a : F) :
    Matrix (Fin (Fintype.card F)) (Fin (Fintype.card F)) ℂ :=
  fun i j => ((Real.sqrt (Fintype.card F) : ℝ) : ℂ)⁻¹ * ψ (a * (e.symm i) ^ 2 + e.symm j * e.symm i)

theorem of_sqrt_inv_sq (q : ℕ) :
    ((Real.sqrt q : ℝ) : ℂ)⁻¹ * ((Real.sqrt q : ℝ) : ℂ)⁻¹ = (q : ℂ)⁻¹ := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg q)]
  simp

theorem of_M_entry {F : Type} [Field F] [Fintype F] (ψ : AddChar F ℂ)
    (e : F ≃ Fin (Fintype.card F)) (a a' : F) (j j' : Fin (Fintype.card F)) :
    (star (of_M ψ e a) * of_M ψ e a') j j'
      = ((Fintype.card F : ℕ) : ℂ)⁻¹ *
        ∑ x : F, ψ ((a' - a) * x ^ 2 + (e.symm j' - e.symm j) * x) := by
  rw [Matrix.mul_apply, Finset.mul_sum]
  refine Fintype.sum_equiv e.symm _ _ (fun i => ?_)
  simp only [Matrix.star_apply, of_M, star_mul', RCLike.star_def, map_inv₀, Complex.conj_ofReal]
  rw [mul_mul_mul_comm, of_sqrt_inv_sq, of_conj_mul_apply]
  congr 2
  ring

theorem of_M_unitary {F : Type} [Field F] [Fintype F] (ψ : AddChar F ℂ) (hψ : ψ ≠ 1)
    (e : F ≃ Fin (Fintype.card F)) (a : F) :
    of_M ψ e a ∈ Matrix.unitaryGroup (Fin (Fintype.card F)) ℂ := by
  classical
  rw [Matrix.mem_unitaryGroup_iff']
  ext j j'
  rw [of_M_entry, Matrix.one_apply]
  have hprim : ψ.IsPrimitive := AddChar.IsPrimitive.of_ne_one hψ
  have : ∀ x : F, (a - a) * x ^ 2 + (e.symm j' - e.symm j) * x = x * (e.symm j' - e.symm j) := by
    intro x; ring
  simp_rw [this, AddChar.sum_mulShift _ hprim]
  have hq : ((Fintype.card F : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  by_cases hjj : j = j'
  · subst hjj; simp [hq]
  · have : e.symm j' - e.symm j ≠ 0 := by
      rw [sub_ne_zero]; exact fun h => hjj (e.symm.injective h).symm
    simp [this, hjj]

/-- Unbiasedness is symmetric. -/
theorem of_isUnbiased_symm {d : ℕ} {U V : UMat d} (h : IsUnbiased U V) : IsUnbiased V U := by
  intro i j
  have : relativeUnitary V U i j = star (relativeUnitary U V j i) := by
    simp only [relativeUnitary, ← Matrix.star_apply, star_mul, star_star]
  rw [this, norm_star]
  exact h j i

theorem hasCompleteMUBs_of_odd_char_internal (F : Type) [Field F] [Fintype F] (h2 : ringChar F ≠ 2) :
    HasCompleteMUBs (Fintype.card F) := by
  classical
  set q := Fintype.card F with hqdef
  let ψ : AddChar F ℂ := AddChar.FiniteField.primitiveChar_to_Complex F
  have hprim : ψ.IsPrimitive := AddChar.FiniteField.primitiveChar_to_Complex_isPrimitive F
  have hψ : ψ ≠ 1 := by
    intro h
    have := hprim (one_ne_zero (α := F))
    apply this
    rw [h]; ext x; simp
  let e : F ≃ Fin q := Fintype.equivFin F
  have hq : ((q : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hqR : ((q : ℕ) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  let N : F → UMat q := fun a => ⟨of_M ψ e a, of_M_unitary ψ hψ e a⟩
  -- the standard basis against every phase basis
  have h1 : ∀ a : F, IsUnbiased (1 : UMat q) (N a) := by
    intro a i j
    simp only [relativeUnitary, N, OneMemClass.coe_one, star_one, one_mul, of_M]
    rw [norm_mul, AddChar.norm_apply, mul_one, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), inv_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  -- two phase bases of distinct slopes
  have h3 : ∀ a a' : F, a ≠ a' → IsUnbiased (N a) (N a') := by
    intro a a' haa i j
    simp only [relativeUnitary, N]
    rw [of_M_entry, norm_mul, mul_pow,
      quadSum_normSq_internal F h2 ψ hψ _ _ (sub_ne_zero.mpr (Ne.symm haa)), norm_inv,
      Complex.norm_natCast]
    field_simp
    rfl
  refine ⟨Fin.cons (1 : UMat q) (fun k : Fin q => N (e.symm k)), ?_⟩
  intro m n hmn
  induction m using Fin.cases with
  | zero =>
    induction n using Fin.cases with
    | zero => exact absurd rfl hmn
    | succ k => simpa using h1 (e.symm k)
  | succ k =>
    induction n using Fin.cases with
    | zero => simpa using of_isUnbiased_symm (h1 (e.symm k))
    | succ k' =>
      have hk : k ≠ k' := fun h => hmn (by rw [h])
      simpa using h3 (e.symm k) (e.symm k') (fun h => hk (e.symm.injective h))

end QuantumDesigns
