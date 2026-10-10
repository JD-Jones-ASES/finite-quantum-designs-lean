module

public import QuantumDesigns.Defs

/-!
# Three mutually unbiased bases in every dimension `d ≥ 2`, directly

A second route to `hasMUBs_three` (which `Tensor.lean` derives from the prime-power theorem): this module proves
it without any finite field. Let `ω = exp(2πi/d)`, `ζ = exp(πi/d)` (so `ζ² = ω`), and take the three
bases: the standard basis `1`; the Fourier matrix `F j k = (√d)⁻¹ ω^{jk}`; the chirped Fourier matrix
`C j k = (√d)⁻¹ ζ^{j(j + d)} ω^{jk}`, with `j, k` read in `ZMod d` and the exponent `j(j + d)` computed on the
representatives `0 ≤ j < d`. The chirp `χ j = ζ^{j(j+d)}` has modulus one and satisfies the functional equation
`χ (j + t) = χ j χ t ω^{jt}` on `ZMod d`: the exponents agree modulo `2d` whether `(j + t) mod d` wraps or not.

- `F` unitary and unbiased to `1`: `Σ_j ω^{j(k' − k)} = d δ` (`ZMod.stdAddChar`, primitive, with
  `AddChar.sum_mulShift`); every entry has `‖·‖² = 1/d`.
- `C = D F` with `D` the diagonal unitary of the chirp, so `C` is unitary and unbiased to `1`.
- `F^* C` has `(k, k')` entry `(1/d) S` with `S = Σ_j χ j ω^{j(k' − k)}`; by the functional equation and the
  substitution `j = j' + t`, `conj S · S = Σ_t χ t ω^{t(k'−k)} Σ_{j'} ω^{j' t} = d χ 0 = d`, so `‖(F^* C) k k'‖² = 1/d`.

Index the three bases by `Fin 3` (`![1, F, C]`); `IsMUBFamily` by `Fin` case analysis with symmetry.
-/

@[expose] public section

open Complex Matrix

namespace QuantumDesigns

/-! ## Character sums over a finite commutative ring -/

section Generic

variable {R : Type*} [CommRing R] [Fintype R] [DecidableEq R]

theorem ch_star_eq_inv {u : ℂ} (hu : ‖u‖ = 1) : star u = u⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  have h := Complex.conj_mul' u
  rw [hu] at h
  simpa using h

theorem ch_star_mul_self {u : ℂ} (hu : ‖u‖ = 1) : star u * u = 1 := by
  rw [ch_star_eq_inv hu, inv_mul_cancel₀]
  intro h
  rw [h, norm_zero] at hu
  exact zero_ne_one hu

omit [DecidableEq R] in
theorem ch_star_psi (ψ : AddChar R ℂ) (a b : R) : star (ψ a) * ψ b = ψ (b - a) := by
  rw [ch_star_eq_inv (AddChar.norm_apply ψ a), ← AddChar.map_neg_eq_inv, ← AddChar.map_add_eq_mul,
    sub_eq_add_neg, add_comm]

theorem ch_orth {ψ : AddChar R ℂ} (hψ : ψ.IsPrimitive) (k k' : R) :
    ∑ j : R, star (ψ (j * k)) * ψ (j * k') = if k = k' then (Fintype.card R : ℂ) else 0 := by
  simp_rw [ch_star_psi, ← mul_sub]
  rw [AddChar.sum_mulShift _ hψ]
  by_cases h : k = k'
  · subst h
    simp
  · have h' : k' - k ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
    simp [h, h']

theorem ch_cross_sum {ψ : AddChar R ℂ} (hψ : ψ.IsPrimitive) {χ : R → ℂ} (hχ1 : ∀ j, ‖χ j‖ = 1)
    (hχ : ∀ j t, χ (j + t) = χ j * χ t * ψ (j * t)) (m : R) :
    star (∑ j : R, χ j * ψ (j * m)) * (∑ j : R, χ j * ψ (j * m)) = (Fintype.card R : ℂ) := by
  have h0 : χ 0 = 1 := by
    have h := hχ 0 0
    simp only [add_zero, mul_zero, AddChar.map_zero_eq_one, mul_one] at h
    have hne : χ 0 ≠ 0 := by
      intro h'
      have := hχ1 0
      rw [h', norm_zero] at this
      exact zero_ne_one this
    exact (mul_left_cancel₀ hne (by rw [mul_one]; exact h)).symm
  have step : ∀ j' : R, ∑ j : R, star (χ j' * ψ (j' * m)) * (χ j * ψ (j * m))
      = ∑ t : R, χ t * ψ (t * m) * ψ (j' * t) := by
    intro j'
    rw [← Equiv.sum_comp (Equiv.addLeft j')]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [Equiv.coe_addLeft]
    rw [hχ, add_mul, AddChar.map_add_eq_mul, star_mul']
    have h1 := ch_star_mul_self (hχ1 j')
    have h2 := ch_star_mul_self (AddChar.norm_apply ψ (j' * m))
    linear_combination (star (ψ (j' * m)) * ψ (j' * m) * (χ t * ψ (t * m) * ψ (j' * t))) * h1
      + (χ t * ψ (t * m) * ψ (j' * t)) * h2
  rw [star_sum, Finset.sum_mul_sum, Finset.sum_congr rfl fun j' _ => step j', Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  simp_rw [AddChar.sum_mulShift _ hψ]
  simp [h0]

theorem ch_norm_sq_cross {ψ : AddChar R ℂ} (hψ : ψ.IsPrimitive) {χ : R → ℂ} (hχ1 : ∀ j, ‖χ j‖ = 1)
    (hχ : ∀ j t, χ (j + t) = χ j * χ t * ψ (j * t)) (m : R) :
    ‖∑ j : R, χ j * ψ (j * m)‖ ^ 2 = (Fintype.card R : ℝ) := by
  have h := ch_cross_sum hψ hχ1 hχ m
  have h2 : ((‖∑ j : R, χ j * ψ (j * m)‖ ^ 2 : ℝ) : ℂ) = (Fintype.card R : ℂ) := by
    rw [Complex.ofReal_pow, ← Complex.conj_mul']
    exact h
  exact_mod_cast h2

end Generic

/-! ## The chirp on `ZMod N` -/

section Phase

variable {N : ℕ} [NeZero N]

/-- `ζ = exp(πi/N)`. -/
noncomputable def ch_z (N : ℕ) : ℂ := Complex.exp (Real.pi * I / N)

omit [NeZero N] in
theorem ch_z_norm : ‖ch_z N‖ = 1 := by
  have : (Real.pi : ℂ) * I / N = ((Real.pi / N : ℝ) : ℂ) * I := by push_cast; ring
  rw [ch_z, this, Complex.norm_exp_ofReal_mul_I]

theorem ch_z_pow_two_mul : ch_z N ^ (2 * N) = 1 := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  rw [ch_z, ← Complex.exp_nat_mul]
  have : ((2 * N : ℕ) : ℂ) * (Real.pi * I / N) = 2 * Real.pi * I := by
    push_cast
    field_simp
  rw [this, Complex.exp_two_pi_mul_I]

theorem ch_z_pow_add (E x : ℕ) : ch_z N ^ (E + 2 * N * x) = ch_z N ^ E := by
  rw [pow_add, pow_mul, ch_z_pow_two_mul, one_pow, mul_one]

theorem ch_psi_eq (x : ZMod N) : ZMod.stdAddChar x = ch_z N ^ (2 * x.val) := by
  have hx : x = ((x.val : ℤ) : ZMod N) := by simp
  conv_lhs => rw [hx]
  rw [ZMod.stdAddChar_coe, ch_z, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- The chirp `χ j = ζ^{j(j + N)}` on representatives. -/
noncomputable def ch_chi (N : ℕ) (j : ZMod N) : ℂ := ch_z N ^ (j.val * (j.val + N))

omit [NeZero N] in
theorem ch_chi_norm (j : ZMod N) : ‖ch_chi N j‖ = 1 := by
  rw [ch_chi, norm_pow, ch_z_norm, one_pow]

theorem ch_exp_key (N a b : ℕ) (hN : 0 < N) (ha : a < N) (hb : b < N) :
    ∃ x y : ℕ, ((a + b) % N) * ((a + b) % N + N) + 2 * N * x
      = a * (a + N) + b * (b + N) + 2 * (a * b % N) + 2 * N * y := by
  have hs : (a + b) / N < 2 := by rw [Nat.div_lt_iff_lt_mul hN]; omega
  have h1 := Nat.mod_add_div (a + b) N
  have h2 := Nat.mod_add_div (a * b) N
  generalize (a + b) % N = c at h1 ⊢
  generalize (a + b) / N = s at h1 hs
  generalize a * b % N = r at h2 ⊢
  generalize a * b / N = q at h2
  interval_cases s
  · refine ⟨0, q, ?_⟩
    zify at h1 h2 ⊢
    linear_combination ((c : ℤ) + a + b + N) * h1 - 2 * h2
  · refine ⟨a + b, q, ?_⟩
    zify at h1 h2 ⊢
    linear_combination ((c : ℤ) + a + b) * h1 - 2 * h2

theorem ch_chi_add (j t : ZMod N) :
    ch_chi N (j + t) = ch_chi N j * ch_chi N t * ZMod.stdAddChar (j * t) := by
  obtain ⟨x, y, h⟩ := ch_exp_key N j.val t.val (Nat.pos_of_ne_zero (NeZero.ne N)) (ZMod.val_lt j)
    (ZMod.val_lt t)
  rw [ch_psi_eq, ch_chi, ch_chi, ch_chi, ZMod.val_add, ZMod.val_mul, ← pow_add, ← pow_add,
    ← ch_z_pow_add (N := N) (((j.val + t.val) % N) * ((j.val + t.val) % N + N)) x, h, ch_z_pow_add]

end Phase

/-! ## The three bases in dimension `n + 2` -/

section Bases

variable (n : ℕ)

/-- `(√(n+2))⁻¹ φ j ω^{jk}` on `ZMod (n + 2)`. -/
noncomputable def ch_mat (φ : ZMod (n + 2) → ℂ) : Matrix (ZMod (n + 2)) (ZMod (n + 2)) ℂ :=
  fun j k => (((Real.sqrt ((n + 2 : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) * (φ j * ZMod.stdAddChar (j * k))

theorem ch_scal :
    star ((((Real.sqrt ((n + 2 : ℕ) : ℝ))⁻¹ : ℝ) : ℂ)) * (((Real.sqrt ((n + 2 : ℕ) : ℝ))⁻¹ : ℝ) : ℂ)
      = ((n + 2 : ℕ) : ℂ)⁻¹ := by
  have hs : star ((((Real.sqrt ((n + 2 : ℕ) : ℝ))⁻¹ : ℝ) : ℂ))
      = (((Real.sqrt ((n + 2 : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) := Complex.conj_ofReal _
  rw [hs, ← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg _)]
  push_cast
  rfl

theorem ch_mat_unitary (φ : ZMod (n + 2) → ℂ) (hφ : ∀ j, ‖φ j‖ = 1) :
    ch_mat n φ ∈ Matrix.unitaryGroup (ZMod (n + 2)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext k k'
  rw [Matrix.mul_apply]
  simp only [Matrix.star_apply, ch_mat]
  have key : ∀ j : ZMod (n + 2),
      star ((((Real.sqrt ((n + 2 : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) * (φ j * ZMod.stdAddChar (j * k)))
        * ((((Real.sqrt ((n + 2 : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) * (φ j * ZMod.stdAddChar (j * k')))
      = ((n + 2 : ℕ) : ℂ)⁻¹ * (star (ZMod.stdAddChar (j * k)) * ZMod.stdAddChar (j * k')) := by
    intro j
    rw [star_mul', star_mul']
    have h1 := ch_scal n
    have h2 := ch_star_mul_self (hφ j)
    linear_combination (star (φ j) * φ j * (star (ZMod.stdAddChar (j * k)) *
      ZMod.stdAddChar (j * k'))) * h1 + ((n + 2 : ℕ) : ℂ)⁻¹ * (star (ZMod.stdAddChar (j * k)) *
      ZMod.stdAddChar (j * k')) * h2
  rw [Finset.sum_congr rfl fun j _ => key j, ← Finset.mul_sum,
    ch_orth (ZMod.isPrimitive_stdAddChar (n + 2)), ZMod.card, Matrix.one_apply]
  split_ifs
  · exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (by omega))
  · exact mul_zero _

theorem ch_unbiased_one (φ : ZMod (n + 2) → ℂ) (hφ : ∀ j, ‖φ j‖ = 1) (i j : ZMod (n + 2)) :
    ‖(star (1 : Matrix (ZMod (n + 2)) (ZMod (n + 2)) ℂ) * ch_mat n φ) i j‖ ^ 2
      = ((n + 2 : ℕ) : ℝ)⁻¹ := by
  rw [star_one, one_mul]
  simp only [ch_mat]
  rw [norm_mul, norm_mul, hφ, AddChar.norm_apply, mul_one, mul_one,
    Complex.norm_of_nonneg (by positivity), inv_pow, Real.sq_sqrt (Nat.cast_nonneg _)]

theorem ch_unbiased_FC (k k' : ZMod (n + 2)) :
    ‖(star (ch_mat n (fun _ => 1)) * ch_mat n (ch_chi (n + 2))) k k'‖ ^ 2 = ((n + 2 : ℕ) : ℝ)⁻¹ := by
  rw [Matrix.mul_apply]
  simp only [Matrix.star_apply, ch_mat]
  have key : ∀ j : ZMod (n + 2),
      star ((((Real.sqrt ((n + 2 : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) * (1 * ZMod.stdAddChar (j * k)))
        * ((((Real.sqrt ((n + 2 : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) * (ch_chi (n + 2) j * ZMod.stdAddChar (j * k')))
      = ((n + 2 : ℕ) : ℂ)⁻¹ * (ch_chi (n + 2) j * ZMod.stdAddChar (j * (k' - k))) := by
    intro j
    rw [mul_sub, ← ch_star_psi, star_mul', star_mul', star_one]
    have h1 := ch_scal n
    linear_combination (ch_chi (n + 2) j * (star (ZMod.stdAddChar (j * k)) *
      ZMod.stdAddChar (j * k'))) * h1
  rw [Finset.sum_congr rfl fun j _ => key j, ← Finset.mul_sum, norm_mul, mul_pow,
    ch_norm_sq_cross (ZMod.isPrimitive_stdAddChar (n + 2)) ch_chi_norm ch_chi_add, ZMod.card,
    norm_inv, Complex.norm_natCast]
  have hN : ((n + 2 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp

end Bases

theorem ch_unbiased_symm {d : ℕ} {U V : UMat d} (h : IsUnbiased U V) : IsUnbiased V U := by
  intro i j
  have hr : relativeUnitary V U = star (relativeUnitary U V) := by
    simp [relativeUnitary, star_mul]
  rw [hr, Matrix.star_apply, norm_star, h]

theorem hasMUBs_three_chirp (d : ℕ) (hd : 2 ≤ d) : HasMUBs d 3 := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 2 := ⟨d - 2, by omega⟩
  let I : UMat (n + 2) := ⟨1, one_mem _⟩
  let F : UMat (n + 2) := ⟨ch_mat n (fun _ => 1), ch_mat_unitary n _ (fun _ => by simp)⟩
  let C : UMat (n + 2) := ⟨ch_mat n (ch_chi (n + 2)), ch_mat_unitary n _ ch_chi_norm⟩
  have hIF : IsUnbiased I F := ch_unbiased_one n _ (fun _ => by simp)
  have hIC : IsUnbiased I C := ch_unbiased_one n _ ch_chi_norm
  have hFC : IsUnbiased F C := ch_unbiased_FC n
  refine ⟨![I, F, C], ?_⟩
  intro a b hab
  fin_cases a <;> fin_cases b
  all_goals first
    | exact absurd rfl hab
    | exact hIF
    | exact hIC
    | exact hFC
    | exact ch_unbiased_symm hIF
    | exact ch_unbiased_symm hIC
    | exact ch_unbiased_symm hFC

end QuantumDesigns
