module

public import QuantumDesigns.GapCore

/-!
# Fourier inversion on the diagonal

In a basis `U` with projectors `P_j`, the Hilbert–Schmidt inner product of `w_k = Σ_j ζ^{j(k+1)} P_j` with `X` is
`Σ_j conj(ζ^{j(k+1)}) x_j`, `x_j = gp_diag U X j = ⟨P_j, X⟩` (`gp_dft_inner_w`, from the linearity of the flattening
and `gp_diag_eq_inner`): the discrete Fourier transform of the diagonal `j ↦ x_j` at the frequency
`k + 1 ∈ {1, …, d − 1}`. If every such transform vanishes, Fourier inversion
`d x_l = Σ_{m<d} ζ^{lm} Σ_j conj(ζ^{jm}) x_j` (the character sums `Σ_{m<d} ζ^{lm} conj(ζ^{jm})` are `d δ_{jl}`,
`gp_dft_orth`, from `bd_geom_zero` and `bd_not_dvd`) keeps only the frequency `m = 0`: `d x_l = Σ_j x_j = Tr X`
(`gp_dft_sum_diag`: `Σ_j Tr(P_j X) = Tr X` from `Σ_j P_j = 1`, which is `U U^* = 1`).
-/

@[expose] public section
noncomputable section

namespace QuantumDesigns

/-- The flattening commutes with finite weighted sums. -/
theorem gp_dft_vec_sum {d : ℕ} {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    (A : ι → Matrix (Fin d) (Fin d) ℂ) :
    bd_vec (∑ j ∈ s, c j • A j) = ∑ j ∈ s, c j • bd_vec (A j) := by
  have h : (fun p : Fin d × Fin d => (∑ j ∈ s, c j • A j) p.1 p.2) =
      ∑ j ∈ s, c j • (fun p : Fin d × Fin d => A j p.1 p.2) := by
    funext p
    simp [Matrix.sum_apply, Finset.sum_apply]
  simp only [bd_vec, h, WithLp.toLp_sum, WithLp.toLp_smul]

/-- The inner product of `w_k` with `X` is the discrete Fourier transform of the diagonal of `X` at `k + 1`. -/
theorem gp_dft_inner_w {d : ℕ} (U : UMat d) (X : Matrix (Fin d) (Fin d) ℂ) (k : Fin (d - 1)) :
    inner ℂ (bd_vec (gp_w U k)) (bd_vec X) =
      ∑ j : Fin d, star (bd_zeta d ^ ((j : ℕ) * ((k : ℕ) + 1))) * gp_diag U X j := by
  rw [gp_w, gp_dft_vec_sum, sum_inner]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inner_smul_left, gp_diag_eq_inner]
  rfl

/-- The projectors of a basis sum to the identity (`U U^* = 1`). -/
theorem gp_dft_sum_proj {d : ℕ} (U : UMat d) : ∑ j : Fin d, bd_proj U j = 1 := by
  have h := Matrix.mem_unitaryGroup_iff.mp U.2
  ext a b
  rw [← h, Matrix.sum_apply, Matrix.mul_apply]
  simp [bd_proj, Matrix.star_apply]

/-- The diagonal of `X` in a basis sums to the trace. -/
theorem gp_dft_sum_diag {d : ℕ} (U : UMat d) (X : Matrix (Fin d) (Fin d) ℂ) :
    ∑ j : Fin d, gp_diag U X j = Matrix.trace X := by
  simp only [gp_diag]
  rw [← Matrix.trace_sum, ← Finset.sum_mul, gp_dft_sum_proj, one_mul]

/-- Orthogonality of the characters: `Σ_{m<d} ζ^{lm} conj(ζ^{jm}) = d δ_{jl}`. -/
theorem gp_dft_orth {d : ℕ} (hd : d ≠ 0) (j l : Fin d) :
    ∑ m : Fin d, bd_zeta d ^ ((l : ℕ) * m) * star (bd_zeta d ^ ((j : ℕ) * m)) =
      if j = l then (d : ℂ) else 0 := by
  split_ifs with hjl
  · subst hjl
    have h1 : ∀ m : Fin d, bd_zeta d ^ ((j : ℕ) * m) * star (bd_zeta d ^ ((j : ℕ) * m)) = 1 :=
      fun m => by rw [mul_comm]; exact bd_conj_mul_self hd _
    simp only [h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  · refine Eq.trans ?_ (bd_geom_zero hd ((d - 1) * j + l) (bd_not_dvd j.2 l.2 (fun e => hjl (Fin.ext e))))
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [star_pow, bd_star_zeta hd, ← pow_mul, ← pow_mul, ← pow_add]
    congr 1
    ring

/-- A matrix orthogonal (Hilbert–Schmidt) to every weighted projector `w_k`, `k < d − 1`, of a basis has the
constant diagonal `Tr(X)/d` in that basis. -/
theorem gp_flat_of_orth {d : ℕ} (U : UMat d) (X : Matrix (Fin d) (Fin d) ℂ)
    (h : ∀ k : Fin (d - 1), inner ℂ (bd_vec (gp_w U k)) (bd_vec X) = 0) (l : Fin d) :
    gp_diag U X l = Matrix.trace X / d := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by have := l.2; omega⟩
  have hd : n + 1 ≠ 0 := Nat.succ_ne_zero n
  have hd' : ((n + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd
  rw [eq_div_iff hd', ← gp_dft_sum_diag U X]
  have hF : ∑ m : Fin (n + 1), bd_zeta (n + 1) ^ ((l : ℕ) * m) *
      ∑ j : Fin (n + 1), star (bd_zeta (n + 1) ^ ((j : ℕ) * m)) * gp_diag U X j =
      gp_diag U X l * ((n + 1 : ℕ) : ℂ) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    have h2 : ∀ j : Fin (n + 1), ∑ m : Fin (n + 1), bd_zeta (n + 1) ^ ((l : ℕ) * m) *
        (star (bd_zeta (n + 1) ^ ((j : ℕ) * m)) * gp_diag U X j) =
        (if j = l then ((n + 1 : ℕ) : ℂ) else 0) * gp_diag U X j := by
      intro j
      rw [← gp_dft_orth hd j l, Finset.sum_mul]
      refine Finset.sum_congr rfl fun m _ => ?_
      ring
    simp only [h2]
    rw [Finset.sum_eq_single l (fun j _ hj => by rw [ite_eq_right hj, zero_mul])
      (fun hl => absurd (Finset.mem_univ l) hl), ite_eq_left rfl, mul_comm]
  have hz : ∀ k : Fin n, ∑ j : Fin (n + 1),
      star (bd_zeta (n + 1) ^ ((j : ℕ) * ((k : ℕ) + 1))) * gp_diag U X j = 0 := by
    intro k
    have hk := h ⟨k, by have := k.isLt; omega⟩
    rw [gp_dft_inner_w] at hk
    exact hk
  rw [← hF, Fin.sum_univ_succ]
  simp only [Fin.val_succ, hz, mul_zero, Finset.sum_const_zero, add_zero, Fin.val_zero, pow_zero,
    star_one, one_mul]

end QuantumDesigns
