module

public import QuantumDesigns.Reconstruct
public import QuantumDesigns.GapCore

/-!
# Second moments, Hilbert–Schmidt norms and purity

Complete sets of mutually unbiased bases and SIC families are complex projective 2-designs
(Klappenecker–Rötteler 2005, Theorems 3 and 5; for SICs, Renes–Blume-Kohout–Scott–Caves 2004, p. 4). The bilinear
form of that property, `Σ_{s,l} Tr(X P_{s,l}) Tr(Y P_{s,l}) = Tr(XY) + Tr X · Tr Y` and
`(d + 1) Σ_i Tr(X P_i) Tr(Y P_i) = d (Tr(XY) + Tr X · Tr Y)` (Scott 2006, eq. (8), traced against `Y`), is derived
here from the reconstruction formulas of `Reconstruct.lean` by pairing with a second matrix under the trace. With
`Y = X*` the identities give the Hilbert–Schmidt norm with its trace term; with `X − Y` for `Tr X = Tr Y` the
distance; with a Hermitian `ρ` of trace one the purity `Tr(ρ²)`. The SIC norm, distance and purity statements use the
POVM outcomes `Tr(X P_i)/d`, hence the factor `d(d + 1)`; no SIC statement needs a hypothesis on `d`.
-/

@[expose] public section
noncomputable section

namespace QuantumDesigns

lemma tm_sic_sum_proj {d : ℕ} (Φ : Fin (d ^ 2) → StateVector d) (h : IsSICFamily d Φ) :
    ∑ i, gz_P (Φ i) = (d : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hi := sic_reconstruction_internal Φ h (1 : Matrix (Fin d) (Fin d) ℂ)
  change (1 : Matrix (Fin d) (Fin d) ℂ) =
    ∑ i, ((((d : ℂ) + 1) * Matrix.trace (1 * gz_P (Φ i)) - Matrix.trace (1 : Matrix (Fin d) (Fin d) ℂ)) /
      (d : ℂ)) • gz_P (Φ i) at hi
  simp only [Matrix.one_mul, gz_trace_P (h.1 _), Matrix.trace_one, Fintype.card_fin,
    mul_one, add_sub_cancel_left, one_div] at hi
  have hs := congrArg (fun A : Matrix (Fin d) (Fin d) ℂ => (d : ℂ) • A) hi
  simpa only [Finset.smul_sum, smul_smul, mul_inv_cancel₀ hd0, one_smul] using hs.symm

lemma tm_sic_sum_pair {d : ℕ} (Φ : Fin (d ^ 2) → StateVector d) (h : IsSICFamily d Φ)
    (X : Matrix (Fin d) (Fin d) ℂ) :
    ∑ i, Matrix.trace (X * gz_P (Φ i)) = (d : ℂ) * Matrix.trace X := by
  rw [← Matrix.trace_sum, ← Matrix.mul_sum, tm_sic_sum_proj Φ h]
  simp only [Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, smul_eq_mul]

/-- The bilinear second moment of a complete MUB family, without assumptions on `X` and `Y`. -/
theorem mub_second_moment_internal {d : ℕ} (B : Fin (d + 1) → UMat d) (hB : IsMUBFamily B)
    (X Y : Matrix (Fin d) (Fin d) ℂ) :
    let P := fun s l => Matrix.vecMulVec
      (fun a => (B s : Matrix (Fin d) (Fin d) ℂ) a l)
      (fun b => star ((B s : Matrix (Fin d) (Fin d) ℂ) b l))
    (∑ s, ∑ l, Matrix.trace (X * P s l) * Matrix.trace (Y * P s l)) =
      Matrix.trace (X * Y) + Matrix.trace X * Matrix.trace Y := by
  dsimp only
  simp only [rc_proj_eq]
  have hr := mub_reconstruction_internal B hB X
  simp only [rc_proj_eq] at hr
  have hh := congrArg (fun A : Matrix (Fin d) (Fin d) ℂ => Matrix.trace (A * Y)) hr
  have hc : ∀ s l, Matrix.trace (bd_proj (B s) l * Y) = Matrix.trace (Y * bd_proj (B s) l) :=
    fun s l => Matrix.trace_mul_comm _ _
  simp only [Matrix.sub_mul, Matrix.sum_mul, Matrix.smul_mul, Matrix.trace_sub, Matrix.trace_sum,
    Matrix.trace_smul, smul_eq_mul, Matrix.one_mul, hc] at hh
  linear_combination -hh

/-- The bilinear second moment of a SIC family, in a denominator-free form valid also at `d = 0`. -/
theorem sic_second_moment_internal {d : ℕ} (Φ : Fin (d ^ 2) → StateVector d) (h : IsSICFamily d Φ)
    (X Y : Matrix (Fin d) (Fin d) ℂ) :
    let P := fun i => Matrix.vecMulVec (fun k => Φ i k) (fun l => star (Φ i l))
    ((d : ℂ) + 1) * (∑ i, Matrix.trace (X * P i) * Matrix.trace (Y * P i)) =
      (d : ℂ) * (Matrix.trace (X * Y) + Matrix.trace X * Matrix.trace Y) := by
  dsimp only
  change ((d : ℂ) + 1) * (∑ i, Matrix.trace (X * gz_P (Φ i)) * Matrix.trace (Y * gz_P (Φ i))) =
    (d : ℂ) * (Matrix.trace (X * Y) + Matrix.trace X * Matrix.trace Y)
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hr := sic_reconstruction_internal Φ h X
  have hh := congrArg (fun A : Matrix (Fin d) (Fin d) ℂ => Matrix.trace (A * Y)) hr
  simp only [Matrix.sum_mul, Matrix.smul_mul, Matrix.trace_sum, Matrix.trace_smul,
    smul_eq_mul] at hh
  change Matrix.trace (X * Y) = ∑ i,
    ((((d : ℂ) + 1) * Matrix.trace (X * gz_P (Φ i)) - Matrix.trace X) / (d : ℂ)) *
      Matrix.trace (gz_P (Φ i) * Y) at hh
  have hc : ∀ i, Matrix.trace (gz_P (Φ i) * Y) = Matrix.trace (Y * gz_P (Φ i)) :=
    fun i => Matrix.trace_mul_comm _ _
  simp only [hc] at hh
  have hs : (∑ i, ((((d : ℂ) + 1) * Matrix.trace (X * gz_P (Φ i)) - Matrix.trace X) / (d : ℂ)) *
      Matrix.trace (Y * gz_P (Φ i))) =
      (((d : ℂ) + 1) * (∑ i, Matrix.trace (X * gz_P (Φ i)) * Matrix.trace (Y * gz_P (Φ i))) -
        Matrix.trace X * (∑ i, Matrix.trace (Y * gz_P (Φ i)))) / (d : ℂ) := by
    simp only [div_eq_mul_inv, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi <;> ring
  rw [hs, tm_sic_sum_pair Φ h Y] at hh
  have he := (eq_div_iff hd0).mp hh
  linear_combination -he

lemma tm_star_sic_proj {d : ℕ} (ψ : StateVector d) : star (gz_P ψ) = gz_P ψ := by
  ext a b
  simp only [Matrix.star_apply, gz_P, Matrix.vecMulVec_apply,
    star_mul', star_star]
  ring

lemma tm_trace_star_mul {d : ℕ} (X P : Matrix (Fin d) (Fin d) ℂ) (hP : star P = P) :
    Matrix.trace (star X * P) = star (Matrix.trace (X * P)) := by
  rw [← Matrix.trace_conjTranspose, ← Matrix.star_eq_conjTranspose, star_mul, hP]
  exact Matrix.trace_mul_comm _ _

lemma tm_trace_star_self {d : ℕ} (X : Matrix (Fin d) (Fin d) ℂ) :
    Matrix.trace (star X * X) = ((∑ a, ∑ b, Complex.normSq (X a b) : ℝ) : ℂ) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.star_apply]
  rw [Finset.sum_comm]
  push_cast
  simp only [Complex.normSq_eq_conj_mul_self, starRingEnd_apply]

/-- The data `Tr(X P_{s,l})` of a complete set give the Hilbert–Schmidt norm with its trace term. -/
theorem mub_hilbert_schmidt_internal {d : ℕ} (B : Fin (d + 1) → UMat d) (hB : IsMUBFamily B)
    (X : Matrix (Fin d) (Fin d) ℂ) :
    let P := fun s l => Matrix.vecMulVec
      (fun a => (B s : Matrix (Fin d) (Fin d) ℂ) a l)
      (fun b => star ((B s : Matrix (Fin d) (Fin d) ℂ) b l))
    (∑ s, ∑ l, Complex.normSq (Matrix.trace (X * P s l))) =
      (∑ a, ∑ b, Complex.normSq (X a b)) + Complex.normSq (Matrix.trace X) := by
  dsimp only
  simp only [rc_proj_eq]
  have hh := mub_second_moment_internal B hB (star X) X
  dsimp only at hh
  simp only [rc_proj_eq] at hh
  have hp : ∀ s l, Matrix.trace (star X * bd_proj (B s) l) =
      star (Matrix.trace (X * bd_proj (B s) l)) :=
    fun s l => tm_trace_star_mul X _ (gp_proj_star (B s) l)
  have ht : Matrix.trace (star X) = star (Matrix.trace X) := Matrix.trace_conjTranspose X
  rw [tm_trace_star_self, ht] at hh
  simp only [hp] at hh
  apply Complex.ofReal_injective
  push_cast at hh ⊢
  simpa only [Complex.normSq_eq_conj_mul_self, starRingEnd_apply] using hh

lemma tm_sic_hilbert_schmidt {d : ℕ} (Φ : Fin (d ^ 2) → StateVector d) (h : IsSICFamily d Φ)
    (X : Matrix (Fin d) (Fin d) ℂ) :
    ((d : ℝ) + 1) * (∑ i, Complex.normSq (Matrix.trace (X * gz_P (Φ i)))) =
      (d : ℝ) * ((∑ a, ∑ b, Complex.normSq (X a b)) + Complex.normSq (Matrix.trace X)) := by
  have hh := sic_second_moment_internal Φ h (star X) X
  change ((d : ℂ) + 1) * (∑ i, Matrix.trace (star X * gz_P (Φ i)) * Matrix.trace (X * gz_P (Φ i))) =
    (d : ℂ) * (Matrix.trace (star X * X) + Matrix.trace (star X) * Matrix.trace X) at hh
  have hp : ∀ i, Matrix.trace (star X * gz_P (Φ i)) =
      star (Matrix.trace (X * gz_P (Φ i))) := fun i => tm_trace_star_mul X _ (tm_star_sic_proj _)
  have ht : Matrix.trace (star X) = star (Matrix.trace X) := Matrix.trace_conjTranspose X
  rw [tm_trace_star_self, ht] at hh
  simp only [hp] at hh
  apply Complex.ofReal_injective
  push_cast at hh ⊢
  simpa only [Complex.normSq_eq_conj_mul_self, starRingEnd_apply] using hh

/-- The SIC-POVM outcomes `Tr(X P_i)/d` give the Hilbert–Schmidt norm with its trace term; at `d = 0` both sides
vanish. -/
theorem sic_hilbert_schmidt_internal {d : ℕ}
    (Φ : Fin (d ^ 2) → StateVector d) (h : IsSICFamily d Φ) (X : Matrix (Fin d) (Fin d) ℂ) :
    let P := fun i => Matrix.vecMulVec (fun k => Φ i k) (fun l => star (Φ i l))
    (d : ℝ) * ((d : ℝ) + 1) * (∑ i, Complex.normSq (Matrix.trace (X * P i) / (d : ℂ))) =
      (∑ a, ∑ b, Complex.normSq (X a b)) + Complex.normSq (Matrix.trace X) := by
  dsimp only
  change (d : ℝ) * ((d : ℝ) + 1) * (∑ i, Complex.normSq (Matrix.trace (X * gz_P (Φ i)) / (d : ℂ))) = _
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hn : Complex.normSq (d : ℂ) = (d : ℝ) ^ 2 := by simp [sq]
  simp only [Complex.normSq_div, hn, ← Finset.sum_div]
  calc
    (d : ℝ) * ((d : ℝ) + 1) * ((∑ i, Complex.normSq (Matrix.trace (X * gz_P (Φ i)))) / (d : ℝ) ^ 2) =
        (((d : ℝ) + 1) * (∑ i, Complex.normSq (Matrix.trace (X * gz_P (Φ i))))) / (d : ℝ) := by
          field_simp
    _ = _ := by rw [tm_sic_hilbert_schmidt Φ h X]; field_simp

/-- For equal-trace matrices the data of a complete set give the squared Hilbert–Schmidt distance. -/
theorem mub_tomography_distance_internal {d : ℕ} (B : Fin (d + 1) → UMat d) (hB : IsMUBFamily B)
    (X Y : Matrix (Fin d) (Fin d) ℂ) (htr : Matrix.trace X = Matrix.trace Y) :
    let P := fun s l => Matrix.vecMulVec
      (fun a => (B s : Matrix (Fin d) (Fin d) ℂ) a l)
      (fun b => star ((B s : Matrix (Fin d) (Fin d) ℂ) b l))
    (∑ s, ∑ l, Complex.normSq (Matrix.trace (X * P s l) - Matrix.trace (Y * P s l))) =
      ∑ a, ∑ b, Complex.normSq ((X - Y) a b) := by
  have hh := mub_hilbert_schmidt_internal B hB (X - Y)
  dsimp only at hh ⊢
  simpa only [Matrix.sub_mul, Matrix.trace_sub, htr, sub_self, Complex.normSq_zero, add_zero] using hh

/-- For equal-trace matrices the SIC-POVM outcomes give the squared Hilbert–Schmidt distance, with the factor
`d(d + 1)`. -/
theorem sic_tomography_distance_internal {d : ℕ}
    (Φ : Fin (d ^ 2) → StateVector d) (h : IsSICFamily d Φ)
    (X Y : Matrix (Fin d) (Fin d) ℂ) (htr : Matrix.trace X = Matrix.trace Y) :
    let P := fun i => Matrix.vecMulVec (fun k => Φ i k) (fun l => star (Φ i l))
    (d : ℝ) * ((d : ℝ) + 1) *
        (∑ i, Complex.normSq ((Matrix.trace (X * P i) - Matrix.trace (Y * P i)) / (d : ℂ))) =
      ∑ a, ∑ b, Complex.normSq ((X - Y) a b) := by
  have hh := sic_hilbert_schmidt_internal Φ h (X - Y)
  dsimp only at hh ⊢
  simpa only [Matrix.sub_mul, Matrix.trace_sub, htr, sub_self, Complex.normSq_zero, add_zero] using hh

lemma tm_purity_eq {d : ℕ} (ρ : Matrix (Fin d) (Fin d) ℂ) (hρ : Matrix.IsHermitian ρ) :
    (∑ a, ∑ b, Complex.normSq (ρ a b)) = (Matrix.trace (ρ * ρ)).re := by
  have hh := tm_trace_star_self ρ
  have hs : star ρ = ρ := hρ
  rw [hs] at hh
  exact (congrArg Complex.re hh).symm

/-- For a Hermitian `ρ` of trace one the data of a complete set give the purity `Tr(ρ²)`. -/
theorem mub_tomography_purity_internal {d : ℕ} (B : Fin (d + 1) → UMat d) (hB : IsMUBFamily B)
    (ρ : Matrix (Fin d) (Fin d) ℂ) (hρ : Matrix.IsHermitian ρ) (htr : Matrix.trace ρ = 1) :
    let P := fun s l => Matrix.vecMulVec
      (fun a => (B s : Matrix (Fin d) (Fin d) ℂ) a l)
      (fun b => star ((B s : Matrix (Fin d) (Fin d) ℂ) b l))
    (∑ s, ∑ l, Complex.normSq (Matrix.trace (ρ * P s l))) = (Matrix.trace (ρ * ρ)).re + 1 := by
  have hh := mub_hilbert_schmidt_internal B hB ρ
  dsimp only at hh ⊢
  simpa only [htr, Complex.normSq_one, tm_purity_eq ρ hρ] using hh

/-- For a Hermitian `ρ` of trace one the SIC-POVM outcomes give the purity, with the factor `d(d + 1)`. -/
theorem sic_tomography_purity_internal {d : ℕ}
    (Φ : Fin (d ^ 2) → StateVector d) (h : IsSICFamily d Φ)
    (ρ : Matrix (Fin d) (Fin d) ℂ) (hρ : Matrix.IsHermitian ρ) (htr : Matrix.trace ρ = 1) :
    let P := fun i => Matrix.vecMulVec (fun k => Φ i k) (fun l => star (Φ i l))
    (d : ℝ) * ((d : ℝ) + 1) * (∑ i, Complex.normSq (Matrix.trace (ρ * P i) / (d : ℂ))) =
      (Matrix.trace (ρ * ρ)).re + 1 := by
  have hh := sic_hilbert_schmidt_internal Φ h ρ
  dsimp only at hh ⊢
  simpa only [htr, Complex.normSq_one, tm_purity_eq ρ hρ] using hh

end QuantumDesigns
