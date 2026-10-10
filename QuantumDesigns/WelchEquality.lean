module

public import QuantumDesigns.Welch

/-!
# Welch's equality case

For `N` unit vectors with frame operator `S = Σ_i |φ_i⟩⟨φ_i|`, `Σ_{i,j} |⟨φ_i, φ_j⟩|² − N²/d = ‖S − (N/d)·1‖²_HS`
(the identity in the proof of Mixon–Needham–Shonkwiler–Villar, Proposition 1, arXiv:2112.02916), so equality in
Welch's bound holds exactly for a tight frame. If every pairwise squared overlap is at most `α` and the relative
bound `N (1 − α d) = d (1 − α)` is attained, every pairwise squared overlap is `α` and the frame is tight
(Strohmer–Heath 2003, Theorem 2.3); so `d²` unit vectors with every pairwise squared overlap at most `1/(d + 1)`
form a SIC family, with no equiangularity assumed, and a SIC-POVM exists iff such vectors do. With every pairwise
squared overlap at most `1/(d + 1) + ε`, `‖S/d − 1‖²_HS ≤ (d² − 1) ε` for `d ≥ 1`: a bound on the resolution of the
identity, not on the distance to a SIC family.
-/

@[expose] public section
noncomputable section

namespace QuantumDesigns

/-- The squared norm of a flattened matrix is the entrywise sum of squared moduli. -/
lemma we_norm_sq {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) :
    ‖bd_vec A‖ ^ 2 = ∑ a : Fin d, ∑ b : Fin d, ‖A a b‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  rfl

/-- Welch's deficit: the frame potential minus `N²/d` is the squared Hilbert–Schmidt distance of the frame
operator from `(N/d)·1`. -/
theorem we_deficit {d N : ℕ} (Φ : Fin N → StateVector d)
    (hn : ∀ i, IsNormalized (Φ i)) :
    (∑ i, ∑ j, overlapSq (Φ i) (Φ j)) - (N : ℝ) ^ 2 / (d : ℝ) =
      ‖bd_vec (wl_S Φ - ((N : ℂ) / (d : ℂ)) • (1 : Matrix (Fin d) (Fin d) ℂ))‖ ^ 2 := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [overlapSq, bd_vec, EuclideanSpace.norm_eq]
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hvec : bd_vec (wl_S Φ - ((N : ℂ) / (d : ℂ)) • (1 : Matrix (Fin d) (Fin d) ℂ)) =
      bd_vec (wl_S Φ) - ((N : ℂ) / (d : ℂ)) • bd_vec (1 : Matrix (Fin d) (Fin d) ℂ) := rfl
  have hinner : inner ℂ
      (bd_vec (wl_S Φ - ((N : ℂ) / (d : ℂ)) • (1 : Matrix (Fin d) (Fin d) ℂ)))
      (bd_vec (wl_S Φ - ((N : ℂ) / (d : ℂ)) • (1 : Matrix (Fin d) (Fin d) ℂ))) =
      ((∑ i, ∑ j, overlapSq (Φ i) (Φ j) : ℝ) : ℂ) - (N : ℂ) ^ 2 / (d : ℂ) := by
    rw [hvec]
    simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
      wl_inner_S_S, wl_inner_S_one hn, wl_inner_one_S hn, wl_inner_one_one]
    simp only [map_div₀, map_natCast]
    field_simp
    ring
  have hr := congrArg (RCLike.re : ℂ → ℝ) hinner
  rw [inner_self_eq_norm_sq] at hr
  simpa [pow_two] using hr.symm

/-- Equality in Welch's bound holds exactly when the frame operator is `(N/d)·1`. -/
theorem we_equality_iff_tight {d N : ℕ} (Φ : Fin N → StateVector d)
    (hn : ∀ i, IsNormalized (Φ i)) :
    (∑ i, ∑ j, overlapSq (Φ i) (Φ j) = (N : ℝ) ^ 2 / (d : ℝ)) ↔
      wl_S Φ = ((N : ℂ) / (d : ℂ)) • (1 : Matrix (Fin d) (Fin d) ℂ) := by
  have h := we_deficit Φ hn
  constructor
  · intro heq
    rw [heq, sub_self] at h
    have hz : bd_vec (wl_S Φ - ((N : ℂ) / (d : ℂ)) •
        (1 : Matrix (Fin d) (Fin d) ℂ)) = 0 := by
      apply norm_eq_zero.mp
      nlinarith [norm_nonneg (bd_vec (wl_S Φ - ((N : ℂ) / (d : ℂ)) •
        (1 : Matrix (Fin d) (Fin d) ℂ)))]
    apply sub_eq_zero.mp
    ext a b
    exact congrArg (fun v : EuclideanSpace ℂ (Fin d × Fin d) => v (a, b)) hz
  · intro heq
    rw [heq, sub_self] at h
    have hz : bd_vec (0 : Matrix (Fin d) (Fin d) ℂ) = 0 := rfl
    rw [hz, norm_zero, zero_pow (by decide : 2 ≠ 0)] at h
    exact sub_eq_zero.mp h

/-- The sum of the model overlaps with diagonal `1` and off-diagonal `α`. -/
lemma we_model_sum (N : ℕ) (α : ℝ) :
    ∑ i : Fin N, ∑ j : Fin N, (if i = j then 1 else α) =
      (N : ℝ) * (1 + ((N : ℝ) - 1) * α) := by
  have he : ∀ i j : Fin N, (if i = j then (1 : ℝ) else α) =
      α + if i = j then 1 - α else 0 := by
    intro i j
    split_ifs <;> ring
  simp only [he, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  ring

/-- If the upper estimate on the frame potential is attained, each individual upper estimate is attained. -/
lemma we_constant_of_sum_eq {d N : ℕ} {α : ℝ} (Φ : Fin N → StateVector d)
    (hn : ∀ i, IsNormalized (Φ i))
    (ho : ∀ i j, i ≠ j → overlapSq (Φ i) (Φ j) ≤ α)
    (hs : ∑ i, ∑ j, overlapSq (Φ i) (Φ j) = (N : ℝ) * (1 + ((N : ℝ) - 1) * α)) :
    HasConstantOverlapSq α Φ := by
  have hterm : ∀ i j, overlapSq (Φ i) (Φ j) ≤ if i = j then 1 else α := by
    intro i j
    by_cases hij : i = j
    · subst j
      simp only [gz_overlap_self (hn i), ite_true, le_refl]
    · simpa only [ite_eq_right hij] using ho i j hij
  have hrows : ∀ i, ∑ j, overlapSq (Φ i) (Φ j) = ∑ j, (if i = j then 1 else α) := by
    have htotal : ∑ i, ∑ j, overlapSq (Φ i) (Φ j) = ∑ i : Fin N, ∑ j : Fin N,
        (if i = j then 1 else α) := hs.trans (we_model_sum N α).symm
    exact fun i => (Finset.sum_eq_sum_iff_of_le (fun i _ =>
      Finset.sum_le_sum (fun j _ => hterm i j))).mp htotal i (Finset.mem_univ i)
  intro i j hij
  have heq := (Finset.sum_eq_sum_iff_of_le (fun j _ => hterm i j)).mp (hrows i) j (Finset.mem_univ j)
  simpa only [ite_eq_right hij] using heq

/-- At equality in the relative bound, a bounded-overlap family is equiangular and tight; at `d = 0` there is no
unit vector, so `N = 0` and both conclusions are empty. -/
theorem we_relative_equality {d N : ℕ} {α : ℝ}
    (Φ : Fin N → StateVector d) (hn : ∀ i, IsNormalized (Φ i))
    (ho : ∀ i j, i ≠ j → overlapSq (Φ i) (Φ j) ≤ α)
    (heq : (N : ℝ) * (1 - α * (d : ℝ)) = (d : ℝ) * (1 - α)) :
    HasConstantOverlapSq α Φ ∧
      wl_S Φ = ((N : ℂ) / (d : ℂ)) • (1 : Matrix (Fin d) (Fin d) ℂ) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exact ⟨fun i _ _ => absurd (hn i) (gz_not_normalized_zero _), by ext a; exact a.elim0⟩
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hmodel : (N : ℝ) * (1 + ((N : ℝ) - 1) * α) = (N : ℝ) ^ 2 / (d : ℝ) := by
    apply (eq_div_iff hdR.ne').mpr
    linear_combination -(N : ℝ) * heq
  have hs : ∑ i, ∑ j, overlapSq (Φ i) (Φ j) = (N : ℝ) ^ 2 / (d : ℝ) :=
    le_antisymm (hmodel ▸ wl_sum_le Φ hn ho) (welch_bound_internal Φ hn)
  exact ⟨we_constant_of_sum_eq Φ hn ho (hs.trans hmodel.symm),
    (we_equality_iff_tight Φ hn).mp hs⟩

/-- `d²` unit vectors with every pairwise squared overlap at most `1/(d + 1)` form a SIC family. -/
theorem we_isSICFamily_of_overlapSq_le {d : ℕ} (Φ : Fin (d ^ 2) → StateVector d)
    (hn : ∀ i, IsNormalized (Φ i))
    (ho : ∀ i j, i ≠ j → overlapSq (Φ i) (Φ j) ≤ sicOverlapSq d) : IsSICFamily d Φ := by
  refine ⟨hn, ?_⟩
  have hd1 : (d : ℝ) + 1 ≠ 0 := by positivity
  have heq : ((d ^ 2 : ℕ) : ℝ) * (1 - sicOverlapSq d * (d : ℝ)) =
      (d : ℝ) * (1 - sicOverlapSq d) := by
    simp only [sicOverlapSq, Nat.cast_pow]
    field_simp
    ring
  exact (we_relative_equality Φ hn ho heq).1

/-- `d²` unit vectors whose pairwise squared overlaps exceed `1/(d + 1)` by at most `ε` have a normalized frame
operator within squared Hilbert–Schmidt distance `(d² − 1) ε` of the identity. -/
theorem we_frame_defect_le {d : ℕ} (hd : 0 < d) (ε : ℝ)
    (Φ : Fin (d ^ 2) → StateVector d) (hn : ∀ i, IsNormalized (Φ i))
    (ho : ∀ i j, i ≠ j → overlapSq (Φ i) (Φ j) ≤ sicOverlapSq d + ε) :
    ‖bd_vec ((d : ℂ)⁻¹ • wl_S Φ - (1 : Matrix (Fin d) (Fin d) ℂ))‖ ^ 2 ≤
      ((d : ℝ) ^ 2 - 1) * ε := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hd1 : (d : ℝ) + 1 ≠ 0 := by positivity
  have hratio : ((d ^ 2 : ℕ) : ℂ) / (d : ℂ) = (d : ℂ) := by
    push_cast
    field_simp
  have hbase : ((d ^ 2 : ℕ) : ℝ) ^ 2 / (d : ℝ) = (d : ℝ) ^ 3 := by
    push_cast
    field_simp
  have hmodel : ((d ^ 2 : ℕ) : ℝ) * (1 + (((d ^ 2 : ℕ) : ℝ) - 1) * (sicOverlapSq d + ε)) =
      (d : ℝ) ^ 3 + (d : ℝ) ^ 2 * ((d : ℝ) ^ 2 - 1) * ε := by
    simp only [sicOverlapSq, Nat.cast_pow]
    field_simp
    ring
  have hdef := we_deficit Φ hn
  rw [hratio, hbase] at hdef
  have hupper := wl_sum_le Φ hn ho
  rw [hmodel] at hupper
  have hbound : ‖bd_vec (wl_S Φ - (d : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ))‖ ^ 2 ≤
      (d : ℝ) ^ 2 * ((d : ℝ) ^ 2 - 1) * ε := by
    linarith
  have hscaled : bd_vec ((d : ℂ)⁻¹ • wl_S Φ - (1 : Matrix (Fin d) (Fin d) ℂ)) =
      (d : ℂ)⁻¹ • bd_vec (wl_S Φ - (d : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)) := by
    change (d : ℂ)⁻¹ • bd_vec (wl_S Φ) - bd_vec (1 : Matrix (Fin d) (Fin d) ℂ) =
      (d : ℂ)⁻¹ • (bd_vec (wl_S Φ) - (d : ℂ) • bd_vec (1 : Matrix (Fin d) (Fin d) ℂ))
    rw [smul_sub, smul_smul, inv_mul_cancel₀ hdC, one_smul]
  rw [hscaled, norm_smul, mul_pow, norm_inv, Complex.norm_natCast]
  have h := mul_le_mul_of_nonneg_left hbound (sq_nonneg ((d : ℝ)⁻¹))
  have hcancel : (d : ℝ)⁻¹ ^ 2 * ((d : ℝ) ^ 2 * ((d : ℝ) ^ 2 - 1) * ε) =
      ((d : ℝ) ^ 2 - 1) * ε := by
    field_simp
  rwa [hcancel] at h

/-! ## The statements of Challenge.lean -/

/-- Welch's deficit in the entrywise form of the Challenge. -/
theorem welch_deficit_internal {d N : ℕ} (Φ : Fin N → StateVector d)
    (hn : ∀ i, IsNormalized (Φ i)) :
    (∑ i, ∑ j, overlapSq (Φ i) (Φ j)) - (N : ℝ) ^ 2 / (d : ℝ) =
      ∑ a : Fin d, ∑ b : Fin d, Complex.normSq
        (((∑ i, Matrix.vecMulVec (fun k => Φ i k) (fun l => star (Φ i l))) -
          ((N : ℂ) / (d : ℂ)) • (1 : Matrix (Fin d) (Fin d) ℂ)) a b) := by
  simpa only [we_norm_sq, wl_S, gz_P, Complex.normSq_eq_norm_sq] using we_deficit Φ hn

/-- Equality in Welch's bound holds exactly for a tight frame, `Σ_i |φ_i⟩⟨φ_i| = (N/d)·1`. -/
theorem welch_equality_iff_tight_internal {d N : ℕ} (Φ : Fin N → StateVector d)
    (hn : ∀ i, IsNormalized (Φ i)) :
    (∑ i, ∑ j, overlapSq (Φ i) (Φ j) = (N : ℝ) ^ 2 / (d : ℝ)) ↔
      (∑ i, Matrix.vecMulVec (fun k => Φ i k) (fun l => star (Φ i l))) =
        ((N : ℂ) / (d : ℂ)) • (1 : Matrix (Fin d) (Fin d) ℂ) := by
  simpa only [wl_S, gz_P] using we_equality_iff_tight Φ hn

/-- At equality in the relative bound every pairwise squared overlap is `α` and the frame operator is `(N/d)·1`. -/
theorem welch_relative_equality_internal {d N : ℕ} {α : ℝ}
    (Φ : Fin N → StateVector d) (hn : ∀ i, IsNormalized (Φ i))
    (ho : ∀ i j, i ≠ j → overlapSq (Φ i) (Φ j) ≤ α)
    (heq : (N : ℝ) * (1 - α * (d : ℝ)) = (d : ℝ) * (1 - α)) :
    HasConstantOverlapSq α Φ ∧
      (∑ i, Matrix.vecMulVec (fun k => Φ i k) (fun l => star (Φ i l))) =
        ((N : ℂ) / (d : ℂ)) • (1 : Matrix (Fin d) (Fin d) ℂ) := by
  simpa only [wl_S, gz_P] using we_relative_equality Φ hn ho heq

/-- `d²` unit vectors with every pairwise squared overlap at most `1/(d + 1)` form a SIC family. -/
theorem isSICFamily_of_overlapSq_le_internal {d : ℕ} (Φ : Fin (d ^ 2) → StateVector d)
    (hn : ∀ i, IsNormalized (Φ i))
    (ho : ∀ i j, i ≠ j → overlapSq (Φ i) (Φ j) ≤ sicOverlapSq d) : IsSICFamily d Φ :=
  we_isSICFamily_of_overlapSq_le Φ hn ho

/-- A SIC-POVM exists iff `d²` unit vectors with every pairwise squared overlap at most `1/(d + 1)` exist. -/
theorem hasSICPOVM_iff_overlapSq_le_internal (d : ℕ) :
    HasSICPOVM d ↔ ∃ Φ : Fin (d ^ 2) → StateVector d,
      (∀ i, IsNormalized (Φ i)) ∧ ∀ i j, i ≠ j → overlapSq (Φ i) (Φ j) ≤ sicOverlapSq d := by
  constructor
  · rintro ⟨Φ, hn, ho⟩
    exact ⟨Φ, hn, fun i j hij => (ho hij).le⟩
  · rintro ⟨Φ, hn, ho⟩
    exact ⟨Φ, we_isSICFamily_of_overlapSq_le Φ hn ho⟩

/-- The resolution-of-identity defect of `d²` unit vectors with pairwise squared overlaps at most `1/(d + 1) + ε`
is at most `(d² − 1) ε`, for `d ≥ 1`. -/
theorem frame_defect_le_of_overlapSq_le_internal {d : ℕ} (hd : 1 ≤ d) (ε : ℝ)
    (Φ : Fin (d ^ 2) → StateVector d) (hn : ∀ i, IsNormalized (Φ i))
    (ho : ∀ i j, i ≠ j → overlapSq (Φ i) (Φ j) ≤ sicOverlapSq d + ε) :
    ∑ a : Fin d, ∑ b : Fin d, Complex.normSq
      (((d : ℂ)⁻¹ • (∑ i, Matrix.vecMulVec (fun k => Φ i k) (fun l => star (Φ i l))) -
        (1 : Matrix (Fin d) (Fin d) ℂ)) a b) ≤ ((d : ℝ) ^ 2 - 1) * ε := by
  simpa only [we_norm_sq, wl_S, gz_P, Complex.normSq_eq_norm_sq] using
    we_frame_defect_le (Nat.pos_of_ne_zero (by omega)) ε Φ hn ho

end QuantumDesigns
