module

public import QuantumDesigns.Defs

/-!
# Gerzon's bound over `ℂ`, its sharpness, the equality case, the frame identity

For `Φ : Fin N → StateVector d` with every `Φ i` normalized and `overlapSq (Φ i) (Φ j) = c` for `i ≠ j`, let
`P_i = gz_P (Φ i) = vecMulVec (Φ i) (star ∘ Φ i)`, the matrix with entries `Φ i k · conj(Φ i l)`, and let
`gz_pair ψ : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] ℂ` be the pairing `A ↦ Σ_{k,l} A k l · conj(ψ k) ψ l`.

**Pairing identity** (`gz_pairing`, `gz_pair_P`): `gz_pair (Φ j) (P_i) = overlapSq (Φ i) (Φ j)` as a complex number
(`Finset.sum_mul_sum`, `Fintype.sum_prod_type`, `Complex.mul_conj`), which is `1` for `i = j` (`gz_normalized`:
`Σ_k conj(ψ k) ψ k = 1` for a unit vector, from `EuclideanSpace.norm_eq`) and `c` for `i ≠ j`; also `gz_pair ψ 1 = 1`
and `trace (P_i) = 1` (`gz_pair_one`, `gz_trace_P`).

**Bound.** From `Σ_i g_i • P_i = 0`, pairing with `Φ_j` gives `(1 − c) g_j + c S = 0` with `S = Σ_i g_i` (`gz_pair_eq`);
summing over `j`, `S (1 − c + N c) = 0`; for `N ≥ 2`, `c ≥ 0` (a squared norm), so `S = 0`, then `g_j = 0` since `c ≠ 1`
(`gz_linIndep`); the `P_i` are linearly independent in `Matrix (Fin d) (Fin d) ℂ`, of finrank `d · d`
(`Module.finrank_matrix`), hence `N ≤ d²` (`LinearIndependent.fintype_card_le_finrank`). For `N ≤ 1`: `N = 1` forces
`d ≥ 1`, since no vector of `StateVector 0` is normalized (`gz_not_normalized_zero`).

**Sharpness.** `Φ i = EuclideanSpace.single 0 1` for all `i` (`d ≥ 1`): normalized, every overlap `1`.

**Equality** (`gz_core`, `N = d²`, `d ≥ 2`): the `P_i` span (`LinearIndependent.span_eq_top_of_card_eq_finrank`), so
`1 = Σ_i a_i • P_i`; pairing with each `Φ_j` gives `(1 − c) a_j + c A = 1` with `A = Σ a_i`, and the trace gives `A = d`;
summing the pairing equations over `j`, `d³ c + (1 − c) d = d²`, i.e. `d (d − 1)(c (d + 1) − 1) = 0`, so `c = 1/(d + 1)`;
then each `a_j = 1/d`, which is the frame identity. `hasSICPOVM_iff_equiangular`: `→` with `c = 1/(d + 1) ≠ 1`
(`gz_sic_ne_one`); `←` by `gerzon_equality`. `card_le_of_sicOverlapSq`: at `d = 0` no vector is normalized, so `N = 0`;
otherwise `gerzon_bound` with `sicOverlapSq d ≠ 1`.
-/

@[expose] public section

namespace QuantumDesigns

/-- The rank-one matrix `ψ ψ†`, with entries `ψ k * conj (ψ l)`. -/
def gz_P {d : ℕ} (ψ : StateVector d) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.vecMulVec (fun k => ψ k) (fun l => star (ψ l))

/-- The linear functional `A ↦ ψ† A ψ = Σ_{k,l} A k l * conj (ψ k) * ψ l`. -/
def gz_pair {d : ℕ} (ψ : StateVector d) : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] ℂ where
  toFun A := ∑ k, ∑ l, A k l * (star (ψ k) * ψ l)
  map_add' A B := by simp only [Matrix.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' a A := by
    simp only [Matrix.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum, RingHom.id_apply]

theorem gz_pair_apply {d : ℕ} (ψ : StateVector d) (A : Matrix (Fin d) (Fin d) ℂ) :
    gz_pair ψ A = ∑ k, ∑ l, A k l * (star (ψ k) * ψ l) := rfl

/-- The pairing identity: `ψ† (φ φ†) ψ = |⟨φ, ψ⟩|²`. -/
theorem gz_pairing {d : ℕ} (φ ψ : StateVector d) :
    ∑ k, ∑ l, (φ k * star (φ l)) * (star (ψ k) * ψ l) = ((overlapSq φ ψ : ℝ) : ℂ) := by
  unfold overlapSq
  rw [Complex.normSq_eq_conj_mul_self, map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  simp only [map_mul, starRingEnd_apply, star_star]
  ring

theorem gz_pair_P {d : ℕ} (φ ψ : StateVector d) :
    gz_pair ψ (gz_P φ) = ((overlapSq φ ψ : ℝ) : ℂ) := by
  simp only [gz_pair_apply, gz_P, Matrix.vecMulVec_apply]
  exact gz_pairing φ ψ

theorem gz_normalized {d : ℕ} {ψ : StateVector d} (h : IsNormalized ψ) :
    ∑ k, star (ψ k) * ψ k = 1 := by
  have h2 : ∑ k, ‖ψ k‖ ^ 2 = (1 : ℝ) := by
    rw [← EuclideanSpace.norm_sq_eq]
    unfold IsNormalized at h
    rw [h]; norm_num
  have hk : ∀ k, star (ψ k) * ψ k = ((‖ψ k‖ ^ 2 : ℝ) : ℂ) := by
    intro k
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self, starRingEnd_apply]
  simp_rw [hk]
  rw [← Complex.ofReal_sum, h2]
  simp

theorem gz_overlap_self {d : ℕ} {ψ : StateVector d} (h : IsNormalized ψ) : overlapSq ψ ψ = 1 := by
  unfold overlapSq
  rw [gz_normalized h]
  simp

theorem gz_pair_one {d : ℕ} {ψ : StateVector d} (h : IsNormalized ψ) : gz_pair ψ 1 = 1 := by
  rw [gz_pair_apply, ← gz_normalized h]
  simp [Matrix.one_apply]

theorem gz_trace_P {d : ℕ} {ψ : StateVector d} (h : IsNormalized ψ) : (gz_P ψ).trace = 1 := by
  rw [← gz_normalized h]
  simp only [Matrix.trace, gz_P, Matrix.diag, Matrix.vecMulVec_apply]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

theorem gz_not_normalized_zero (ψ : StateVector 0) : ¬ IsNormalized ψ := by
  simp [IsNormalized, EuclideanSpace.norm_eq]

theorem gz_pair_eq {d N : ℕ} {c : ℝ} {Φ : Fin N → StateVector d}
    (hn : ∀ i, IsNormalized (Φ i)) (ho : HasConstantOverlapSq c Φ) (g : Fin N → ℂ) (j : Fin N) :
    gz_pair (Φ j) (∑ i, g i • gz_P (Φ i)) = (c : ℂ) * ∑ i, g i + (1 - c) * g j := by
  have ho' : Pairwise fun i j => overlapSq (Φ i) (Φ j) = c := ho
  rw [map_sum]
  simp only [map_smul, smul_eq_mul, gz_pair_P]
  have key : ∀ i, g i * ((overlapSq (Φ i) (Φ j) : ℝ) : ℂ)
      = (c : ℂ) * g i + if i = j then (1 - c) * g j else 0 := by
    intro i
    by_cases hij : i = j
    · subst hij
      rw [gz_overlap_self (hn i)]
      simp only [Complex.ofReal_one, ite_true]
      ring
    · rw [ho' hij]
      simp only [hij, ite_false]
      ring
  rw [Finset.sum_congr rfl (fun i _ => key i), Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_ite_eq']
  simp

theorem gz_linIndep {d N : ℕ} (hN : 2 ≤ N) {c : ℝ} (hc : c ≠ 1) {Φ : Fin N → StateVector d}
    (hn : ∀ i, IsNormalized (Φ i)) (ho : HasConstantOverlapSq c Φ) :
    LinearIndependent ℂ (fun i => gz_P (Φ i)) := by
  have ho' : Pairwise fun i j => overlapSq (Φ i) (Φ j) = c := ho
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hj : ∀ j, (c : ℂ) * ∑ i, g i + (1 - c) * g j = 0 := by
    intro j
    rw [← gz_pair_eq hn ho g j, hg, map_zero]
  have hc0 : 0 ≤ c := by
    have h01 : (⟨0, by omega⟩ : Fin N) ≠ ⟨1, by omega⟩ := Fin.ne_of_val_ne (by norm_num)
    rw [← ho' h01]
    exact Complex.normSq_nonneg _
  have hsum : ((N : ℂ) * c + (1 - c)) * ∑ i, g i = 0 := by
    have h := Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => hj j)
    rw [Finset.sum_add_distrib, Finset.sum_const, ← Finset.mul_sum, Finset.sum_const_zero,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
    linear_combination h
  have hne : ((N : ℂ) * c + (1 - c)) ≠ 0 := by
    have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
    have : (0 : ℝ) < (N : ℝ) * c + (1 - c) := by nlinarith
    exact_mod_cast this.ne'
  have hS : ∑ i, g i = 0 := (mul_eq_zero.mp hsum).resolve_left hne
  intro j
  have h := hj j
  rw [hS, mul_zero, zero_add] at h
  have h1c : (1 - (c : ℂ)) ≠ 0 := by
    have : (1 - c) ≠ 0 := sub_ne_zero.mpr (Ne.symm hc)
    exact_mod_cast this
  exact (mul_eq_zero.mp h).resolve_left h1c

theorem gz_sic_ne_one {d : ℕ} (hd : 1 ≤ d) : sicOverlapSq d ≠ 1 := by
  unfold sicOverlapSq
  intro h
  rw [inv_eq_one] at h
  have : (d : ℝ) = 0 := by linarith
  have : d = 0 := by exact_mod_cast this
  omega

theorem gerzon_bound_internal {d N : ℕ} {c : ℝ} (hc : c ≠ 1) (Φ : Fin N → StateVector d)
    (hn : ∀ i, IsNormalized (Φ i)) (ho : HasConstantOverlapSq c Φ) : N ≤ d ^ 2 := by
  rcases N with _ | _ | N
  · simp
  · have hd : d ≠ 0 := by
      rintro rfl
      exact gz_not_normalized_zero _ (hn 0)
    have : 0 < d ^ 2 := by positivity
    omega
  · have hli := gz_linIndep (by omega) hc hn ho
    have := hli.fintype_card_le_finrank
    simpa [Module.finrank_matrix, sq] using this

theorem gerzon_sharp_internal (d N : ℕ) (hd : 1 ≤ d) :
    ∃ Φ : Fin N → StateVector d, (∀ i, IsNormalized (Φ i)) ∧ HasConstantOverlapSq 1 Φ := by
  refine ⟨fun _ => EuclideanSpace.single ⟨0, hd⟩ 1, fun _ => ?_, fun i j _ => ?_⟩
  · simp [IsNormalized]
  · simp [overlapSq]

theorem gz_core {d : ℕ} (hd : 2 ≤ d) {c : ℝ} (hc : c ≠ 1) (Φ : Fin (d ^ 2) → StateVector d)
    (hn : ∀ i, IsNormalized (Φ i)) (ho : HasConstantOverlapSq c Φ) :
    ∃ a : Fin (d ^ 2) → ℂ, ∑ i, a i • gz_P (Φ i) = 1 ∧
      (∀ j, (c : ℂ) * ∑ i, a i + (1 - c) * a j = 1) ∧ ∑ i, a i = d := by
  have hN : 2 ≤ d ^ 2 := by nlinarith
  have hli := gz_linIndep hN hc hn ho
  have hspan := hli.span_eq_top_of_card_eq_finrank' (by simp [Module.finrank_matrix, sq])
  have h1 : (1 : Matrix (Fin d) (Fin d) ℂ) ∈ Submodule.span ℂ (Set.range fun i => gz_P (Φ i)) := by
    rw [hspan]; exact Submodule.mem_top
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp h1
  refine ⟨a, ha, fun j => ?_, ?_⟩
  · rw [← gz_pair_eq hn ho a j, ha, gz_pair_one (hn j)]
  · have h := congrArg Matrix.trace ha
    rw [Matrix.trace_sum] at h
    simp only [Matrix.trace_smul, gz_trace_P (hn _), smul_eq_mul, mul_one, Matrix.trace_one,
      Fintype.card_fin] at h
    exact h

theorem gerzon_equality_internal {d : ℕ} (hd : 2 ≤ d) {c : ℝ} (hc : c ≠ 1) (Φ : Fin (d ^ 2) → StateVector d)
    (hn : ∀ i, IsNormalized (Φ i)) (ho : HasConstantOverlapSq c Φ) : c = sicOverlapSq d := by
  obtain ⟨a, -, hj, hA⟩ := gz_core hd hc Φ hn ho
  have hsum := Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => hj j)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← Finset.mul_sum, hA, mul_one] at hsum
  have hR : (d : ℝ) ^ 2 * (c * d) + (1 - c) * d = (d : ℝ) ^ 2 := by
    have : (((d : ℝ) ^ 2 * (c * d) + (1 - c) * d : ℝ) : ℂ) = (((d : ℝ) ^ 2 : ℝ) : ℂ) := by
      push_cast at hsum ⊢
      linear_combination hsum
    exact_mod_cast this
  unfold sicOverlapSq
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hmul : c * ((d : ℝ) + 1) = 1 := by
    have h : (d : ℝ) * ((d : ℝ) - 1) * (c * (d + 1) - 1) = 0 := by linear_combination hR
    rcases mul_eq_zero.mp h with h | h
    · rcases mul_eq_zero.mp h with h | h <;> nlinarith
    · linarith
  exact eq_inv_of_mul_eq_one_left hmul

theorem gerzon_frame_internal {d : ℕ} (hd : 2 ≤ d) {c : ℝ} (hc : c ≠ 1) (Φ : Fin (d ^ 2) → StateVector d)
    (hn : ∀ i, IsNormalized (Φ i)) (ho : HasConstantOverlapSq c Φ) :
    ∑ i, (d : ℂ)⁻¹ • Matrix.vecMulVec (fun k => Φ i k) (fun l => star (Φ i l)) = 1 := by
  obtain ⟨a, ha, hj, hA⟩ := gz_core hd hc Φ hn ho
  have hceq := gerzon_equality_internal hd hc Φ hn ho
  have hd1 : (d : ℂ) + 1 ≠ 0 := by
    have : (d : ℝ) + 1 ≠ 0 := by positivity
    exact_mod_cast this
  have hu : ((d : ℂ) + 1)⁻¹ * ((d : ℂ) + 1) = 1 := inv_mul_cancel₀ hd1
  have hai : ∀ i, a i = (d : ℂ)⁻¹ := by
    intro i
    have h := hj i
    rw [hA, hceq] at h
    unfold sicOverlapSq at h
    push_cast at h
    apply eq_inv_of_mul_eq_one_left
    linear_combination ((d : ℂ) + 1) * h - ((d : ℂ) - a i) * hu
  rw [← ha]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hai i]
  rfl

theorem isSICFamily_frame_internal {d : ℕ} (hd : 2 ≤ d) (Φ : Fin (d ^ 2) → StateVector d)
    (h : IsSICFamily d Φ) :
    ∑ i, (d : ℂ)⁻¹ • Matrix.vecMulVec (fun k => Φ i k) (fun l => star (Φ i l)) = 1 :=
  gerzon_frame_internal hd (gz_sic_ne_one (by omega)) Φ h.1 h.2

theorem hasSICPOVM_iff_equiangular_internal (d : ℕ) (hd : 2 ≤ d) :
    HasSICPOVM d ↔ ∃ c : ℝ, c ≠ 1 ∧ ∃ Φ : Fin (d ^ 2) → StateVector d,
      (∀ i, IsNormalized (Φ i)) ∧ HasConstantOverlapSq c Φ := by
  constructor
  · rintro ⟨Φ, hn, ho⟩
    exact ⟨sicOverlapSq d, gz_sic_ne_one (by omega), Φ, hn, ho⟩
  · rintro ⟨c, hc, Φ, hn, ho⟩
    have hce := gerzon_equality_internal hd hc Φ hn ho
    subst hce
    exact ⟨Φ, hn, ho⟩

theorem card_le_of_sicOverlapSq_internal {d N : ℕ} (Φ : Fin N → StateVector d)
    (hn : ∀ i, IsNormalized (Φ i)) (ho : HasConstantOverlapSq (sicOverlapSq d) Φ) : N ≤ d ^ 2 := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · rcases N with _ | N
    · simp
    · exact absurd (hn 0) (gz_not_normalized_zero _)
  · exact gerzon_bound_internal (gz_sic_ne_one hd) Φ hn ho

end QuantumDesigns
