module

public import QuantumDesigns

/-!
# Solution

Each statement of `Challenge.lean`, restated verbatim and closed by the internal theorem of the same
name with the suffix `_internal` (the modules of `QuantumDesigns/`; VERIFICATION.md names the module of
each theorem). This module does not import `Challenge.lean`; the definitions come from
`QuantumDesigns/Defs.lean`, which restates those of the Challenge character for character.
-/

@[expose] public section

namespace QuantumDesigns

theorem hasMUBs_le (d : ℕ) (hd : 2 ≤ d) (m : ℕ) (h : HasMUBs d m) : m ≤ d + 1 :=
  hasMUBs_le_internal d hd m h

theorem hasMUBs_one_dim (m : ℕ) : HasMUBs 1 m :=
  hasMUBs_one_dim_internal m

theorem hasMUBs_of_le {d k l : ℕ} (hkl : k ≤ l) (h : HasMUBs d l) : HasMUBs d k :=
  hasMUBs_of_le_internal hkl h

theorem hasMUBs_mul {m n k : ℕ} (hm : HasMUBs m k) (hn : HasMUBs n k) : HasMUBs (m * n) k :=
  hasMUBs_mul_internal hm hn

theorem hasMUBs_of_forall_primePow (d k : ℕ) (hd : d ≠ 0)
    (h : ∀ p ∈ d.primeFactors, k ≤ p ^ d.factorization p + 1) : HasMUBs d k :=
  hasMUBs_of_forall_primePow_internal d k hd h

theorem hasMUBs_three (d : ℕ) (hd : 2 ≤ d) : HasMUBs d 3 :=
  hasMUBs_three_internal d hd

theorem quadSum_normSq (F : Type) [Field F] [Fintype F] (h2 : ringChar F ≠ 2)
    (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) (c e : F) (hc : c ≠ 0) :
    ‖∑ x : F, ψ (c * x ^ 2 + e * x)‖ ^ (2 : ℕ) = Fintype.card F :=
  quadSum_normSq_internal F h2 ψ hψ c e hc

theorem hasCompleteMUBs_of_odd_char (F : Type) [Field F] [Fintype F] (h2 : ringChar F ≠ 2) :
    HasCompleteMUBs (Fintype.card F) :=
  hasCompleteMUBs_of_odd_char_internal F h2

theorem isMaxMUBCount_odd_prime_pow (p k : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hk : 1 ≤ k) :
    IsMaxMUBCount (p ^ k) (p ^ k + 1) :=
  isMaxMUBCount_odd_prime_pow_internal p k hp hp2 hk

theorem hasCompleteMUBs_two_pow (n : ℕ) (hn : 1 ≤ n) : HasCompleteMUBs (2 ^ n) :=
  hasCompleteMUBs_two_pow_internal n hn

theorem isMaxMUBCount_two_pow (n : ℕ) (hn : 1 ≤ n) : IsMaxMUBCount (2 ^ n) (2 ^ n + 1) :=
  isMaxMUBCount_two_pow_internal n hn

theorem isMaxMUBCount_prime_pow (p k : ℕ) (hp : p.Prime) (hk : 1 ≤ k) :
    IsMaxMUBCount (p ^ k) (p ^ k + 1) :=
  isMaxMUBCount_prime_pow_internal p k hp hk

theorem hasCompleteMUBs_iff_isMaxMUBCount (d : ℕ) (hd : 2 ≤ d) :
    HasCompleteMUBs d ↔ IsMaxMUBCount d (d + 1) :=
  hasCompleteMUBs_iff_isMaxMUBCount_internal d hd

theorem isMaxMUBCount_two : IsMaxMUBCount 2 3 :=
  isMaxMUBCount_two_internal

theorem isMaxMUBCount_four : IsMaxMUBCount 4 5 :=
  isMaxMUBCount_four_internal

theorem isMaxMUBCount_eight : IsMaxMUBCount 8 9 :=
  isMaxMUBCount_eight_internal

theorem gerzon_bound {d N : ℕ} {c : ℝ} (hc : c ≠ 1) (Φ : Fin N → StateVector d)
    (hn : ∀ i, IsNormalized (Φ i)) (ho : HasConstantOverlapSq c Φ) : N ≤ d ^ 2 :=
  gerzon_bound_internal hc Φ hn ho

theorem gerzon_sharp (d N : ℕ) (hd : 1 ≤ d) :
    ∃ Φ : Fin N → StateVector d, (∀ i, IsNormalized (Φ i)) ∧ HasConstantOverlapSq 1 Φ :=
  gerzon_sharp_internal d N hd

theorem gerzon_equality {d : ℕ} (hd : 2 ≤ d) {c : ℝ} (hc : c ≠ 1) (Φ : Fin (d ^ 2) → StateVector d)
    (hn : ∀ i, IsNormalized (Φ i)) (ho : HasConstantOverlapSq c Φ) : c = sicOverlapSq d :=
  gerzon_equality_internal hd hc Φ hn ho

theorem gerzon_frame {d : ℕ} (hd : 2 ≤ d) {c : ℝ} (hc : c ≠ 1) (Φ : Fin (d ^ 2) → StateVector d)
    (hn : ∀ i, IsNormalized (Φ i)) (ho : HasConstantOverlapSq c Φ) :
    ∑ i, (d : ℂ)⁻¹ • Matrix.vecMulVec (fun k => Φ i k) (fun l => star (Φ i l)) = 1 :=
  gerzon_frame_internal hd hc Φ hn ho

theorem isSICFamily_frame {d : ℕ} (hd : 2 ≤ d) (Φ : Fin (d ^ 2) → StateVector d) (h : IsSICFamily d Φ) :
    ∑ i, (d : ℂ)⁻¹ • Matrix.vecMulVec (fun k => Φ i k) (fun l => star (Φ i l)) = 1 :=
  isSICFamily_frame_internal hd Φ h

theorem hasSICPOVM_iff_equiangular (d : ℕ) (hd : 2 ≤ d) :
    HasSICPOVM d ↔ ∃ c : ℝ, c ≠ 1 ∧ ∃ Φ : Fin (d ^ 2) → StateVector d,
      (∀ i, IsNormalized (Φ i)) ∧ HasConstantOverlapSq c Φ :=
  hasSICPOVM_iff_equiangular_internal d hd

theorem card_le_of_sicOverlapSq {d N : ℕ} (Φ : Fin N → StateVector d)
    (hn : ∀ i, IsNormalized (Φ i)) (ho : HasConstantOverlapSq (sicOverlapSq d) Φ) : N ≤ d ^ 2 :=
  card_le_of_sicOverlapSq_internal Φ hn ho

theorem hasSICPOVM_two : HasSICPOVM 2 :=
  hasSICPOVM_two_internal

theorem hasSICPOVM_three : HasSICPOVM 3 :=
  hasSICPOVM_three_internal

theorem hasSICPOVM_eight : HasSICPOVM 8 :=
  hasSICPOVM_eight_internal

theorem hasCompleteMUBs_of_hasMUBs_self (d : ℕ) (h : HasMUBs d d) : HasCompleteMUBs d :=
  hasCompleteMUBs_of_hasMUBs_self_internal d h

theorem exists_isMUBFamily_extension {d : ℕ} (B : Fin d → UMat d) (hB : IsMUBFamily B) :
    ∃ C : Fin (d + 1) → UMat d, IsMUBFamily C ∧ ∀ r : Fin d, C r.succ = B r :=
  exists_isMUBFamily_extension_internal B hB

theorem hasCompleteMUBs_of_le_hasMUBs {d k : ℕ} (hk : d ≤ k) (h : HasMUBs d k) : HasCompleteMUBs d :=
  hasCompleteMUBs_of_le_hasMUBs_internal hk h

theorem isMaxMUBCount_ne_self (d : ℕ) (hd : 2 ≤ d) : ¬ IsMaxMUBCount d d :=
  isMaxMUBCount_ne_self_internal d hd

theorem isMaxMUBCount_dichotomy (d : ℕ) (hd : 2 ≤ d) (k : ℕ) (h : IsMaxMUBCount d k) :
    k = d + 1 ∨ k < d :=
  isMaxMUBCount_dichotomy_internal d hd k h

theorem hasMUBs_two (d : ℕ) : HasMUBs d 2 :=
  hasMUBs_two_internal d

theorem hasMUBs_prime_pow_iff (p k : ℕ) (hp : p.Prime) (hk : 1 ≤ k) (m : ℕ) :
    HasMUBs (p ^ k) m ↔ m ≤ p ^ k + 1 :=
  hasMUBs_prime_pow_iff_internal p k hp hk m

theorem isMaxMUBCount_unique {d k l : ℕ} (hk : IsMaxMUBCount d k) (hl : IsMaxMUBCount d l) : k = l :=
  isMaxMUBCount_unique_internal hk hl

theorem exists_isMaxMUBCount (d : ℕ) (hd : 2 ≤ d) : ∃ k, IsMaxMUBCount d k :=
  exists_isMaxMUBCount_internal d hd

theorem not_exists_isMaxMUBCount_one : ¬ ∃ k, IsMaxMUBCount 1 k :=
  not_exists_isMaxMUBCount_one_internal

theorem isMaxMUBCount_bounds (d : ℕ) (hd : 2 ≤ d) (k : ℕ) (h : IsMaxMUBCount d k) :
    3 ≤ k ∧ k ≤ d + 1 :=
  isMaxMUBCount_bounds_internal d hd k h

theorem mutuallyUnbiasedBases_dim6_bounds : HasMUBs 6 3 ∧ ∀ m : ℕ, HasMUBs 6 m → m ≤ 7 :=
  mutuallyUnbiasedBases_dim6_bounds_internal

theorem not_isMaxMUBCount_six_six : ¬ IsMaxMUBCount 6 6 :=
  not_isMaxMUBCount_six_six_internal

theorem mub_reconstruction {d : ℕ} (B : Fin (d + 1) → UMat d) (hB : IsMUBFamily B)
    (X : Matrix (Fin d) (Fin d) ℂ) :
    X = ∑ s, ∑ l, Matrix.trace (X * Matrix.vecMulVec (fun a => (B s : Matrix (Fin d) (Fin d) ℂ) a l)
          (fun b => star ((B s : Matrix (Fin d) (Fin d) ℂ) b l))) •
        Matrix.vecMulVec (fun a => (B s : Matrix (Fin d) (Fin d) ℂ) a l)
          (fun b => star ((B s : Matrix (Fin d) (Fin d) ℂ) b l)) -
      Matrix.trace X • (1 : Matrix (Fin d) (Fin d) ℂ) :=
  mub_reconstruction_internal B hB X

theorem sic_reconstruction {d : ℕ} (Φ : Fin (d ^ 2) → StateVector d) (h : IsSICFamily d Φ)
    (X : Matrix (Fin d) (Fin d) ℂ) :
    X = ∑ i, ((((d : ℂ) + 1) * Matrix.trace (X * Matrix.vecMulVec (fun k => Φ i k) (fun l => star (Φ i l))) -
          Matrix.trace X) / (d : ℂ)) • Matrix.vecMulVec (fun k => Φ i k) (fun l => star (Φ i l)) :=
  sic_reconstruction_internal Φ h X

theorem welch_bound {d N : ℕ} (Φ : Fin N → StateVector d) (hn : ∀ i, IsNormalized (Φ i)) :
    (N : ℝ) ^ 2 / (d : ℝ) ≤ ∑ i, ∑ j, overlapSq (Φ i) (Φ j) :=
  welch_bound_internal Φ hn

theorem welch_bound_of_constantOverlap {d N : ℕ} {c : ℝ} (hN : 2 ≤ N) (Φ : Fin N → StateVector d)
    (hn : ∀ i, IsNormalized (Φ i)) (ho : HasConstantOverlapSq c Φ) :
    ((N : ℝ) - d) / ((d : ℝ) * ((N : ℝ) - 1)) ≤ c :=
  welch_bound_of_constantOverlap_internal hN Φ hn ho

theorem welch_card_bound {d N : ℕ} {α : ℝ} (hα : α * (d : ℝ) < 1) (Φ : Fin N → StateVector d)
    (hn : ∀ i, IsNormalized (Φ i)) (ho : ∀ i j, i ≠ j → overlapSq (Φ i) (Φ j) ≤ α) :
    (N : ℝ) * (1 - α * (d : ℝ)) ≤ (d : ℝ) * (1 - α) :=
  welch_card_bound_internal hα Φ hn ho

theorem card_le_of_overlapSq_le_sic {d N : ℕ} (Φ : Fin N → StateVector d) (hn : ∀ i, IsNormalized (Φ i))
    (ho : ∀ i j, i ≠ j → overlapSq (Φ i) (Φ j) ≤ sicOverlapSq d) : N ≤ d ^ 2 :=
  card_le_of_overlapSq_le_sic_internal Φ hn ho

theorem hasSICPOVM_four : HasSICPOVM 4 :=
  hasSICPOVM_four_internal

theorem mub_second_moment {d : ℕ} (B : Fin (d + 1) → UMat d) (hB : IsMUBFamily B)
    (X Y : Matrix (Fin d) (Fin d) ℂ) :
    let P := fun s l => Matrix.vecMulVec
      (fun a => (B s : Matrix (Fin d) (Fin d) ℂ) a l)
      (fun b => star ((B s : Matrix (Fin d) (Fin d) ℂ) b l))
    (∑ s, ∑ l, Matrix.trace (X * P s l) * Matrix.trace (Y * P s l)) =
      Matrix.trace (X * Y) + Matrix.trace X * Matrix.trace Y :=
  mub_second_moment_internal B hB X Y

theorem sic_second_moment {d : ℕ} (Φ : Fin (d ^ 2) → StateVector d) (h : IsSICFamily d Φ)
    (X Y : Matrix (Fin d) (Fin d) ℂ) :
    let P := fun i => Matrix.vecMulVec (fun k => Φ i k) (fun l => star (Φ i l))
    ((d : ℂ) + 1) * (∑ i, Matrix.trace (X * P i) * Matrix.trace (Y * P i)) =
      (d : ℂ) * (Matrix.trace (X * Y) + Matrix.trace X * Matrix.trace Y) :=
  sic_second_moment_internal Φ h X Y

theorem mub_hilbert_schmidt {d : ℕ} (B : Fin (d + 1) → UMat d) (hB : IsMUBFamily B)
    (X : Matrix (Fin d) (Fin d) ℂ) :
    let P := fun s l => Matrix.vecMulVec
      (fun a => (B s : Matrix (Fin d) (Fin d) ℂ) a l)
      (fun b => star ((B s : Matrix (Fin d) (Fin d) ℂ) b l))
    (∑ s, ∑ l, Complex.normSq (Matrix.trace (X * P s l))) =
      (∑ a, ∑ b, Complex.normSq (X a b)) + Complex.normSq (Matrix.trace X) :=
  mub_hilbert_schmidt_internal B hB X

theorem sic_hilbert_schmidt {d : ℕ}
    (Φ : Fin (d ^ 2) → StateVector d) (h : IsSICFamily d Φ) (X : Matrix (Fin d) (Fin d) ℂ) :
    let P := fun i => Matrix.vecMulVec (fun k => Φ i k) (fun l => star (Φ i l))
    (d : ℝ) * ((d : ℝ) + 1) * (∑ i, Complex.normSq (Matrix.trace (X * P i) / (d : ℂ))) =
      (∑ a, ∑ b, Complex.normSq (X a b)) + Complex.normSq (Matrix.trace X) :=
  sic_hilbert_schmidt_internal Φ h X

theorem mub_tomography_distance {d : ℕ} (B : Fin (d + 1) → UMat d) (hB : IsMUBFamily B)
    (X Y : Matrix (Fin d) (Fin d) ℂ) (htr : Matrix.trace X = Matrix.trace Y) :
    let P := fun s l => Matrix.vecMulVec
      (fun a => (B s : Matrix (Fin d) (Fin d) ℂ) a l)
      (fun b => star ((B s : Matrix (Fin d) (Fin d) ℂ) b l))
    (∑ s, ∑ l, Complex.normSq (Matrix.trace (X * P s l) - Matrix.trace (Y * P s l))) =
      ∑ a, ∑ b, Complex.normSq ((X - Y) a b) :=
  mub_tomography_distance_internal B hB X Y htr

theorem sic_tomography_distance {d : ℕ}
    (Φ : Fin (d ^ 2) → StateVector d) (h : IsSICFamily d Φ)
    (X Y : Matrix (Fin d) (Fin d) ℂ) (htr : Matrix.trace X = Matrix.trace Y) :
    let P := fun i => Matrix.vecMulVec (fun k => Φ i k) (fun l => star (Φ i l))
    (d : ℝ) * ((d : ℝ) + 1) *
        (∑ i, Complex.normSq ((Matrix.trace (X * P i) - Matrix.trace (Y * P i)) / (d : ℂ))) =
      ∑ a, ∑ b, Complex.normSq ((X - Y) a b) :=
  sic_tomography_distance_internal Φ h X Y htr

theorem mub_tomography_purity {d : ℕ} (B : Fin (d + 1) → UMat d) (hB : IsMUBFamily B)
    (ρ : Matrix (Fin d) (Fin d) ℂ) (hρ : Matrix.IsHermitian ρ) (htr : Matrix.trace ρ = 1) :
    let P := fun s l => Matrix.vecMulVec
      (fun a => (B s : Matrix (Fin d) (Fin d) ℂ) a l)
      (fun b => star ((B s : Matrix (Fin d) (Fin d) ℂ) b l))
    (∑ s, ∑ l, Complex.normSq (Matrix.trace (ρ * P s l))) = (Matrix.trace (ρ * ρ)).re + 1 :=
  mub_tomography_purity_internal B hB ρ hρ htr

theorem sic_tomography_purity {d : ℕ}
    (Φ : Fin (d ^ 2) → StateVector d) (h : IsSICFamily d Φ)
    (ρ : Matrix (Fin d) (Fin d) ℂ) (hρ : Matrix.IsHermitian ρ) (htr : Matrix.trace ρ = 1) :
    let P := fun i => Matrix.vecMulVec (fun k => Φ i k) (fun l => star (Φ i l))
    (d : ℝ) * ((d : ℝ) + 1) * (∑ i, Complex.normSq (Matrix.trace (ρ * P i) / (d : ℂ))) =
      (Matrix.trace (ρ * ρ)).re + 1 :=
  sic_tomography_purity_internal Φ h ρ hρ htr

theorem welch_deficit {d N : ℕ} (Φ : Fin N → StateVector d) (hn : ∀ i, IsNormalized (Φ i)) :
    (∑ i, ∑ j, overlapSq (Φ i) (Φ j)) - (N : ℝ) ^ 2 / (d : ℝ) =
      ∑ a : Fin d, ∑ b : Fin d, Complex.normSq
        (((∑ i, Matrix.vecMulVec (fun k => Φ i k) (fun l => star (Φ i l))) -
          ((N : ℂ) / (d : ℂ)) • (1 : Matrix (Fin d) (Fin d) ℂ)) a b) :=
  welch_deficit_internal Φ hn

theorem welch_equality_iff_tight {d N : ℕ} (Φ : Fin N → StateVector d) (hn : ∀ i, IsNormalized (Φ i)) :
    (∑ i, ∑ j, overlapSq (Φ i) (Φ j) = (N : ℝ) ^ 2 / (d : ℝ)) ↔
      (∑ i, Matrix.vecMulVec (fun k => Φ i k) (fun l => star (Φ i l))) =
        ((N : ℂ) / (d : ℂ)) • (1 : Matrix (Fin d) (Fin d) ℂ) :=
  welch_equality_iff_tight_internal Φ hn

theorem welch_relative_equality {d N : ℕ} {α : ℝ}
    (Φ : Fin N → StateVector d) (hn : ∀ i, IsNormalized (Φ i))
    (ho : ∀ i j, i ≠ j → overlapSq (Φ i) (Φ j) ≤ α)
    (heq : (N : ℝ) * (1 - α * (d : ℝ)) = (d : ℝ) * (1 - α)) :
    HasConstantOverlapSq α Φ ∧
      (∑ i, Matrix.vecMulVec (fun k => Φ i k) (fun l => star (Φ i l))) =
        ((N : ℂ) / (d : ℂ)) • (1 : Matrix (Fin d) (Fin d) ℂ) :=
  welch_relative_equality_internal Φ hn ho heq

theorem isSICFamily_of_overlapSq_le {d : ℕ} (Φ : Fin (d ^ 2) → StateVector d)
    (hn : ∀ i, IsNormalized (Φ i))
    (ho : ∀ i j, i ≠ j → overlapSq (Φ i) (Φ j) ≤ sicOverlapSq d) : IsSICFamily d Φ :=
  isSICFamily_of_overlapSq_le_internal Φ hn ho

theorem hasSICPOVM_iff_overlapSq_le (d : ℕ) :
    HasSICPOVM d ↔ ∃ Φ : Fin (d ^ 2) → StateVector d,
      (∀ i, IsNormalized (Φ i)) ∧ ∀ i j, i ≠ j → overlapSq (Φ i) (Φ j) ≤ sicOverlapSq d :=
  hasSICPOVM_iff_overlapSq_le_internal d

theorem frame_defect_le_of_overlapSq_le {d : ℕ} (hd : 1 ≤ d) (ε : ℝ)
    (Φ : Fin (d ^ 2) → StateVector d) (hn : ∀ i, IsNormalized (Φ i))
    (ho : ∀ i j, i ≠ j → overlapSq (Φ i) (Φ j) ≤ sicOverlapSq d + ε) :
    ∑ a : Fin d, ∑ b : Fin d, Complex.normSq
      (((d : ℂ)⁻¹ • (∑ i, Matrix.vecMulVec (fun k => Φ i k) (fun l => star (Φ i l))) -
        (1 : Matrix (Fin d) (Fin d) ℂ)) a b) ≤ ((d : ℝ) ^ 2 - 1) * ε :=
  frame_defect_le_of_overlapSq_le_internal hd ε Φ hn ho

end QuantumDesigns
