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

end QuantumDesigns
