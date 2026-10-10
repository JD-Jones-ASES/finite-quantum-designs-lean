module

public import QuantumDesigns.Bound
public import QuantumDesigns.Gerzon

/-!
# Welch's bound

For unit vectors `φ_1, …, φ_N` of `ℂ^d` with projectors `P_i = gz_P (φ_i) = |φ_i⟩⟨φ_i|` and frame operator
`S = Σ_i P_i`: `Tr S = N` (`gz_trace_P`) and `Tr(S^* S) = Σ_{i,j} Tr(P_i P_j) = Σ_{i,j} overlapSq (φ_i) (φ_j)`
(`gz_pair_P`: the pairing of `P_j` with `φ_i` is the squared overlap). The Cauchy–Schwarz inequality in the
flattened matrix space (`bd_vec`, `bd_inner_vec`; `norm_inner_le_norm`) for the identity and `S`:
`|⟨1, S⟩|² ≤ ‖1‖² ‖S‖²`, that is `N² ≤ d · Σ_{i,j} overlapSq (φ_i) (φ_j)` (`welch_bound_internal`; Welch 1974,
the first bound, in the frame-potential form of Benedetto–Fickus 2003). With a constant overlap `c` on the `N(N − 1)`
pairs: `N²/d ≤ N + N(N − 1) c`, so `c ≥ (N − d)/(d(N − 1))` for `N ≥ 2` (`welch_bound_of_constantOverlap_internal`;
`c ≥ 0` is automatic, a squared norm). With every pairwise overlap at most `α` and `α d < 1`:
`N²/d ≤ N + N(N − 1) α`, so `N (1 − α d) ≤ d (1 − α)` (`welch_card_bound_internal`; `N = 0` is immediate); at
`α = 1/(d + 1)` this is `N ≤ d²` (`card_le_of_overlapSq_le_sic_internal`): the SIC angle is the smallest common
bound a family of `d²` unit vectors can have, and a family at or below it has at most `d²` members.
-/

@[expose] public section
noncomputable section

namespace QuantumDesigns

/-- Welch's bound: `N` unit vectors of `ℂ^d` have `Σ_{i,j} |⟨φ_i, φ_j⟩|² ≥ N²/d`. -/
theorem welch_bound_internal {d N : ℕ} (Φ : Fin N → StateVector d) (hn : ∀ i, IsNormalized (Φ i)) :
    (N : ℝ) ^ 2 / (d : ℝ) ≤ ∑ i, ∑ j, overlapSq (Φ i) (Φ j) := sorry

/-- Welch's bound for a constant overlap: `c ≥ (N − d)/(d(N − 1))` for `N ≥ 2`. -/
theorem welch_bound_of_constantOverlap_internal {d N : ℕ} {c : ℝ} (hN : 2 ≤ N) (Φ : Fin N → StateVector d)
    (hn : ∀ i, IsNormalized (Φ i)) (ho : HasConstantOverlapSq c Φ) :
    ((N : ℝ) - d) / ((d : ℝ) * ((N : ℝ) - 1)) ≤ c := sorry

/-- The relative bound: every pairwise squared overlap at most `α`, `α d < 1`, gives `N (1 − α d) ≤ d (1 − α)`. -/
theorem welch_card_bound_internal {d N : ℕ} {α : ℝ} (hα : α * (d : ℝ) < 1) (Φ : Fin N → StateVector d)
    (hn : ∀ i, IsNormalized (Φ i)) (ho : ∀ i j, i ≠ j → overlapSq (Φ i) (Φ j) ≤ α) :
    (N : ℝ) * (1 - α * (d : ℝ)) ≤ (d : ℝ) * (1 - α) := sorry

/-- At most `d²` unit vectors of `ℂ^d` have every pairwise squared overlap at most `1/(d + 1)`. -/
theorem card_le_of_overlapSq_le_sic_internal {d N : ℕ} (Φ : Fin N → StateVector d)
    (hn : ∀ i, IsNormalized (Φ i)) (ho : ∀ i j, i ≠ j → overlapSq (Φ i) (Φ j) ≤ sicOverlapSq d) :
    N ≤ d ^ 2 := sorry

end QuantumDesigns
