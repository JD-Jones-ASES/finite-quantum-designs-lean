module

public import QuantumDesigns.Bound
public import QuantumDesigns.GapCore
public import QuantumDesigns.GapPhi
public import QuantumDesigns.GapKraus
public import QuantumDesigns.GapDFT
public import QuantumDesigns.GapSchwarz
public import QuantumDesigns.GapDiag

/-!
# Weiner's gap: `d` mutually unbiased bases of `ℂ^d` complete to `d + 1`

Given `B : Fin d → UMat d` pairwise unbiased (`d ≥ 1`; the cases `d ≤ 1` are `hasMUBs_one_dim_internal` and the
empty dimension): the Kraus family `K_0, …, K_{d−1}` of `gp_exists_kraus`, orthogonal to every `w_{r,k}`, is flat
(`gp_flat_of_orth` through `gp_vec_w`), so `Φ(K_i) = K_i` and `Φ(K_i^*) = K_i^*` (`gp_Phi_of_flat`, `gp_flat_star`);
`Φ` preserves traces (`gp_Phi_trace`) and `Σ_i K_i^* K_i = 1`, so by `gp_commute_of_fixed` every `K_i` and every
`K_i^*` commutes with every `K_j`; hence the `2d` Hermitian matrices `K_i + K_i^*` and `i (K_i − K_i^*)` pairwise
commute (expand), and `gp_simultaneous_diag` gives a unitary `W` in whose columns every `K_i` is diagonal
(`K_i = ((K_i + K_i^*) − i·(i (K_i − K_i^*)))/2`). For a column `ε_l` of `W` with projector `Q_l = bd_proj W l`:
`K_i^* Q_l K_i = |D_i(l)|² Q_l` (a diagonal matrix conjugating a rank-one projector of its own eigenbasis), and
`Σ_i |D_i(l)|² = (W^* (Σ_i K_i^* K_i) W)_{ll} = 1`, so `Φ(Q_l) = Q_l`; by `gp_flat_Phi`, `Q_l` is flat:
`gp_diag (B s) Q_l l' = Tr(Q_l)/d = 1/d`, i.e. `‖((B s)^* W)_{l' l}‖² = 1/d` (`gp_diag_apply`): `W` is unbiased to
every `B s`. The family `Fin.snoc B W : Fin (d + 1) → UMat d` is then pairwise unbiased (the pairs inside `B` by
hypothesis, the pairs with `W` by the above and its symmetry).

The corollaries: `d ≤ k` bases restrict to `d` (`hasMUBs_of_le_internal`); for `d ≥ 2`, `IsMaxMUBCount d d` would
put `d + 1 ≤ d`; the dichotomy from the bound `k ≤ d + 1` (`hasMUBs_le_internal`); dimension six as the instance
`d = 6`.
-/

@[expose] public section
noncomputable section

namespace QuantumDesigns

/-- Weiner's gap (Weiner 2013, Corollary 3.4): `d` mutually unbiased bases of `ℂ^d` extend to `d + 1`. -/
theorem hasCompleteMUBs_of_hasMUBs_self_internal (d : ℕ) (h : HasMUBs d d) : HasCompleteMUBs d := sorry

theorem hasCompleteMUBs_of_le_hasMUBs_internal {d k : ℕ} (hk : d ≤ k) (h : HasMUBs d k) :
    HasCompleteMUBs d := sorry

theorem isMaxMUBCount_ne_self_internal (d : ℕ) (hd : 2 ≤ d) : ¬ IsMaxMUBCount d d := sorry

theorem isMaxMUBCount_dichotomy_internal (d : ℕ) (hd : 2 ≤ d) (k : ℕ) (h : IsMaxMUBCount d k) :
    k = d + 1 ∨ k < d := sorry

theorem not_isMaxMUBCount_six_six_internal : ¬ IsMaxMUBCount 6 6 := sorry

end QuantumDesigns
