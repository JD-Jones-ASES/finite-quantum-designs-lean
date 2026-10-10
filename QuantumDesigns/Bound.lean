module

public import QuantumDesigns.Defs

/-!
# The bound `HasMUBs d m → m ≤ d + 1` for `d ≥ 2`, and its sharpness

Lane **bound**. The projector argument (Bandyopadhyay–Boykin–Roychowdhury–Vatan 2002, Theorem 3.5; the general-`d`
lemmas of XC0R's formalization of `d = 6`, adapted): for a basis `U` and a column `j`, `P_j = U_{·j} U_{·j}^*` is a
rank-one projector with `⟨P_j, P_l⟩ = δ_{jl}` inside a basis and `⟨P_j^U, P_l^V⟩ = 1/d` across two unbiased bases
(Hilbert–Schmidt inner product, flattened to `EuclideanSpace ℂ (Fin d × Fin d)`). For each basis `r < m` and each
`k ∈ ZMod d`, `k ≠ 0`, the combination `w_{r,k} = Σ_j ψ(k j) P_j^r` (`ψ = ZMod.stdAddChar`) is traceless and
`‖w_{r,k}‖² = d`; these `m (d − 1)` vectors are pairwise orthogonal (frequency orthogonality inside a basis by
`AddChar.sum_mulShift`; across bases every `⟨P_j^r, P_l^s⟩ = 1/d` is constant, so the sum factors as
`(1/d) Σ_j ψ(−kj) Σ_l ψ(k'l) = 0`), and all are orthogonal to the identity matrix (trace zero). Linear independence
of `1 + m(d − 1)` nonzero pairwise orthogonal vectors in a space of dimension `d²`
(`linearIndependent_of_ne_zero_of_inner_eq_zero`, `LinearIndependent.fintype_card_le_finrank`,
`finrank_euclideanSpace`) gives `1 + m(d − 1) ≤ d²`, hence `m ≤ d + 1` for `d ≥ 2`.
-/

@[expose] public section

namespace QuantumDesigns

theorem hasMUBs_le_internal (d : ℕ) (hd : 2 ≤ d) (m : ℕ) (h : HasMUBs d m) : m ≤ d + 1 := sorry

theorem hasMUBs_one_dim_internal (m : ℕ) : HasMUBs 1 m := sorry

theorem hasMUBs_of_le_internal {d k l : ℕ} (hkl : k ≤ l) (h : HasMUBs d l) : HasMUBs d k := sorry

end QuantumDesigns
