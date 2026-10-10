module

public import QuantumDesigns.Bound
public import QuantumDesigns.Gerzon

/-!
# Reconstruction: complete sets of mutually unbiased bases and SIC families are informationally complete

**A complete set of `d + 1` mutually unbiased bases** (Ivanović 1981; Wootters–Fields 1989). With
`P_{s,l} = bd_proj (B s) l` and `T(X) = Σ_{s,l} Tr(X P_{s,l}) P_{s,l} − Tr(X)·1`, both sides of
`X = T(X)` are linear in `X`, and the `d²` flattened vectors `1, w_{r,k}` of `bd_fam B` are linearly independent
(the family of `hasMUBs_le_internal`, with `m = d + 1`: `1 + (d + 1)(d − 1) = d²`), hence span the matrix space
(`LinearIndependent.span_eq_top_of_card_eq_finrank'`, `finrank_euclideanSpace`); so it suffices to check
`T(1) = 1` (`Σ_{s,l} P_{s,l} = (d + 1)·1`, `Tr 1 = d`) and `T(P_{r,j}) = P_{r,j}` (`Tr(P_{r,j} P_{s,l})` is `δ_{jl}`
for `s = r` and `1/d` for `s ≠ r`, `bd_inner_proj_same`, `bd_inner_proj_unbiased`; the other `d` bases each
contribute `(1/d) Σ_l P_{s,l} = (1/d)·1`, in all `1`, cancelled by `Tr(P_{r,j})·1 = 1`), the `w_{r,k}` being
combinations of the `P_{r,j}` (`mub_reconstruction_internal`).

**A SIC family** (Renes–Blume-Kohout–Scott–Caves 2004, §II). The `d²` projectors `P_i = gz_P (φ_i)` are linearly
independent (`gz_linIndep`, `c = 1/(d + 1) ≠ 1`), hence a basis of the matrix space; writing `X = Σ_i a_i P_i`,
the pairing with `φ_j` (`gz_pair_eq`) gives `Tr(X P_j) = (1 − c) a_j + c Σ_i a_i` and the trace gives
`Tr X = Σ_i a_i`, so `a_j = ((d + 1) Tr(X P_j) − Tr X)/d` (`sic_reconstruction_internal`; `d = 0` is the empty
matrix, `d = 1` the single projector `1`).
-/

@[expose] public section
noncomputable section

namespace QuantumDesigns

/-- A complete set of mutually unbiased bases reconstructs every matrix from its diagonals:
`X = Σ_{s,l} Tr(X P_{s,l}) P_{s,l} − Tr(X)·1`. -/
theorem mub_reconstruction_internal {d : ℕ} (B : Fin (d + 1) → UMat d) (hB : IsMUBFamily B)
    (X : Matrix (Fin d) (Fin d) ℂ) :
    X = ∑ s, ∑ l, Matrix.trace (X * Matrix.vecMulVec (fun a => (B s : Matrix (Fin d) (Fin d) ℂ) a l)
          (fun b => star ((B s : Matrix (Fin d) (Fin d) ℂ) b l))) •
        Matrix.vecMulVec (fun a => (B s : Matrix (Fin d) (Fin d) ℂ) a l)
          (fun b => star ((B s : Matrix (Fin d) (Fin d) ℂ) b l)) -
      Matrix.trace X • (1 : Matrix (Fin d) (Fin d) ℂ) := sorry

/-- A SIC family reconstructs every matrix: `X = Σ_i ((d + 1) Tr(X P_i) − Tr X)/d · P_i`. -/
theorem sic_reconstruction_internal {d : ℕ} (Φ : Fin (d ^ 2) → StateVector d) (h : IsSICFamily d Φ)
    (X : Matrix (Fin d) (Fin d) ℂ) :
    X = ∑ i, ((((d : ℂ) + 1) * Matrix.trace (X * Matrix.vecMulVec (fun k => Φ i k) (fun l => star (Φ i l))) -
          Matrix.trace X) / (d : ℂ)) • Matrix.vecMulVec (fun k => Φ i k) (fun l => star (Φ i l)) := sorry

end QuantumDesigns
