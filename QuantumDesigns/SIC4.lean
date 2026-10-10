module

public import QuantumDesigns.Defs
public import QuantumDesigns.SIC4Tables

/-!
# A SIC-POVM in dimension 4

The sixteen vectors of a Weyl–Heisenberg orbit of an exact fiducial vector of `ℂ⁴` (the lane records the source
and the fiducial here), normalized, with every pairwise squared overlap `1/5`.
-/

@[expose] public section
noncomputable section

namespace QuantumDesigns

theorem hasSICPOVM_four_internal : HasSICPOVM 4 := sorry

end QuantumDesigns
