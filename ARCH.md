# Architecture and lane protocol, second fleet (working document; not part of the published repository)

## What the first fleet built (main at 1ea7431, VERIFY: PASS)

26 compared theorems over the 14 formal-conjectures definitions (OQP 13 and 23, restated verbatim, NOTICE): the
`d + 1` bound and its sharpness, restriction, the tensor bound and the factorization corollary, three bases in every
`d ≥ 2`, complete sets in every prime-power dimension (odd `q` by Weyl differencing, `2ⁿ` by the ℤ/4 trace-form
bases, `2, 4, 8` by kernel tables), the iff for complete sets, Gerzon's bound with its equality case and the frame
identity, SIC ⇒ POVM, the equiangular iff, SIC maximality, `HasSICPOVM 2, 3, 8`. Modules: `Defs`, `Bound`, `Tensor`,
`OddField`, `TwoPow`, `SmallTables`/`Small`, `Chirp`, `PrimePow`, `Gerzon`, `SICTables`/`SIC`, `Main`. PROOF.md
describes every proof with the Lean names; read it for the helpers you may reuse (`bd_proj`, `bd_vec`,
`bd_inner_vec`, `bd_inner_proj_same`, `bd_inner_proj_unbiased`, `bd_zeta`, `bd_geom_zero`, `bd_w`, `bd_inner_w_*`,
`bd_fam`, `gz_P`, `gz_pair`, `gz_pair_P`, `gz_pair_eq`, `gz_linIndep`, `gz_trace_P`, `of_isUnbiased_symm`, …).

## What this fleet adds (19 new pinned statements in `Challenge.lean`)

| Module | Lane | Imports | Pinned statements (sorried in the skeleton) |
| --- | --- | --- | --- |
| `GapCore` | **phi** | Bound | the definitions `gp_diag`, `gp_pinch`, `gp_w`, `gp_Phi`, `gp_Flat`, `gp_unvec`; `gp_unvec_vec`, `gp_vec_unvec`, `gp_vec_w`, `gp_inner_vec_eq_trace`, `gp_diag_eq_inner` |
| `GapPhi` | **phi** | GapCore | `gp_diag_apply`, `gp_proj_mul_mul_proj`, `gp_sum_proj`, `gp_trace_proj`, `gp_star_proj`, `gp_pinch_eq`, `gp_sum_diag`, `gp_diag_proj_same`, `gp_diag_proj_unbiased`, `gp_diag_pinch_same`, `gp_diag_pinch_unbiased`, `gp_Phi_one`, `gp_Phi_trace`, `gp_Phi_star`, `gp_flat_Phi`, `gp_Phi_of_flat`, `gp_flat_star`, `gp_flat_one` |
| `GapKraus` | **kraus** | GapCore, GapPhi | `gp_onb_sum` (Weiner's Lemma 2.1), `gp_w_sum`, `gp_exists_kraus` (Lemma 3.2) |
| `GapDFT` | **dft** | GapCore | `gp_flat_of_orth` |
| `GapSchwarz` | **schwarz** | GapCore | `gp_schwarz_defect`, `gp_eq_zero_of_trace_sum_star_mul_self`, `gp_commute_of_fixed` |
| `GapDiag` | **diag** | Defs | `gp_simultaneous_diag` |
| `GapMain` | **gapmain** | all Gap modules, Bound | `hasCompleteMUBs_of_hasMUBs_self_internal` (Weiner's gap), `hasCompleteMUBs_of_le_hasMUBs_internal`, `isMaxMUBCount_ne_self_internal`, `isMaxMUBCount_dichotomy_internal`, `not_isMaxMUBCount_six_six_internal` |
| `Welch` | **welch** | Bound, Gerzon | `welch_bound_internal`, `welch_bound_of_constantOverlap_internal`, `welch_card_bound_internal`, `card_le_of_overlapSq_le_sic_internal` |
| `Reconstruct` | **reconstruct** | Bound, Gerzon | `mub_reconstruction_internal`, `sic_reconstruction_internal` |
| `Count` | **count** | Bound, Tensor, Chirp, Main | `hasMUBs_two_internal`, `hasMUBs_prime_pow_iff_internal`, `isMaxMUBCount_unique_internal`, `exists_isMaxMUBCount_internal`, `not_exists_isMaxMUBCount_one_internal`, `isMaxMUBCount_bounds_internal`, `mutuallyUnbiasedBases_dim6_bounds_internal` |
| `SIC4Tables`, `SIC4` | **sic4** (stretch) | Defs | `hasSICPOVM_four_internal` |

Each module's docstring carries its proof plan (the route of Weiner's paper, arXiv:0902.0635v2, made elementary:
no Choi inequality, no double commutant — the Kadison–Schwarz defect of the Kraus form is written out as a sum of
squares, and the missing basis is a common eigenbasis of the commuting flat matrices). Dependencies between lanes
go only through the pinned statements: a lane *uses* another module's sorried theorem as a black box (add a
`public import QuantumDesigns.<Module>` line to your own module if you need one — only your own module's import
block may change) and never waits for it. The desk merges finished lanes.

## Rules (binding for every lane)

1. Every statement in your module is PINNED: keep its name, hypotheses and conclusion. Add helpers freely in your
   file, prefixed with your lane prefix (`gp_`, `wl_`, `rc_`, `ct_`, `s4_`). If a pin is false or unprovable as
   stated, prove the nearest correct version under a new name, leave the pin with `sorry`, and report it under
   `wrong_pins`. The `phi` lane owns `GapCore` and `GapPhi` both.
2. Never edit any other file (other modules, `Challenge.lean`, `Solution.lean`, scripts) except to add an import
   line to your own module. If you need a fact from another module that is not pinned there, prove a private copy
   in your file named `aux_…` and report the duplication.
3. Build ONLY with `bash scripts/lane-build.sh QuantumDesigns.<YourModule>` from your worktree root (two
   machine-wide build slots and a free-memory wait; the box has 16 GB and little free). Never run `lake build` or
   `lean` directly, never several targets in one call, never two builds at once. Read the whole output: grep for
   `error` and `sorry` separately; a build that prints "Build completed successfully" with sorry warnings is not done.
4. Kernel-only: no `native_decide`, `axiom`, `unsafe`, `partial`, `implemented_by`, `mutual`, `opaque`, `sorry`
   (except pins still open); `decide +kernel` is allowed. Mathlib v4.35.0-rc2 at `.lake/packages/mathlib` (grep it
   for names; it is a junction, read-only). Known renames: `le_or_lt` is `le_or_gt`; `Basis` is `Module.Basis`;
   `inner ℂ x y` takes the field; inside `open Matrix`, `zpow_mul`/`one_zpow` need `_root_.`; `Equiv.sum_comp`
   resolves to the Perm version (use `Fintype.sum_equiv`); `omega` has no dark shadow (pick disjuncts first);
   `section` variable hypotheses need `include`; `EuclideanSpace` vectors are `WithLp.toLp 2 f` and apply as functions.
5. Commit on your branch as you go (`git add QuantumDesigns/<Module>.lean; git commit -m "..."`); never push;
   scratch files go under your worktree (never `/tmp`, which is shared across lanes).
6. Time box per lane in the brief; then stop and report what is closed. Partial progress with every closed statement
   committed is valuable; do not leave the file in a non-building state at the end.
7. A statement's docstring is published: no lane residue ("Lane:", "TODO"), no owner's name, no "record".
