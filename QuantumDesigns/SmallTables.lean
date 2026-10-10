module

/-!
# The exponent tables in dimensions 2, 4 and 8 and their kernel check

A leaf importing nothing beyond `Init`. `sm_tabD[a][b][x]` is the exponent `E` of the entry `c · i^E` (`‖c‖² = 1/d`; `Small.lean` takes
`c = (√2)⁻¹`, `1/2`, `(1 + i)/4`) of basis `a`,
column `b`, row `x` (the trace-form construction over `𝔽_{2ⁿ}` in the polynomial basis). `sm_check tab d` evaluates,
for every pair of columns `(a, b)`, `(a', b')`, the Gaussian integer `Σ_x i^{3 E_a(b,x) + E_{a'}(b',x)}`
(`3 E ≡ −E mod 4`) as the pair `(Σ re, Σ im)` and asserts: `= (d, 0)` on the diagonal, `= (0, 0)` for two columns
of one basis, and squared modulus `d` across bases. The recursions are explicit `Nat.rec`s, so the checks reduce
in the kernel (`decide +kernel`).
-/

@[expose] public section

namespace QuantumDesigns

/-- The real part of `i^k`. -/
def sm_re (k : Nat) : Int := if k % 4 = 0 then 1 else if k % 4 = 2 then -1 else 0

/-- The imaginary part of `i^k`. -/
def sm_im (k : Nat) : Int := if k % 4 = 1 then 1 else if k % 4 = 3 then -1 else 0

/-- `Σ_{x < n} re(i^{g x})`. -/
noncomputable def sm_sumRe (g : Nat → Nat) (n : Nat) : Int :=
  Nat.rec (motive := fun _ => Int) 0 (fun i acc => acc + sm_re (g i)) n

/-- `Σ_{x < n} im(i^{g x})`. -/
noncomputable def sm_sumIm (g : Nat → Nat) (n : Nat) : Int :=
  Nat.rec (motive := fun _ => Int) 0 (fun i acc => acc + sm_im (g i)) n

/-- `p i` for every `i < n`. -/
noncomputable def sm_all (n : Nat) (p : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun i acc => acc && p i) n

/-- The table entry: basis `a`, column `b`, row `x`. -/
def sm_E (tab : List (List (List Nat))) (a b x : Nat) : Nat := ((tab.getD a []).getD b []).getD x 0

/-- The inner-product test for one pair of columns. -/
noncomputable def sm_pairOK (tab : List (List (List Nat))) (d a b a' b' : Nat) : Bool :=
  let g := fun x => 3 * sm_E tab a b x + sm_E tab a' b' x
  let re := sm_sumRe g d
  let im := sm_sumIm g d
  if a = a' then
    (if b = b' then re == (d : Int) && im == 0 else re == 0 && im == 0)
  else re * re + im * im == (d : Int)

/-- The test over all pairs of columns. -/
noncomputable def sm_check (tab : List (List (List Nat))) (d : Nat) : Bool :=
  sm_all d fun a => sm_all d fun b => sm_all d fun a' => sm_all d fun b' => sm_pairOK tab d a b a' b'

/-- The exponent table in dimension 2. -/
def sm_tab2 : List (List (List Nat)) :=
  [[[0, 0], [0, 2]],
   [[0, 1], [0, 3]]]

/-- The exponent table in dimension 4. -/
def sm_tab4 : List (List (List Nat)) :=
  [[[0, 0, 0, 0], [0, 2, 0, 2], [0, 0, 2, 2], [0, 2, 2, 0]],
   [[0, 0, 1, 3], [0, 2, 1, 1], [0, 0, 3, 1], [0, 2, 3, 3]],
   [[0, 1, 0, 3], [0, 3, 0, 1], [0, 1, 2, 1], [0, 3, 2, 3]],
   [[0, 1, 1, 2], [0, 3, 1, 0], [0, 1, 3, 0], [0, 3, 3, 2]]]

/-- The exponent table in dimension 8. -/
def sm_tab8 : List (List (List Nat)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 2, 0, 2, 0, 2, 0, 2], [0, 0, 2, 2, 0, 0, 2, 2], [0, 2, 2, 0, 0, 2, 2, 0], [0, 0, 0, 0, 2, 2, 2, 2], [0, 2, 0, 2, 2, 0, 2, 0], [0, 0, 2, 2, 2, 2, 0, 0], [0, 2, 2, 0, 2, 0, 0, 2]],
   [[0, 1, 1, 0, 1, 0, 2, 3], [0, 3, 1, 2, 1, 2, 2, 1], [0, 1, 3, 2, 1, 0, 0, 1], [0, 3, 3, 0, 1, 2, 0, 3], [0, 1, 1, 0, 3, 2, 0, 1], [0, 3, 1, 2, 3, 0, 0, 3], [0, 1, 3, 2, 3, 2, 2, 3], [0, 3, 3, 0, 3, 0, 2, 1]],
   [[0, 1, 0, 3, 0, 1, 2, 1], [0, 3, 0, 1, 0, 3, 2, 3], [0, 1, 2, 1, 0, 1, 0, 3], [0, 3, 2, 3, 0, 3, 0, 1], [0, 1, 0, 3, 2, 3, 0, 3], [0, 3, 0, 1, 2, 1, 0, 1], [0, 1, 2, 1, 2, 3, 2, 1], [0, 3, 2, 3, 2, 1, 2, 3]],
   [[0, 0, 1, 1, 1, 3, 0, 2], [0, 2, 1, 3, 1, 1, 0, 0], [0, 0, 3, 3, 1, 3, 2, 0], [0, 2, 3, 1, 1, 1, 2, 2], [0, 0, 1, 1, 3, 1, 2, 0], [0, 2, 1, 3, 3, 3, 2, 2], [0, 0, 3, 3, 3, 1, 0, 2], [0, 2, 3, 1, 3, 3, 0, 0]],
   [[0, 1, 1, 2, 0, 3, 1, 0], [0, 3, 1, 0, 0, 1, 1, 2], [0, 1, 3, 0, 0, 3, 3, 2], [0, 3, 3, 2, 0, 1, 3, 0], [0, 1, 1, 2, 2, 1, 3, 2], [0, 3, 1, 0, 2, 3, 3, 0], [0, 1, 3, 0, 2, 1, 1, 0], [0, 3, 3, 2, 2, 3, 1, 2]],
   [[0, 0, 0, 2, 1, 1, 1, 3], [0, 2, 0, 0, 1, 3, 1, 1], [0, 0, 2, 0, 1, 1, 3, 1], [0, 2, 2, 2, 1, 3, 3, 3], [0, 0, 0, 2, 3, 3, 3, 1], [0, 2, 0, 0, 3, 1, 3, 3], [0, 0, 2, 0, 3, 3, 1, 3], [0, 2, 2, 2, 3, 1, 1, 1]],
   [[0, 0, 1, 3, 0, 2, 3, 3], [0, 2, 1, 1, 0, 0, 3, 1], [0, 0, 3, 1, 0, 2, 1, 1], [0, 2, 3, 3, 0, 0, 1, 3], [0, 0, 1, 3, 2, 0, 1, 1], [0, 2, 1, 1, 2, 2, 1, 3], [0, 0, 3, 1, 2, 0, 3, 3], [0, 2, 3, 3, 2, 2, 3, 1]],
   [[0, 1, 0, 1, 1, 2, 3, 0], [0, 3, 0, 3, 1, 0, 3, 2], [0, 1, 2, 3, 1, 2, 1, 2], [0, 3, 2, 1, 1, 0, 1, 0], [0, 1, 0, 1, 3, 0, 1, 2], [0, 3, 0, 3, 3, 2, 1, 0], [0, 1, 2, 3, 3, 0, 3, 0], [0, 3, 2, 1, 3, 2, 3, 2]]]


theorem sm_tab2_ok : sm_check sm_tab2 2 = true := by decide +kernel

theorem sm_tab4_ok : sm_check sm_tab4 4 = true := by decide +kernel

theorem sm_tab8_ok : sm_check sm_tab8 8 = true := by decide +kernel

end QuantumDesigns
