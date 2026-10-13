import Mathlib
import Submission.Work.WilG4c.Hyps
import Submission.Work.WilG4c.StepCleanDefs
import Submission.Work.WilG1.Basic
import Submission.Work.WilG2.Tnorm
import Submission.Work.WilG2.CompBound
import Submission.Work.WilG2.CompMain
import Submission.Work.WilG3.Defs
import Submission.Work.WilG4a.Defs
import Submission.Work.WilG4b.Basic
import Submission.Work.WilG5.Basic
import Submission.Work.WilG5.Reindex
import Submission.Work.WilG5.Reindex2
import Submission.Work.WilG5.Reindex3
-- The §5.5 per-cell engine and its assembly, imported through the *clean* copies in
-- `Submission/Work/WilG4c/Clean/` (see the note at the end of `STEPCLEAN_NOTES.md`): the
-- original engine chain reaches `Submission.Work.WilG4c.StepCellAux1`, which declares
-- `Work.WilG4c.init_append` a second time (with a different implicit-argument shape than
-- `Submission.Work.WilG4c.AlBadParDefs`, imported below through the fibre-core chain), and Lean
-- refuses to import both into one environment.  The clean copies are verbatim copies of the
-- engine modules with that one declaration renamed, and with the imports of the copied modules
-- redirected, so that the original `StepCellAux1` is never loaded here.
import Submission.Work.WilG4c.Clean.Asm
import Submission.Work.WilG4c.FibreBadCoresSharp

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG

/-- **BNZ §5.5 — final clean up.**  From `FLem` for families that are `1`-Lipschitz and `C^r`
on the whole cube with all derivative norms `≤ 1` (`Work.WilkG4c.PSmooth`), deduce `FLem` for
families whose derivatives are only bounded *where defined* (`Work.WilkG4c.PYLipDef`).

Plan (BNZ §5.5).  Let `V_{i,α}` be the locus, inside the cube, where `F_i^{(α)}` is undefined
(`|α| ≤ r`); `hder` makes these `Ω`-bounded.  A cell decomposition (`hcd`) compatible with all
`V_{i,α}` gives `poly(D,r,k)` cells, inducing one of the parameter space `Λ × I_x`.  The family
algebraic lemma — `ih` in dimension `n` applied to the cell parametrisations
`(Λ × I_x) × I^n → cell` obtained from the cell decomposition (BNZ Lemma 5.1 plus cell
decomposition, "alg-lem-family") — gives, for each cell `C_ν`, `poly(D,r,|log ε|)` maps
`φ_{ν,η} : (Λ × I_x) × I^n → C_ν` with unit `r`-norms and `Ω`-bounded graphs.  Since `F` is
`1`-Lipschitz one may pull back by each `(φ_{ν,η}, x)`, getting families for which the
non-smooth locus `V` is a union of graphs of `Ω`-bounded functions `G_1,…,G_q`
(`q = poly(D,k,r)`) with `G_1 = G_q = 0`; a further application of `ih` (dimension `n`) plus
affine pullbacks makes `‖G_{j}‖_r ≤ 1`, and the strips
`(Λ × I^n) \ V = ⋃_i (Λ × I^n) ⊙ (G_i, G_{i+1})` are covered by the affine maps
`(x,t) ↦ (x, tG_{i+1} + (1-t)G_i)` (again of bounded `r`-norm), and one more pullback reduces
to the case `V = ∅`, i.e. to `PSmooth` for each piece, to which `hP3` applies.

Take the `Finset` union of the chart families of the pieces: the counts add and the
format/degree are unchanged (each chart must satisfy the conditions for all `l ∈ Λ`, so apply
`hP3` with the whole parameter set on each pullback family). -/
theorem StepClean (S : SOMin) (hcd : S.SharpCD) (hder : S.SharpDeriv) (n p : ℕ) (hn : 1 ≤ n)
    (h1 : ∀ q, F1Affine S q) (ih : ∀ q, FLem S q n) (hchoice : Work.WilkG4c.ChoiceHyp S)
    (hP3 : Work.WilkG4c.FLemP S p (n + 1) (Work.WilkG4c.PSmooth p n)) :
    Work.WilkG4c.FLemP S p (n + 1) (Work.WilkG4c.PYLipDef p n) := by
  exact Work.WilG4c.FLemPOfFibreCores S hcd n p hn ih
    (Work.WilG4c.FibreBadCoresSharp S hcd hder p (n + 1))

end Work.WilG4c

/-! ### Alias under the alternative namespace spelling

Parts of the area (`Submission/Work/WilG4c/G4step.lean`) spell this namespace `Work.WilkG4c`;
we record the same theorem under that spelling so that the §5.2–§5.5 assembly can call it. -/

namespace Work.WilkG4c

open WilkiesDesign WilkiesDesign.CG

/-- Alias of `Work.WilG4c.StepClean` (same statement, alternative namespace spelling). -/
theorem StepClean (S : SOMin) (hcd : S.SharpCD) (hder : S.SharpDeriv) (n p : ℕ) (hn : 1 ≤ n)
    (h1 : ∀ q, F1Affine S q) (ih : ∀ q, FLem S q n) (hchoice : Work.WilkG4c.ChoiceHyp S)
    (hP3 : Work.WilkG4c.FLemP S p (n + 1) (Work.WilkG4c.PSmooth p n)) :
    Work.WilkG4c.FLemP S p (n + 1) (Work.WilkG4c.PYLipDef p n) :=
  Work.WilG4c.StepClean S hcd hder n p hn h1 ih hchoice hP3

end Work.WilkG4c
