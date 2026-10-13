import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.ClassCRHS.SmoothOpenRHS
import Submission.Work.FTS.StrongEps.ClassCRHS.smoothOpen_L12_radial_classC
import Submission.Work.FTS.StrongPersist.H6Rows.NZaux.L12AddFstar
import Submission.Work.FTS.StrongEps.ClassCRHS.FtotMoments

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5Aux2

open scoped Real Topology
open MeasureTheory Set Filter

/-- **The two moments `L₁₂(F_* + w)` and `FK(F_* + w)` are `C^∞` on the open quadrant for a
profile `w` of the class `ClassC α`** — with no elliptic data at all.

This is the `ClassC`-native version of the first two conjuncts of
`ClassCRHS.SmoothOpenRHS`: the elliptic package `hell` is *not* used, because

* `z ↦ L₁₂(w)(z)` is `C^∞` on `(0,∞)` from `ClassC.reg` + `ClassC.mem` alone
  (`ClassCRHS.smoothOpen_L12_radial_classC`), while the older route went through
  `smoothOpen_L12_radial` and the elliptic field `hell`;
* `z ↦ FK(w)(z) = 3 F_*(w)(z)` is radial smooth from `ClassC.fsm` alone
  (`RXT.velPert_FK_eq`), no elliptic data either;
* the `F_*`-halves are explicit (`smoothOpen_L12_Fstar_rad`, `smoothOpen_FK_Fstar_rad`), and the
  two halves add by `NZaux.L12AddFstar` respectively `GalFields.RHS.FK_add_of_slices`. -/
theorem prof_cont_moments {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {w : ℝ → ℝ → ℝ}
    (hw : Work.FTS.ClassC.ClassC α w) :
    Work.FTS.EllipticEst.SmoothOpen
        (fun z (_ : ℝ) => Work.Construction.L12 (Work.Construction.Ftot α w) z) ∧
      Work.FTS.EllipticEst.SmoothOpen
        (fun z (_ : ℝ) => Work.Construction.FK (Work.Construction.Ftot α w) z) := by
  -- the `ℋ⁴`-honesty of `w`, from the `ℋ⁷`-honesty of the class
  have hmem4 : Work.Spaces.HkMem α 4 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hw.reg 4 (by norm_num) hw.mem
  -- `SmoothOpen (z ↦ L₁₂(w)(z))`: no elliptic data needed
  have hL12w : Work.FTS.EllipticEst.SmoothOpen
      (fun z (_ : ℝ) => Work.Construction.L12 w z) :=
    Work.FTS.StrongEps.ClassCRHS.smoothOpen_L12_radial_classC hα hw
  -- `SmoothOpen (z ↦ FK(w)(z))`: `FK F = 3 F_*(F)`, so only `ClassC.fsm` is used
  have hFKw : Work.FTS.EllipticEst.SmoothOpen
      (fun z (_ : ℝ) => Work.Construction.FK w z) := by
    have hr : ∀ n : ℕ, ContDiffOn ℝ n (fun z : ℝ => 3 * Work.Elliptic.Fstar w z)
        (Set.Ioi 0) :=
      fun n => contDiffOn_const.mul (hw.fsm n)
    have hmain := Work.FTS.NonlinRows.smoothOpen_radial
      (r := fun z : ℝ => 3 * Work.Elliptic.Fstar w z) hr
    refine hmain.congr ?_
    rintro z θ _ _ _
    exact (Work.FTS_RegExport.RXT.velPert_FK_eq w z).symm
  -- the two `F_*`-moments are explicit
  have hL12F : Work.FTS.EllipticEst.SmoothOpen
      (fun z (_ : ℝ) => Work.Construction.L12 (Work.Construction.Fstar α) z) :=
    Work.FTS.GalFields.RHS.smoothOpen_L12_Fstar_rad α hα hα1
  have hFKF : Work.FTS.EllipticEst.SmoothOpen
      (fun z (_ : ℝ) => Work.Construction.FK (Work.Construction.Fstar α) z) :=
    Work.FTS.GalFields.RHS.smoothOpen_FK_Fstar_rad α hα hα1
  constructor
  · -- the first moment `L₁₂(F_* + w)`
    refine (Work.FTS.NonlinRows.smoothOpen_add hL12F hL12w).congr ?_
    rintro z θ hz _ _
    exact (Work.FTS.StrongPersist.H6Rows.NZaux.L12AddFstar hα hα1 hw.reg hmem4 z hz).symm
  · -- the second moment `FK(F_* + w)`
    refine (Work.FTS.NonlinRows.smoothOpen_add hFKF hFKw).congr ?_
    rintro z θ hz _ _
    exact (Work.FTS.GalFields.RHS.FK_add_of_slices
      (a := Work.Construction.Fstar α) (b := w) (ne_of_gt hz)
      (Work.Stability.integrableOn_slice_Fstar α hα z)
      (Work.FTS.GalBasis.cc.integrableOn_slice_of_SmoothOpen_HkMem hw.reg hmem4 hz)).symm

end Work.FTS.StrongEps.E5Aux2
