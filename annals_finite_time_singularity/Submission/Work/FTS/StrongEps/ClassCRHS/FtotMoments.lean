import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.ClassC.Defs
import Submission.Work.FTS.GalFields.RHS.smoothOpen_N_Ftot_gal
import Submission.Work.FTS.NonlinRows.NRow1_7Aux
import Submission.Work.FTS.StrongPersist.H6Rows.NZaux.L12AddFstar
import Submission.Work.FTS_RegExport.RXT.velPert

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.ClassCRHS

theorem FtotMoments {α Ce : ℝ} {w Φg : Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hα1 : α ≤ 1)
    (hw : Work.FTS.ClassC.ClassC α w)
    (hell : Work.FTS.VocabO.EllPkgGo α Ce w Φg) :
    Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.L12 (Work.Construction.Ftot α w) z) ∧
    Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.FK (Work.Construction.Ftot α w) z) := by
  -- the `ℋ⁴`-honesty of `w` (the class gives `ℋ⁷`)
  have hmem4 : Work.Spaces.HkMem α 4 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hw.reg 4 (by norm_num) hw.mem
  -- the `F_*`-moments are explicit
  have hL12F : Work.FTS.EllipticEst.SmoothOpen
      (fun z (_ : ℝ) => Work.Construction.L12 (Work.Construction.Fstar α) z) :=
    Work.FTS.GalFields.RHS.smoothOpen_L12_Fstar_rad α hα hα1
  have hFKF : Work.FTS.EllipticEst.SmoothOpen
      (fun z (_ : ℝ) => Work.Construction.FK (Work.Construction.Fstar α) z) :=
    Work.FTS.GalFields.RHS.smoothOpen_FK_Fstar_rad α hα hα1
  -- the `w`-halves
  have hL12w : Work.FTS.EllipticEst.SmoothOpen
      (fun z (_ : ℝ) => Work.Construction.L12 w z) :=
    Work.FTS.NonlinRows.smoothOpen_L12_radial hα hell.smooth hell.V.1.1
  have hFKw : Work.FTS.EllipticEst.SmoothOpen
      (fun z (_ : ℝ) => Work.Construction.FK w z) := by
    have hr : ∀ n : ℕ, ContDiffOn ℝ n (fun z : ℝ => 3 * Work.Elliptic.Fstar w z) (Set.Ioi 0) :=
      fun n => contDiffOn_const.mul (hw.fsm n)
    have hmain := Work.FTS.NonlinRows.smoothOpen_radial
      (r := fun z : ℝ => 3 * Work.Elliptic.Fstar w z) hr
    refine hmain.congr ?_
    rintro z θ _ _ _
    exact (Work.FTS_RegExport.RXT.velPert_FK_eq w z).symm
  constructor
  · refine (Work.FTS.NonlinRows.smoothOpen_add hL12F hL12w).congr ?_
    rintro z θ hz _ _
    exact (Work.FTS.StrongPersist.H6Rows.NZaux.L12AddFstar hα hα1 hw.reg hmem4 z hz).symm
  · refine (Work.FTS.NonlinRows.smoothOpen_add hFKF hFKw).congr ?_
    rintro z θ hz _ _
    exact (Work.FTS.GalFields.RHS.FK_add_of_slices (a := Work.Construction.Fstar α) (b := w)
      (ne_of_gt hz)
      (Work.Stability.integrableOn_slice_Fstar α hα z)
      (Work.FTS.GalBasis.cc.integrableOn_slice_of_SmoothOpen_HkMem hw.reg hmem4 hz)).symm

end Work.FTS.StrongEps.ClassCRHS
