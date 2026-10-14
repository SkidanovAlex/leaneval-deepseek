import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EllipticEst.Tools.aesm_Fpair_fts
import Submission.Work.FTS.EllipticEst.integrableOn_Bmom_div
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.sq_mul_div_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.TT

set_option autoImplicit false

/-! ## The general cross-honesty lemma -/

/-- **Cross honesty from the two diagonal honesties and open-quadrant smoothness.**

If `g` and `h` are honest (`HkMem α 0`, hence `IPMem` on the diagonal) and each agrees on the
open quadrant with a `C^∞` profile (`AgreeOnQ g g'`, `SmoothOpen g'`, and likewise for `h`),
then the mixed pairing `IPMem g h` is honest.  The two `SmoothOpen` representatives supply the
a.e. strong measurability of the mixed integrand off the null boundary of the quadrant, and the
polarisation inequality `|g h| ≤ g² + h²` does the rest. -/
theorem ipMem_of_HkMem_agreeOnQ_tt {α : ℝ} {g h g' h' : ℝ → ℝ → ℝ}
    (hg' : Work.FTS.EllipticEst.SmoothOpen g') (hh' : Work.FTS.EllipticEst.SmoothOpen h')
    (hgg : Work.FTS.EllipticEst.AgreeOnQ g g') (hhh : Work.FTS.EllipticEst.AgreeOnQ h h')
    (hmg : Work.Spaces.HkMem α 0 g) (hmh : Work.Spaces.HkMem α 0 h) :
    Work.FTS.EllipticEst.AngSecond.IPMem g h :=
  Work.FTS.EllipticEst.AngClean.IPMem_of_diag_aesm
    (Work.FTS.EllipticEst.AngClean.HkMem_zero_IPMem hmg)
    (Work.FTS.EllipticEst.AngClean.HkMem_zero_IPMem hmh)
    (fun z hz => Work.FTS.EllipticEst.Honest.AesmCross.aesmSliceCross hg' hh' hgg hhh z hz)
    (Work.FTS.EllipticEst.Honest.AesmCross.aesmProdCross hg' hh' hgg hhh)

/-! ## The pairing of the Step-2 radial term with the mixed second derivative -/

theorem ipMemUHtermFts (α : ℝ) (u G : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    (hU : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u))
    (hH : Work.Spaces.HkMem α 0
      (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ)) :
    Work.FTS.EllipticEst.AngSecond.IPMem (Work.FTS.EllipticEst.H2W.Ae.grad u)
      (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ) := by
  -- `u` is `C^∞` on the open quadrant, hence so are `z ∂_z u` and `z ∂_z ∂_θθ u`.
  have hu : Work.FTS.EllipticEst.SmoothOpen u :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hgrad : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.EllipticEst.H2W.Ae.grad u) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl
      Work.FTS.EllipticEst.Cert.smoothOpen_z_bsl
      (Work.FTS.EllipticEst.SmoothOpen.pz hu)
  have hsec : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl
      Work.FTS.EllipticEst.Cert.smoothOpen_z_bsl
      (Work.FTS.EllipticEst.SmoothOpen.pz
        (Work.FTS.EllipticEst.Cert.smoothOpen_pthIter_bsl hu 2))
  exact ipMem_of_HkMem_agreeOnQ_tt hgrad hsec
    (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ => rfl) hU hH

end Work.FTS.EllipticEst.TT
