/-
Copyright: work module for the Elgindi finite-time singularity project.

# Honesty of the pairing `⟨z∂_z u, z∂_z∂_θθ u⟩` of the almost-everywhere Step-2 estimate

The angular Step-2 estimate (`Work.FTS.EllipticEst.angular_second_order_est`, Step 2 of
`prop:H2` of T. M. Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the
incompressible Euler equations on `ℝ³`*, Annals of Math. **194** (2021)) pairs the radial
first-order term `Grad = z ∂_z u` against the second angular derivative `B = ∂_θθ u`, via the
weighted pairing `AngSecond.IPMem`.  In the Cartesian decomposition of that step the second
factor appears as the *mixed* radial derivative of `B`, i.e. as
`z · ∂_z (∂_θθ u) = z ∂_z (pthIter 2 u)`.

`IPMem g h` is honesty of the pairing `IP g h = ∫_z ∫_θ g z θ * h z θ * w z² * σ θ`: the
integrand is integrable slicewise in `θ` and then in `z`.  This module proves that the pairing
above is honest as soon as the two factors are honest in the weighted space `ℋ⁰`
(`Work.Spaces.HkMem α 0`).

## Route

The class `AeData` makes `u` `C^∞` on the *open* quadrant, so that both profiles agree there
with `C^∞` functions (themselves, in fact): `z ∂_z u` and `z ∂_z ∂_θθ u`.  Two `ℋ⁰`-honest
profiles which are smooth on the open quadrant have an honest mixed pairing:

* the two diagonal pairings `IPMem g g`, `IPMem h h` are `HkMem α 0 g`, `HkMem α 0 h`
  (`AngClean.HkMem_zero_IPMem`);
* the mixed pairing follows from the polarisation `|g h| ≤ g² + h²` together with the a.e.
  strong measurability of the mixed integrand, supplied by the open-quadrant smoothness of the
  two representatives (`AesmCross.aesmSliceCross`, `AesmCross.aesmProdCross`).

`ipMem_of_HkMem_agreeOnQ_tt` is that general statement; it is the local copy of
`Work.FTS.EllipticEst.Honest.IPMem_of_HkMem_agreeOnQ` (which lives behind the `EllHyp`
re-scoping) and keeps this module independent of that re-scoping.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.AngSecond.Defs
import Submission.Work.FTS.EllipticEst.AngClean.HkMem_zero_IPMem
import Submission.Work.FTS.EllipticEst.AngClean.IPMem_F_Phi
import Submission.Work.FTS.EllipticEst.Honest.AesmCross.aesmSliceCross
import Submission.Work.FTS.EllipticEst.Honest.AesmCross.aesmProdCross
import Submission.Work.FTS.EllipticEst.Cert.SmoothOpen_bslOp

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
