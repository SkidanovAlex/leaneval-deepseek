import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.PsiInt_sq_mul_w_le_open
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

/-- **Cauchy--Schwarz for the `j`-th radial moment `F_*(D_z^j F)`** (open-quadrant
source).  This is `PsiInt_sq_mul_w_le_open` with `u = F`: the `j`-th radial moment
`PsiInt F j z = ∫_θ D_z^j F(z,θ) sinθcos²θ dθ` of `F` is *by definition* the angular
moment `F_*(D_z^j F)(z)`, and the integrability hypothesis needed by the
Cauchy--Schwarz estimate is furnished by `integrableOn_zSummand` from `F ∈ ℋ^k`
(together with `j ≤ k`). -/
theorem FstarDzIter_sq_mul_w_le_open (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ)
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (hmem : Work.Spaces.HkMem α k F) (j : ℕ) (hj : j ≤ k)
    {z : ℝ} (hz : 0 < z) :
    (Work.Elliptic.Fstar (Work.Spaces.DzIter j F) z) ^ 2 * (Work.Spaces.w z) ^ 2
      ≤ (π / 2) * ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.DzIter j F z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  have hzI : z ∈ Work.Spaces.Iz := by rw [Work.Spaces.Iz]; exact le_of_lt hz
  have hU : IntegrableOn (fun θ : ℝ => (Work.Spaces.DzIter j F z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      Work.Spaces.Iθ :=
    integrableOn_zSummand α k hF hmem j hj hzI
  have h := PsiInt_sq_mul_w_le_open F hF j hz hU
  simpa only [PsiInt, Work.Elliptic.Fstar] using h

end Work.FTS.EllipticEst
