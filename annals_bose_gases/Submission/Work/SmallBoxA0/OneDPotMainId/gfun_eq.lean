import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SmallBoxA0.OneDPotGfunUfun
import Submission.Work.SmallBoxA0.OneDPotMainId.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SmallBoxA0.OneDPotMainId

theorem gfun_eq {R : ℝ} (hR : 0 < R) (p : ℝ → ℝ)
    (hp : MeasureTheory.IntegrableOn (fun r : ℝ => r ^ 2 * p r) (Set.Ioo (0 : ℝ) R))
    (hp0 : ∀ r : ℝ, R ≤ r → p r = 0)
    {r : ℝ} (hr : 0 < r) :
    Work.SmallBoxA0.Gfun p r = Work.SmallBoxA0.Ufun p r / r :=
  Work.SmallBoxA0.OneDPotGfunUfun hR p hp hp0 hr

end Work.SmallBoxA0.OneDPotMainId
