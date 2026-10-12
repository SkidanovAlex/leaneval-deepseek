import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.SmallBoxA0.OneDPotMainId.Defs
import Submission.Work.SmallBoxA0.primitive_integrable
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SmallBoxA0.OneDPotMainId

theorem tailI_intervalIntegrable {R : ℝ} (hR : 0 < R) (p : ℝ → ℝ)
    (hp : MeasureTheory.IntegrableOn (fun r : ℝ => r ^ 2 * p r) (Set.Ioo (0 : ℝ) R)) :
    IntervalIntegrable (Work.SmallBoxA0.TailI p R) MeasureTheory.volume 0 R := by
  -- `TailI p R r = ∫ s in r..R, u s` with `u s = s * p s`, and `s * u s = s ^ 2 * p s`.
  have h := Work.SmallBoxA0.primitive_integrable (R := R) hR (u := fun s : ℝ => s * p s)
    (by simpa only [pow_two, mul_assoc] using hp)
  show IntervalIntegrable (fun r : ℝ => ∫ s in r..R, s * p s) MeasureTheory.volume 0 R
  exact h

end Work.SmallBoxA0.OneDPotMainId
