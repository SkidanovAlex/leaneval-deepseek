import Mathlib
import Submission.Work.FIArea3.BoxDefs
import Submission.Work.FIArea4.polarBox_card_le
import Submission.Work.FIArea6.card_fiber_mod_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea3.JointCount

open Finset Work.FIPlan
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

/-- `|z|²` as a rational integer equals `re² + im²`. -/
lemma gnorm_eq_re_im_class (z : GaussianInt) : (gnorm z : ℤ) = z.re ^ 2 + z.im ^ 2 := by
  rw [gnorm, Zsqrtd.norm]
  have h : (0 : ℤ) ≤ z.re * z.re - (-1) * z.im * z.im := by
    nlinarith [sq_nonneg z.re, sq_nonneg z.im]
  rw [Int.natAbs_of_nonneg h]; ring

/-- `Δ(z₁,z) = Re(z₁)·Im(z) - Im(z₁)·Re(z)`. -/
lemma Delta_class (z₁ z : GaussianInt) :
    Delta z₁ z = z₁.re * z.im - z₁.im * z.re := by
  have hstar : star z₁ = (⟨z₁.re, -z₁.im⟩ : GaussianInt) := Zsqrtd.star_mk z₁.re z₁.im
  rw [Delta, hstar, Zsqrtd.im_mul]
  ring

end

end Work.FIArea3.JointCount
