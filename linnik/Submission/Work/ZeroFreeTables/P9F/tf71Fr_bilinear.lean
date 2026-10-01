import Mathlib
import Submission.Work.ZeroFreeTables.P9F.Defs

noncomputable section
open scoped Real
namespace Work.ZeroFreeTables

/-- **The bilinear form of the closed form.**  For `0 < θ < π/2`, `lam ≠ 0`, `z ≠ 0`, the
closed form `tf71Fr` is affine in `θ` and in `E = tf71Ec θ lam z`:
`tf71Fr θ lam z = P00 + P10·θ + E·(P01 + P11·θ)`. -/
theorem tf71Fr_bilinear (θ lam z : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (hlam : lam ≠ 0) (hz : z ≠ 0) :
    tf71Fr θ lam z = tf71P00 θ lam z + tf71P10 θ lam z * θ
      + tf71Ec θ lam z * (tf71P01 θ lam z + tf71P11 θ lam z * θ) := by
  have htan : Real.tan θ ≠ 0 := by
    exact ne_of_gt (Real.tan_pos_of_pos_of_lt_pi_div_two hθ0 hθ1)
  have h1T : 1 + Real.tan θ ^ 2 ≠ 0 := by positivity
  have hD : tf71Dc θ lam z ≠ 0 := by
    unfold tf71Dc
    have : 0 < (lam * Real.tan θ) ^ 2 := by positivity
    intro h; nlinarith [sq_nonneg z, sq_nonneg (lam * Real.tan θ)]
  have hz2 : z ^ 2 ≠ 0 := pow_ne_zero 2 hz
  have hlamt : lam * Real.tan θ ≠ 0 := mul_ne_zero hlam htan
  simp only [tf71Fr, tf71P00, tf71P10, tf71P01, tf71P11, tf71Jc0, tf71JcE, tf71Js0, tf71JsE,
    tf71KcTE, tf71KcE, tf71Jc, tf71Js, tf71I5, tf71I4, tf71Kc, tf71γ, tf71ζ,
    tf71s2, tf71c2, tf71Bcf]
  field_simp
  ring

end Work.ZeroFreeTables
