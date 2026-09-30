import Mathlib
import Submission.Commons.Analysis.Complex.conj_cpow_ofReal_of_nonneg

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped ComplexConjugate

namespace Work.BMF

/-- Conjugation of a complex power of a nonnegative real. -/
private lemma conj_cpow_ofReal (x : ℝ) (hx : 0 ≤ x) (z : ℂ) :
    (starRingEnd ℂ) ((x:ℂ)^z) = (x:ℂ)^((starRingEnd ℂ) z) :=
  Commons.Analysis.Complex.conj_cpow_ofReal_of_nonneg hx z

/-- The **frozen second-moment kernel identity**: the product of the frozen frequency
`x^{2+it}` with the conjugate of `x^{2+is}` collapses to `x^{4+i(t-s)}`. -/
theorem frozen_l2_cpow {x : ℝ} (hx : 0 < x) (a : ℝ → ℂ) (t s : ℝ) :
    (a t * (x:ℂ)^(2 + Complex.I*(t:ℂ))) * (starRingEnd ℂ) (a s * (x:ℂ)^(2 + Complex.I*(s:ℂ)))
      = (a t * (starRingEnd ℂ) (a s)) * (x:ℂ)^(4 + Complex.I*((t - s : ℝ):ℂ)) := by
  have hxc : (x:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hconj : (starRingEnd ℂ) ((x:ℂ)^(2 + Complex.I*(s:ℂ)))
      = (x:ℂ)^(2 - Complex.I*(s:ℂ)) := by
    rw [conj_cpow_ofReal x hx.le]
    congr 1
    simp only [map_add, map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
    ring
  have hkey : (x:ℂ)^(2 + Complex.I*(t:ℂ)) * (x:ℂ)^(2 - Complex.I*(s:ℂ))
      = (x:ℂ)^(4 + Complex.I*((t - s : ℝ):ℂ)) := by
    rw [← Complex.cpow_add (2 + Complex.I*(t:ℂ)) (2 - Complex.I*(s:ℂ)) hxc]
    congr 1
    push_cast
    ring
  rw [map_mul, hconj]
  calc (a t * (x:ℂ)^(2 + Complex.I*(t:ℂ)))
          * ((starRingEnd ℂ) (a s) * (x:ℂ)^(2 - Complex.I*(s:ℂ)))
      = (a t * (starRingEnd ℂ) (a s))
          * ((x:ℂ)^(2 + Complex.I*(t:ℂ)) * (x:ℂ)^(2 - Complex.I*(s:ℂ))) := by ring
    _ = (a t * (starRingEnd ℂ) (a s)) * (x:ℂ)^(4 + Complex.I*((t - s : ℝ):ℂ)) := by
        rw [hkey]

end Work.BMF
