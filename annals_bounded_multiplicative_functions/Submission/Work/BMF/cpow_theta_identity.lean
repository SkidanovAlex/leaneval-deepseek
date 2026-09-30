import Mathlib
import Submission.Work.BMF.parseval_kernels

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The window kernel as a cpow multiple of the average kernel

For `x, h > 0` and `t : ℝ` one has
`x^{it} · Θ(h/x, t) = winKern h x t = ((x+h)^{1+it} - x^{1+it}) / (h(1+it))`,

i.e. the normalised window kernel is the average kernel `Θ` rescaled by the
low-frequency factor `x^{it}`.  This is the identity behind writing the Perron
integral of the short-interval sum as an integral against `Θ`, and it is used
in the reduction of the Parseval bound to the smallness of `Δ`.
-/

namespace Work.BMF

theorem cpow_theta_identity (h x t : ℝ) (hx : 0 < x) (hh : 0 < h) :
    ((x : ℂ) ^ (Complex.I * (t : ℂ))) * (Work.BMF.Theta (h / x) t)
      = (((x + h : ℝ) : ℂ) ^ (1 + Complex.I * (t : ℂ)) - ((x : ℂ) ^ (1 + Complex.I * (t : ℂ))))
          / ((h : ℂ) * (1 + Complex.I * (t : ℂ))) := by
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hh0 : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  have hδ : 0 ≤ 1 + h / x := by positivity
  have hdx0 : ((h / x : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < h / x := div_pos hh hx
    exact_mod_cast this.ne'
  have hw0 : (1 + Complex.I * (t : ℂ)) ≠ 0 := by
    intro hc
    have h := congrArg Complex.re hc
    simp at h
  have hD0 : (((h / x : ℝ) : ℂ) * (1 + Complex.I * (t : ℂ))) ≠ 0 := mul_ne_zero hdx0 hw0
  have hK0 : (h : ℂ) * (1 + Complex.I * (t : ℂ)) ≠ 0 := mul_ne_zero hh0 hw0
  have hxdc : (x : ℂ) * ((h / x : ℝ) : ℂ) = (h : ℂ) := by
    rw [← Complex.ofReal_mul]; congr 1; field_simp
  have hxcBc : (x : ℂ) * ((1 + h / x : ℝ) : ℂ) = ((x + h : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul]; congr 1; field_simp
  have hnum1 : (x : ℂ) ^ (Complex.I * (t : ℂ)) * (x : ℂ)
      = (x : ℂ) ^ (1 + Complex.I * (t : ℂ)) := by
    calc (x : ℂ) ^ (Complex.I * (t : ℂ)) * (x : ℂ)
        = (x : ℂ) ^ (Complex.I * (t : ℂ)) * (x : ℂ) ^ (1 : ℂ) := by rw [Complex.cpow_one]
      _ = (x : ℂ) ^ (Complex.I * (t : ℂ) + 1) :=
            (Complex.cpow_add (Complex.I * (t : ℂ)) 1 hx0).symm
      _ = (x : ℂ) ^ (1 + Complex.I * (t : ℂ)) := by congr 1; ring
  have hnum2 : (x : ℂ) ^ (1 + Complex.I * (t : ℂ))
        * ((1 + h / x : ℝ) : ℂ) ^ (1 + Complex.I * (t : ℂ))
      = ((x + h : ℝ) : ℂ) ^ (1 + Complex.I * (t : ℂ)) := by
    rw [← Complex.mul_cpow_ofReal_nonneg (le_of_lt hx) hδ (1 + Complex.I * (t : ℂ)), hxcBc]
  have hKdiv : ((h : ℂ) * (1 + Complex.I * (t : ℂ)))
        / (((h / x : ℝ) : ℂ) * (1 + Complex.I * (t : ℂ))) = (x : ℂ) := by
    rw [div_eq_iff hD0, ← mul_assoc, hxdc]
  have hmain : (x : ℂ) ^ (Complex.I * (t : ℂ))
        * (((1 + h / x : ℝ) : ℂ) ^ (1 + Complex.I * (t : ℂ)) - 1) * (x : ℂ)
      = ((x + h : ℝ) : ℂ) ^ (1 + Complex.I * (t : ℂ))
          - (x : ℂ) ^ (1 + Complex.I * (t : ℂ)) := by
    calc (x : ℂ) ^ (Complex.I * (t : ℂ))
            * (((1 + h / x : ℝ) : ℂ) ^ (1 + Complex.I * (t : ℂ)) - 1) * (x : ℂ)
        = (x : ℂ) ^ (Complex.I * (t : ℂ)) * (x : ℂ)
            * ((1 + h / x : ℝ) : ℂ) ^ (1 + Complex.I * (t : ℂ))
            - (x : ℂ) ^ (Complex.I * (t : ℂ)) * (x : ℂ) := by ring
      _ = (x : ℂ) ^ (1 + Complex.I * (t : ℂ))
            * ((1 + h / x : ℝ) : ℂ) ^ (1 + Complex.I * (t : ℂ))
            - (x : ℂ) ^ (1 + Complex.I * (t : ℂ)) := by rw [hnum1]
      _ = _ := by rw [hnum2]
  have hstep : (x : ℂ) ^ (Complex.I * (t : ℂ))
        * ((((1 + h / x : ℝ) : ℂ) ^ (1 + Complex.I * (t : ℂ)) - 1)
            / (((h / x : ℝ) : ℂ) * (1 + Complex.I * (t : ℂ))))
        * ((h : ℂ) * (1 + Complex.I * (t : ℂ)))
      = (x : ℂ) ^ (Complex.I * (t : ℂ))
          * (((1 + h / x : ℝ) : ℂ) ^ (1 + Complex.I * (t : ℂ)) - 1) * (x : ℂ) := by
    rw [mul_assoc, div_mul_eq_mul_div, mul_div_assoc, hKdiv, mul_assoc]
  rw [eq_div_iff hK0]
  unfold Work.BMF.Theta
  rw [hstep, hmain]

end Work.BMF
