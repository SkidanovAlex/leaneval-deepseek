import Mathlib
import Submission.Work.Geometry.Ulam.derivWithin_Icc_eq_deriv

namespace Commons.Geometry.Ulam

open MeasureTheory Set Filter
open scoped ContDiff Pointwise Interval Topology

set_option autoImplicit false

/-- The second one-sided/global derivative link: if `R` is differentiable at `0`
and `deriv R` is differentiable at `0`, then the second one-sided derivative of
`R` on `[0, π/2]` at `0` is the global second derivative. -/
lemma derivWithin_derivWithin_Icc_eq_deriv_deriv_of_differentiableAt
    {R : ℝ → ℝ}
    (hR_diff : DifferentiableAt ℝ R 0)
    (hR_diff2 : DifferentiableAt ℝ (deriv R) 0) :
    derivWithin (derivWithin R (Set.Icc 0 (Real.pi / 2)))
      (Set.Icc 0 (Real.pi / 2)) 0 = deriv (deriv R) 0 := by
  have hzero_pi : (0 : ℝ) < Real.pi / 2 := by linarith [Real.pi_pos]
  have hfirst : derivWithin R (Set.Icc 0 (Real.pi / 2)) 0 = deriv R 0 :=
    derivWithin_Icc_eq_deriv_of_differentiableAt hR_diff
  have hev : derivWithin R (Set.Icc 0 (Real.pi / 2))
      =ᶠ[𝓝[Set.Icc 0 (Real.pi / 2)] 0] deriv R := by
    change ∀ᶠ x in 𝓝[Set.Icc 0 (Real.pi / 2)] 0,
      derivWithin R (Set.Icc 0 (Real.pi / 2)) x = deriv R x
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0) hzero_pi] with x hx hxIcc
    by_cases hx0 : x = 0
    · subst hx0
      exact hfirst
    · have hx_pos : 0 < x := lt_of_le_of_ne hxIcc.1 (Ne.symm hx0)
      have hx_lt : x < Real.pi / 2 := hx.2
      have hmem : Set.Icc 0 (Real.pi / 2) ∈ 𝓝 x := Icc_mem_nhds hx_pos hx_lt
      exact derivWithin_of_mem_nhds hmem
  have hcongr :
      derivWithin (derivWithin R (Set.Icc 0 (Real.pi / 2)))
        (Set.Icc 0 (Real.pi / 2)) 0 =
      derivWithin (deriv R) (Set.Icc 0 (Real.pi / 2)) 0 :=
    hev.derivWithin_eq hfirst
  rw [hcongr]
  exact derivWithin_Icc_eq_deriv_of_differentiableAt hR_diff2

end Commons.Geometry.Ulam
