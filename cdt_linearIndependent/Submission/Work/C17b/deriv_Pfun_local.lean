import Mathlib
import Submission.Work.C17.seventeen_defs

/-!
# Local differentiation of the `P`-series branch

The analytic function `Work.C17.Pfun a b ra rb rab r0` is (locally, near the origin and inside the
disc of convergence of the unlikely series `P`) of the shape
`z ↦ κ · y₁ z · log (x_s − z) + hh z`
(see `Work.C17.logP_local_plan`).  This file differentiates such a representation: since `deriv` is a
purely local operation, the derivative of `Pfun` at a point of the domain is the derivative of the
right hand side.  The logarithm is holomorphic at `x_s − z` because `|z| < x_s` forces
`Re (x_s − z) > 0`.
-/

namespace Work.C17b

/-- `HasDerivAt` for a *pointwise* product, stated with an explicit lambda so that the function
appearing in the conclusion is syntactically the lambda form (the `Pi` instances of `ℂ → ℂ`
otherwise get in the way of rewriting). -/
private lemma hasDerivAt_fun_mul (f g : ℂ → ℂ) (x : ℂ) (f' g' : ℂ) (hf : HasDerivAt f f' x)
    (hg : HasDerivAt g g' x) :
    HasDerivAt (fun w => f w * g w) (f' * g x + f x * g') x := by
  have h := hf.mul hg
  have hfun : (f * g) = fun w => f w * g w := rfl
  rw [hfun] at h
  exact h

/-- `HasDerivAt` for a *pointwise* sum, stated with an explicit lambda (see
`hasDerivAt_fun_mul`). -/
private lemma hasDerivAt_fun_add (f g : ℂ → ℂ) (x : ℂ) (f' g' : ℂ) (hf : HasDerivAt f f' x)
    (hg : HasDerivAt g g' x) :
    HasDerivAt (fun w => f w + g w) (f' + g') x := by
  have h := hf.add hg
  have hfun : (f + g) = fun w => f w + g w := rfl
  rw [hfun] at h
  exact h

theorem deriv_Pfun_local (a b : ℚ) (ra rb rab r0 : ℤ) (κ : ℂ) (y1 hh : ℂ → ℂ) {δ : ℝ}
    (hy1 : DifferentiableOn ℂ y1 (Metric.ball ((Work.C17.xs (a : ℝ) (b : ℝ) : ℝ) : ℂ) δ))
    (hhh : DifferentiableOn ℂ hh (Metric.ball ((Work.C17.xs (a : ℝ) (b : ℝ) : ℝ) : ℂ) δ))
    (hloc : ∀ z ∈ Metric.ball ((Work.C17.xs (a : ℝ) (b : ℝ) : ℝ) : ℂ) δ ∩ Metric.ball (0 : ℂ) (Work.C17.xs (a : ℝ) (b : ℝ)),
      Work.C17.Pfun a b ra rb rab r0 z
        = κ * y1 z * Complex.log (((Work.C17.xs (a : ℝ) (b : ℝ) : ℝ) : ℂ) - z) + hh z) :
    ∀ z ∈ Metric.ball ((Work.C17.xs (a : ℝ) (b : ℝ) : ℝ) : ℂ) δ ∩ Metric.ball (0 : ℂ) (Work.C17.xs (a : ℝ) (b : ℝ)),
      deriv (Work.C17.Pfun a b ra rb rab r0) z
        = κ * (deriv y1 z * Complex.log (((Work.C17.xs (a : ℝ) (b : ℝ) : ℝ) : ℂ) - z)
            - y1 z * (((Work.C17.xs (a : ℝ) (b : ℝ) : ℝ) : ℂ) - z)⁻¹) + deriv hh z := by
  set C : ℂ := ((Work.C17.xs (a : ℝ) (b : ℝ) : ℝ) : ℂ) with hC
  have hxrC : C.re = Work.C17.xs (a : ℝ) (b : ℝ) := by
    rw [hC]; simp
  intro z hz
  obtain ⟨hz1, hz2⟩ := hz
  -- `z` lies in the disc of radius `x_s` around the origin, so `x_s - z` is off the branch cut.
  have hnorm : ‖z‖ < Work.C17.xs (a : ℝ) (b : ℝ) := by
    rw [Metric.mem_ball, dist_zero_right] at hz2
    exact hz2
  have hslit : C - z ∈ Complex.slitPlane := by
    rw [Complex.slitPlane]
    left
    rw [Complex.sub_re, hxrC]
    have := Complex.re_le_norm z
    linarith
  -- differentiability of `y₁` and `hh` at `z`, from the local hypotheses.
  have hz1' : z ∈ Metric.ball ((Work.C17.xs (a : ℝ) (b : ℝ) : ℝ) : ℂ) δ := by
    simpa only [hC] using hz1
  have hy1at : HasDerivAt y1 (deriv y1 z) z :=
    hy1.hasDerivAt (Metric.isOpen_ball.mem_nhds hz1')
  have hhhat : HasDerivAt hh (deriv hh z) z :=
    hhh.hasDerivAt (Metric.isOpen_ball.mem_nhds hz1')
  -- `deriv` only sees the germ: replace `Pfun` by its local expression.
  have heq : Work.C17.Pfun a b ra rb rab r0 =ᶠ[nhds z]
      (fun w : ℂ => κ * y1 w * Complex.log (C - w) + hh w) := by
    refine Filter.eventuallyEq_of_mem
      (s := Metric.ball C δ ∩ Metric.ball (0 : ℂ) (Work.C17.xs (a : ℝ) (b : ℝ))) ?_ ?_
    · exact (Metric.isOpen_ball.inter Metric.isOpen_ball).mem_nhds ⟨hz1, hz2⟩
    · intro w hw
      obtain ⟨hw1, hw2⟩ := hw
      have hw1' : w ∈ Metric.ball ((Work.C17.xs (a : ℝ) (b : ℝ) : ℝ) : ℂ) δ := by
        simpa only [hC] using hw1
      simpa only [← hC] using hloc w ⟨hw1', hw2⟩
  -- derivative of the logarithm term
  have hlogd : HasDerivAt (fun w : ℂ => Complex.log (C - w)) (-((C - z)⁻¹)) z := by
    have hlin : HasDerivAt (fun w : ℂ => C - w) (-1) z := by
      simpa using (hasDerivAt_id z).const_sub C
    have hlc := (Complex.hasDerivAt_log hslit).comp z hlin
    have hfun : (Complex.log ∘ fun w : ℂ => C - w) = fun w : ℂ => Complex.log (C - w) := rfl
    rw [hfun] at hlc
    simpa only [div_eq_mul_inv, mul_neg, mul_one] using hlc
  have hκy : HasDerivAt (fun w : ℂ => κ * y1 w) (κ * deriv y1 z) z := hy1at.const_mul κ
  have hgd := hasDerivAt_fun_mul (fun w : ℂ => κ * y1 w) (fun w : ℂ => Complex.log (C - w)) z
    (κ * deriv y1 z) (-((C - z)⁻¹)) hκy hlogd
  have hV : (κ * deriv y1 z) * Complex.log (C - z) + (κ * y1 z) * (-((C - z)⁻¹)) + deriv hh z
      = κ * (deriv y1 z * Complex.log (C - z) - y1 z * (C - z)⁻¹) + deriv hh z := by ring
  have hmain := hasDerivAt_fun_add (fun w : ℂ => κ * y1 w * Complex.log (C - w)) hh z
    ((κ * deriv y1 z) * Complex.log (C - z) + (κ * y1 z) * (-((C - z)⁻¹))) (deriv hh z) hgd hhhat
  rw [hV] at hmain
  rw [heq.deriv_eq, hmain.deriv]

end Work.C17b
