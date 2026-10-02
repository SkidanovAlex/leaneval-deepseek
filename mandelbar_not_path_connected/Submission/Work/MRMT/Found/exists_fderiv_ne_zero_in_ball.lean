import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Found

/-- For a real number `r`, the norm of the corresponding complex number is `|r|`. -/
lemma norm_ofReal_complex (r : ℝ) : ‖((r : ℝ) : ℂ)‖ = |r| := by simp

/-- If an injective `C¹` map `F : ℂ → ℂ` had `fderiv ℝ F = 0` on a ball, then `F` would be
constant there, contradicting injectivity. Hence every ball around any point contains a
point where the Fréchet derivative is nonzero. -/
theorem exists_fderiv_ne_zero_in_ball {F : ℂ → ℂ} (hF : ContDiff ℝ 1 F)
    (hinj : Function.Injective F) (x : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ c ∈ Metric.ball x ε, fderiv ℝ F c ≠ 0 := by
  by_contra h
  simp only [not_exists, not_and, not_not] at h
  have hdiff : DifferentiableOn ℝ F (Metric.ball x ε) :=
    (hF.differentiable (by norm_num)).differentiableOn
  have hEq : Set.EqOn (fderiv ℝ F) 0 (Metric.ball x ε) := fun c hc => h c hc
  -- `x + ε/2` is a second point of the ball, distinct from `x`.
  have hne : x + (ε/2 : ℂ) ≠ x := by
    intro hc
    have h2 : ((ε/2 : ℝ) : ℂ) = 0 := by
      have := congrArg (fun z : ℂ => z - x) hc
      simpa using this
    have h3 : ε / 2 = 0 := by
      have := congrArg Complex.re h2
      simpa using this
    linarith
  have hb : x + (ε/2 : ℂ) ∈ Metric.ball x ε := by
    rw [Metric.mem_ball, Complex.dist_eq]
    have h1 : x + (ε/2 : ℂ) - x = (ε/2 : ℂ) := by ring
    rw [h1]
    have h2 : ‖(ε/2 : ℂ)‖ = ε/2 := by
      rw [show (ε/2 : ℂ) = ((ε/2 : ℝ) : ℂ) by push_cast; ring]
      rw [norm_ofReal_complex (ε/2), abs_of_pos (by linarith : (0:ℝ) < ε/2)]
    rw [h2]; linarith
  -- `F` is constant on the ball, so `F x = F (x + ε/2)`, contradicting injectivity.
  have hconst : F x = F (x + (ε/2 : ℂ)) :=
    (Metric.isOpen_ball).is_const_of_fderiv_eq_zero (convex_ball x ε).isPreconnected
      hdiff hEq (Metric.mem_ball_self hε) hb
  exact hne (hinj hconst).symm

end Work.MRMT.Found
