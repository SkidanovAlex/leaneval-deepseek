import Mathlib
import Submission.Work.GenShared.periods_defs
import Submission.Work.GenShared.riccati_aux

namespace Work.GenShared

open Complex Metric Work.GenShared

/-- The zero set of a nonzero polynomial over `ℂ` is finite. -/
lemma finite_setOf_poly_eval_eq_zero {p : Polynomial ℂ} (hp : p ≠ 0) :
    {z : ℂ | p.eval z = 0}.Finite := by
  simpa [Polynomial.IsRoot] using Polynomial.finite_setOfPred_isRoot hp

/-- Given `y1 : ℂ → ℂ` differentiable on the ball `ball x0 δ` and nonzero at some point of it, and
rational functions `a`, `b` with `b ≠ 0`, there is a point `z` of the ball at which `y1 z ≠ 0`,
`a` and `b` are regular (`Rreg`, i.e. their canonical denominators do not vanish) and the canonical
numerator of `b` does not vanish.  This is the "generic point" on which the Riccati computation of
`Work.GenShared.riccati_core` is performed. -/
theorem exists_good_point {x0 : ℂ} {δ : ℝ} {y1 : ℂ → ℂ}
    (hy1 : DifferentiableOn ℂ y1 (ball x0 δ)) (hy1ne : ∃ z ∈ ball x0 δ, y1 z ≠ 0)
    {a b : RatFunc ℂ} (hb : b ≠ 0) :
    ∃ z ∈ ball x0 δ, y1 z ≠ 0 ∧ Rreg a z ∧ Rreg b z ∧ b.num.eval z ≠ 0 := by
  -- a point of the ball at which `y1` does not vanish
  obtain ⟨z0, hz0, hy1z0⟩ := hy1ne
  have hd : dist x0 z0 < δ := by
    have h := hz0
    rw [Metric.mem_ball] at h
    rwa [dist_comm] at h
  -- by continuity, `y1` is nonzero on a whole ball around it
  have hcont : ContinuousAt y1 z0 :=
    hy1.continuousOn.continuousAt (Metric.isOpen_ball.mem_nhds hz0)
  obtain ⟨ε1, hε1pos, hε1sub⟩ :=
    Metric.mem_nhds_iff.mp (hcont.eventually_ne hy1z0)
  -- shrink it so that it stays inside `ball x0 δ`
  set ε := min ε1 (δ - dist x0 z0) with hεdef
  have hεpos : 0 < ε := lt_min hε1pos (sub_pos.mpr hd)
  have hεle1 : ε ≤ ε1 := min_le_left _ _
  have hεle2 : ε ≤ δ - dist x0 z0 := min_le_right _ _
  -- the bad set is finite: the poles of `a`, `b` and the zeros of `b.num`
  have hfinA : {z : ℂ | a.denom.eval z = 0}.Finite :=
    finite_setOf_poly_eval_eq_zero (RatFunc.denom_ne_zero a)
  have hfinB : {z : ℂ | b.denom.eval z = 0}.Finite :=
    finite_setOf_poly_eval_eq_zero (RatFunc.denom_ne_zero b)
  have hfinN : {z : ℂ | b.num.eval z = 0}.Finite :=
    finite_setOf_poly_eval_eq_zero (RatFunc.num_ne_zero hb)
  have hF : ({z : ℂ | a.denom.eval z = 0} ∪ {z : ℂ | b.denom.eval z = 0}
      ∪ {z : ℂ | b.num.eval z = 0}).Finite := (hfinA.union hfinB).union hfinN
  -- an infinite ball minus a finite set is nonempty
  obtain ⟨z, hz⟩ := ((ball_infinite z0 hεpos).sdiff hF).nonempty
  have hdist : dist z z0 < ε := by
    have h := hz.1
    rwa [Metric.mem_ball] at h
  have hdist' : dist z0 z < ε := by rwa [dist_comm] at hdist
  have hznot : z ∉ ({z : ℂ | a.denom.eval z = 0} ∪ {z : ℂ | b.denom.eval z = 0}
      ∪ {z : ℂ | b.num.eval z = 0}) := hz.2
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or] at hznot
  obtain ⟨⟨hna, hnb⟩, hnn⟩ := hznot
  refine ⟨z, ?_, ?_, ?_, ?_, ?_⟩
  · -- `z` lies in the original ball
    rw [Metric.mem_ball, dist_comm]
    have h1 : dist x0 z ≤ dist x0 z0 + dist z0 z := dist_triangle x0 z0 z
    linarith
  · -- `y1 z ≠ 0` by the choice of `ε1`
    have hb1 : z ∈ ball z0 ε1 := by
      rw [Metric.mem_ball, dist_comm]
      exact lt_of_lt_of_le hdist' hεle1
    exact hε1sub hb1
  · exact hna
  · exact hnb
  · exact hnn

end Work.GenShared
