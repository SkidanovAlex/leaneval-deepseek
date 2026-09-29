import Mathlib
import Submission.CDTPlan.Interfaces
import Submission.Work.CPsi.psiC_base
import Submission.Work.CPsi.psiC_continuous
import Submission.Work.CPsi.psiC_differentiable
import Submission.Work.CPsi.psiC_deriv_zero
import Submission.Work.CPsi.lune_norm_lt_one

/-! Guidance from the project lead (the requester):

# Area PsiC — analytic facts on ψ_C (`Submission.CDTPlan.PsiCFacts`)

ψ_C(z) = −(3/4)·lune(23/10, z), lune(c,z) = (z(1+c²) − 1 − c² + √R(z))/(2(c²−1)),
R(z) = (1+c²)²(1+z)² − 16c²z, principal √ (`(·) ^ (1/2 : ℂ)`).
- Branch: R(z) ∉ (−∞,0] for |z| < 1 (if R(z) = −s with s ≥ 0 then z is a root of
  A z² + (2A−16c²) z + (A+s) = 0, A = (1+c²)²; for c = 23/10 the discriminant is negative, roots are
  conjugate with |z|² = (A+s)/A ≥ 1). So √R is holomorphic on the open disc (`Complex.cpow`
  differentiable on the slit plane) and continuous on the closed disc (R vanishes only at the two
  circle points where it is 0, and cpow (1/2) is continuous at 0 — check `continuousAt_cpow_const`
  hypotheses; at 0 use |w^{1/2}| = |w|^{1/2}).
- ψ_C(0) = 0 (√R(0) = 1+c²); lune(c,·)'(0) = (c²−1)/(c²+1) (conformal radius of the lune, paper eq.
  firstgobblesize) = 429/629 for c = 23/10, so ψ_C'(0) = −(3/4)(429/629) = −1287/2516 (compute the
  derivative of the explicit formula at 0; numerically −0.5115262).
- |ψ_C(z)| ≤ 3/4 on the closed disc: lune(c,·) maps the disc into the closed unit disc (it is the
  inverse of the Möbius-type map f(w) = w((c²+1)+(c²−1)w)/((c²−1)+(c²+1)w) of the lune onto the disc;
  equivalently prove |lune(c,z)| ≤ 1 directly: lune(c,z) = w is a root of
  (c²−1)w² … — find the quadratic w satisfies (f(w) = z) and use that f maps |w| ≥ 1 (outside the
  lune complement) to |f(w)| ≥ 1). Choose whichever proof is shorter; a numerical certificate is NOT
  acceptable here (the statement is for all z).
- ψ_C(z) = 0 ⇒ z = 0: from f(lune(c,z)) = z and f(0) = 0.

# How it is proved here

The elementary algebra of the lune map is in `Submission.Work.CPsi.psiC_base`: with
`B = 1 + c² = 629/100`, `C = c² - 1 = 429/100` and `R(z) = B²(1+z)² - 16c²z = B²(z²-2αz+1)`
(`1 - α² = 4C²(B²-C²)/B⁴ > 0`), the lune map `w = lune (23/10) z` satisfies the quadratic relation
`C w² + B(1-z) w - C z = 0`, whence `f w = z` for *every* `z`, and `‖f w‖ = 1` for `‖w‖ = 1`.
The baseline/negativity analysis (if `R z = -s`, `s ≥ 0`, then `‖z‖² = 1 + s/B² ≥ 1`) places `R`
outside the branch cut on the closed disc.

On top of that base module, four independent analytic pieces were established in parallel:
`psiC_continuous` (continuity on the closed disc), `psiC_differentiable` (holomorphy on the open
disc), `psiC_deriv_zero` (`ψ_C'(0) = -1287/2516`) and `lune_norm_lt_one` (the lune map sends the
open disc strictly into itself).  This file assembles them:

* the closed-disc bound `‖lune‖ ≤ 1` follows by closure, since `z ↦ ‖lune z‖` is continuous on the
  closed disc and `< 1` on the dense open disc, which gives `‖ψ_C z‖ ≤ 3/4`;
* `ψ_C z = 0 ⇒ z = 0` is immediate from `f (lune z) = z` and `f 0 = 0`.
-/

namespace Work.CPsi

open Submission.CDTPlan Complex Metric
open scoped ComplexConjugate

noncomputable section

/-- `lune (23/10)` is continuous on the closed unit disc (obtained from `psiC_continuous`
by rescaling). -/
theorem lune_continuousOn_closedBall :
    ContinuousOn (fun z : ℂ => lune (23 / 10) z) (closedBall (0 : ℂ) 1) := by
  have h : (fun z : ℂ => lune (23 / 10) z) = fun z => -(4 / 3 : ℂ) * psiC z := by
    funext z; simp only [psiC]; ring
  rw [h]
  exact psiC_continuous.const_mul _

theorem norm_lt_one_of_mem_ball {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) : ‖z‖ < 1 := by
  simpa only [Metric.mem_ball, dist_zero_right] using hz

theorem norm_le_one_of_mem_closedBall {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) 1) : ‖z‖ ≤ 1 := by
  simpa only [Metric.mem_closedBall, dist_zero_right] using hz

/-- `ψ_C 0 = 0`. -/
theorem psiC_zero : psiC 0 = 0 := by
  have h : lune (23 / 10) 0 = gobL 0 := lune_eq 0
  rw [psiC, h, gobL_zero]
  ring

/-- `ψ_C` has the single zero `0` (inside the closed disc, and in fact everywhere). -/
theorem psiC_eq_zero {z : ℂ} (h : psiC z = 0) : z = 0 := by
  have h1 : gobL z = 0 := by
    have h' : -(3 / 4 : ℂ) * gobL z = 0 := by simpa only [psiC, lune_eq] using h
    exact (mul_eq_zero.mp h').resolve_left (by norm_num)
  have h2 : gobF (gobL z) = gobF 0 := by rw [h1]
  rw [gobF_gobL, gobF_zero] at h2
  exact h2

/-- The lune map sends the closed unit disc into the closed unit disc: `< 1` on the (dense) open
disc and continuity on the closed disc. -/
theorem lune_norm_le_one {z : ℂ} (hz : ‖z‖ ≤ 1) : ‖lune (23 / 10) z‖ ≤ 1 := by
  have hcont : ContinuousOn (fun w : ℂ => ‖lune (23 / 10) w‖) (closedBall (0 : ℂ) 1) :=
    lune_continuousOn_closedBall.norm
  have hcl : IsClosed (closedBall (0 : ℂ) 1 ∩ {w : ℂ | ‖lune (23 / 10) w‖ ≤ 1}) :=
    hcont.preimage_isClosed_of_isClosed Metric.isClosed_closedBall isClosed_Iic
  have h1 : ball (0 : ℂ) 1 ⊆ closedBall (0 : ℂ) 1 ∩ {w : ℂ | ‖lune (23 / 10) w‖ ≤ 1} :=
    fun w hw =>
      ⟨ball_subset_closedBall hw, le_of_lt (lune_norm_lt_one w (norm_lt_one_of_mem_ball hw))⟩
  have h2 : closure (ball (0 : ℂ) 1) ⊆ closedBall (0 : ℂ) 1 ∩ {w : ℂ | ‖lune (23 / 10) w‖ ≤ 1} :=
    (closure_mono h1).trans (le_of_eq hcl.closure_eq)
  rw [closure_ball (0 : ℂ) one_ne_zero] at h2
  exact (h2 (by simpa only [Metric.mem_closedBall, dist_zero_right] using hz)).2

/-- `‖ψ_C‖ ≤ 3/4` on the closed unit disc. -/
theorem psiC_norm_le {z : ℂ} (hz : ‖z‖ ≤ 1) : ‖psiC z‖ ≤ 3 / 4 := by
  have h := lune_norm_le_one hz
  rw [psiC, norm_mul, norm_neg]
  have h34 : ‖(3 / 4 : ℂ)‖ = 3 / 4 := by norm_num
  rw [h34]
  linarith

end

theorem psiC_facts : PsiCFacts := by
  refine ⟨psiC_continuous, psiC_differentiable, psiC_zero, psiC_deriv_zero, ?_, ?_⟩
  · intro z hz
    exact psiC_norm_le (norm_le_one_of_mem_closedBall hz)
  · intro z _ hz
    exact psiC_eq_zero hz

end Work.CPsi
