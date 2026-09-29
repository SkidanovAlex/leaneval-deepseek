import Mathlib
import Submission.Work.APsi.defs
import Submission.Work.APsi.lune_facts

/-!
# Area `Ψ_A`: the derivative of `lune c` does not vanish on the open unit disc

For `c > 1` the lune map `lune c` is a conformal isomorphism of the open unit disc onto the
lune `L(c)` (Calegari--Dimitrov--Tang, arXiv:2408.15403): it is the inverse of the degree-two
rational map `luneF c w = w(B + Cw)/(C + Bw)`, `B = 1 + c²`, `C = c² - 1`.  Hence its derivative
is nowhere zero on the disc.

The proof is purely algebraic: `luneF c ∘ lune c = id` (`luneF_lune`), so differentiating the
composition at any `z` in the disc (where `lune c` is holomorphic and `luneF c` is differentiable
at `lune c z`, the denominator `C + B·lune c z` being nonzero) gives
`deriv (luneF c) (lune c z) * deriv (lune c) z = 1`, whence `deriv (lune c) z ≠ 0`.
-/

namespace Work.APsi

open Submission.CDTPlan Metric

noncomputable section

/-- `luneF c` is differentiable at `lune c z` for every `z`: it is a quotient of polynomials and
the denominator `luneC c + luneB c * lune c z` is nonzero (`lune_pole_ne`). -/
theorem differentiableAt_luneF_lune (c : ℝ) (hc : 1 < c) (z : ℂ) :
    DifferentiableAt ℂ (luneF c) (lune c z) := by
  have hne := lune_pole_ne c hc z
  have hnum : DifferentiableAt ℂ (fun w : ℂ => w * (luneB c + luneC c * w)) (lune c z) := by
    fun_prop
  have hden : DifferentiableAt ℂ (fun w : ℂ => luneC c + luneB c * w) (lune c z) := by
    fun_prop
  have h : luneF c = fun w : ℂ => w * (luneB c + luneC c * w) / (luneC c + luneB c * w) := rfl
  rw [h]
  exact hnum.div hden hne

/-- The derivative of `lune c` is nowhere zero on the open unit disc. -/
theorem deriv_lune_ne_zero (c : ℝ) (hc : 1 < c) :
    ∀ z : ℂ, ‖z‖ < 1 → deriv (Submission.CDTPlan.lune c) z ≠ 0 := by
  intro z hz
  have hzball : z ∈ ball (0 : ℂ) 1 := by
    rw [Metric.mem_ball, dist_zero_right]
    exact hz
  have hdiffz : DifferentiableAt ℂ (lune c) z :=
    (lune_differentiableOn_ball c hc).differentiableAt (isOpen_ball.mem_nhds hzball)
  have hdiffF : DifferentiableAt ℂ (luneF c) (lune c z) := differentiableAt_luneF_lune c hc z
  have hcomp : (luneF c) ∘ (lune c) = id := funext fun w => luneF_lune c hc w
  have h1 : deriv (luneF c) (lune c z) * deriv (lune c) z = 1 := by
    rw [← deriv_comp z hdiffF hdiffz, hcomp, deriv_id]
  intro hzero
  rw [hzero, mul_zero] at h1
  exact one_ne_zero h1.symm

end

end Work.APsi
