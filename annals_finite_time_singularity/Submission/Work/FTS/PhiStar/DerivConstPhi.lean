import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.VocabO
import Submission.Work.FTS.PhiStar.Psi0Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.PhiStar.DerivConstPhi`

The angular model `ψ` (`L₀ψ = Γ̄`, encoded by `hode` below) makes the first integral of the
`Φ`-equation constant: with `v = ψ / sin 2θ` and `μ = sin²θ cos³θ`, the function

`θ ↦ μ(θ) v(θ) - G₀(θ)/2`

has vanishing derivative on `(0, π/2)`.  This is the elementary content behind
`PsiDivS2EqPfun` (where the constant is turned into a formula for `deriv v`).

The computation: `hode` reads `sin 2θ · v' = (6 sin²θ − 4 cos²θ) v − Γ̄`, hence

`(μ v)' = μ' v + μ v' = sinθ cos²θ · [ (2cos²θ − 3sin²θ) v + (3sin²θ − 2cos²θ) v ] + ½ sinθ cos²θ Γ̄`,

the bracket cancels identically, while `G₀' = − sinθ cos²θ Γ̄` supplies the other half.
-/

noncomputable section

open scoped Real ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar

set_option autoImplicit false

theorem DerivConstPhi {α : ℝ} (hα : 0 ≤ α) {ψ : ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n ψ (Set.Ioo 0 (Real.pi / 2)))
    (hode : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Real.sin (2 * θ) * deriv (fun t => deriv (fun θ' => ψ θ' / Real.sin (2 * θ')) t) θ
        = (6 * Real.sin θ ^ 2 - 4 * Real.cos θ ^ 2)
            * deriv (fun θ' => ψ θ' / Real.sin (2 * θ')) θ - Work.FTS.VocabO.GamBar α θ) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      deriv (fun t => Real.sin t ^ 2 * Real.cos t ^ 3
          * deriv (fun θ' => ψ θ' / Real.sin (2 * θ')) t - Work.FTS.PhiStar.Gzero α t / 2) θ = 0 := by
  intro θ hθ
  obtain ⟨hθ1, hθ2⟩ := hθ
  have hne : 2 * Real.sin θ * Real.cos θ ≠ 0 := by
    have h1 : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ1 (by linarith [hθ2, Real.pi_pos])
    have h2 : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ2⟩
    positivity
  -- name the divided function `u = ψ / sin 2θ`
  set u : ℝ → ℝ := fun t => ψ t / Real.sin (2 * t) with hu
  -- `u` is smooth on the open interval
  have husm : ∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo 0 (Real.pi / 2)) := by
    intro n
    rw [hu]
    refine (hsm n).div (by fun_prop) ?_
    intro t ht
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [ht.1])
      (by linarith [ht.2, Real.pi_pos]))
  -- hence `deriv u` is differentiable at `θ`
  have huAt : ContDiffAt ℝ 2 u θ :=
    (husm 2).contDiffAt (isOpen_Ioo.mem_nhds ⟨hθ1, hθ2⟩)
  have hu1 : ContDiffAt ℝ 1 (deriv u) θ := huAt.derivWithin (m := 1) (by norm_num)
  have hudiff : DifferentiableAt ℝ (deriv u) θ := hu1.differentiableAt_one
  -- the ODE, phrased in terms of `u`
  have hode_u : Real.sin (2 * θ) * deriv (deriv u) θ
      = (6 * Real.sin θ ^ 2 - 4 * Real.cos θ ^ 2) * deriv u θ
        - Work.FTS.VocabO.GamBar α θ := by
    rw [hu]
    exact hode θ ⟨hθ1, hθ2⟩
  -- the derivative of `μ = sin²θ cos³θ`
  have hsin_deriv : HasDerivAt (fun t : ℝ => Real.sin t ^ 2 * Real.cos t ^ 3)
      (2 * Real.sin θ * Real.cos θ ^ 4 - 3 * Real.sin θ ^ 3 * Real.cos θ ^ 2) θ := by
    have h1 : HasDerivAt (fun t : ℝ => Real.sin t ^ 2) (2 * Real.sin θ * Real.cos θ) θ := by
      have h := (Real.hasDerivAt_sin θ).pow 2
      rw [show ((fun t : ℝ => Real.sin t) ^ 2) = fun t : ℝ => Real.sin t ^ 2 from by
        funext t; rw [Pi.pow_apply]] at h
      simpa using h
    have h2 : HasDerivAt (fun t : ℝ => Real.cos t ^ 3)
        (3 * Real.cos θ ^ 2 * (-Real.sin θ)) θ := by
      have h := (Real.hasDerivAt_cos θ).pow 3
      rw [show ((fun t : ℝ => Real.cos t) ^ 3) = fun t : ℝ => Real.cos t ^ 3 from by
        funext t; rw [Pi.pow_apply]] at h
      simpa using h
    have h := h1.mul h2
    convert h using 1
    ring
  have hv : HasDerivAt (deriv u) (deriv (deriv u) θ) θ := hudiff.hasDerivAt
  have hprod : HasDerivAt (fun t : ℝ => Real.sin t ^ 2 * Real.cos t ^ 3 * deriv u t)
      ((2 * Real.sin θ * Real.cos θ ^ 4 - 3 * Real.sin θ ^ 3 * Real.cos θ ^ 2) * deriv u θ
        + (Real.sin θ ^ 2 * Real.cos θ ^ 3) * deriv (deriv u) θ) θ := hsin_deriv.mul hv
  have hG := hasDerivAt_Gzero α hα ⟨hθ1, hθ2⟩
  have hF : HasDerivAt (fun t : ℝ => Real.sin t ^ 2 * Real.cos t ^ 3 * deriv u t
        - Gzero α t / 2)
      ((2 * Real.sin θ * Real.cos θ ^ 4 - 3 * Real.sin θ ^ 3 * Real.cos θ ^ 2) * deriv u θ
        + (Real.sin θ ^ 2 * Real.cos θ ^ 3) * deriv (deriv u) θ
        - (-(Real.sin θ * Real.cos θ ^ 2 * Work.FTS.VocabO.GamBar α θ)) / 2) θ :=
    hprod.sub (hG.div_const 2)
  rw [hF.deriv]
  -- solve the ODE for the second derivative and substitute
  have hd2 : deriv (deriv u) θ = ((6 * Real.sin θ ^ 2 - 4 * Real.cos θ ^ 2) * deriv u θ
      - Work.FTS.VocabO.GamBar α θ) / (2 * Real.sin θ * Real.cos θ) := by
    rw [eq_div_iff hne, mul_comm, ← Real.sin_two_mul]
    exact hode_u
  rw [hd2]
  field_simp
  ring

end Work.FTS.PhiStar
