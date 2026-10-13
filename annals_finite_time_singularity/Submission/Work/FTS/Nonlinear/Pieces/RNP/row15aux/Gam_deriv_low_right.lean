import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.dthU_Gam

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# A lower bound for `|∂_θ Γ|` near `θ = π/2` (the right end of the angular interval)

With `Γ(θ) = (sin θ · cos²θ)^{α/3}` one has
`Γ = sin^{α/3}θ · cos^{2α/3}θ`, hence
`Γ'(θ) = (α/3) sin^{α/3-1}θ · cos^{2α/3-1}θ · (cos²θ - 2 sin²θ)`, and
`cos²θ - 2 sin²θ = -(3 sin²θ - 1) < 0` for `θ ≥ π/3`.

Therefore, for `0 < α ≤ 1` and `θ ∈ [π/3, π/2)`,
`|Γ'(θ)| = (α/3) · (3 sin²θ - 1) · sin^{α/3-1}θ · cos^{2α/3-1}θ`.

On this range `sin θ ∈ [√3/2, 1]`, so (the exponent `α/3 - 1` being `≤ 0`)
`sin^{α/3-1}θ ≥ 1`, while `3 sin²θ - 1 ≥ 5/4`.  Hence

`|Γ'(θ)| ≥ (5/12) · α · cos^{2α/3-1}θ`,

which is the statement below with `c = 5/12` (the `cos`-powers match *exactly*: the
exponent `2α/3 - 1` is precisely the one carried by both sides, which is what makes
the estimate uniform as `cos θ → 0`).
-/

namespace Work.FTS.Nonlinear.Pieces.RNP.row15aux

theorem Gam_deriv_low_right :
    ∃ c : ℝ, 0 < c ∧ ∀ (α θ : ℝ), 0 < α → α ≤ 1 →
      θ ∈ Set.Ico (Real.pi / 3) (Real.pi / 2) →
        c * α * (Real.cos θ) ^ (2 * α / 3 - 1) ≤ |deriv (Work.Spaces.Gam α) θ| := by
  refine ⟨5 / 12, by norm_num, fun α θ hα hα1 hθ => ?_⟩
  have hpi : 0 < Real.pi := Real.pi_pos
  have hθ3 : Real.pi / 3 ≤ θ := hθ.1
  have hθ2 : θ < Real.pi / 2 := hθ.2
  have hθpos : 0 < θ := by linarith
  have hsinpos : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθpos (by linarith)
  have hsinle1 : Real.sin θ ≤ 1 := Real.sin_le_one θ
  have hcospo : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith, hθ2⟩
  have hcosnn : 0 ≤ Real.cos θ := le_of_lt hcospo
  -- `sin θ ≥ sin(π/3) = √3/2` on `[π/3, π/2]`
  have hsin_ge : Real.sin (Real.pi / 3) ≤ Real.sin θ :=
    Real.monotoneOn_sin ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ hθ3
  have hsin2 : (3 : ℝ) / 4 ≤ Real.sin θ ^ 2 := by
    have h1 : Real.sin θ ≥ √3 / 2 := by rw [← Real.sin_pi_div_three]; exact hsin_ge
    have h2 := pow_le_pow_left₀ (show (0 : ℝ) ≤ √3 / 2 by positivity) h1 2
    have h3 : (√3 / 2 : ℝ) ^ 2 = 3 / 4 := by
      rw [div_pow, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
      norm_num
    linarith
  have h3sin : (5 : ℝ) / 4 ≤ 3 * Real.sin θ ^ 2 - 1 := by linarith
  -- the derivative of `Γ`, via the chain rule for `x ↦ x^{α/3}` on the positive inner function
  have hGpos : 0 < Real.sin θ * Real.cos θ ^ 2 := by positivity
  have hprod : HasDerivAt (fun t => Real.sin t * Real.cos t ^ 2)
      (Real.cos θ * Real.cos θ ^ 2
        + Real.sin θ * (2 * Real.cos θ ^ (2 - 1) * (-Real.sin θ))) θ :=
    (Real.hasDerivAt_sin θ).mul ((Real.hasDerivAt_cos θ).pow 2)
  have hrpow := hprod.rpow_const (p := α / 3) (Or.inl (ne_of_gt hGpos))
  have hderiv : deriv (Work.Spaces.Gam α) θ
      = (Real.cos θ * Real.cos θ ^ 2
          + Real.sin θ * (2 * Real.cos θ ^ (2 - 1) * (-Real.sin θ))) * (α / 3)
        * (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3 - 1) := hrpow.deriv
  have hfd : Real.cos θ * Real.cos θ ^ 2
        + Real.sin θ * (2 * Real.cos θ ^ (2 - 1) * (-Real.sin θ))
      = Real.cos θ * (Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2) := by
    norm_num
    ring
  have hneg : Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2 = -(3 * Real.sin θ ^ 2 - 1) := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  have hkey : deriv (Work.Spaces.Gam α) θ
      = - ((α / 3) * (3 * Real.sin θ ^ 2 - 1) * (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3 - 1)
          * Real.cos θ) := by
    rw [hderiv, hfd, hneg]
    ring
  have hvalpos : 0 < (α / 3) * (3 * Real.sin θ ^ 2 - 1)
      * (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3 - 1) * Real.cos θ := by
    have h1 : 0 < 3 * Real.sin θ ^ 2 - 1 := by linarith
    have h2 : 0 < (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3 - 1) := Real.rpow_pos_of_pos hGpos _
    have h3 : 0 < α / 3 := by linarith
    exact mul_pos (mul_pos (mul_pos h3 h1) h2) hcospo
  have habs : |deriv (Work.Spaces.Gam α) θ|
      = (α / 3) * (3 * Real.sin θ ^ 2 - 1) * (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3 - 1)
          * Real.cos θ := by
    rw [hkey, abs_neg, abs_of_pos hvalpos]
  rw [habs]
  -- `(cos²θ)^{α/3-1} = cos^{2(α/3-1)}θ`
  have hcos2p : (Real.cos θ ^ 2 : ℝ) ^ (α / 3 - 1) = Real.cos θ ^ (2 * (α / 3 - 1)) := by
    rw [← Real.rpow_two (Real.cos θ), ← Real.rpow_mul hcosnn 2 (α / 3 - 1)]
  have hle' : Real.sin θ * Real.cos θ ^ 2 ≤ Real.cos θ ^ 2 := by
    nlinarith [hsinle1, sq_nonneg (Real.cos θ), hcosnn]
  -- since `sin θ ≤ 1` and `α/3 - 1 ≤ 0`, `(cos²θ)^{α/3-1} ≤ (sin θ cos²θ)^{α/3-1}`
  have hstep1 : Real.cos θ ^ (2 * (α / 3 - 1)) ≤ (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3 - 1) := by
    have h := Real.rpow_le_rpow_of_nonpos hGpos hle' (show α / 3 - 1 ≤ 0 by linarith)
    rwa [hcos2p] at h
  -- `cos^{2(α/3-1)}θ · cos θ = cos^{2α/3-1}θ`
  have hB : Real.cos θ ^ (2 * (α / 3 - 1)) * Real.cos θ = Real.cos θ ^ (2 * α / 3 - 1) := by
    have h1 : Real.cos θ ^ (2 * (α / 3 - 1)) * Real.cos θ ^ (1 : ℝ)
        = Real.cos θ ^ (2 * α / 3 - 1) := by
      rw [← Real.rpow_add hcospo]
      congr 1
      ring
    simpa using h1
  have hstep2 : Real.cos θ ^ (2 * α / 3 - 1)
      ≤ (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3 - 1) * Real.cos θ := by
    rw [← hB]
    exact mul_le_mul_of_nonneg_right hstep1 hcosnn
  have hck : 0 ≤ Real.cos θ ^ (2 * α / 3 - 1) := Real.rpow_nonneg hcosnn _
  have hcoef : (5 / 12) * α ≤ (α / 3) * (3 * Real.sin θ ^ 2 - 1) := by nlinarith [hα, h3sin]
  have hC : 0 ≤ (α / 3) * (3 * Real.sin θ ^ 2 - 1) := by linarith
  calc (5 / 12) * α * Real.cos θ ^ (2 * α / 3 - 1)
      ≤ ((α / 3) * (3 * Real.sin θ ^ 2 - 1)) * Real.cos θ ^ (2 * α / 3 - 1) :=
        mul_le_mul_of_nonneg_right hcoef hck
    _ ≤ ((α / 3) * (3 * Real.sin θ ^ 2 - 1))
          * ((Real.sin θ * Real.cos θ ^ 2) ^ (α / 3 - 1) * Real.cos θ) :=
        mul_le_mul_of_nonneg_left hstep2 hC
    _ = (α / 3) * (3 * Real.sin θ ^ 2 - 1) * (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3 - 1)
          * Real.cos θ := by ring

end Work.FTS.Nonlinear.Pieces.RNP.row15aux
