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

namespace Work.FTS.Nonlinear.Pieces.RNP.row15aux

/-- On the left half of the angular interval, `Γ = (sin θ cos²θ)^{α/3}` has a derivative
bounded below by a constant times `α (sin θ)^{α/3 - 1}`.

Indeed, on `(0, π/6]` one has `sin θ ≤ 1/2` and `cos θ ≥ 1/2`, hence
`d/dθ (sin θ cos²θ) = cos θ (1 - 3 sin²θ) ≥ 1/8`, while
`(sin θ cos²θ)^{α/3 - 1} = (sin θ)^{α/3 - 1} (cos²θ)^{α/3 - 1} ≥ (sin θ)^{α/3 - 1}`
because `cos²θ ≤ 1` and `α/3 - 1 ≤ 0`.  The constant `1/24 = (1/8)·(1/3)` is therefore
admissible. -/
theorem Gam_deriv_low_left :
    ∃ c : ℝ, 0 < c ∧ ∀ (α θ : ℝ), 0 < α → α ≤ 1 →
      θ ∈ Set.Ioc (0 : ℝ) (Real.pi / 6) →
        c * α * (Real.sin θ) ^ (α / 3 - 1) ≤ |deriv (Work.Spaces.Gam α) θ| := by
  refine ⟨1 / 24, by norm_num, ?_⟩
  intro α θ hα hα1 hθ
  have hθ0 : 0 < θ := hθ.1
  have hθ6 : θ ≤ Real.pi / 6 := hθ.2
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith [Real.pi_pos])
  -- `sin θ ≤ 1/2`, from monotonicity of `sin` on `[-π/2, π/2]`
  have hsin_half : Real.sin θ ≤ 1 / 2 := by
    rw [← Real.sin_pi_div_six]
    exact (Real.strictMonoOn_sin.le_iff_le (by constructor <;> linarith [Real.pi_pos])
      (by constructor <;> linarith [Real.pi_pos])).mpr hθ6
  -- `cos θ ≥ 1/2`, from antitonicity of `cos` on `[0, π]`
  have hcos_ge : 1 / 2 ≤ Real.cos θ := by
    have h1 : Real.cos (Real.pi / 6) ≤ Real.cos θ :=
      Real.cos_le_cos_of_nonneg_of_le_pi (le_of_lt hθ0) (by linarith [Real.pi_pos]) hθ6
    have h2 : (1 : ℝ) / 2 ≤ Real.cos (Real.pi / 6) := by
      rw [Real.cos_pi_div_six]
      have h3 : (1 : ℝ) ≤ Real.sqrt 3 := by
        rw [← Real.sqrt_one]
        exact Real.sqrt_le_sqrt (by norm_num)
      linarith
    linarith
  have hcos_pos : 0 < Real.cos θ := lt_of_lt_of_le (by norm_num) hcos_ge
  have hsq : Real.cos θ ^ 2 ≤ 1 := by nlinarith [Real.cos_le_one θ, hcos_ge]
  have hsin2_le : Real.sin θ ^ 2 ≤ 1 / 4 := by
    calc Real.sin θ ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := pow_le_pow_left₀ (le_of_lt hsin) hsin_half 2
      _ = 1 / 4 := by norm_num
  have h1m3 : 1 / 4 ≤ 1 - 3 * Real.sin θ ^ 2 := by nlinarith
  -- the derivative of `θ ↦ sin θ · cos²θ`
  have hprod : HasDerivAt (fun t : ℝ => Real.sin t * Real.cos t ^ 2)
      (Real.cos θ * Real.cos θ ^ 2
        + Real.sin θ * (2 * Real.cos θ ^ (2 - 1) * (-Real.sin θ))) θ :=
    (Real.hasDerivAt_sin θ).mul ((Real.hasDerivAt_cos θ).pow 2)
  have hG : 0 < Real.sin θ * Real.cos θ ^ 2 := mul_pos hsin (pow_pos hcos_pos 2)
  have hrpow := hprod.rpow_const (p := α / 3) (Or.inl (ne_of_gt hG))
  have hderiv : deriv (fun t : ℝ => Work.Spaces.Gam α t) θ
      = (Real.cos θ * Real.cos θ ^ 2
          + Real.sin θ * (2 * Real.cos θ ^ (2 - 1) * (-Real.sin θ)))
        * (α / 3) * (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3 - 1) := hrpow.deriv
  -- the differential factor equals `cos θ (1 - 3 sin²θ)`
  have hbracket : Real.cos θ * Real.cos θ ^ 2
        + Real.sin θ * (2 * Real.cos θ ^ (2 - 1) * (-Real.sin θ))
      = Real.cos θ * (Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2) := by
    norm_num
    ring
  have hbracket' : Real.cos θ * (Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2)
      = Real.cos θ * (1 - 3 * Real.sin θ ^ 2) := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  have hf' : (1 : ℝ) / 8 ≤ Real.cos θ * (1 - 3 * Real.sin θ ^ 2) := by
    have h := mul_le_mul hcos_ge h1m3 (by norm_num) (le_trans (by norm_num) hcos_ge)
    norm_num at h
    exact h
  have hf'0 : (0 : ℝ) ≤ Real.cos θ * (1 - 3 * Real.sin θ ^ 2) := le_trans (by norm_num) hf'
  have hB : (0 : ℝ) ≤ α / 3 := by linarith
  have hexp : α / 3 - 1 ≤ 0 := by linarith
  -- the `cos`-factor of the split power is at least `1`
  have hcosfac : 1 ≤ (Real.cos θ ^ 2) ^ (α / 3 - 1) := by
    have h := Real.rpow_le_rpow_of_nonpos (x := Real.cos θ ^ 2) (y := 1)
      (by positivity) hsq hexp
    rwa [Real.one_rpow] at h
  have hsinp : 0 ≤ (Real.sin θ) ^ (α / 3 - 1) := Real.rpow_nonneg (le_of_lt hsin) _
  have hsplit : (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3 - 1)
      = (Real.sin θ) ^ (α / 3 - 1) * (Real.cos θ ^ 2) ^ (α / 3 - 1) :=
    Real.mul_rpow (le_of_lt hsin) (by positivity)
  have hC : (Real.sin θ) ^ (α / 3 - 1) ≤ (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3 - 1) := by
    rw [hsplit]
    calc (Real.sin θ) ^ (α / 3 - 1)
        = (Real.sin θ) ^ (α / 3 - 1) * 1 := by ring
      _ ≤ (Real.sin θ) ^ (α / 3 - 1) * (Real.cos θ ^ 2) ^ (α / 3 - 1) :=
          mul_le_mul_of_nonneg_left hcosfac hsinp
  have hle : (1 / 24) * α * (Real.sin θ) ^ (α / 3 - 1) ≤ deriv (Work.Spaces.Gam α) θ := by
    rw [hderiv, hbracket, hbracket']
    have h24 : (1 / 24 : ℝ) * α = (1 / 8) * (α / 3) := by ring
    rw [h24]
    calc (1 / 8) * (α / 3) * (Real.sin θ) ^ (α / 3 - 1)
        ≤ (Real.cos θ * (1 - 3 * Real.sin θ ^ 2)) * (α / 3)
            * (Real.sin θ) ^ (α / 3 - 1) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hf' hB) hsinp
      _ ≤ (Real.cos θ * (1 - 3 * Real.sin θ ^ 2)) * (α / 3)
            * (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3 - 1) :=
          mul_le_mul_of_nonneg_left hC (mul_nonneg hf'0 hB)
  have hdnn : 0 ≤ deriv (Work.Spaces.Gam α) θ := le_trans (by positivity) hle
  rwa [abs_of_nonneg hdnn]

end Work.FTS.Nonlinear.Pieces.RNP.row15aux
