import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row15aux.Gam_deriv_bounds
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row15aux.Gam_deriv_low_left
import Submission.Work.FTS.Nonlinear.FstarPkg.Fstar_W
import Submission.Work.Construction.Basic
import Submission.Work.Spaces.c_bounds
import Submission.Work.Construction.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.Pieces.RNP.row15aux

/-- **Lower bound for `|∂_θ F_*|` near `θ = 0`.**  For `0 < α ≤ 1` and every `z > 0` there is
`c > 0` with `c·θ^{α/3-1} ≤ |∂_θ F_*(z,θ)|` for all `θ ∈ (0,π/6)`.

The profile is `F_*(z,θ) = α(Γ(θ)/c)·2z/(1+z)²`, so by `Work.Construction.pth_Fstar_eq`

  `∂_θF_*(z,θ) = α·(Γ'(θ)/c)·2z/(1+z)²`,

and every factor except `Γ'(θ)` is positive (for `z > 0` and `α > 0`, since `1/10 ≤ c(α)` by
`Work.Spaces.c_bounds`).  So it suffices to bound `|Γ'(θ)|` from below.  By
`Gam_deriv_low_left`, `|Γ'(θ)| ≥ (1/24)·α·(sin θ)^{α/3-1}` on `(0,π/6]`; and since
`sin θ ≤ θ` while the exponent `α/3 - 1 ≤ 0`, the monotonicity of `x ↦ x^{α/3-1}` on
`(0,∞)` gives `θ^{α/3-1} ≤ (sin θ)^{α/3-1}`. -/
theorem pth_Fstar_lower {α z : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hz : 0 < z) :
    ∃ c : ℝ, 0 < c ∧ ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 6),
      c * θ ^ (α / 3 - 1) ≤ |Work.Spaces.pth (Work.Construction.Fstar α) z θ| := by
  obtain ⟨c₀, hc₀pos, hc₀⟩ := Gam_deriv_low_left
  have hcb := Work.Spaces.c_bounds α hα hα1
  have hcpos : 0 < Work.Spaces.c α := by linarith [hcb.1]
  have hFpos : 0 < Work.FM.Fstar z := by
    rw [Work.FM.Fstar]
    positivity
  refine ⟨c₀ * α ^ 2 * Work.FM.Fstar z / Work.Spaces.c α, by positivity, ?_⟩
  intro θ hθ
  have hθ0 : 0 < θ := hθ.1
  have hθ6 : θ ≤ Real.pi / 6 := le_of_lt hθ.2
  have hsin : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith [hθ.2, Real.pi_pos])
  have hsinle : Real.sin θ ≤ θ := le_of_lt (Real.sin_lt hθ0)
  have hexp : α / 3 - 1 ≤ 0 := by linarith
  have hpow : θ ^ (α / 3 - 1) ≤ (Real.sin θ) ^ (α / 3 - 1) :=
    Real.rpow_le_rpow_of_nonpos hsin hsinle hexp
  have hGam := hc₀ α θ hα hα1 ⟨hθ0, hθ6⟩
  have hstep : c₀ * α * θ ^ (α / 3 - 1) ≤ |deriv (Work.Spaces.Gam α) θ| := by
    refine le_trans ?_ hGam
    exact mul_le_mul_of_nonneg_left hpow (by positivity)
  have hpth : Work.Spaces.pth (Work.Construction.Fstar α) z θ
      = α * (deriv (fun t : ℝ => Work.Spaces.Gam α t) θ / Work.Spaces.c α)
        * Work.FM.Fstar z := Work.Construction.pth_Fstar_eq hα
  have hfac : 0 ≤ α * Work.FM.Fstar z / Work.Spaces.c α := by positivity
  have habs : |Work.Spaces.pth (Work.Construction.Fstar α) z θ|
      = (α * Work.FM.Fstar z / Work.Spaces.c α)
        * |deriv (fun t : ℝ => Work.Spaces.Gam α t) θ| := by
    rw [hpth, abs_mul, abs_mul, abs_div, abs_of_pos hα, abs_of_pos hcpos, abs_of_pos hFpos]
    ring_nf
  rw [habs]
  calc c₀ * α ^ 2 * Work.FM.Fstar z / Work.Spaces.c α * θ ^ (α / 3 - 1)
      = (α * Work.FM.Fstar z / Work.Spaces.c α) * (c₀ * α * θ ^ (α / 3 - 1)) := by
        ring_nf
    _ ≤ (α * Work.FM.Fstar z / Work.Spaces.c α)
          * |deriv (fun t : ℝ => Work.Spaces.Gam α t) θ| :=
        mul_le_mul_of_nonneg_left hstep hfac

end Work.FTS.Nonlinear.Pieces.RNP.row15aux
