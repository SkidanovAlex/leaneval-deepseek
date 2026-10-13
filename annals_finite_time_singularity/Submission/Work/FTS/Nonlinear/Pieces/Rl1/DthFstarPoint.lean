import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Submission.Work.FTS.Nonlinear.FstarPkgAll
import Submission.Work.FTS.Nonlinear.FstarPkg.DthFstar_W
import Submission.Work.Spaces.Gamma_WlInf

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.Pieces.Rl1

/-- The `z`-decay of `D_θ F_*`: `|D_θ F_*(z,θ)| ≤ C α² z/(1+z)²` for `0 < α ≤ 1`, `z > 0`,
`θ ∈ Iθ`, with a universal constant.  Route: `FstarDthFactor α 0 0` (in
`Submission/Work/FTS/Nonlinear/FstarPkg/DthFstar_W.lean`) gives
`D_θ F_* = (2α/c(α))·hKer z·dthU^[1]Γ`; `dthU_Gam_le 1` gives `|D_θΓ| ≤ α·tBound 0 0·Γ`;
`Gam_bounds` gives `Γ ≤ 1`; `hKer z = z/(1+z)²`; `Fstar_coef_leD'` gives `|2α/c| ≤ 20α`, so
`C = 20·tBound 0 0` works. (This is the `k = 0` case of the proved `DthFstar_z_bound` with the
`hKer` factor kept instead of bounded by `1`.) -/
theorem DthFstarPoint : ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, 0 < α → α ≤ 1 →
    ∀ z : ℝ, 0 < z → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.Dth (Work.Construction.Fstar α) z θ| ≤ C * α ^ 2 * (z / (1 + z) ^ 2) := by
  -- The constant: `20·tBound 0 0` already works, `+ 1` only to be strictly positive.
  refine ⟨20 * Work.Spaces.tBound 0 0 + 1,
    by linarith [Work.Spaces.tBound_nonneg 0 0], ?_⟩
  intro α hα hα1 z hz θ hθ
  -- `FstarDthFactor α 0 0` factorizes `D_θ F_*` into radial part × angular part.
  have hfac := Work.FTS.Nonlinear.FstarPkg.DthAux.FstarDthFactor α 0 0 z θ
  simp only [Work.Spaces.pzIter_zero, Work.Spaces.DthIter_zero, Function.iterate_zero, id_eq]
    at hfac
  rw [hfac, abs_mul, abs_mul]
  -- `hKer z = z/(1+z)² ≥ 0`
  have hker_abs : |Work.Spaces.hKer z| = z / (1 + z) ^ 2 := by
    rw [Work.Spaces.hKer_apply]
    exact abs_of_nonneg (div_nonneg (le_of_lt hz) (by positivity))
  rw [hker_abs]
  have hcoef := Work.FTS.Nonlinear.FstarPkg.DthAux.Fstar_coef_leD' α hα hα1
  -- `|D_θΓ| ≤ α·tBound 0 0·Γ ≤ α·tBound 0 0`
  have hdth : |Work.Spaces.dthU^[1] (fun t => Work.Spaces.Gam α t) θ|
      ≤ α * Work.Spaces.tBound 0 0 := by
    have h := Work.Spaces.dthU_Gam_le 1 (by norm_num) α hα hα1 θ hθ
    have hG := (Work.Spaces.Gam_bounds α θ hα hθ).2
    have h1 : |Work.Spaces.dthU^[1] (fun t => Work.Spaces.Gam α t) θ|
        ≤ α * Work.Spaces.tBound 0 0 * Work.Spaces.Gam α θ := by simpa using h
    calc |Work.Spaces.dthU^[1] (fun t => Work.Spaces.Gam α t) θ|
        ≤ α * Work.Spaces.tBound 0 0 * Work.Spaces.Gam α θ := h1
      _ ≤ α * Work.Spaces.tBound 0 0 * 1 :=
          mul_le_mul_of_nonneg_left hG
            (mul_nonneg (le_of_lt hα) (Work.Spaces.tBound_nonneg 0 0))
      _ = α * Work.Spaces.tBound 0 0 := by ring
  have hzdiv : 0 ≤ z / (1 + z) ^ 2 := div_nonneg (le_of_lt hz) (by positivity)
  have hb : 0 ≤ (20 : ℝ) * α * (z / (1 + z) ^ 2) :=
    mul_nonneg (mul_nonneg (by norm_num) (le_of_lt hα)) hzdiv
  -- multiply the two bounds and collect `α²`; the `hKer` factor is kept.
  refine le_trans (mul_le_mul (mul_le_mul hcoef le_rfl hzdiv (by positivity)) hdth
    (abs_nonneg _) hb) ?_
  nlinarith [Work.Spaces.tBound_nonneg 0 0, sq_nonneg α, hzdiv, hα]

end Work.FTS.Nonlinear.Pieces.Rl1
