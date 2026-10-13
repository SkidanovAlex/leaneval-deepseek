import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.BSIdent.Defs
import Submission.Work.FTS.BSIdent.Cyl.DecayAux.Basic
import Submission.Work.FTS.BSIdent.Weyl.Levels.rho_mul_rpow_weight_le_two

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The constants of the sharp (`q = 1`) meridian decay estimate

The `Cyl.DecayAux` chain proves the decay of `merPsiT` with a profile rate `(π/2-θ)^q`, `q > 2`,
and needs `3 ≤ p·λ`.  The sharp version needed by the reconstruction (`Weyl.Levels`) has the
profile rate with `q = 1` (the weight `π/2 - θ` in the leading order only, the `θ`-derivative
losing that weight entirely) and only `2 ≤ p·λ`.  The two total constants of that estimate live
here so that the several files producing it agree on their values.
-/

noncomputable section

open scoped Topology

namespace Work.FTS.BSIdent.Weyl.Levels

set_option autoImplicit false

/-- The constant in the `(1+ρ)^{-1}` bound for the two partial derivatives `∂_z ψ`, `∂_r ψ`
of the meridian stream function, in the sharp (`q = 1`) regime.  It is
`(2·(π/2) + p·(π/2) + 1)·|c|·C₀·(2·max 1 (b^λ))`: the three chain-rule terms contribute
`2·(π/2)`, `p·(π/2)` and `1` times the common factor `|c|·C₀·(ρ·(1+w)^{-λ})`, and the last is
bounded by `2·max 1 (b^λ)/(1+ρ)`. -/
noncomputable def decayKzrOne (p c C₀ lam b : ℝ) : ℝ :=
  (2 * (Real.pi / 2) + p * (Real.pi / 2) + 1) * (|c| * C₀ * (2 * max 1 (b ^ lam)))

/-- The constant in the `(1+ρ)^{-1}` bound for `ψ/r`, in the sharp (`q = 1`) regime:
`|c|·C₀·(π/2)·(2·max 1 (b^λ))`, the `π/2` coming from Jordan's inequality
`π/2 - θ ≤ (π/2)·cos θ = (π/2)·r/ρ`. -/
noncomputable def decayKqOne (c C₀ lam b : ℝ) : ℝ :=
  |c| * C₀ * (Real.pi / 2) * (2 * max 1 (b ^ lam))

theorem decayKzrOne_nonneg {p c C₀ lam b : ℝ} (hC₀ : 0 ≤ C₀) (hp : 0 ≤ p) :
    0 ≤ decayKzrOne p c C₀ lam b := by
  have h1 : (0 : ℝ) ≤ 2 * (Real.pi / 2) + p * (Real.pi / 2) + 1 := by
    have := mul_nonneg hp (by positivity : (0 : ℝ) ≤ Real.pi / 2)
    linarith [Real.pi_pos]
  have h2 : (0 : ℝ) ≤ 2 * max 1 (b ^ lam) :=
    mul_nonneg (by norm_num) (le_trans zero_le_one (le_max_left 1 (b ^ lam)))
  rw [decayKzrOne]
  exact mul_nonneg h1 (mul_nonneg (mul_nonneg (abs_nonneg c) hC₀) h2)

theorem decayKqOne_nonneg {c C₀ lam b : ℝ} (hC₀ : 0 ≤ C₀) : 0 ≤ decayKqOne c C₀ lam b := by
  have h2 : (0 : ℝ) ≤ 2 * max 1 (b ^ lam) :=
    mul_nonneg (by norm_num) (le_trans zero_le_one (le_max_left 1 (b ^ lam)))
  have h3 : (0 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  rw [decayKqOne]
  exact mul_nonneg (mul_nonneg (mul_nonneg (abs_nonneg c) hC₀) h3) h2

end Work.FTS.BSIdent.Weyl.Levels
