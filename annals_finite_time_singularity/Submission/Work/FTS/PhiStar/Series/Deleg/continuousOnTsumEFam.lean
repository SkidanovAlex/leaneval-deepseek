import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.PhiStar.Gegenbauer.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.gC_ode

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Continuity of a series in the Dirichlet eigenbasis `eFam`

`eFam m θ = cos θ · C_{2m+1}^{(3/2)}(sin θ)` is a (trigonometric) polynomial in `θ`, hence
continuous.  If the coefficients `b m` satisfy the pointwise domination
`|b m · eFam m θ| ≤ u m` on the *whole* open interval `(0, π/2)` for a summable majorant `u`,
then the Weierstrass M-test gives uniform convergence of the series on `(0, π/2)`, and a uniform
limit of continuous functions is continuous there.  This is the content of `continuousOnTsumEFam`.
-/

namespace Work.FTS.PhiStar.Series.Deleg

open scoped Real

/-- `eFam m` is continuous: it is `cos θ` times the polynomial `gC (2m+1)` evaluated at `sin θ`. -/
lemma continuous_eFam_deleg (m : ℕ) :
    Continuous (Work.FTS.PhiStar.Gegenbauer.eFam m) :=
  Real.continuous_cos.mul
    ((Work.FTS.PhiStar.Gegenbauer.contDiff_gC (2 * m + 1)).continuous.comp Real.continuous_sin)

theorem continuousOnTsumEFam (b : ℕ → ℝ) (u : ℕ → ℝ) (hu : Summable u)
    (h : ∀ m : ℕ, ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      |b m * Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ u m) :
    ContinuousOn (fun θ : ℝ => ∑' m : ℕ, b m * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
  refine continuousOn_tsum (s := Set.Ioo 0 (Real.pi / 2))
    (f := fun m θ => b m * Work.FTS.PhiStar.Gegenbauer.eFam m θ) (u := u)
    (fun m => ?_) hu (fun m θ hθ => ?_)
  · exact (continuous_const.mul (continuous_eFam_deleg m)).continuousOn
  · rw [Real.norm_eq_abs]
    exact h m θ hθ

end Work.FTS.PhiStar.Series.Deleg
