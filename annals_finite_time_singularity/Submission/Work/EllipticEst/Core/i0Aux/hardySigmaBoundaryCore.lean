import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.EllipticEst.Core.i0Aux.InterpDefs
import Submission.Work.FTS.EllipticEst.H2W.AeW.cotFluxIdentity

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.Core.i0Aux

/-- `sin (2θ) > 0` for `θ ∈ (0, π/2)`. -/
private lemma sin_two_pos_of_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2])

/-- **Weighted Hardy inequality with boundary term, on a compact subinterval of `(0, π/2)`.**

For `f` of class `C¹` on the open interval `(0, π/2)` and `0 < a < b < π/2`,

```
∫_a^b sin(2θ)^{-(η+2)} f²
  ≤ (1/(4η)) ∫_a^b sin(2θ)^{-η} (f')²
    + (1/2) ( cos(2a) sin(2a)^{-(η+1)} f(a)² - cos(2b) sin(2b)^{-(η+1)} f(b)² ),  η = 99/100.
```

This is the boundary form of the sharp Hardy inequality for the weight `sin(2θ)^{-η}`; it is an
immediate consequence of the exact cot-flux identity `cotFluxIdentity`, in which the left-hand
side equals the two displayed terms *minus* the nonnegative flux deficit
`(1/(4η)) ∫_a^b sin(2θ)^{-η}(f' - 2η cot(2θ) f)²`. -/
theorem hardySigmaBoundaryCore : ∀ (f : ℝ → ℝ) (a b : ℝ), 0 < a → a < b → b < Real.pi / 2 → ContDiffOn ℝ 1 f (Set.Ioo 0 (Real.pi / 2)) → (∫ θ in a..b, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta + 2)) * (f θ) ^ 2) ≤ (1 / (4 * Work.Spaces.eta)) * (∫ θ in a..b, Work.FTS.EllipticEst.thEta θ * (deriv f θ) ^ 2) + (1 / 2) * (Real.cos (2 * a) * (Real.sin (2 * a)) ^ (-(Work.Spaces.eta + 1)) * (f a) ^ 2 - Real.cos (2 * b) * (Real.sin (2 * b)) ^ (-(Work.Spaces.eta + 1)) * (f b) ^ 2) := by
  intro f a b ha hab hb hf
  -- the exact cot-flux identity
  have hkey := Work.FTS.EllipticEst.H2W.AeW.cotFluxIdentity (f := f) hf ha hab hb
  -- the flux deficit is nonnegative
  have hYnn : 0 ≤ ∫ θ in a..b, Work.FTS.EllipticEst.thEta θ
      * (deriv f θ - 2 * Work.Spaces.eta * Real.cot (2 * θ) * f θ) ^ 2 := by
    refine intervalIntegral.integral_nonneg hab.le (fun u hu => ?_)
    have hmem : u ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      ⟨lt_of_lt_of_le ha hu.1, lt_of_le_of_lt hu.2 hb⟩
    have hst : 0 ≤ Work.FTS.EllipticEst.thEta u := by
      rw [Work.FTS.EllipticEst.thEta]
      exact Real.rpow_nonneg (le_of_lt (sin_two_pos_of_Ioo hmem)) _
    exact mul_nonneg hst (sq_nonneg _)
  have hcoef : 0 ≤ (1 / (4 * Work.Spaces.eta)) * (∫ θ in a..b, Work.FTS.EllipticEst.thEta θ
      * (deriv f θ - 2 * Work.Spaces.eta * Real.cot (2 * θ) * f θ) ^ 2) :=
    mul_nonneg (le_of_lt (one_div_pos.mpr (by linarith [Work.Spaces.eta_pos]))) hYnn
  rw [hkey]
  have hrew : (1 / (4 * Work.Spaces.eta))
          * (∫ θ in a..b, Work.FTS.EllipticEst.thEta θ * (deriv f θ) ^ 2)
        - (1 / 2) * (Real.cos (2 * b) * (Real.sin (2 * b)) ^ (-(Work.Spaces.eta + 1)) * (f b) ^ 2
            - Real.cos (2 * a) * (Real.sin (2 * a)) ^ (-(Work.Spaces.eta + 1)) * (f a) ^ 2)
        - (1 / (4 * Work.Spaces.eta)) * (∫ θ in a..b, Work.FTS.EllipticEst.thEta θ
            * (deriv f θ - 2 * Work.Spaces.eta * Real.cot (2 * θ) * f θ) ^ 2)
      = (1 / (4 * Work.Spaces.eta))
          * (∫ θ in a..b, Work.FTS.EllipticEst.thEta θ * (deriv f θ) ^ 2)
        + (1 / 2) * (Real.cos (2 * a) * (Real.sin (2 * a)) ^ (-(Work.Spaces.eta + 1)) * (f a) ^ 2
            - Real.cos (2 * b) * (Real.sin (2 * b)) ^ (-(Work.Spaces.eta + 1)) * (f b) ^ 2)
        - (1 / (4 * Work.Spaces.eta)) * (∫ θ in a..b, Work.FTS.EllipticEst.thEta θ
            * (deriv f θ - 2 * Work.Spaces.eta * Real.cot (2 * θ) * f θ) ^ 2) := by
    ring
  rw [hrew]
  exact sub_le_self _ hcoef

end Work.EllipticEst.Core.i0Aux
