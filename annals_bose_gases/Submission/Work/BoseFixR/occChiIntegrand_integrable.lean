import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixR

set_option maxHeartbeats 2000000

/-!
# Integrability of the occupancy–cutoff integrand on the `N`-particle box

For a *continuous* configuration function `Φ : X n → ℝ` the integrand

`x ↦ (Φ x)^2 · Σᵢ χ_{B(u)}(xᵢ)`

of the second localisation (FS §5) is a continuous function on the
finite-dimensional space `X n = (ℝ³)ⁿ`; the `N`-particle box `abox n ℓ` is
compact, hence of finite measure, so the integrand is integrable on it.

The only non-elementary input is the continuity of the cutoff
`χ_{B(u)}(x) = χ(x/ℓ)·χ_M(x/(ℓd) − u)` as a function of `x`
(`Work.SmallBoxSliding.chiSmallB_continuous_joint`, valid for every `M`, hence
in particular for the possibly degenerate `M = 0`).
-/

theorem occChiIntegrand_integrable {n : ℕ} {M : ℕ} {ℓ d : ℝ} {u : EuclideanSpace ℝ (Fin 3)}
    {Φ : Submission.BoseGases.X n → ℝ} (hℓ : 0 < ℓ) (hΦ : Continuous Φ) :
    MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X n =>
        (Φ x) ^ 2 * ∑ i : Fin n, Submission.BoseGases.chiSmallB M ℓ d u (x i))
      (Submission.BoseGases.abox n ℓ) := by
  -- the `i`-th occupancy factor is continuous in the configuration
  have hsingle : ∀ i : Fin n, Continuous (fun x : Submission.BoseGases.X n =>
      Submission.BoseGases.chiSmallB M ℓ d u (x i)) := by
    intro i
    have hb := Work.SmallBoxSliding.chiSmallB_continuous_joint M ℓ d i
    exact hb.comp (continuous_const.prodMk continuous_id)
  have hsum : Continuous (fun x : Submission.BoseGases.X n =>
      ∑ i : Fin n, Submission.BoseGases.chiSmallB M ℓ d u (x i)) :=
    continuous_finsetSum _ (fun i _ => hsingle i)
  have hcont : Continuous (fun x : Submission.BoseGases.X n =>
      (Φ x) ^ 2 * ∑ i : Fin n, Submission.BoseGases.chiSmallB M ℓ d u (x i)) :=
    (hΦ.pow 2).mul hsum
  -- a continuous function on the compact `N`-particle box is integrable
  exact hcont.continuousOn.integrableOn_compact (Submission.BoseGases.abox_compact n hℓ)

end Work.BoseFixR
