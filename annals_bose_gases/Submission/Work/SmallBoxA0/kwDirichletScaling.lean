import Mathlib.Tactic.Have
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SmallBoxA0.KinWitnessDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SmallBoxA0

open MeasureTheory Metric
open scoped ContDiff Topology Real BigOperators ENNReal
open Submission BoseGases
open Work.SmallBoxA0

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- Scaling law of the Dirichlet energy of the bump: for `0 < c`,
`∫ z : ℝ³, Σ_{k : Fin 3} (∂_k (kwBump c) z)^2 = c⁻¹ * kwE`, where
`kwBump c z = chiBase (c • z)` and `kwE = ∫ w : ℝ³, Σ_k (fderiv ℝ chiBase w (kcStdBasis k))^2`
is the Dirichlet energy of the unscaled bump (both defined in
`Submission/Work/SmallBoxA0/KinWitnessDefs.lean`).

HINT.  `fderiv_comp_smul c (f := chiBase)` reads
`fderiv ℝ (fun z => chiBase (c • z)) z = c • fderiv ℝ chiBase (c • z)`, which after unfolding
`kwBump` gives `fderiv ℝ (kwBump c) z (kcStdBasis k) = c * fderiv ℝ chiBase (c • z) (kcStdBasis k)`
(`ContinuousLinearMap.smul_apply`).  Squaring and summing over `k : Fin 3`,
`Σ_k (fderiv ℝ (kwBump c) z (kcStdBasis k))^2 = c^2 * G (c • z)` with
`G w := Σ_k (fderiv ℝ chiBase w (kcStdBasis k))^2` (`Finset.sum_congr`, `mul_pow`, `Finset.mul_sum`).
Then `∫ z, c^2 * G (c • z) = c^2 * ∫ z, G (c • z)`
(`MeasureTheory.integral_const_mul`), `= c^2 * ((c^3)⁻¹ * ∫ w, G w)`
(`Submission.BoseGases.integral_comp_smul_left` with `ℓ = c`), and this is `c⁻¹ * kwE` because
`kwE = ∫ w, G w` by definition (`field_simp`/`ring` with `hc : 0 < c`). -/
lemma kwDirichletScaling {c : ℝ} (hc : 0 < c) :
    (∫ z : EuclideanSpace ℝ (Fin 3), ∑ k : Fin 3, (fderiv ℝ (kwBump c) z (kcStdBasis k)) ^ 2)
      = c⁻¹ * kwE := by
  -- The chain rule: differentiating the dilation `z ↦ c • z` multiplies `fderiv` by `c`.
  have hfd : ∀ z : ℝ³, fderiv ℝ (kwBump c) z = c • fderiv ℝ chiBase (c • z) := by
    intro z
    show fderiv ℝ (fun z => chiBase (c • z)) z = c • fderiv ℝ chiBase (c • z)
    exact fderiv_comp_smul c
  -- Squaring and summing over the three coordinate directions.
  have hsum : ∀ z : ℝ³, (∑ k : Fin 3, (fderiv ℝ (kwBump c) z (kcStdBasis k)) ^ 2)
      = c ^ 2 * ∑ k : Fin 3, (fderiv ℝ chiBase (c • z) (kcStdBasis k)) ^ 2 := by
    intro z
    rw [show (∑ k : Fin 3, (fderiv ℝ (kwBump c) z (kcStdBasis k)) ^ 2)
        = ∑ k : Fin 3, c ^ 2 * (fderiv ℝ chiBase (c • z) (kcStdBasis k)) ^ 2 from
      Finset.sum_congr rfl (fun k _ => by rw [hfd z, smul_apply]; ring)]
    rw [Finset.mul_sum]
  -- Rewrite the integrand pointwise.
  rw [show (∫ z : ℝ³, ∑ k : Fin 3, (fderiv ℝ (kwBump c) z (kcStdBasis k)) ^ 2)
      = ∫ z : ℝ³, c ^ 2 * (∑ k : Fin 3, (fderiv ℝ chiBase (c • z) (kcStdBasis k)) ^ 2) from
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => hsum z)]
  -- Pull the constant `c ^ 2` out of the integral.
  rw [MeasureTheory.integral_const_mul]
  -- Substitute `z ↦ c • z`: the volume scales by `(c ^ 3)⁻¹`.
  rw [show (∫ z : ℝ³, ∑ k : Fin 3, (fderiv ℝ chiBase (c • z) (kcStdBasis k)) ^ 2)
      = (c ^ 3)⁻¹ * ∫ w : ℝ³, ∑ k : Fin 3, (fderiv ℝ chiBase w (kcStdBasis k)) ^ 2 from
    Submission.BoseGases.integral_comp_smul_left
      (g := fun w : ℝ³ => ∑ k : Fin 3, (fderiv ℝ chiBase w (kcStdBasis k)) ^ 2) hc]
  -- The remaining integral is `kwE` by definition.
  rw [show (∫ w : ℝ³, ∑ k : Fin 3, (fderiv ℝ chiBase w (kcStdBasis k)) ^ 2) = kwE from rfl]
  -- `c ^ 2 * ((c ^ 3)⁻¹ * kwE) = c⁻¹ * kwE` for `0 < c`.
  field_simp

end Work.SmallBoxA0
