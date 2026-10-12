import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseKinLoc.NeuFrac.neuFrac_add_const_L2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseKinLoc.NeuFrac.neuFracTrialVal_const_mul`

The functional `neuFracTrialVal ℓ a2 u ψ g` (FS `eq:DefT`, first term) is the sum

`∫_Λ ψ² − 2 a2 ∫_Λ ψ·g + a2·(Σ_k ∫_Λ (∂_k g)² + a2 ∫_Λ g²)`,   `Λ = lamBox ℓ u`.

Replacing the state `ψ` by `c·ψ` and the trial `g` by `c·g` scales the *unnested* terms by
`c²`: `∫_Λ (cψ)² = c² ∫_Λ ψ²`, `∫_Λ (cψ)(cg) = c² ∫_Λ ψ·g`, `∫_Λ (c g)² = c² ∫_Λ g²`, and
each derivative integral by `c²` (`∂_k(c g) = c ∂_k g`).  This is exactly the statement below.

The identities hold *unconditionally* — there is no integrability hypothesis on `ψ` — because
the Bochner integral of a non-integrable integrand is `0` (`MeasureTheory.integral_undef`) and
`MeasureTheory.integral_const_mul` is stated without integrability hypotheses.  The only
hypothesis is `hg : ContDiff ℝ ⊤ g`, needed so that `g` is differentiable and the chain rule
`fderiv ℝ (fun z => c * g z) z = c • fderiv ℝ g z` applies.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseKinLoc.NeuFrac

open Submission.BoseGases

theorem neuFracTrialVal_const_mul {ℓ a2 c : ℝ} {u : EuclideanSpace ℝ (Fin 3)} {ψ g : EuclideanSpace ℝ (Fin 3) → ℝ} (hg : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) g) :
    Work.BoseKinLoc.NeuFrac.neuFracTrialVal ℓ a2 u (fun z => c * ψ z) (fun z => c * g z) = c ^ 2 * Work.BoseKinLoc.NeuFrac.neuFracTrialVal ℓ a2 u ψ g := by
  have hgdiff : Differentiable ℝ g := hg.differentiable (by simp)
  -- `∫_Λ (cψ)² = c² ∫_Λ ψ²`
  have hI1 : (∫ z in lamBox ℓ u, (c * ψ z) ^ 2)
      = c ^ 2 * (∫ z in lamBox ℓ u, (ψ z) ^ 2) := by
    have h : (fun z => (c * ψ z) ^ 2) = (fun z => c ^ 2 * (ψ z) ^ 2) := by
      funext z; ring
    rw [h]
    exact integral_const_mul (c ^ 2) (fun z => (ψ z) ^ 2)
  -- `∫_Λ (cψ)(cg) = c² ∫_Λ ψ·g`
  have hI2 : (∫ z in lamBox ℓ u, (c * ψ z) * (c * g z))
      = c ^ 2 * (∫ z in lamBox ℓ u, ψ z * g z) := by
    have h : (fun z => (c * ψ z) * (c * g z)) = (fun z => c ^ 2 * (ψ z * g z)) := by
      funext z; ring
    rw [h]
    exact integral_const_mul (c ^ 2) (fun z => ψ z * g z)
  -- `∫_Λ (cg)² = c² ∫_Λ g²`
  have hI4 : (∫ z in lamBox ℓ u, (c * g z) ^ 2)
      = c ^ 2 * (∫ z in lamBox ℓ u, (g z) ^ 2) := by
    have h : (fun z => (c * g z) ^ 2) = (fun z => c ^ 2 * (g z) ^ 2) := by
      funext z; ring
    rw [h]
    exact integral_const_mul (c ^ 2) (fun z => (g z) ^ 2)
  -- each derivative integral scales by `c²`
  have hderiv : ∀ k : Fin 3,
      (∫ z in lamBox ℓ u, (fderiv ℝ (fun z => c * g z) z (kcStdBasis k)) ^ 2)
        = c ^ 2 * (∫ z in lamBox ℓ u, (fderiv ℝ g z (kcStdBasis k)) ^ 2) := by
    intro k
    have hpt : ∀ z, fderiv ℝ (fun z => c * g z) z (kcStdBasis k)
        = c * fderiv ℝ g z (kcStdBasis k) := by
      intro z
      rw [fderiv_const_mul (hgdiff.differentiableAt) c]
      rw [smul_apply]
      rfl
    have h : (fun z => (fderiv ℝ (fun z => c * g z) z (kcStdBasis k)) ^ 2)
        = (fun z => c ^ 2 * (fderiv ℝ g z (kcStdBasis k)) ^ 2) := by
      funext z; rw [hpt z]; ring
    rw [h]
    exact integral_const_mul (c ^ 2) (fun z => (fderiv ℝ g z (kcStdBasis k)) ^ 2)
  -- the finite sum scales by `c²`
  have hsum : (∑ k : Fin 3, ∫ z in lamBox ℓ u,
        (fderiv ℝ (fun z => c * g z) z (kcStdBasis k)) ^ 2)
      = c ^ 2 * (∑ k : Fin 3, ∫ z in lamBox ℓ u,
        (fderiv ℝ g z (kcStdBasis k)) ^ 2) := by
    rw [Finset.sum_congr rfl (fun k _ => hderiv k)]
    exact (Finset.mul_sum Finset.univ (fun k : Fin 3 =>
      ∫ z in lamBox ℓ u, (fderiv ℝ g z (kcStdBasis k)) ^ 2) (c ^ 2)).symm
  unfold neuFracTrialVal
  rw [hI1, hI2, hsum, hI4]
  ring

end Work.BoseKinLoc.NeuFrac
