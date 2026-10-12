import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BSKinetic.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BSKinetic

open MeasureTheory
open scoped ContDiff Topology Real BigOperators
open Submission.BoseGases

set_option autoImplicit false

/-- **The kinetic word as a sum of slot fibres.**  Peeling one particle at a time out of the
product box `abox (n+1) ℓ`, the box-restricted Dirichlet word

`kinWord (n+1) ℓ Φ = Σᵢ Σ_k ∫_{abox (n+1) ℓ} (∂_{i,k}Φ)²`

is the slot sum of the one-body Dirichlet words of the fibres `z ↦ Φ(x_{i←z})` over the
remaining box `abox n ℓ`:

`Σᵢ ∫_{abox n ℓ} Σₖ ∫_{acube ℓ} (∂_{z,k} (z ↦ Φ(x_{i←z})))²`.

The two ingredients are the measure-preserving peel of the centred box
(`Submission.BoseGases.abox_integral_peel`) and the chain rule identifying the fibre
derivative with the master derivative along the slot-`i` coordinate direction
(`Submission.BoseGases.fiber_fderiv_kcDir`). -/
theorem kinWord_eq_slotSum {ℓ : ℝ} (hℓ : 0 < ℓ) (n : ℕ)
    (Φ : Submission.BoseGases.X (n + 1) → ℝ) (hΦ : ContDiff ℝ (⊤ : ENat) Φ) :
    Submission.BoseGases.kinWord (n + 1) ℓ Φ
      = ∑ i : Fin (n + 1), ∫ r in Submission.BoseGases.abox n ℓ,
          ∑ k : Fin 3, ∫ z in Submission.BoseGases.acube ℓ,
            (fderiv ℝ (fun w : EuclideanSpace ℝ (Fin 3) =>
                Φ (Submission.BoseGases.kcInsN n i (w, r))) z
              (Submission.BoseGases.kcStdBasis k)) ^ 2 := by
  -- The per-slot identity: peel slot `i`, then exchange the sum over the three coordinates
  -- with the integral over the remaining box.
  have hkey : ∀ i : Fin (n + 1),
      (∑ k : Fin 3, ∫ x in abox (n + 1) ℓ, (fderiv ℝ Φ x (kcDir (n + 1) i k)) ^ 2)
        = ∫ r in abox n ℓ, ∑ k : Fin 3, ∫ z in acube ℓ,
            (fderiv ℝ (fun w : EuclideanSpace ℝ (Fin 3) =>
                Φ (kcInsN n i (w, r))) z (kcStdBasis k)) ^ 2 := by
    intro i
    -- each coordinate square is integrable on the centred `(n+1)`-box
    have hFint : ∀ k : Fin 3,
        IntegrableOn (fun x : X (n + 1) => (fderiv ℝ Φ x (kcDir (n + 1) i k)) ^ 2)
          (abox (n + 1) ℓ) volume := by
      intro k
      exact integrableOn_abox_of_continuous hℓ
        ((firstDir_contDiff hΦ (kcDir (n + 1) i k)).continuous.pow 2)
    -- the peel of one coordinate square
    have hpeel : ∀ k : Fin 3,
        (∫ x in abox (n + 1) ℓ, (fderiv ℝ Φ x (kcDir (n + 1) i k)) ^ 2)
          = ∫ r in abox n ℓ, ∫ z in acube ℓ,
              (fderiv ℝ Φ (kcInsN n i (z, r)) (kcDir (n + 1) i k)) ^ 2 :=
      fun k => abox_integral_peel (i := i) (F := fun x : X (n + 1) =>
          (fderiv ℝ Φ x (kcDir (n + 1) i k)) ^ 2) (hFint k)
    -- the peeled fibres are integrable in the remaining box
    have hGint : ∀ k : Fin 3,
        Integrable (fun r : X n => ∫ z in acube ℓ,
            (fderiv ℝ Φ (kcInsN n i (z, r)) (kcDir (n + 1) i k)) ^ 2)
          ((volume : Measure (X n)).restrict (abox n ℓ)) :=
      fun k => abox_peel_inner_integrable (i := i)
        (F := fun x : X (n + 1) => (fderiv ℝ Φ x (kcDir (n + 1) i k)) ^ 2) (hFint k)
    calc
      (∑ k : Fin 3, ∫ x in abox (n + 1) ℓ, (fderiv ℝ Φ x (kcDir (n + 1) i k)) ^ 2)
          = ∑ k : Fin 3, ∫ r in abox n ℓ, ∫ z in acube ℓ,
              (fderiv ℝ Φ (kcInsN n i (z, r)) (kcDir (n + 1) i k)) ^ 2 := by
            exact Finset.sum_congr rfl (fun k _ => hpeel k)
      _ = ∫ r in abox n ℓ, ∑ k : Fin 3, ∫ z in acube ℓ,
              (fderiv ℝ Φ (kcInsN n i (z, r)) (kcDir (n + 1) i k)) ^ 2 := by
            exact (integral_finsetSum Finset.univ (fun k _ => hGint k)).symm
      _ = ∫ r in abox n ℓ, ∑ k : Fin 3, ∫ z in acube ℓ,
              (fderiv ℝ (fun w : EuclideanSpace ℝ (Fin 3) =>
                Φ (kcInsN n i (w, r))) z (kcStdBasis k)) ^ 2 := by
            apply integral_congr_ae
            filter_upwards with r
            apply Finset.sum_congr rfl
            intro k _
            apply integral_congr_ae
            filter_upwards with z
            rw [fiber_fderiv_kcDir i hΦ r z k]
  unfold kinWord
  exact Finset.sum_congr rfl (fun i _ => hkey i)

end Work.BSKinetic
