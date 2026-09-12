import Mathlib
import Submission.Work.Lattice.TangentCriterion
import Submission.Work.Lattice.MaxPhiFlag
import Submission.Work.Lattice.MaxAttainment
import Submission.GeometryOfNumbers.ImageLatticeCovolume
import Submission.Work.Lattice.IntrinsicIndex

/-!
# The §3 lattice as an `imageSpan`, and the flag on it

The §3 lattice is `Λ_t = a_t Λ₀` with `Λ₀ = s_x ℤᵈ` (`s_x` the orthogonal representative of `x`).
For the flag layer (`MaxPhiFlag.exists_tight_flag`) one needs `Λ_t` as an object with the
`ZSpan` instances (`DiscreteTopology`, `IsZLattice`) and with the *same* carrier as the image
`Λ₀.map (a_t |_ℤ)` used by the data (`FlowDataMax.flowMaxData_eq_maxRankData`).

This module records the translations:

* `imageSpan_scaleMapEquiv` — `eFlow ℓ t` is the coercion of `scaleMapEquiv`;
* `imageSpan_map_eq` — `(imageSpan g).map (eFlow ℓ t |_ℤ) = imageSpan (g.trans E)`, so the flowed
  lattice is again an `imageSpan` (hence carries all `ZSpan` instances);
* `bddBelow_maxRankDataSet_imageSpan` — the max-norm data of `imageSpan (g.trans E)` is bounded
  below (transported from `MaxAttainment.bddBelow_maxRankDataSet_imageSpan_flow`).

Module `Submission.Work.Lattice.FlowLatticeImage`, namespace `Submission.FlowLatticeImage`.
-/

noncomputable section

open Module exteriorPower InnerProductGeometry Real Filter
open scoped BigOperators Topology
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

namespace Submission.FlowLatticeImage

open Submission.ExteriorCoordinates
open Submission.DiagonalFlow
open Submission.MaxNorm
open Submission.MaxNormPolygon
open Submission.FlowRateAsymptotic
open Submission.FlowDataMax
open Submission.ImageLattice
open Submission.FlowLattice
open Submission.MaxRankData
open Submission.MaxAttainment

variable {d : ℕ}

/-- The exponential flow `eFlow ℓ t` is the coercion of the `scaleMapEquiv` with
`a = exp(−t/ℓ)`, `b = exp(t/(d−ℓ))`. -/
lemma eFlow_eq_scaleMapEquiv (ℓ : ℕ) (t : ℝ) :
    eFlow (d := d) ℓ t =
      ((scaleMapEquiv (d := d) (Real.exp (-t / (ℓ : ℝ)))
        (Real.exp (t / ((d - ℓ : ℕ) : ℝ))) ℓ
        (Real.exp_ne_zero _) (Real.exp_ne_zero _)) : RD d →ₗ[ℝ] RD d) := by
  rw [eFlow_eq]
  rfl

/-- **The flowed lattice is again an `imageSpan`.** -/
theorem imageSpan_map_eq (g : RD d ≃ₗ[ℝ] RD d) (ℓ : ℕ) (t : ℝ) :
    (imageSpan (d := d) g).map ((eFlow (d := d) ℓ t).restrictScalars ℤ) =
      imageSpan (d := d) (g.trans (scaleMapEquiv (d := d) (Real.exp (-t / (ℓ : ℝ)))
        (Real.exp (t / ((d - ℓ : ℕ) : ℝ))) ℓ
        (Real.exp_ne_zero _) (Real.exp_ne_zero _))) := by
  set E : RD d ≃ₗ[ℝ] RD d := scaleMapEquiv (d := d) (Real.exp (-t / (ℓ : ℝ)))
    (Real.exp (t / ((d - ℓ : ℕ) : ℝ))) ℓ (Real.exp_ne_zero _) (Real.exp_ne_zero _) with hE
  have hef : eFlow (d := d) ℓ t = (E : RD d →ₗ[ℝ] RD d) := by
    rw [hE]; exact eFlow_eq_scaleMapEquiv (d := d) ℓ t
  rw [hef, imageSpan_eq_map (d := d) g, imageSpan_eq_map (d := d) (g.trans E)]
  have hcomp : ((g.trans E : RD d ≃ₗ[ℝ] RD d) : RD d →ₗ[ℝ] RD d).restrictScalars ℤ =
      ((E : RD d →ₗ[ℝ] RD d).restrictScalars ℤ).comp ((g : RD d →ₗ[ℝ] RD d).restrictScalars ℤ) := by
    ext x
    rfl
  rw [hcomp, ← Submodule.map_comp]

/-- **The §3 flowed lattice is full-rank.** -/
theorem finrank_imageSpan (g : RD d ≃ₗ[ℝ] RD d) :
    Module.finrank ℤ (imageSpan (d := d) g) = d :=
  Submission.IntrinsicIndex.finrank_zLattice (Λ := imageSpan (d := d) g)

/-- **The max-norm data of the flowed §3 lattice is bounded below** (in the `imageSpan`
presentation of the lattice). -/
theorem bddBelow_maxRankDataSet_imageSpan {ℓ j : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) (hjd : j ≤ d)
    (hj1 : 1 ≤ j) (s : RD d ≃ₗᵢ[ℝ] RD d) (t : ℝ) :
    BddBelow (maxRankDataSet (d := d)
      (imageSpan (d := d) ((s : RD d ≃ₗ[ℝ] RD d).trans (scaleMapEquiv (d := d)
        (Real.exp (-t / (ℓ : ℝ))) (Real.exp (t / ((d - ℓ : ℕ) : ℝ))) ℓ
        (Real.exp_ne_zero _) (Real.exp_ne_zero _)))) j hjd) := by
  rw [← imageSpan_map_eq (d := d) (s : RD d ≃ₗ[ℝ] RD d) ℓ t]
  exact bddBelow_maxRankDataSet_imageSpan_flow (d := d) hℓ0 hℓd hjd hj1 s t

end Submission.FlowLatticeImage

end
