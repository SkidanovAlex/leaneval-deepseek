import Mathlib
import Submission.Work.Lattice.PolygonUniformBound
import Submission.Work.Lattice.PhiPolygonCompare
import Submission.Commons.Lattice.SuccessiveMinima.Basic

/-!
# The successive minimum vs. the polygon slope *below* the rank

The §3 extraction charges the `Δω_s` vectors added from the flag member of rank `j_s = jb s` to
the slope of the polygon on the block *below* `j_s`, i.e. it needs

    `log λ_{j_s}(Λ_t) ≤ phiSlope (Λ₀) (j_s − 1) + O(1)`.

This is the Prop.-4(2) inequality `|log λ_j − dslope (phiPolygon Λ_t A)(j−1)| ≤ Kconst + 2Ad²`
combined with the Lipschitz comparison of the slacked polygon slopes.

Module `Submission.Work.Extraction.LambdaPred`, namespace `Submission.LambdaPred`.
-/

noncomputable section
open Module exteriorPower InnerProductGeometry Real
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1200000

namespace Submission.LambdaPred

open Submission.ExteriorCoordinates
open Submission.MaxPhiAccounting
open Submission.MaxPhiPolygon
open Submission.PhiPolygon
open Submission.Prop42Upper
open Submission.LatticePolygon
open Submission.SlopeLambda
open Submission.Polygon
open Submission.ImageLattice
open Submission.FlowLatticeImage
open Submission.FlagMemberCriterion
open Submission.GraysonLattice
open Submission.MaxRankData
open Submission.PhiPolygonCompare
open Submission.SuccessiveMinima

variable {d : ℕ}

/-- **The `pred` interface.**  For the §3 flow lattice `Λ_t = (s · a_t)(ℤᵈ)` and `1 ≤ j ≤ d`,

    `log λ_j(Λ_t) ≤ phiSlope (imageSpan s) ℓ A t (j − 1) + (Kconst d + 2 A d² + 2 dataCeil d)`. -/
theorem log_successiveMinimum_le_phiSlope_pred {ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d)
    (s : RD d ≃ₗᵢ[ℝ] RD d) (t A : ℝ) (hA : 0 ≤ A) {j : ℕ} (hj1 : 1 ≤ j) (hjd : j ≤ d)
    (hBdd : ∀ (m : ℕ) (hm : m ≤ d), BddBelow (maxRankDataSet (d := d)
      (imageSpan (d := d) ((s : RD d ≃ₗ[ℝ] RD d).trans (eEquiv (d := d) ℓ t))) m hm)) :
    Real.log (successiveMinimum (E := RD d) (imageSpan (d := d)
        ((s : RD d ≃ₗ[ℝ] RD d).trans (eEquiv (d := d) ℓ t))) j) ≤
      phiSlope (d := d) (imageSpan (d := d) (s : RD d ≃ₗ[ℝ] RD d)) ℓ A t (j - 1) +
        (Kconst d + 2 * A * (d : ℝ) ^ 2 + 2 * dataCeil d) := by
  classical
  have hd0 : 0 < d := lt_of_lt_of_le hℓ0 (le_of_lt hℓd)
  set Λ : Submodule ℤ (RD d) :=
    imageSpan (d := d) ((s : RD d ≃ₗ[ℝ] RD d).trans (eEquiv (d := d) ℓ t)) with hΛ
  have hfin : Module.finrank ℤ Λ = d := finrank_imageSpan (d := d) _
  have hBddΛ : ∀ (m : ℕ) (hm : m ≤ d), BddBelow (maxRankDataSet (d := d) Λ m hm) := by
    intro m hm
    rw [hΛ]
    exact hBdd m hm
  have hprop := abs_log_successiveMinimum_sub_dslope_phi_le (d := d) hd0 Λ hfin hA hj1 hjd
  have hlip := dslope_phiPolygon_le_maxphiPolygon (d := d) Λ hfin A hBddΛ (i := j - 1) (by omega)
  have hpoly : ∀ i, maxphiPolygon (d := d) Λ A i = phiPolygonT (d := d)
      (imageSpan (d := d) (s : RD d ≃ₗ[ℝ] RD d)) ℓ A t i := by
    intro i
    rw [hΛ]
    exact (phiPolygonT_eq_maxphiPolygon_imageSpan (d := d) (s : RD d ≃ₗ[ℝ] RD d) ℓ t A i).symm
  have hflow : Polygon.dslope (maxphiPolygon (d := d) Λ A) (j - 1) =
      phiSlope (d := d) (imageSpan (d := d) (s : RD d ≃ₗ[ℝ] RD d)) ℓ A t (j - 1) := by
    simp only [Polygon.dslope, phiSlope]
    rw [hpoly (j - 1), hpoly ((j - 1) + 1), Nat.sub_add_cancel hj1]
  have h1 : Real.log (successiveMinimum (E := RD d) Λ j) -
      Polygon.dslope (phiPolygon (d := d) Λ A) (j - 1) ≤
      Kconst d + 2 * A * (d : ℝ) ^ 2 := by
    rw [abs_sub_le_iff] at hprop
    exact hprop.1
  have h2 : Polygon.dslope (phiPolygon (d := d) Λ A) (j - 1) ≤
      Polygon.dslope (maxphiPolygon (d := d) Λ A) (j - 1) + 2 * dataCeil d := hlip
  rw [hflow] at h2
  have hgoal : Real.log (successiveMinimum (E := RD d) Λ j) ≤
      phiSlope (d := d) (imageSpan (d := d) (s : RD d ≃ₗ[ℝ] RD d)) ℓ A t (j - 1) +
        (Kconst d + 2 * A * (d : ℝ) ^ 2 + 2 * dataCeil d) := by
    linarith [h1, h2]
  exact hgoal

end Submission.LambdaPred

end
