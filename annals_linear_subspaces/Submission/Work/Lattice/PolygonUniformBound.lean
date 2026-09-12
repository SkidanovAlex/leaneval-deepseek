import Mathlib
import Submission.Work.Lattice.FlagMemberCriterion
import Submission.Work.Lattice.SlopeLambda
import Submission.Work.Lattice.PhiPolygonCompare
import Submission.Work.Lattice.MaxFlagMinima

/-!
# The uniform bound on the slacked flow polygon (convexity with vanishing endpoints)

The Grayson data of the §3 flow lattice `Λ_t = (a_t ∘ s)(ℤᵈ)` has **vanishing endpoints**:
`phiData 0 = 0` (the zero subgroup) and `phiData d = 0` (the flow is unimodular, so the covolume
of the full lattice stays `1`).  A convex function with equal endpoint values lies below its chord,
hence

    `phiPolygonT Λ₀ ℓ A t j ≤ 0`   for every `0 ≤ j ≤ d`,

**uniformly in `t`** and in the isometry `s`.  Comparing the slacked max-norm polygon with the
Euclidean slacked polygon (at most `dataCeil` higher) and with the intrinsic Grayson polygon
(`polygon ≤ phiPolygon`), one gets the *uniform* bound

    `polygon Λ_t j ≤ dataCeil d`

and therefore, by Prop. 4(2),

    `Σ_{i<j} log λ_{i+1}(Λ_t) ≤ dataCeil d + Kconst d`.

This is the uniform (good-time free) bound on the *prefix products* of the successive minima of
the flowed lattice; it is the input that bounds the wedge norms of the §3 extraction without
appealing to the time selection.

Module `Submission.Work.Lattice.PolygonUniformBound`, namespace `Submission.PolygonUniformBound`.
-/

noncomputable section
open Module exteriorPower InnerProductGeometry Real
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1200000

namespace Submission.PolygonUniformBound

open Submission.ExteriorCoordinates
open Submission.Prop42Upper
open Submission.LatticePolygon
open Submission.SlopeLambda
open Submission.Polygon
open Submission.ImageLattice
open Submission.FlowLatticeImage
open Submission.MaxRankData
open Submission.MaxFlagMinima
open Submission.FlagMemberCriterion
open Submission.GraysonLattice

variable {d : ℕ}

/-- **The slacked flow polygon is `≤ 0`.**  It is convex (`phiPolygonT_convex`) with vanishing
endpoints (`phiPolygonT_zero`, `phiPolygonT_top`), hence lies below the chord `≡ 0`. -/
theorem phiPolygonT_nonpos {ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) (A : ℝ)
    (g : RD d ≃ₗᵢ[ℝ] RD d) (t : ℝ) {j : ℕ} (hjd : j ≤ d) :
    Submission.MaxPhiAccounting.phiPolygonT (d := d)
      (imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d)) ℓ A t j ≤ 0 := by
  have hd0 : 0 < d := lt_of_lt_of_le hℓ0 (le_of_lt hℓd)
  set c := Submission.MaxPhiAccounting.phiPolygonT (d := d)
    (imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d)) ℓ A t with hc
  have hconv : Submission.Polygon.DiscreteConvexOn c d :=
    Submission.MaxPhiAccounting.phiPolygonT_convex _ ℓ A t
  have h0 : c 0 = 0 := Submission.MaxPhiAccounting.phiPolygonT_zero _ ℓ A t
  have hd : c d = 0 := Submission.MaxPhiAccounting.phiPolygonT_top hℓ0 hℓd A g t
  have hchord := chord_le_of_discreteConvex hconv (m := 0) (j := j) (n := d)
    (Nat.zero_le j) hjd le_rfl
  rw [h0, hd, Nat.sub_zero, Nat.sub_zero] at hchord
  simp only [mul_zero, add_zero] at hchord
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd0
  by_contra hneg
  push Not at hneg
  nlinarith [hchord]

/-- The slacked Euclidean data of the flowed lattice is at most the slacked max-norm data plus
the norm-comparability ceiling `dataCeil`. -/
theorem phiData_le_maxphiData_add {ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) (A : ℝ)
    (g : RD d ≃ₗᵢ[ℝ] RD d) (t : ℝ) {i : ℕ} (hi : i ≤ d) :
    Submission.PhiPolygon.phiData (d := d)
        (imageSpan (d := d) ((g : RD d ≃ₗ[ℝ] RD d).trans (eEquiv (d := d) ℓ t))) A i ≤
      Submission.MaxPhiPolygon.maxphiData (d := d)
        (imageSpan (d := d) ((g : RD d ≃ₗ[ℝ] RD d).trans (eEquiv (d := d) ℓ t))) A i +
        dataCeil d := by
  set Λ : Submodule ℤ (RD d) :=
    imageSpan (d := d) ((g : RD d ≃ₗ[ℝ] RD d).trans (eEquiv (d := d) ℓ t)) with hΛ
  have hfin : Module.finrank ℤ Λ = d := finrank_imageSpan (d := d) _
  rcases Nat.eq_zero_or_pos i with hi0 | hipos
  · subst hi0
    have h1 : rankData (d := d) Λ 0 = 0 := LatticePolygon.rankData_zero (d := d) Λ
    have h2 : Submission.MaxPhiPolygon.maxphiData (d := d) Λ A 0 = 0 := by
      rw [Submission.MaxPhiPolygon.maxphiData, dif_pos hi]
      rw [maxRankData_eq_zero hi rfl]
      ring
    rw [Submission.PhiPolygon.phiData, h1, h2]
    have := dataCeil_nonneg d
    push_cast
    linarith
  · have hbdd : BddBelow (maxRankDataSet (d := d) Λ i hi) := by
      rw [hΛ]
      exact bddBelow_maxRankDataSet_imageSpan (d := d) hℓ0 hℓd hi hipos g t
    have h := rankData_le_maxRankData_add (d := d) hipos hi Λ hfin hbdd
    rw [Submission.PhiPolygon.phiData, Submission.MaxPhiPolygon.maxphiData, dif_pos hi]
    linarith [h]

/-- **The intrinsic polygon of the §3 flow lattice is uniformly bounded by `dataCeil`.** -/
theorem polygon_imageSpan_le_dataCeil {ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) (A : ℝ) (hA : 0 ≤ A)
    (g : RD d ≃ₗᵢ[ℝ] RD d) (t : ℝ) {j : ℕ} (hjd : j ≤ d) :
    polygon (d := d) (imageSpan (d := d) ((g : RD d ≃ₗ[ℝ] RD d).trans (eEquiv (d := d) ℓ t))) j ≤
      dataCeil d := by
  set Λ : Submodule ℤ (RD d) :=
    imageSpan (d := d) ((g : RD d ≃ₗ[ℝ] RD d).trans (eEquiv (d := d) ℓ t)) with hΛ
  have hfin : Module.finrank ℤ Λ = d := finrank_imageSpan (d := d) _
  have hmono : polygon (d := d) Λ j ≤ Submission.PhiPolygon.phiPolygon (d := d) Λ A j :=
    Submission.PhiPolygonCompare.polygon_le_phiPolygon (d := d) Λ hfin hA hjd
  have hdata : ∀ i ≤ d, Submission.PhiPolygon.phiData (d := d) Λ A i ≤
      Submission.MaxPhiPolygon.maxphiData (d := d) Λ A i + dataCeil d := by
    intro i hi
    rw [hΛ]
    exact phiData_le_maxphiData_add (d := d) hℓ0 hℓd A g t hi
  have hpoly : Submission.PhiPolygon.phiPolygon (d := d) Λ A j ≤
      Submission.MaxPhiPolygon.maxphiPolygon (d := d) Λ A j + dataCeil d := by
    have h1 : Submission.PhiPolygon.phiPolygon (d := d) Λ A j =
        largestConvexMinorant d (Submission.PhiPolygon.phiData (d := d) Λ A) j := by
      rw [Submission.PhiPolygon.phiPolygon, hfin]
    have h2 : Submission.MaxPhiPolygon.maxphiPolygon (d := d) Λ A j =
        largestConvexMinorant d (Submission.MaxPhiPolygon.maxphiData (d := d) Λ A) j := by
      rw [Submission.MaxPhiPolygon.maxphiPolygon, hfin]
    rw [h1, h2]
    exact largestConvexMinorant_le_add _ _ (fun i hi => hdata i hi) hjd
  have hbridge : Submission.MaxPhiPolygon.maxphiPolygon (d := d) Λ A j =
      Submission.MaxPhiAccounting.phiPolygonT (d := d)
        (imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d)) ℓ A t j := by
    rw [hΛ]
    exact (phiPolygonT_eq_maxphiPolygon_imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d) ℓ t A j).symm
  have hnonpos : Submission.MaxPhiPolygon.maxphiPolygon (d := d) Λ A j ≤ 0 := by
    rw [hbridge]
    exact phiPolygonT_nonpos (d := d) hℓ0 hℓd A g t hjd
  linarith [hmono, hpoly, hnonpos]

/-- **The uniform prefix bound on the successive minima of the flowed lattice.** -/
theorem prSum_imageSpan_le {ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) (A : ℝ) (hA : 0 ≤ A)
    (g : RD d ≃ₗᵢ[ℝ] RD d) (t : ℝ) {j : ℕ} (hjd : j ≤ d) :
    prSum (d := d) (imageSpan (d := d) ((g : RD d ≃ₗ[ℝ] RD d).trans (eEquiv (d := d) ℓ t))) j ≤
      dataCeil d + Kconst d := by
  have hd0 : 0 < d := lt_of_lt_of_le hℓ0 (le_of_lt hℓd)
  set Λ : Submodule ℤ (RD d) :=
    imageSpan (d := d) ((g : RD d ≃ₗ[ℝ] RD d).trans (eEquiv (d := d) ℓ t)) with hΛ
  have hfin : Module.finrank ℤ Λ = d := finrank_imageSpan (d := d) _
  have h1 := prSum_le_polygon_add_Kconst (d := d) hd0 Λ hfin (j := j) hjd
  have h2 : polygon (d := d) Λ j ≤ dataCeil d := by
    rw [hΛ]
    exact polygon_imageSpan_le_dataCeil (d := d) hℓ0 hℓd A hA g t hjd
  linarith

end Submission.PolygonUniformBound

end
