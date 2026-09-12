import Mathlib
import Submission.Work.Lattice.MaxPhiAccounting
import Submission.Work.Lattice.PhiPolygonCompare
import Submission.Work.Lattice.MaxFlagMinima
import Submission.Work.Lattice.FlowLatticeImage
import Submission.Work.Lattice.FlagMemberCriterion

/-!
# The successive minima of the §3 flow lattice vs. the slopes of the slacked polygon

The §3 extraction (Prop 5 of de Saxcé) needs, for the flag member at the angular rank `jb s` of
the slacked max-norm polygon, an upper bound on the *ambient* successive minimum `λ_{jb s}(Λ_t)`
in terms of the *slope* `phiSlope_s` of the polygon.  This module proves the interface

    `log λ_j(Λ_t) ≤ phiSlope_s + O(1)`      (`j = jb s`),

by combining

* Prop 4(2) for the *Euclidean* slacked polygon (`PhiPolygonCompare`),
* monotonicity of the slopes of a convex polygon,
* the Lipschitz property of the slope operator `Submission.Polygon.largestConvexMinorant` for the sup norm
  (`PolygonLipschitz`), with the sup-norm distance `≤ (1/2) log (choose d j) ≤ d log 2 / 2`
  between the max-norm and the Euclidean slacked data,
* the identification of the flow polygon with the intrinsic polygon of the flowed lattice
  (`TangentCriterion.phiPolygonT_eq_maxphiPolygon`).

Module `Submission.Work.Lattice.SlopeLambda`, namespace `Submission.SlopeLambda`.
-/

noncomputable section
open Module exteriorPower InnerProductGeometry Real
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

namespace Submission.SlopeLambda

open Submission.ExteriorCoordinates
open Submission.MaxNorm
open Submission.MaxNormFlow
open Submission.MaxPhiAccounting
open Submission.MaxPhiPolygon
open Submission.LatticePolygon
open Submission.MaxRankData
open Submission.MaxAttainment
open Submission.UniformBddBelow
open Submission.GraysonData
open Submission.ImageLattice
open Submission.Prop42Upper
open Submission.SuccessiveMinima
open Submission.GraysonLattice
open Submission.MaxFlagMinima
open Submission.FlagMemberCriterion
open Submission.FlowLatticeImage
open Submission.PhiPolygonCompare
open Submission.TangentCriterion
open Submission.FlowDataMax
open Submission.MaxNormPolygon
open Submission.IntrinsicIndex

variable {d : ℕ}

/-- The sup-norm ceiling of the norm-comparability factor between the max-norm and the Euclidean
slacked data. -/
noncomputable def dataCeil (d : ℕ) : ℝ := (d : ℝ) * Real.log 2 / 2

lemma dataCeil_nonneg (d : ℕ) : 0 ≤ dataCeil d := by
  unfold dataCeil; positivity

lemma log_choose_le_dataCeil {j : ℕ} (hj : j ≤ d) :
    (1 / 2) * Real.log (Nat.choose d j) ≤ dataCeil d := by
  have h2 : (Nat.choose d j : ℝ) ≤ (2 : ℝ) ^ d := by
    exact_mod_cast Nat.choose_le_two_pow d j
  have hpos : 0 < (Nat.choose d j : ℝ) := by
    exact_mod_cast Nat.choose_pos hj
  have h := Real.log_le_log hpos h2
  rw [Real.log_pow] at h
  unfold dataCeil
  linarith

/-! ## Congruence of the data along equal lattices -/

lemma maxRankDataSet_congr {Λ Λ' : Submodule ℤ (E d)} (h : Λ = Λ') {j : ℕ} (hj : j ≤ d) :
    maxRankDataSet (d := d) Λ j hj = maxRankDataSet (d := d) Λ' j hj := by
  subst h
  rfl

lemma maxRankData_congr {Λ Λ' : Submodule ℤ (E d)} (h : Λ = Λ') {j : ℕ} (hj : j ≤ d) :
    maxRankData (d := d) Λ j hj = maxRankData (d := d) Λ' j hj := by
  simp only [maxRankData, maxRankDataSet_congr h hj]

lemma maxphiData_congr {Λ Λ' : Submodule ℤ (E d)} (h : Λ = Λ') (A : ℝ) (j : ℕ) :
    maxphiData (d := d) Λ A j = maxphiData (d := d) Λ' A j := by
  unfold maxphiData
  by_cases hj : j ≤ d
  · rw [dif_pos hj, dif_pos hj, maxRankData_congr h hj]
  · rw [dif_neg hj, dif_neg hj]

/-! ## The comparison of the two data functions -/

/-- The Euclidean rank data is at most the max-norm data plus the norm-comparability factor. -/
theorem rankData_le_maxRankData_add {j : ℕ} (hj1 : 1 ≤ j) (hjd : j ≤ d)
    (Λ : Submodule ℤ (E d)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (hΛfin : Module.finrank ℤ Λ = d) (hBdd : BddBelow (maxRankDataSet (d := d) Λ j hjd)) :
    rankData (d := d) Λ j ≤ maxRankData (d := d) Λ j hjd + dataCeil d := by
  obtain ⟨W, hWΛ, hdim, hcov⟩ :=
    exists_subgroup_maxCovol_eq_maxRankData (d := d) (Λ := Λ) hΛfin hj1 hjd hBdd
  have hmem : Real.log (latticeCovol W) ∈ rankDataSet (d := d) Λ j :=
    ⟨W, hWΛ, hdim, rfl⟩
  have hbdd : BddBelow (rankDataSet (d := d) Λ j) :=
    rankData_bddBelow_of_lattice (d := d) Λ hΛfin j hjd
  have h1 : rankData (d := d) Λ j ≤ Real.log (latticeCovol W) := csInf_le hbdd hmem
  have h2 : latticeCovol W ≤ Real.exp (maxRankData (d := d) Λ j hjd +
      (1 / 2) * Real.log (Nat.choose d (subDim W))) :=
    latticeCovol_le_exp_of_maxCovol_le (d := d) (Λ := Λ) (hΛfin := hΛfin) (W := W)
      (hWΛ := hWΛ) (B := maxRankData (d := d) Λ j hjd) (le_of_eq hcov)
  rw [hdim] at h2
  have hW0 : W ≠ ⊥ := by
    intro hbot
    have h0 : subDim W = 0 := by
      rw [hbot]
      exact (subDim_eq_zero_iff_bot (⊥ : Submodule ℤ (E d))).mpr rfl
    omega
  have hpos : 0 < latticeCovol W := latticeCovol_pos (d := d) (Λ := Λ) (X := W) (hXΛ := hWΛ) hW0
  have h3 : Real.log (latticeCovol W) ≤ maxRankData (d := d) Λ j hjd +
      (1 / 2) * Real.log (Nat.choose d j) :=
    (Real.log_le_log hpos h2).trans_eq (Real.log_exp _)
  have h4 := log_choose_le_dataCeil (d := d) (j := j) hjd
  linarith

/-- The pointwise sup-norm distance between the slacked max-norm data and the slacked Euclidean
data is at most `dataCeil`. -/
theorem maxphiData_abs_sub_le (Λ : Submodule ℤ (E d)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (hΛfin : Module.finrank ℤ Λ = d) (A : ℝ) {j : ℕ} (hj : j ≤ d)
    (hBdd : BddBelow (maxRankDataSet (d := d) Λ j hj)) :
    |maxphiData (d := d) Λ A j - Submission.PhiPolygon.phiData (d := d) Λ A j| ≤ dataCeil d := by
  have hmax : maxphiData (d := d) Λ A j =
      maxRankData (d := d) Λ j hj + A * ((j : ℝ) * ((d : ℝ) - (j : ℝ))) := by
    unfold maxphiData
    rw [dif_pos hj]
  have hphi : Submission.PhiPolygon.phiData (d := d) Λ A j =
      rankData (d := d) Λ j + A * ((j : ℝ) * ((d : ℝ) - (j : ℝ))) := rfl
  rw [hmax, hphi]
  rcases Nat.eq_zero_or_pos j with hj0 | hjpos
  · subst hj0
    rw [maxRankData_eq_zero (Nat.zero_le d) rfl, Submission.LatticePolygon.rankData_zero]
    simp [abs_zero, dataCeil_nonneg]
  · have h1 : maxRankData (d := d) Λ j hj ≤ rankData (d := d) Λ j :=
      maxRankData_le_rankData (d := d) Λ hΛfin hj hBdd
    have h2 : rankData (d := d) Λ j ≤ maxRankData (d := d) Λ j hj + dataCeil d :=
      rankData_le_maxRankData_add hjpos hj Λ hΛfin hBdd
    rw [abs_sub_le_iff]
    constructor <;> linarith

/-- The slopes of the slacked max-norm polygon are at most the slopes of the slacked Euclidean
polygon plus `2 · dataCeil`. -/
theorem dslope_phiPolygon_le_maxphiPolygon (Λ : Submodule ℤ (E d)) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (hΛfin : Module.finrank ℤ Λ = d) (A : ℝ)
    (hBdd : ∀ (j : ℕ) (hj : j ≤ d), BddBelow (maxRankDataSet (d := d) Λ j hj))
    {i : ℕ} (hi : i + 1 ≤ d) :
    Submission.Polygon.dslope (Submission.PhiPolygon.phiPolygon (d := d) Λ A) i ≤ Submission.Polygon.dslope (maxphiPolygon (d := d) Λ A) i +
      2 * dataCeil d := by
  have hpoint : ∀ j : ℕ, j ≤ Module.finrank ℤ Λ →
      |maxphiData (d := d) Λ A j - Submission.PhiPolygon.phiData (d := d) Λ A j| ≤ dataCeil d := by
    intro j hj
    rw [hΛfin] at hj
    exact maxphiData_abs_sub_le (d := d) Λ hΛfin A hj (hBdd j hj)
  have h := Submission.Polygon.abs_dslope_largestConvexMinorant_sub_le (d := Module.finrank ℤ Λ)
    (maxphiData (d := d) Λ A) (Submission.PhiPolygon.phiData (d := d) Λ A) (C := dataCeil d) hpoint
    (i := i) (by rw [hΛfin]; exact hi)
  have hmax : Submission.Polygon.largestConvexMinorant (Module.finrank ℤ Λ) (maxphiData (d := d) Λ A) =
      maxphiPolygon (d := d) Λ A := rfl
  have hphi : Submission.Polygon.largestConvexMinorant (Module.finrank ℤ Λ) (Submission.PhiPolygon.phiData (d := d) Λ A) =
      Submission.PhiPolygon.phiPolygon (d := d) Λ A := rfl
  rw [hmax, hphi] at h
  rw [abs_sub_le_iff] at h
  linarith [h.1]



/-! ## The interface -/

/-- `maxData` unfolds to the flow max-norm data (for `1 ≤ j ≤ d`). -/
lemma maxData_eq_flowMaxData {Λ₀ : Submodule ℤ (RD d)} {ℓ : ℕ} {t : ℝ} {j : ℕ}
    (hj1 : 1 ≤ j) (hjd : j ≤ d) :
    maxData (d := d) Λ₀ ℓ t j = flowMaxData (d := d) Λ₀ ℓ t j hjd := by
  have h : (1 ≤ j ∧ j ≤ d) := ⟨hj1, hjd⟩
  simp only [maxData, dif_pos h]

/-- **Auxiliary form** of the interface, with the flowed lattice an explicit parameter equal to
`(imageSpan g).map (a_t)`. -/
theorem log_successiveMinimum_le_phiSlope_aux {ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d)
    (g : RD d ≃ₗ[ℝ] RD d) (t A : ℝ) (hA : 0 ≤ A) {j : ℕ} (hj1 : 1 ≤ j) (hjd : j + 1 ≤ d)
    (Λ : Submodule ℤ (E d)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (hΛfin : Module.finrank ℤ Λ = d)
    (hΛ : Λ = (imageSpan (d := d) g).map ((eFlow (d := d) ℓ t).restrictScalars ℤ))
    (hBdd : ∀ (m : ℕ) (hm : m ≤ d), BddBelow (maxRankDataSet (d := d) Λ m hm)) :
    Real.log (successiveMinimum (E := E d) Λ j) ≤
      phiSlope (d := d) (imageSpan (d := d) g) ℓ A t j +
        (Kconst d + 2 * A * (d : ℝ) ^ 2 + 2 * dataCeil d) := by
  classical
  have hd0 : 0 < d := lt_of_lt_of_le hℓ0 (le_of_lt hℓd)
  have hprop := abs_log_successiveMinimum_sub_dslope_phi_le (d := d) hd0 Λ hΛfin hA hj1
    (le_of_lt hjd)
  have hmono : Submission.Polygon.dslope (Submission.PhiPolygon.phiPolygon (d := d) Λ A) (j - 1) ≤ Submission.Polygon.dslope (Submission.PhiPolygon.phiPolygon (d := d) Λ A) j :=
    Submission.Polygon.dslope_mono (Submission.Polygon.largestConvexMinorant_convex (Module.finrank ℤ Λ) (Submission.PhiPolygon.phiData (d := d) Λ A))
      (i := j - 1) (j := j) (by omega) (by rw [hΛfin]; omega)
  have hlip := dslope_phiPolygon_le_maxphiPolygon (d := d) Λ hΛfin A hBdd (i := j) hjd
  -- the bridge: the slacked max-norm polygon of `Λ` is the flow polygon of `imageSpan g`
  have hdata : ∀ i, maxphiData (d := d) Λ A i =
        Submission.MaxPhiAccounting.phiData (d := d) (imageSpan (d := d) g) ℓ A t i := by
    intro i
    by_cases hi : i ≤ d
    · rcases Nat.eq_zero_or_pos i with hi0 | hipos
      · subst hi0
        have h1 : maxphiData (d := d) Λ A 0 = 0 := by
          rw [maxphiData, dif_pos (Nat.zero_le d), maxRankData_eq_zero (Nat.zero_le d) rfl]
          ring
        have h2 : Submission.MaxPhiAccounting.phiData (d := d) (imageSpan (d := d) g) ℓ A t 0 = 0 := by
          rw [Submission.MaxPhiAccounting.phiData, maxData,
            dif_neg (by omega : ¬ (1 ≤ 0 ∧ 0 ≤ d))]
          ring
        rw [h1, h2]
      · have hkey : maxRankData (d := d) Λ i hi =
            flowMaxData (d := d) (imageSpan (d := d) g) ℓ t i hi := by
          simp only [maxRankData, flowMaxData]
          rw [maxRankDataSet_congr (d := d) hΛ hi,
            flowMaxDataSet_eq_maxRankDataSet (d := d) (Λ₀ := imageSpan (d := d) g) ℓ t i hi]
        rw [maxphiData, dif_pos hi, Submission.MaxPhiAccounting.phiData,
          maxData_eq_flowMaxData (d := d) (Λ₀ := imageSpan (d := d) g) (ℓ := ℓ) (t := t)
            (j := i) hipos hi, hkey]
        ring
    · rw [maxphiData, dif_neg hi, Submission.MaxPhiAccounting.phiData, maxData,
        dif_neg (by omega : ¬ (1 ≤ i ∧ i ≤ d))]
      ring
  have hfun : maxphiData (d := d) Λ A =
      Submission.MaxPhiAccounting.phiData (d := d) (imageSpan (d := d) g) ℓ A t := funext hdata
  have hpoly : ∀ i, maxphiPolygon (d := d) Λ A i =
      phiPolygonT (d := d) (imageSpan (d := d) g) ℓ A t i := by
    intro i
    simp only [maxphiPolygon, phiPolygonT, hΛfin, hfun]
  have hflow : Submission.Polygon.dslope (maxphiPolygon (d := d) Λ A) j =
      phiSlope (d := d) (imageSpan (d := d) g) ℓ A t j := by
    simp only [Submission.Polygon.dslope, phiSlope]
    rw [hpoly j, hpoly (j + 1)]
  have h1 : Real.log (successiveMinimum (E := E d) Λ j) -
      Submission.Polygon.dslope (Submission.PhiPolygon.phiPolygon (d := d) Λ A) (j - 1) ≤
      Kconst d + 2 * A * (d : ℝ) ^ 2 := by
    rw [abs_sub_le_iff] at hprop
    exact hprop.1
  calc Real.log (successiveMinimum (E := E d) Λ j)
      ≤ Submission.Polygon.dslope (Submission.PhiPolygon.phiPolygon (d := d) Λ A) (j - 1) +
          (Kconst d + 2 * A * (d : ℝ) ^ 2) := by linarith [h1]
    _ ≤ Submission.Polygon.dslope (Submission.PhiPolygon.phiPolygon (d := d) Λ A) j +
          (Kconst d + 2 * A * (d : ℝ) ^ 2) := by linarith [hmono]
    _ ≤ Submission.Polygon.dslope (maxphiPolygon (d := d) Λ A) j + 2 * dataCeil d +
          (Kconst d + 2 * A * (d : ℝ) ^ 2) := by linarith [hlip]
    _ = phiSlope (d := d) (imageSpan (d := d) g) ℓ A t j +
          (Kconst d + 2 * A * (d : ℝ) ^ 2 + 2 * dataCeil d) := by
        rw [hflow]; ring

/-- **The successive minimum of the flow lattice is bounded by the slope of the slacked polygon.**
For the §3 flow lattice `Λ_t = (s · a_t)(ℤᵈ) = imageSpan (s.trans (eEquiv ℓ t))` and any
`1 ≤ j`, `j + 1 ≤ d`:

    `log λ_j(Λ_t) ≤ phiSlope (imageSpan s) ℓ A t j + (Kconst d + 2 A d² + 2 dataCeil d)`. -/
theorem log_successiveMinimum_le_phiSlope {ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d)
    (s : RD d ≃ₗᵢ[ℝ] RD d) (t A : ℝ) (hA : 0 ≤ A) {j : ℕ} (hj1 : 1 ≤ j) (hjd : j + 1 ≤ d)
    (hBdd : ∀ (m : ℕ) (hm : m ≤ d),
      BddBelow (maxRankDataSet (d := d) (imageSpan (d := d)
        ((s : RD d ≃ₗ[ℝ] RD d).trans (eEquiv (d := d) ℓ t))) m hm)) :
    Real.log (successiveMinimum (imageSpan (d := d)
        ((s : RD d ≃ₗ[ℝ] RD d).trans (eEquiv (d := d) ℓ t))) j) ≤
      phiSlope (d := d) (imageSpan (d := d) (s : RD d ≃ₗ[ℝ] RD d)) ℓ A t j +
        (Kconst d + 2 * A * (d : ℝ) ^ 2 + 2 * dataCeil d) := by
  have hmap : (imageSpan (d := d) (s : RD d ≃ₗ[ℝ] RD d)).map
      ((eFlow (d := d) ℓ t).restrictScalars ℤ) =
      imageSpan (d := d) ((s : RD d ≃ₗ[ℝ] RD d).trans (eEquiv (d := d) ℓ t)) :=
    imageSpan_map_eq (d := d) (s : RD d ≃ₗ[ℝ] RD d) ℓ t
  exact log_successiveMinimum_le_phiSlope_aux (d := d) hℓ0 hℓd
    (s : RD d ≃ₗ[ℝ] RD d) t A hA hj1 hjd
    (imageSpan (d := d) ((s : RD d ≃ₗ[ℝ] RD d).trans (eEquiv (d := d) ℓ t)))
    (finrank_imageSpan (d := d) _) hmap.symm hBdd

end Submission.SlopeLambda

end
