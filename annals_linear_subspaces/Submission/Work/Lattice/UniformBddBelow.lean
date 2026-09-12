import Mathlib
import Submission.Work.Lattice.LatticePolygon
import Submission.Work.Lattice.GraysonLattice
import Submission.Work.Lattice.PresentationLattice
import Submission.Work.Lattice.FamilySpanMinkowski
import Submission.Work.Lattice.SublatticeMinimaGe
import Submission.Commons.Lattice.SuccessiveMinima.positive
import Submission.Commons.Analysis.InnerProductSpace.unitBall_volume_pos
import Submission.Commons.Analysis.InnerProductSpace.unitBall_volume_eq_dim

/-!
# P2/P3-general (b): uniform rank-data boundedness for arbitrary lattices

For EVERY full-rank lattice `Λ ≤ ℝᵈ` the per-rank Grayson data is bounded below:

    `rankData_bddBelow_of_lattice` :  ∀ r ≤ d, BddBelow (rankDataSet Λ r)

The per-rank bound comes from Λ's own successive minima: for a rank-`r` subgroup
`W ≤ Λ` (presented as `W = span ℤ (range u)` with `u : Fin r → E d` `ℝ`-independent by
`PresentationLattice.exists_basis_family_of_le_lattice`),
- Minkowski's second theorem (upper) on the family span
  (`FamilySpanMinkowski.minkowski_second_upper_familySpan`) gives
  `∏_{i≤r} λᵢ(W) · vol(unit ball of V) ≤ 2^{2r} · covol(W)`, `V := realSpan W`;
- the unit-ball volume of `V` equals that of the Euclidean `r`-ball
  (`Commons.unitBall_volume_eq_dim`, isometry invariance) — a positive, rank-only constant
  (`Commons.unitBall_volume_pos`);
- the sublattice bound `λᵢ(W) ≥ λᵢ(Λ)` (`SublatticeMinimaGe.successiveMinimum_ge_of_le_span`)
  and positivity of `λᵢ(Λ)` (`Commons.positive`) give `∏_{i≤r} λᵢ(W) ≥ ∏_{i≤r} λᵢ(Λ) > 0`;

hence `covol(W) ≥ v_r · ∏_{i≤r} λᵢ(Λ) / 2^{2r} > 0`, uniformly over rank-`r` subgroups,
so `log covol(W)` is bounded below by a constant depending only on `Λ` and `r`.

All declarations are Mathlib + Submission (GraysonLattice/PresentationLattice/
FamilySpanMinkowski/SublatticeMinimaGe) + Commons.
-/

noncomputable section

open Set Module Real
open scoped BigOperators ENNReal
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1200000

namespace Submission.UniformBddBelow

open Submission.GraysonData
open Submission.GraysonLattice
open Submission.LatticePolygon
open Submission.SublatticeGe
open Commons.Lattice.SuccessiveMinima

/-- The volume of the unit ball of the Euclidean `r`-space (the rank-only constant `v_r`). -/
noncomputable def unitBallVol (r : ℕ) : ℝ :=
  ENNReal.toReal (MeasureTheory.volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin r)) 1))

/-- The volume of the Euclidean `r`-ball is positive for `0 < r`. -/
lemma unitBallVol_pos {r : ℕ} (hr0 : 0 < r) : 0 < unitBallVol r := by
  classical
  dsimp [unitBallVol]
  have hnt : Nontrivial (EuclideanSpace ℝ (Fin r)) := by
    let e : EuclideanSpace ℝ (Fin r) := (EuclideanSpace.basisFun (Fin r) ℝ) ⟨0, hr0⟩
    refine ⟨e, 0, ?_⟩
    exact (EuclideanSpace.basisFun (Fin r) ℝ).toBasis.linearIndependent.ne_zero ⟨0, hr0⟩
  haveI : Nontrivial (EuclideanSpace ℝ (Fin r)) := hnt
  exact Commons.Analysis.InnerProductSpace.unitBall_volume_pos
    (E := EuclideanSpace ℝ (Fin r))

/-- **Family-span covolume bound, rank-uniform**: for a full-rank lattice `Λ` and an
`ℝ`-independent member family `u : Fin r → E d` (`0 < r ≤ d`), the own-span covolume of
`span ℤ (range u)` is bounded below by `v_r · ∏_{i≤r} λᵢ(Λ) / 2^{2r}` — Minkowski-2 on
the family span + sublattice-minima-ge + isometry-invariance of the unit-ball volume. -/
lemma covol_span_rank_lower_bound {d r : ℕ} (hr0 : 0 < r) (Λ : Submodule ℤ (E d))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] (hΛfin : Module.finrank ℤ Λ = d) (hrd : r ≤ d)
    (u : Fin r → E d) (huΛ : ∀ k : Fin r, u k ∈ (Λ : Set (E d)))
    (hli : LinearIndependent ℝ u) :
    unitBallVol r * (∏ i : Fin r, successiveMinimum Λ (i.val + 1)) ≤
      (2 : ℝ) ^ (2 * r) * latticeCovol (Submodule.span ℤ (Set.range u)) := by
  classical
  have hM := FamilySpanMinkowski.minkowski_second_upper_familySpan (d := d) (r := r)
    hr0 u hli
  -- hM : (∏ λ_i(W))·vol(B_{Vf u}) ≤ 2^{2r}·latticeCovol W  (W := span(range u))
  -- per-index: λ_i(Λ) ≤ λ_i(W)
  have hge : ∀ i : Fin r, successiveMinimum Λ (i.val + 1) ≤
      successiveMinimum (E := E d) (Submodule.span ℤ (Set.range u)) (i.val + 1) := by
    intro i
    have hi1 : 1 ≤ i.val + 1 := by omega
    have hri : i.val + 1 ≤ r := by omega
    exact successiveMinimum_ge_of_le_span Λ u huΛ hli hi1 hri
  have hnonnegΛ : ∀ i : Fin r, 0 ≤ successiveMinimum Λ (i.val + 1) := by
    intro i
    exact successiveMinimum_nonneg Λ (i.val + 1) (by rw [hΛfin]; omega)
  have hprod : (∏ i : Fin r, successiveMinimum Λ (i.val + 1)) ≤
      (∏ i : Fin r, successiveMinimum (E := E d)
        (Submodule.span ℤ (Set.range u)) (i.val + 1)) := by
    exact Finset.prod_le_prod (s := Finset.univ)
      (f := fun i : Fin r => successiveMinimum Λ (i.val + 1))
      (g := fun i : Fin r => successiveMinimum (E := E d)
        (Submodule.span ℤ (Set.range u)) (i.val + 1))
      (by intro i hi; exact hnonnegΛ i)
      (by intro i hi; exact hge i)
  -- unit-ball volume of V := Vf u equals the Euclidean r-ball volume (V has finrank r)
  have hfinV : Module.finrank ℝ (FamilySpanMinkowski.Vf u) = r :=
    FamilySpanMinkowski.finrank_Vf u hli
  have hvol : ENNReal.toReal (MeasureTheory.volume (Metric.closedBall
      (0 : FamilySpanMinkowski.Vf u) 1)) = unitBallVol r := by
    dsimp [unitBallVol]
    exact Commons.Analysis.InnerProductSpace.unitBall_volume_eq_dim (E := FamilySpanMinkowski.Vf u)
      hfinV
  have hvol0 : 0 ≤ ENNReal.toReal (MeasureTheory.volume (Metric.closedBall
      (0 : FamilySpanMinkowski.Vf u) 1)) := ENNReal.toReal_nonneg
  -- rearrange hM: v_r · ∏λ(W) ≤ 2^{2r}·covol(W)
  have hMvol : unitBallVol r * (∏ i : Fin r, successiveMinimum (E := E d)
        (Submodule.span ℤ (Set.range u)) (i.val + 1)) ≤
      (2 : ℝ) ^ (2 * r) * latticeCovol (Submodule.span ℤ (Set.range u)) := by
    have hmul := hM
    rw [hvol] at hmul
    -- hmul : ∏λ·v ≤ pow·covol ; commute to v·∏λ
    simpa [mul_comm] using hmul
  -- v_r · ∏λ(Λ) ≤ v_r · ∏λ(W) then ≤ pow·covol
  calc
    unitBallVol r * (∏ i : Fin r, successiveMinimum Λ (i.val + 1))
        ≤ unitBallVol r * (∏ i : Fin r, successiveMinimum (E := E d)
            (Submodule.span ℤ (Set.range u)) (i.val + 1)) := by
            exact mul_le_mul_of_nonneg_left hprod (unitBallVol_pos hr0).le
    _ ≤ (2 : ℝ) ^ (2 * r) * latticeCovol (Submodule.span ℤ (Set.range u)) := hMvol

/-- **Uniform rank-data boundedness**: for EVERY full-rank lattice `Λ ≤ ℝᵈ`, the
per-rank Grayson data `rankDataSet Λ r` is bounded below for every `r ≤ d`, with the
bound coming from Λ's own successive minima. -/
lemma bddBelow_rankDataSet_zero {d : ℕ} (Λ : Submodule ℤ (E d)) :
    BddBelow (rankDataSet Λ 0) := by
  refine ⟨0, ?_⟩
  intro x hx
  have hx0 : x = 0 := by
    rw [rankDataSet_zero Λ] at hx
    simpa using hx
  rw [hx0]


theorem rankData_bddBelow_of_lattice {d : ℕ} (Λ : Submodule ℤ (E d)) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (hΛfin : Module.finrank ℤ Λ = d) :
    ∀ r : ℕ, r ≤ d → BddBelow (rankDataSet Λ r) := by
  classical
  intro r hrd
  by_cases hr0 : r = 0
  · subst r
    exact bddBelow_rankDataSet_zero Λ
  · have hr : 0 < r := Nat.pos_of_ne_zero hr0
    -- positive factors for the bound: v_r > 0, each λ_i(Λ) > 0
    have hv : 0 < unitBallVol r := unitBallVol_pos hr
    have hlam : ∀ i : Fin r, 0 < successiveMinimum Λ (i.val + 1) := by
      intro i
      exact positive Λ (i.val + 1) (by omega) (by rw [hΛfin]; omega)
    let B : ℝ := Real.log (unitBallVol r) +
        (∑ i : Fin r, Real.log (successiveMinimum Λ (i.val + 1))) - (2 * r) * Real.log 2
    refine ⟨B, ?_⟩
    intro x hx
    rcases hx with ⟨W, hWle, hdim, hxeq⟩
    rw [hxeq]
    -- W ≠ ⊥ (r ≥ 1)
    have hW0 : W ≠ ⊥ := by
      intro hWbot
      have hdim0 : subDim W = 0 := by
        rw [hWbot]
        exact (subDim_eq_zero_iff_bot (⊥ : Submodule ℤ (E d))).mpr rfl
      omega
    -- present W
    rcases exists_basis_family_of_le_lattice (d := d) Λ hΛfin W hWle hW0 with
      ⟨u, hli, hmem, hW_eq⟩
    -- reindex the presentation family (u : Fin (subDim W)) to Fin r (hdim : subDim W = r)
    let e : Fin (subDim W) ≃ Fin r :=
      ((Fin.castOrderIso (n := subDim W) (m := r) hdim).toEquiv)
    let u' : Fin r → E d := fun k => u (e.symm k)
    have hu'_li : LinearIndependent ℝ u' := by
      have hli' : LinearIndependent ℝ (fun k : Fin r => u (e.symm k)) :=
        hli.comp e.symm e.symm.injective
      simpa [u'] using hli'
    have hu'_mem : ∀ k : Fin r, u' k ∈ (Λ : Set (E d)) := by
      intro k
      simpa [u'] using hmem (e.symm k)
    have hspan' : Submodule.span ℤ (Set.range u') = W := by
      have h1 : Submodule.span ℤ (Set.range u') = Submodule.span ℤ (Set.range u) := by
        dsimp [u']
        exact span_int_range_comp_bijective (u := u) (e := e)
      calc
        Submodule.span ℤ (Set.range u') = Submodule.span ℤ (Set.range u) := h1
        _ = W := hW_eq.symm
    -- covolume transports
    have hcv : latticeCovol (Submodule.span ℤ (Set.range u')) = latticeCovol W := by
      exact congrArg latticeCovol hspan'
    -- apply the family-span bound at rank r
    have hbound := covol_span_rank_lower_bound (d := d) (r := r) hr Λ hΛfin hrd u' hu'_mem hu'_li
    have hbnd : unitBallVol r * (∏ i : Fin r, successiveMinimum Λ (i.val + 1)) ≤
        (2 : ℝ) ^ (2 * r) * latticeCovol W := by
      simpa [hcv] using hbound
    -- positivity of the pieces
    have hvpos : 0 < unitBallVol r := unitBallVol_pos hr
    have hprodpos : 0 < (∏ i : Fin r, successiveMinimum Λ (i.val + 1)) := by
      exact Finset.prod_pos (fun i hi => hlam i)
    have hpowpos : 0 < (2 : ℝ) ^ (2 * r) := by positivity
    have hcovpos : 0 < latticeCovol W := by
      -- covol W = covol(span u') = ‖ιMulti u'‖ > 0
      rw [← hcv]
      have hw : latticeCovol (Submodule.span ℤ (Set.range u')) =
          ‖exteriorPower.ιMulti ℝ r u'‖ := by
        simpa using (latticeCovol_span (d := d) (r := r) hr u' hu'_li)
      rw [hw]
      exact norm_pos_iff.mpr
        (Commons.LinearAlgebra.ExteriorPower.iMulti_ne_zero_of_linearIndependent u' hu'_li)
    -- logs of both sides of hbnd
    have hlogb : Real.log (unitBallVol r * (∏ i : Fin r, successiveMinimum Λ (i.val + 1))) ≤
        Real.log ((2 : ℝ) ^ (2 * r) * latticeCovol W) :=
      Real.log_le_log (mul_pos hvpos hprodpos) hbnd
    have hleft : Real.log (unitBallVol r * (∏ i : Fin r, successiveMinimum Λ (i.val + 1))) =
        Real.log (unitBallVol r) + (∑ i : Fin r, Real.log (successiveMinimum Λ (i.val + 1))) := by
      rw [Real.log_mul (ne_of_gt hvpos) (ne_of_gt hprodpos)]
      congr 1
      exact Real.log_prod (s := Finset.univ) (f := fun i : Fin r =>
        successiveMinimum Λ (i.val + 1)) (by intro i hi; exact ne_of_gt (hlam i))
    have hright : Real.log ((2 : ℝ) ^ (2 * r) * latticeCovol W) =
        (2 * (r : ℝ)) * Real.log 2 + Real.log (latticeCovol W) := by
      rw [Real.log_mul (ne_of_gt hpowpos) (ne_of_gt hcovpos)]
      congr 1
      -- log((2:ℝ)^(2*r)) = (2*r : ℕ) as ℝ · log 2
      have hlr := Real.log_pow (x := (2 : ℝ)) (n := 2 * r)
      -- hlr : log (2 ^ (2*r)) = ↑(2*r) * log 2
      rw [hlr]
      rw [Nat.cast_mul]
      norm_num
    have hlogb2 : Real.log (unitBallVol r) +
          (∑ i : Fin r, Real.log (successiveMinimum Λ (i.val + 1))) ≤
        (2 * (r : ℝ)) * Real.log 2 + Real.log (latticeCovol W) := by
      rwa [hleft, hright] at hlogb
    -- conclude B ≤ log(covol W)
    have hfin : B ≤ Real.log (latticeCovol W) := by
      dsimp [B]
      linarith
    exact hfin

end Submission.UniformBddBelow

end
