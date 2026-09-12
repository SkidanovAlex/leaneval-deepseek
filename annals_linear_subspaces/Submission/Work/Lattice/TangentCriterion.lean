import Mathlib
import Submission.Work.Lattice.ActiveBlock
import Submission.Work.Lattice.MaxPhiAccounting
import Submission.Work.Lattice.MaxNormPolygon
import Submission.Work.Lattice.MaxPhiPolygon

/-!
# The tangency criterion for the flag of the §3 flow

`Submission.ActiveBlock` proves the analytic criterion: if a function `g` bounds the level
function `flowLevel` of a fixed wedge from below, touches it at `t`, and is differentiable at `t`
with derivative `r`, then `r` is at least the flow rate `σ_u` of the *first active* block `u`;
consequently the accounting capacity `effPos` at the rank `j` is at most `j − u`.

This module supplies the two remaining ingredients, in the vocabulary of the slacked max-norm
polygon of the §3 flow:

* `flowMaxData_le_flowLevel` — the max-norm data at any time is at most the level function of any
  fixed presentation family (so that the member of the flag is a *witness* of the data at every
  time);
* `phiPolygonT_eq_sum_phiSlope` — the slacked polygon's *level* function at the rank `j` is the
  sum of its first `j` slopes (`c_t(0) = 0` and telescoping), whence
  `hasDerivAt_phiPolygonT`: the good-time hypothesis (differentiability of the slopes) gives the
  differentiability of `x ↦ phiPolygonT x j` with derivative `phiLevelDeriv`;
* **`effPos_le_of_tangent`** — the packaged criterion: for a tight flag member at the angular rank
  `j`, with the data attained at `t` (`hatt`), the polygon tight at `t` (`htight`) and the
  slopes differentiable at `t`, the accounting capacity is at most `j − u`, where `u` is the
  first active block of the member's presentation family.  This is the input of the §3 extraction
  (`Lemma5General.lemma5_first_assertion` supplies `j − u` vectors with `π₊`-dominance).

Module `Submission.Work.Lattice.TangentCriterion`, namespace `Submission.TangentCriterion`.
-/

noncomputable section

open Module exteriorPower InnerProductGeometry Real Filter
open scoped BigOperators Topology
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

namespace Submission.TangentCriterion

open Submission.ExteriorCoordinates
open Submission.DiagonalFlow
open Submission.MaxNorm
open Submission.MaxNormPolygon
open Submission.FlowRateAsymptotic
open Submission.FlowDataMax
open Submission.Polygon
open Submission.MaxPhiAccounting
open Submission.AccountingOneSided
open Submission.AngularRanks
open Submission.MaxPhiPolygon
open Submission.MaxRankData
open Submission.ActiveBlock

variable {d : ℕ}

/-! ## The data is bounded by the level of a witness family -/

/-- **The max-norm data at any time is at most the level function of any fixed presentation
family.** -/
lemma flowMaxData_le_flowLevel {k ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) {hk : k ≤ d}
    (Λ₀ : Submodule ℤ (RD d)) {w : Fin k → RD d} (hwmem : ∀ i, w i ∈ Λ₀)
    (hwli : LinearIndependent ℝ w) {x : ℝ}
    (hbdd : BddBelow (flowMaxDataSet (d := d) Λ₀ ℓ x k hk)) :
    flowMaxData (d := d) Λ₀ ℓ x k hk ≤
      flowLevel (d := d) ℓ hk (exteriorPower.ιMulti ℝ k w) x :=
  csInf_le hbdd ⟨w, hwmem, hwli, rfl⟩

/-! ## The polygon level function is the sum of its slopes -/

/-- **The slacked polygon at the rank `j` is the sum of its first `j` slopes.** -/
lemma phiPolygonT_eq_sum_phiSlope (Λ₀ : Submodule ℤ (RD d)) (ℓ : ℕ) (A : ℝ) (x : ℝ)
    {j : ℕ} (hj : j ≤ d) :
    phiPolygonT (d := d) Λ₀ ℓ A x j =
      ∑ i ∈ Finset.range j, phiSlope (d := d) Λ₀ ℓ A x i := by
  have h0 : phiPolygonT (d := d) Λ₀ ℓ A x 0 = 0 := phiPolygonT_zero (d := d) Λ₀ ℓ A x
  have htel := Finset.sum_range_sub (f := fun i => phiPolygonT (d := d) Λ₀ ℓ A x i) j
  rw [h0, sub_zero] at htel
  rw [← htel]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [phiSlope]
  rfl

/-- **The differentiability of the slopes gives the differentiability of the polygon level.** -/
lemma hasDerivAt_phiPolygonT (Λ₀ : Submodule ℤ (RD d)) (ℓ : ℕ) (A : ℝ) {j : ℕ} (hj : j ≤ d)
    {t : ℝ} (hdiff : ∀ i ∈ Finset.range j,
      DifferentiableAt ℝ (fun x => phiSlope (d := d) Λ₀ ℓ A x i) t) :
    HasDerivAt (fun x => phiPolygonT (d := d) Λ₀ ℓ A x j)
      (∑ i ∈ Finset.range j, phiSlopeDeriv (d := d) Λ₀ ℓ A t i) t := by
  have hsum : HasDerivAt (fun x => ∑ i ∈ Finset.range j, phiSlope (d := d) Λ₀ ℓ A x i)
      (∑ i ∈ Finset.range j, deriv (fun x => phiSlope (d := d) Λ₀ ℓ A x i) t) t := by
    have h := HasDerivAt.sum (u := Finset.range j)
      (A := fun i => fun x => phiSlope (d := d) Λ₀ ℓ A x i)
      (fun i hi => (hdiff i hi).hasDerivAt)
    have hfun : (∑ i ∈ Finset.range j, (fun x => phiSlope (d := d) Λ₀ ℓ A x i)) =
        (fun x => ∑ i ∈ Finset.range j, phiSlope (d := d) Λ₀ ℓ A x i) :=
      funext (fun x => by simp [Finset.sum_apply])
    rwa [hfun] at h
  have hfun : (fun x => phiPolygonT (d := d) Λ₀ ℓ A x j) =
      (fun x => ∑ i ∈ Finset.range j, phiSlope (d := d) Λ₀ ℓ A x i) :=
    funext fun x => phiPolygonT_eq_sum_phiSlope (d := d) Λ₀ ℓ A x hj
  rw [hfun]
  exact hsum

/-! ## The packaged criterion -/

/-- **The tangency criterion for the flag.**  Let `Λ₀` be the §3 lattice (with the max-norm data
bounded below), `w` a presentation family in `Λ₀` of the flag member at the angular rank `j`
(`w i ∈ Λ₀`, `ℝ`-independent).  Assume

* `hatt` — the member *attains* the data at time `t` (`maxData t j = flowLevel w t`);
* `htight` — the slacked polygon is *tight* at `t` and rank `j` (`phiPolygonT t j = phiData t j`);
* `hdiff` — the good-time hypothesis (all slacked slopes differentiable at `t`);
* `hu` — `u` is the first active block of `w` at `t` (so that `j − u` vectors can be extracted);
* `hbs` — the rank `j` is the angular rank of index `s`.

Then the accounting capacity satisfies `effPos s ≤ j − u`. -/
theorem effPos_le_of_tangent {ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) (Λ₀ : Submodule ℤ (RD d))
    (A : ℝ) {t : ℝ} {j : ℕ} (hj1 : 1 ≤ j) (hjd : j ≤ d)
    (hbdd : ∀ x, BddBelow (flowMaxDataSet (d := d) Λ₀ ℓ x j hjd))
    {w : Fin j → RD d} (hwmem : ∀ i, w i ∈ Λ₀) (hwli : LinearIndependent ℝ w)
    (hwne : exteriorPower.ιMulti ℝ j w ≠ 0)
    (hatt : maxData (d := d) Λ₀ ℓ t j =
      flowLevel (d := d) ℓ hjd (exteriorPower.ιMulti ℝ j w) t)
    (htight : phiPolygonT (d := d) Λ₀ ℓ A t j = phiData (d := d) Λ₀ ℓ A t j)
    (hdiff : ∀ i : Fin d, DifferentiableAt ℝ (fun x => phiSlope (d := d) Λ₀ ℓ A x i.val) t)
    {u : ℕ} (hu : IsFirstActiveBlock (d := d) ℓ hjd t (exteriorPower.ιMulti ℝ j w) u)
    {s : ℕ} (hbs : blockStart d (phiPolygonT (d := d) Λ₀ ℓ A t) s = j) :
    effPos d ℓ (fun s => (blockStart d (phiPolygonT (d := d) Λ₀ ℓ A t) s : ℝ))
      (phiLevelDeriv (d := d) Λ₀ ℓ A t (blockStart d (phiPolygonT (d := d) Λ₀ ℓ A t))) s
      ≤ (j : ℝ) - (u : ℝ) := by
  set jb : ℕ → ℕ := fun s => blockStart d (phiPolygonT (d := d) Λ₀ ℓ A t) s with hjb
  -- the derivative of the polygon level function
  have hder : HasDerivAt (fun x => phiPolygonT (d := d) Λ₀ ℓ A x j)
      (∑ i ∈ Finset.range j, phiSlopeDeriv (d := d) Λ₀ ℓ A t i) t :=
    hasDerivAt_phiPolygonT Λ₀ ℓ A hjd
      (fun i hi => hdiff ⟨i, Nat.lt_of_lt_of_le (Finset.mem_range.mp hi) hjd⟩)
  have hjb_s : jb s = j := by rw [hjb]; exact hbs
  have hder' : HasDerivAt (fun x => phiPolygonT (d := d) Λ₀ ℓ A x j)
      (phiLevelDeriv (d := d) Λ₀ ℓ A t jb s) t := by
    rw [phiLevelDeriv, hjb_s]
    exact hder
  -- the shifted level function
  have hg : HasDerivAt
      (fun x => phiPolygonT (d := d) Λ₀ ℓ A x j - A * (j : ℝ) * ((d : ℝ) - (j : ℝ)))
      (phiLevelDeriv (d := d) Λ₀ ℓ A t jb s) t :=
    hder'.sub_const _
  -- the pointwise bound
  have hle : ∀ x, phiPolygonT (d := d) Λ₀ ℓ A x j - A * (j : ℝ) * ((d : ℝ) - (j : ℝ))
      ≤ flowLevel (d := d) ℓ hjd (exteriorPower.ιMulti ℝ j w) x := by
    intro x
    have h1 : phiPolygonT (d := d) Λ₀ ℓ A x j ≤ phiData (d := d) Λ₀ ℓ A x j :=
      largestConvexMinorant_le_g d (phiData (d := d) Λ₀ ℓ A x) hjd
    have h2 : phiData (d := d) Λ₀ ℓ A x j =
        maxData (d := d) Λ₀ ℓ x j + A * (j : ℝ) * ((d : ℝ) - (j : ℝ)) := rfl
    have h3 : maxData (d := d) Λ₀ ℓ x j = flowMaxData (d := d) Λ₀ ℓ x j hjd :=
      maxData_apply_of (d := d) hj1 hjd
    have h4 := flowMaxData_le_flowLevel (d := d) hℓ0 hℓd Λ₀ hwmem hwli (hbdd x)
    linarith
  -- the touching
  have heq : phiPolygonT (d := d) Λ₀ ℓ A t j - A * (j : ℝ) * ((d : ℝ) - (j : ℝ)) =
      flowLevel (d := d) ℓ hjd (exteriorPower.ιMulti ℝ j w) t := by
    have h2 : phiData (d := d) Λ₀ ℓ A t j =
        maxData (d := d) Λ₀ ℓ t j + A * (j : ℝ) * ((d : ℝ) - (j : ℝ)) := rfl
    rw [htight, h2, hatt]
    ring
  -- the criterion
  have hsig : sig (d := d) j ℓ u ≤ phiLevelDeriv (d := d) Λ₀ ℓ A t jb s :=
    sig_le_deriv_of_le_flowLevel hℓ0 hℓd hjd hwne hg hle heq hu
  refine effPos_le_of_sig_le hℓ0 hℓd ?_ ?_ hsig
  · exact hu.1.1
  · exact_mod_cast hbs

/-! ## Congruence of the largest convex minorant, and the identification of the data

The slacked polygon `phiPolygonT Λ₀ ℓ A t` of the flow data and the intrinsic slacked polygon
`maxphiPolygon Λ_t A` of the flowed lattice `Λ_t = Λ₀.map (eFlow t)` have the *same* values
(and hence the same angular ranks), because their data agree rank by rank
(`phiData_eq_maxphiData`). -/

/-- The set of convex minorants only depends on the values of the data on `{0,…,d}`. -/
lemma minorantSet_congr (d : ℕ) {g g' : ℕ → ℝ} (h : ∀ i ≤ d, g i = g' i) :
    MinorantSet d g = MinorantSet d g' := by
  ext c
  constructor <;> intro hc
  · exact ⟨hc.1, fun i hi => (hc.2 i hi).trans (le_of_eq (h i hi))⟩
  · exact ⟨hc.1, fun i hi => (hc.2 i hi).trans (le_of_eq (h i hi).symm)⟩

/-- The largest convex minorant only depends on the values of the data on `{0,…,d}`. -/
lemma largestConvexMinorant_congr (d : ℕ) {g g' : ℕ → ℝ} (h : ∀ i ≤ d, g i = g' i) (i : ℕ) :
    largestConvexMinorant d g i = largestConvexMinorant d g' i := by
  unfold largestConvexMinorant minorantValues
  rw [minorantSet_congr d h]

/-- **The flow data is the intrinsic slacked data of the flowed lattice.** -/
theorem phiData_eq_maxphiData (Λ₀ : Submodule ℤ (RD d)) (ℓ : ℕ) (A : ℝ) {t : ℝ} {j : ℕ}
    (hj1 : 1 ≤ j) (hjd : j ≤ d) :
    phiData (d := d) Λ₀ ℓ A t j =
      maxphiData (d := d) (Λ₀.map ((eFlow (d := d) ℓ t).restrictScalars ℤ)) A j := by
  rw [maxphiData, dif_pos hjd, phiData, maxData_apply_of (d := d) hj1 hjd,
    flowMaxData_eq_maxRankData]
  ring

/-- **The slacked polygon of the flow is the intrinsic slacked polygon of the flowed lattice.** -/
theorem phiPolygonT_eq_maxphiPolygon (Λ₀ : Submodule ℤ (RD d)) (ℓ : ℕ) (A : ℝ) (t : ℝ)
    (hfin : Module.finrank ℤ (Λ₀.map ((eFlow (d := d) ℓ t).restrictScalars ℤ)) = d) (i : ℕ) :
    phiPolygonT (d := d) Λ₀ ℓ A t i =
      maxphiPolygon (d := d) (Λ₀.map ((eFlow (d := d) ℓ t).restrictScalars ℤ)) A i := by
  unfold phiPolygonT maxphiPolygon
  rw [hfin]
  exact largestConvexMinorant_congr d (fun j hj => by
    by_cases hj1 : 1 ≤ j
    · exact phiData_eq_maxphiData (d := d) Λ₀ ℓ A hj1 hj
    · have hj0 : j = 0 := by omega
      rw [maxphiData, dif_pos hj, phiData, maxData_apply_of_not (d := d) (by omega),
        maxRankData_eq_zero (d := d) hj hj0]
      ring) i

end Submission.TangentCriterion

end
