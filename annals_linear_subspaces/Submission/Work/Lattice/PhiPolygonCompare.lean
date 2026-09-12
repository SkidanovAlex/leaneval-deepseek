import Mathlib
import Submission.Work.Lattice.PhiPolygon
import Submission.Work.Lattice.Prop42Upper

/-!
# Comparing the `φ_A`-polygon with the Grayson polygon (P2-general, part 4)

The slacked functional `φ_A(W) = log covol(W) + A·dim W·(d − dim W)` (`A > 0`) is an
*artifact of the Euclidean setting*: the paper's own functional is `log covol` itself
(`A = 0`, no norm-equivalence error), and its HN flag needs `A > 0` for the strict slack
(`PhiSlack`).  The two polygons differ by a **bounded amount**:

    `polygon Λ j ≤ phiPolygon Λ A j ≤ polygon Λ j + A·d²`   (`0 ≤ A`, `j ≤ d`),

because shifting a convex minorant of the slacked data `phiData = rankData + A·q`
(`q j = j(d−j) ≤ d²`) down by `A·d²` produces a convex minorant of `rankData`.

Consequences:

* Prop 4(2) transfers to the slacked polygon with an `O(A·d²)` error:
  `|log λᵢ(Λ) − (phiPolygon Λ A i − phiPolygon Λ A (i−1))| ≤ Kconst d + 2·A·d²`
  (the paper's Prop 4(2) in the Euclidean model, with the slacked polygon that the
  provable HN flag is built from).

All declarations are Mathlib + Submission (`PhiPolygon`, `Prop42Upper`).
-/

noncomputable section
open Set Module Real
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1200000

namespace Submission.PhiPolygonCompare

open Submission.GraysonData
open Submission.GraysonLattice
open Submission.JoinSubmodularity
open Submission.Polygon
open Submission.LatticePolygon
open Submission.PhiSlack
open Submission.PhiPolygon
open Submission.Prop42Upper
open Commons.Lattice.SuccessiveMinima

/-- Subtracting a constant preserves discrete convexity (the slopes are unchanged). -/
lemma discreteConvexOn_sub_const {c : ℕ → ℝ} {d : ℕ} (hc : DiscreteConvexOn c d) (K : ℝ) :
    DiscreteConvexOn (fun i => c i - K) d := by
  intro i hi
  have h := hc i hi
  dsimp only [Submission.Polygon.dslope] at h ⊢
  linarith

/-- **The Grayson polygon lies below the slacked polygon.** -/
theorem polygon_le_phiPolygon {d : ℕ} (Λ : Submodule ℤ (E d)) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (hΛfin : Module.finrank ℤ Λ = d) {A : ℝ} (hA : 0 ≤ A) {j : ℕ}
    (hj : j ≤ d) : polygon Λ j ≤ phiPolygon Λ A j := by
  have hmem : polygon Λ ∈ MinorantSet d (phiData Λ A) := by
    constructor
    · have h := largestConvexMinorant_convex d (rankData Λ)
      have hpoly : polygon Λ = fun i => largestConvexMinorant d (rankData Λ) i := by
        funext i
        dsimp only [polygon]
        rw [hΛfin]
      rw [hpoly]
      exact h
    · intro i hi
      have h1 : polygon Λ i ≤ rankData Λ i := by
        have h := largestConvexMinorant_le_g d (rankData Λ) (i := i) hi
        dsimp only [polygon]
        rw [hΛfin]
        exact h
      have h2 : (0 : ℝ) ≤ A * ((i : ℝ) * ((d : ℝ) - (i : ℝ))) := by
        have hi0 : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg _
        have hid : (i : ℝ) ≤ (d : ℝ) := by exact_mod_cast hi
        exact mul_nonneg hA (mul_nonneg hi0 (by linarith))
      simp only [phiData]
      linarith
  have h := convexMinorant_le_largest d (phiData Λ A) hmem hj
  dsimp only [phiPolygon]
  rw [hΛfin]
  exact h

/-- **The slacked polygon lies at most `A·d²` above the Grayson polygon.** -/
theorem phiPolygon_le_polygon_add {d : ℕ} (Λ : Submodule ℤ (E d)) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (hΛfin : Module.finrank ℤ Λ = d) {A : ℝ} (hA : 0 ≤ A) {j : ℕ}
    (hj : j ≤ d) : phiPolygon Λ A j ≤ polygon Λ j + A * (d : ℝ) ^ 2 := by
  have hmem : (fun i => phiPolygon Λ A i - A * (d : ℝ) ^ 2) ∈ MinorantSet d (rankData Λ) := by
    constructor
    · have h := phiPolygon_convex (d := d) Λ A
      rw [hΛfin] at h
      exact discreteConvexOn_sub_const h _
    · intro i hi
      have h1 : phiPolygon Λ A i ≤ phiData Λ A i :=
        phiPolygon_le_data (d := d) Λ A (by rw [hΛfin]; exact hi)
      simp only [phiData] at h1
      have h2 : A * ((i : ℝ) * ((d : ℝ) - (i : ℝ))) ≤ A * (d : ℝ) ^ 2 := by
        have hi0 : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg _
        have hid : (i : ℝ) ≤ (d : ℝ) := by exact_mod_cast hi
        have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg _
        have ha : (i : ℝ) * (d : ℝ) ≤ (d : ℝ) * (d : ℝ) := mul_le_mul_of_nonneg_right hid hd0
        have hb : 0 ≤ (i : ℝ) * (i : ℝ) := mul_nonneg hi0 hi0
        have hq : (i : ℝ) * ((d : ℝ) - (i : ℝ)) ≤ (d : ℝ) ^ 2 := by nlinarith
        exact mul_le_mul_of_nonneg_left hq hA
      linarith
  have h := convexMinorant_le_largest d (rankData Λ) hmem hj
  have h' : polygon Λ j = largestConvexMinorant d (rankData Λ) j := by
    dsimp only [polygon]
    rw [hΛfin]
  rw [h']
  linarith

/-- **Comparison of the polygons**: `|phiPolygon Λ A j − polygon Λ j| ≤ A·d²`. -/
theorem abs_phiPolygon_sub_polygon_le {d : ℕ} (Λ : Submodule ℤ (E d)) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (hΛfin : Module.finrank ℤ Λ = d) {A : ℝ} (hA : 0 ≤ A) {j : ℕ}
    (hj : j ≤ d) : |phiPolygon Λ A j - polygon Λ j| ≤ A * (d : ℝ) ^ 2 := by
  have h1 := polygon_le_phiPolygon Λ hΛfin hA hj
  have h2 := phiPolygon_le_polygon_add Λ hΛfin hA hj
  have h3 : (0 : ℝ) ≤ A * (d : ℝ) ^ 2 := mul_nonneg hA (sq_nonneg _)
  rw [abs_sub_le_iff]
  exact ⟨by linarith, by linarith⟩

/-- **Prop 4(2) for the slacked polygon**: for a full-rank lattice, `A ≥ 0`, and
`1 ≤ i ≤ d`,

`|log λᵢ(Λ) − (phiPolygon Λ A i − phiPolygon Λ A (i−1))| ≤ Kconst d + 2·A·d²`. -/
theorem abs_log_successiveMinimum_sub_dslope_phi_le {d : ℕ} (hd : 0 < d)
    (Λ : Submodule ℤ (E d)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (hΛfin : Module.finrank ℤ Λ = d) {A : ℝ} (hA : 0 ≤ A) {i : ℕ} (hi1 : 1 ≤ i)
    (hid : i ≤ d) :
    |Real.log (successiveMinimum Λ i) - Submission.Polygon.dslope (phiPolygon Λ A) (i - 1)| ≤
      Kconst d + 2 * A * (d : ℝ) ^ 2 := by
  have hbase := abs_log_successiveMinimum_sub_dslope_le hd Λ hΛfin hi1 hid
  have hds : Submission.Polygon.dslope (polygon Λ) (i - 1) = polygon Λ i - polygon Λ (i - 1) := by
    simp only [Submission.Polygon.dslope]; rw [Nat.sub_add_cancel hi1]
  have hdsp : Submission.Polygon.dslope (phiPolygon Λ A) (i - 1) =
      phiPolygon Λ A i - phiPolygon Λ A (i - 1) := by
    simp only [Submission.Polygon.dslope]; rw [Nat.sub_add_cancel hi1]
  have him1 : i - 1 ≤ d := by omega
  have h1 := abs_phiPolygon_sub_polygon_le Λ hΛfin hA hid
  have h2 := abs_phiPolygon_sub_polygon_le Λ hΛfin hA him1
  have h3 : (0 : ℝ) ≤ A * (d : ℝ) ^ 2 := mul_nonneg hA (sq_nonneg _)
  rw [hds] at hbase
  rw [hdsp]
  have hkey : phiPolygon Λ A i - phiPolygon Λ A (i - 1) =
      (polygon Λ i - polygon Λ (i - 1)) +
        ((phiPolygon Λ A i - polygon Λ i) - (phiPolygon Λ A (i - 1) - polygon Λ (i - 1))) := by
    ring
  rw [hkey]
  have hb : |(phiPolygon Λ A i - polygon Λ i) -
      (phiPolygon Λ A (i - 1) - polygon Λ (i - 1))| ≤ 2 * (A * (d : ℝ) ^ 2) := by
    calc |(phiPolygon Λ A i - polygon Λ i) - (phiPolygon Λ A (i - 1) - polygon Λ (i - 1))|
        ≤ |phiPolygon Λ A i - polygon Λ i| +
            |phiPolygon Λ A (i - 1) - polygon Λ (i - 1)| := by
          have hX : (phiPolygon Λ A i - polygon Λ i) -
                (phiPolygon Λ A (i - 1) - polygon Λ (i - 1)) =
              (phiPolygon Λ A i - polygon Λ i) +
                (-(phiPolygon Λ A (i - 1) - polygon Λ (i - 1))) := by ring
          rw [hX]
          refine le_trans (abs_add_le _ _) ?_
          rw [abs_neg]
      _ ≤ A * (d : ℝ) ^ 2 + A * (d : ℝ) ^ 2 := add_le_add h1 h2
      _ = 2 * (A * (d : ℝ) ^ 2) := by ring
  calc |Real.log (successiveMinimum Λ i) -
        ((polygon Λ i - polygon Λ (i - 1)) +
          ((phiPolygon Λ A i - polygon Λ i) - (phiPolygon Λ A (i - 1) - polygon Λ (i - 1))))|
      ≤ |Real.log (successiveMinimum Λ i) - (polygon Λ i - polygon Λ (i - 1))| +
          |(phiPolygon Λ A i - polygon Λ i) - (phiPolygon Λ A (i - 1) - polygon Λ (i - 1))| := by
        have hX : Real.log (successiveMinimum Λ i) -
              ((polygon Λ i - polygon Λ (i - 1)) +
                ((phiPolygon Λ A i - polygon Λ i) -
                  (phiPolygon Λ A (i - 1) - polygon Λ (i - 1)))) =
            (Real.log (successiveMinimum Λ i) - (polygon Λ i - polygon Λ (i - 1))) +
              (-((phiPolygon Λ A i - polygon Λ i) -
                (phiPolygon Λ A (i - 1) - polygon Λ (i - 1)))) := by ring
        rw [hX]
        refine le_trans (abs_add_le _ _) ?_
        rw [abs_neg]
    _ ≤ Kconst d + 2 * (A * (d : ℝ) ^ 2) := add_le_add hbase hb
    _ = Kconst d + 2 * A * (d : ℝ) ^ 2 := by ring

end Submission.PhiPolygonCompare
