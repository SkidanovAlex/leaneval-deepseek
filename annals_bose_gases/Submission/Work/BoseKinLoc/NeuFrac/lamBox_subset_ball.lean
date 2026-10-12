import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseKinLoc.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseKinLoc.NeuFrac.lamBox_subset_ball`

The moving box `Λ(u) = ℓu + acube ℓ` of FS `eq:Theta` is contained in the closed ball of
radius `2(|ℓ| + 1)` about its centre `ℓu` (for `ℓ ≤ 0` the box is a point or empty, and the
bound is then trivial).  Consequently `Λ(u)` has finite Lebesgue measure for **every** side
`ℓ`, which is what the integral manipulations on the box need.
-/

noncomputable section

open MeasureTheory Metric
open scoped Topology ENNReal

namespace Work.BoseKinLoc.NeuFrac

open Submission.BoseGases

set_option linter.unusedVariables false

/-- The moving box `Λ(u) = ℓu + acube ℓ` sits in the closed ball of radius `2(|ℓ| + 1)`
about its centre `ℓu`. -/
lemma lamBox_subset_closedBall (ℓ : ℝ) (u : ℝ³) :
    Work.BoseKinLoc.lamBox ℓ u ⊆ closedBall (ℓ • u) (2 * (|ℓ| + 1)) := by
  intro x hx
  have hxc : x - ℓ • u ∈ Submission.BoseGases.acube ℓ := hx
  have hℓ0 : 0 ≤ ℓ := by
    have h0 := hxc 0
    simp only [Set.mem_Icc] at h0
    linarith [h0.1, h0.2]
  rw [mem_closedBall, dist_eq_norm]
  have hsum : ∑ i : Fin 3, ((x - ℓ • u) i) ^ 2 ≤ (2 * (|ℓ| + 1)) ^ 2 := by
    have h1 : ∑ i : Fin 3, ((x - ℓ • u) i) ^ 2 ≤ ∑ _i : Fin 3, (ℓ / 2) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      have hi := hxc i
      simp only [Set.mem_Icc] at hi
      exact sq_le_sq' (by linarith [hi.1] : -(ℓ / 2) ≤ (x - ℓ • u) i) hi.2
    refine le_trans h1 ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [abs_of_nonneg hℓ0]
    nlinarith
  have hnorm : ‖x - ℓ • u‖ ^ 2 ≤ (2 * (|ℓ| + 1)) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simpa using hsum
  have h := sq_le_sq.mp hnorm
  rwa [abs_of_nonneg (norm_nonneg _),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * (|ℓ| + 1))] at h

/-- The moving box has finite Lebesgue measure, for **every** side `ℓ` (it lies in a large
closed ball, which is compact). -/
lemma lamBox_measure_ne_top (ℓ : ℝ) (u : ℝ³) :
    (volume : Measure ℝ³) (Work.BoseKinLoc.lamBox ℓ u) ≠ ∞ := by
  have hsub := lamBox_subset_closedBall ℓ u
  have hfin : (volume : Measure ℝ³) (closedBall (ℓ • u) (2 * (|ℓ| + 1))) < ∞ :=
    (isCompact_closedBall _ _).measure_lt_top
  exact ne_of_lt (lt_of_le_of_lt (measure_mono hsub) hfin)

/-- The moving box is measurable (it is the preimage of the centred cube `acube ℓ` under
the translation `x ↦ x - ℓu`, and `acube ℓ` is a product of closed intervals). -/
lemma measurableSet_lamBox (ℓ : ℝ) (u : ℝ³) :
    MeasurableSet (Work.BoseKinLoc.lamBox ℓ u) := by
  have h : Work.BoseKinLoc.lamBox ℓ u
      = (fun x : ℝ³ => x - ℓ • u) ⁻¹' Submission.BoseGases.acube ℓ := rfl
  rw [h]
  exact (Submission.BoseGases.acube_measurable ℓ).preimage (by fun_prop)

end Work.BoseKinLoc.NeuFrac
