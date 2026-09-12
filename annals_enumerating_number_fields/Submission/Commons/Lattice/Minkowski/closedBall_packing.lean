import Mathlib
import Submission.Commons.Lattice.SuccessiveMinima.Basic

/-!
# Closed-ball packing at the first successive minimum (shared commons)

Boundary-sharpening of `Lattice/Minkowski/ball_packing`: the open/closed-ball boundary has
measure zero (`addHaar_closedBall_eq_addHaar_ball`, `addHaar_sphere` in Mathlib), so the
packing statement holds verbatim for CLOSED balls:

- `volume_real_biUnion_closedBall_pairwise`: a finite family of closed balls whose centres are
  pairwise at distance at least `2r` has real-volume `S.card · vol(closedBall 0 r)` — two
  such closed balls intersect only inside a sphere (`addHaar_sphere` gives measure zero), so
  they are a.e.-disjoint (`measure_biUnion_finset₀`), and each closed ball has the same
  volume as the ball at the origin (closed = open volume by
  `addHaar_closedBall_eq_addHaar_ball`, translation invariance by `addHaar_ball_center`);
- `volume_real_biUnion_closedBall_lattice`: for a lattice `L ≤ EuclideanSpace ℝ (Fin n)` with
  `2r ≤ λ₁(L)`, the real volume of the union of the closed `r`-balls around a finite set of
  lattice points is `S.card * vol(closedBall 0 r)`.

This is the sharp (3.2)-ingredient of Henk's proof of the upper half of Minkowski's second
theorem (`vol(M_q + K₁) = (2q+1)ⁿ vol(K₁)` with `K₁` the closed ball of radius `λ₁/2`).
All declarations are Mathlib-only apart from the successive-minima API import.
-/

noncomputable section

open MeasureTheory MeasureTheory.Measure Set BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Commons.Lattice.Minkowski

abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

lemma volume_real_biUnion_closedBall_pairwise {n : ℕ} (hn : 0 < n) {ι : Type*}
    (S : Finset ι) (x : ι → E n) (r : ℝ)
    (h : ∀ ⦃i⦄, i ∈ S → ∀ ⦃j⦄, j ∈ S → i ≠ j → 2 * r ≤ dist (x i) (x j)) :
    volume.real (⋃ i ∈ S, Metric.closedBall (x i) r) =
      S.card * volume.real (Metric.closedBall (0 : E n) r) := by
  classical
  haveI : Nontrivial (E n) := by
    refine ⟨⟨(EuclideanSpace.basisFun (Fin n) ℝ) ⟨0, hn⟩, 0, ?_⟩⟩
    intro hz
    have hnz : ‖(EuclideanSpace.basisFun (Fin n) ℝ) ⟨0, hn⟩‖ ≠ 0 := by
      rw [(EuclideanSpace.basisFun (Fin n) ℝ).orthonormal.1 ⟨0, hn⟩]
      norm_num
    exact hnz (by rw [hz, norm_zero])
  have hd : (↑S : Set ι).Pairwise
      (Function.onFun (AEDisjoint volume) (fun i : ι => Metric.closedBall (x i) r)) := by
    intro i hi j hj hij
    change AEDisjoint volume (Metric.closedBall (x i) r) (Metric.closedBall (x j) r)
    change volume (Metric.closedBall (x i) r ∩ Metric.closedBall (x j) r) = 0
    have hsub : Metric.closedBall (x i) r ∩ Metric.closedBall (x j) r ⊆ Metric.sphere (x i) r := by
      intro p hp
      have hle_r : dist (x i) p ≤ r := by simpa [dist_comm] using (Metric.mem_closedBall.mp hp.1)
      have hpj' : dist p (x j) ≤ r := Metric.mem_closedBall.mp hp.2
      have hdge : 2 * r ≤ dist (x i) (x j) := h hi hj hij
      have hnotlt : ¬ dist (x i) p < r := by
        intro hpr
        have htri := dist_triangle (x i) p (x j)
        have hab : dist (x i) p + dist p (x j) < 2 * r := by nlinarith
        nlinarith
      have heq : dist (x i) p = r := le_antisymm hle_r (le_of_not_gt hnotlt)
      rw [Metric.mem_sphere]
      simpa [dist_comm] using heq
    exact le_antisymm
      (le_trans (measure_mono hsub) (le_of_eq (addHaar_sphere volume (x i) r)))
      zero_le
  have hnull : ∀ b ∈ S, NullMeasurableSet (Metric.closedBall (x b) r) volume := by
    intro b hb
    exact measurableSet_closedBall.nullMeasurableSet
  have hm : volume (⋃ b ∈ S, Metric.closedBall (x b) r) = ∑ p ∈ S, volume (Metric.closedBall (x p) r) :=
    measure_biUnion_finset₀ hd hnull
  have hsum : (∑ p ∈ S, volume (Metric.closedBall (x p) r)) =
      S.card * volume (Metric.closedBall (0 : E n) r) := by
    calc
      (∑ p ∈ S, volume (Metric.closedBall (x p) r)) = ∑ p ∈ S, volume (Metric.closedBall (0 : E n) r) := by
        apply Finset.sum_congr rfl
        intro p hp
        calc
          volume (Metric.closedBall (x p) r) = volume (Metric.ball (x p) r) := addHaar_closedBall_eq_addHaar_ball volume (x p) r
          _ = volume (Metric.ball (0 : E n) r) := addHaar_ball_center volume (x p) r
          _ = volume (Metric.closedBall (0 : E n) r) := (addHaar_closedBall_eq_addHaar_ball volume (0 : E n) r).symm
      _ = S.card * volume (Metric.closedBall (0 : E n) r) := by
        rw [Finset.sum_const]
        simp [nsmul_eq_mul]
  have hreal := congrArg ENNReal.toReal (hm.trans hsum)
  simpa [measureReal_def, ENNReal.toReal_nsmul, nsmul_eq_mul, mul_comm] using hreal

lemma volume_real_biUnion_closedBall_lattice {n : ℕ} (hn : 0 < n)
    (L : Submodule ℤ (E n)) [DiscreteTopology L] [IsZLattice ℝ L]
    (S : Finset L) (r : ℝ)
    (hr₁ : 2 * r ≤ Commons.Lattice.SuccessiveMinima.successiveMinimum L 1) :
    volume.real (⋃ v ∈ S, Metric.closedBall ((v : E n)) r) =
      S.card * volume.real (Metric.closedBall (0 : E n) r) := by
  classical
  have h : ∀ ⦃i : L⦄, i ∈ S → ∀ ⦃j : L⦄, j ∈ S → i ≠ j →
      2 * r ≤ dist ((i : E n)) ((j : E n)) := by
    intro i hi j hj hij
    have hvw : (i - j : L) ≠ 0 := by
      intro hz
      apply hij
      exact sub_eq_zero.mp hz
    have hmem : Commons.Lattice.SuccessiveMinima.successiveMinimum L 1 ≤
        ‖((i - j : L) : E n)‖ := by
      exact Commons.Lattice.SuccessiveMinima.first_successiveMinimum_le_of_mem (i - j) hvw
    have hdist : dist ((i : E n)) ((j : E n)) = ‖((i - j : L) : E n)‖ := by
      simp [dist_eq_norm, sub_eq_add_neg]
    nlinarith [hr₁, hmem]
  exact volume_real_biUnion_closedBall_pairwise (n := n) hn S (fun v : L => (v : E n)) r h
end Commons.Lattice.Minkowski
