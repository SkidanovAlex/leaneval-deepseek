import Mathlib
import Submission.Commons.Lattice.SuccessiveMinima.Basic

/-!
# Ball packing at the first successive minimum (shared commons)

First ingredient of the box/fibre-integration route to the UPPER half of Minkowski's second
theorem (Henk, *Successive Minima and Lattice Points*, arXiv math/0204158, §3 eq. (3.2)):

- `measure_biUnion_ball_pairwise`: a finite family of open balls whose centres are pairwise
  at distance at least `2r` are pairwise disjoint, so the measure of their union is
  `S.card * μ (ball 0 r)` (translation invariance of the additive Haar measure
  `addHaar_ball_center`);
- `volume_real_biUnion_ball_lattice`: applied to a lattice `L`, if `2r ≤ λ₁(L)` (the first
  successive minimum — every two distinct lattice points are at distance at least `λ₁`, by
  `first_successiveMinimum_le_of_mem`), the real volume of the union of the open `r`-balls
  around the lattice points of a finite set `S` is `S.card * vol(ball 0 r)`.

(These give `vol(M_q + K₁) = (2q+1)ⁿ vol(K₁)` once `K₁` is the ball of radius `λ₁/2` around
`0` and `M_q` is the box of lattice points.)  Both declarations are Mathlib-only apart from
the successive-minima API import.
-/

noncomputable section

open MeasureTheory MeasureTheory.Measure Set BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Commons.Lattice.Minkowski

/-- Finite union of pairwise `2r`-separated open balls has measure `card · μ (ball 0 r)`
(the packing/volume fact behind the `(2q+1)ⁿ vol(K₁)` computation of Minkowski's second
theorem, Henk §3 eq. (3.2)). -/
lemma measure_biUnion_ball_pairwise {α : Type*} [NormedAddCommGroup α] [MeasurableSpace α]
    [BorelSpace α] (μ : Measure α) [μ.IsAddHaarMeasure] {ι : Type*} (S : Finset ι)
    (x : ι → α) (r : ℝ)
    (h : ∀ ⦃i⦄, i ∈ S → ∀ ⦃j⦄, j ∈ S → i ≠ j → 2 * r ≤ dist (x i) (x j)) :
    μ (⋃ i ∈ S, Metric.ball (x i) r) = S.card * μ (Metric.ball (0 : α) r) := by
  classical
  have hd : Set.PairwiseDisjoint (↑S : Set ι) (fun i : ι => Metric.ball (x i) r) := by
    intro i hi j hj hij
    change Disjoint (Metric.ball (x i) r) (Metric.ball (x j) r)
    rw [Set.disjoint_left]
    intro z hzi hzj
    have ht := dist_triangle (x i) z (x j)
    have hlt : dist (x i) z + dist z (x j) < 2 * r := by
      have ha : dist (x i) z < r := by simpa [dist_comm] using (Metric.mem_ball.mp hzi)
      have hb : dist z (x j) < r := Metric.mem_ball.mp hzj
      nlinarith
    have hdij := h hi hj hij
    nlinarith
  calc
    μ (⋃ i ∈ S, Metric.ball (x i) r) = ∑ i ∈ S, μ (Metric.ball (x i) r) := by
          exact measure_biUnion_finset hd (fun b hb => measurableSet_ball)
    _ = ∑ i ∈ S, μ (Metric.ball (0 : α) r) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact addHaar_ball_center μ (x i) r
    _ = S.card * μ (Metric.ball (0 : α) r) := by
          rw [Finset.sum_const]
          simp [nsmul_eq_mul]

/-- Packing at the first successive minimum: translates of the open ball of radius `r`
around lattice points (with `2r ≤ λ₁(L)`) have total real volume `card · vol(ball r)`. -/
lemma volume_real_biUnion_ball_lattice {n : ℕ} (L : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    [DiscreteTopology L] [IsZLattice ℝ L] (S : Finset L) (r : ℝ)
    (hr₁ : 2 * r ≤ Commons.Lattice.SuccessiveMinima.successiveMinimum L 1) :
    volume.real (⋃ v ∈ S, Metric.ball ((v : EuclideanSpace ℝ (Fin n))) r) =
      S.card * volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r) := by
  classical
  have h : ∀ ⦃i : L⦄, i ∈ S → ∀ ⦃j : L⦄, j ∈ S → i ≠ j →
      2 * r ≤ dist ((i : EuclideanSpace ℝ (Fin n))) ((j : EuclideanSpace ℝ (Fin n))) := by
    intro i hi j hj hij
    have hvw : (i - j : L) ≠ 0 := by
      intro hz
      apply hij
      exact sub_eq_zero.mp hz
    have hmem : Commons.Lattice.SuccessiveMinima.successiveMinimum L 1 ≤
        ‖((i - j : L) : EuclideanSpace ℝ (Fin n))‖ := by
      exact Commons.Lattice.SuccessiveMinima.first_successiveMinimum_le_of_mem (i - j) hvw
    have hdist : dist ((i : EuclideanSpace ℝ (Fin n))) ((j : EuclideanSpace ℝ (Fin n))) =
        ‖((i - j : L) : EuclideanSpace ℝ (Fin n))‖ := by
      simp [dist_eq_norm, sub_eq_add_neg]
    nlinarith [hr₁, hmem]
  have hen := measure_biUnion_ball_pairwise (α := EuclideanSpace ℝ (Fin n)) (μ := volume)
    (S := S) (x := fun v : L => (v : EuclideanSpace ℝ (Fin n))) r h
  have hreal := congrArg ENNReal.toReal hen
  -- hreal : volume.real (⋃ ...) = (S.card * volume (ball 0 r)).toReal
  simpa [measureReal_def, ENNReal.toReal_nsmul, nsmul_eq_mul, mul_comm] using hreal
end Commons.Lattice.Minkowski
