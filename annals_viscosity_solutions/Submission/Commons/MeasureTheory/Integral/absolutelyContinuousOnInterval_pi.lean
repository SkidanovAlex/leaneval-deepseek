import Mathlib.MeasureTheory.Function.AbsolutelyContinuous

namespace Commons.MeasureTheory.Integral

open Filter
open AbsolutelyContinuousOnInterval

/-- For the `L²`-norm on a finite product `PiLp 2 (fun _ : ι => E)` (in particular on
`EuclideanSpace E ι`), the distance between two points is bounded by the sum of the distances of
their coordinates. -/
lemma dist_piLp_two_le_sum {ι : Type*} [Fintype ι] {E : Type*} [SeminormedAddCommGroup E]
    (x y : PiLp 2 (fun _ : ι => E)) :
    dist x y ≤ ∑ i, dist (x.ofLp i) (y.ofLp i) := by
  rw [PiLp.dist_eq_of_L2]
  rw [Real.sqrt_le_left (Finset.sum_nonneg fun i _ => dist_nonneg)]
  exact Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => dist_nonneg)

theorem absolutelyContinuousOnInterval_pi {ι : Type*} [Fintype ι] {E : Type*}
    [NormedAddCommGroup E] {f : ℝ → EuclideanSpace E ι} {a b : ℝ}
    (h : ∀ i, AbsolutelyContinuousOnInterval (fun t => (f t).ofLp i) a b) :
    AbsolutelyContinuousOnInterval f a b := by
  rw [AbsolutelyContinuousOnInterval, Metric.tendsto_nhds]
  intro ε hε
  set l := totalLengthFilter ⊓ 𝓟 (disjWithin a b)
  set n : ℝ := (Fintype.card ι : ℝ) + 1 with hn_def
  have hn : 0 < n := by positivity
  set ε' : ℝ := ε / n with hε'_def
  have hε'pos : 0 < ε' := div_pos hε hn
  have hev : ∀ᶠ E in l, ∀ i, ∑ k ∈ Finset.range E.1,
      dist ((f (E.2 k).1).ofLp i) ((f (E.2 k).2).ofLp i) < ε' := by
    rw [Filter.eventually_all]
    intro i
    have hgi := Metric.tendsto_nhds.mp (h i) ε' hε'pos
    filter_upwards [hgi] with E hE
    rwa [Real.dist_eq, sub_zero,
      abs_of_nonneg (Finset.sum_nonneg fun k _ => dist_nonneg)] at hE
  filter_upwards [hev] with E hE
  have hbound : ∑ k ∈ Finset.range E.1, dist (f (E.2 k).1) (f (E.2 k).2) < ε := by
    calc ∑ k ∈ Finset.range E.1, dist (f (E.2 k).1) (f (E.2 k).2)
        ≤ ∑ k ∈ Finset.range E.1, ∑ i : ι,
            dist ((f (E.2 k).1).ofLp i) ((f (E.2 k).2).ofLp i) :=
          Finset.sum_le_sum fun k _ => dist_piLp_two_le_sum _ _
      _ = ∑ i : ι, ∑ k ∈ Finset.range E.1,
            dist ((f (E.2 k).1).ofLp i) ((f (E.2 k).2).ofLp i) := by
          rw [Finset.sum_comm]
      _ ≤ ∑ i : ι, ε' := Finset.sum_le_sum fun i _ => (hE i).le
      _ = (Fintype.card ι : ℝ) * ε' := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ < ε := by
          rw [hε'_def, ← mul_div_assoc, div_lt_iff₀ hn]
          nlinarith [Nat.cast_nonneg (α := ℝ) (Fintype.card ι), hn_def]
  rw [Real.dist_eq, sub_zero,
    abs_of_nonneg (Finset.sum_nonneg fun k _ => dist_nonneg)]
  exact hbound

end Commons.MeasureTheory.Integral