import Mathlib
import Submission.Work.Drive.BoxParityAux
import Submission.Work.Drive.exists_local_normalForm
import Submission.Work.Drive.graph_region_props
import Submission.Work.Drive.crossing_of_deriv_ne_zero
import Submission.Work.Drive.ChartData
import Submission.Work.Drive.exists_chart_cover
import Submission.Work.Drive.chart_visit_bddAbove

/-!
# The positive in-box arc of a flow line through a boundary zero is bounded

`Work.Drive.in_box_arc_right`: if `b` is a zero of `F` on the boundary of the unit box, `b` lies on
exactly one face `i`, the `i`-th component of the flow field at `b` is nonzero, and the flow line of
`flowField F` through `b` enters the interior of the box for small positive times, then the set of
`t > 0` with the whole arc `(0,t)` inside the box is bounded above.

The proof is a compactness argument on the zero set, which is a compact `1`-dimensional object:

* if the arc stayed in the interior for *all* positive times, the whole flow line would stay in the
  compact zero set `zeroSet F`, hence (by the uniqueness of integral curves) it could not be
  periodic, hence would be injective;
* the zero set is covered by finitely many `ChartData` regions, in each of which the `i`-th
  coordinate is a strictly monotone parameter of the flow line (with speed at least `c > 0`) while
  trapped in the bounded slab `(p i - δ, p i + δ)`;
* injectivity forbids a second visit to the same region, so the flow line lives in finitely many
  bounded time intervals, contradicting "for all positive times".
-/

namespace Work.Drive

open scoped ContDiff Topology
open Set

noncomputable section

/-- A point of `bdyZeros F` has a coordinate equal to `0` or `1`. -/
theorem exists_coord_eq_zero_or_one_of_mem_bdyZeros {m : ℕ} {F : Amb m → Tgt m} {b : Amb m}
    (hb : b ∈ bdyZeros F) : ∃ i : Fin (m + 1), b i = 0 ∨ b i = 1 :=
  (((mem_bdyZeros).mp hb).1).2

/-- A point of `bdyZeros F` lies in the closed unit box. -/
theorem mem_unitBox_of_mem_bdyZeros {m : ℕ} {F : Amb m → Tgt m} {b : Amb m}
    (hb : b ∈ bdyZeros F) : b ∈ Submission.Drive.unitBox m :=
  (((mem_bdyZeros).mp hb).1).1

/-- The zero `b` of `F` is not in the interior of the box. -/
theorem not_mem_interior_unitBox_of_mem_bdyZeros {m : ℕ} {F : Amb m → Tgt m} {b : Amb m}
    (hb : b ∈ bdyZeros F) : b ∉ interior (Submission.Drive.unitBox m) := by
  intro hbint
  obtain ⟨i, hi⟩ := exists_coord_eq_zero_or_one_of_mem_bdyZeros hb
  rw [interior_unitBox m] at hbint
  rcases hi with hi | hi
  · have := (hbint i).1; linarith
  · have := (hbint i).2; linarith

/-- **Injectivity of the flow line through a boundary zero, assuming the whole positive arc is in
the interior of the box.**  If the flow line of `flowField F` through the boundary zero `b` stayed
in the interior of the unit box for all positive times, then it could not be periodic: a period `T`
would bring it back to `b`, which is on the boundary.  By uniqueness of integral curves, a
non-periodic flow line is injective. -/
theorem flowCurve_injective_of_interior {m : ℕ} {F : Amb m → Tgt m} (hF : ContDiff ℝ Ctop F)
    {b : Amb m} (hb : b ∈ bdyZeros F)
    (H : ∀ t : ℝ, 0 < t → flowCurve F hF b t ∈ interior (Submission.Drive.unitBox m)) :
    Function.Injective (flowCurve F hF b) := by
  intro s t hst
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hper : Function.Periodic (flowCurve F hF b) (t - s) := by
      have h := flowCurve_periodic_of_eq (s := s) (t := t) hF hst
      simpa [neg_sub] using h.neg
    have hbT : flowCurve F hF b (t - s) = b := by
      simpa [flowCurve_zero F hF b] using hper 0
    have hbint : b ∈ interior (Submission.Drive.unitBox m) := by
      rw [← hbT]
      exact H (t - s) (sub_pos.mpr hlt)
    exact not_mem_interior_unitBox_of_mem_bdyZeros hb hbint
  · have hper : Function.Periodic (flowCurve F hF b) (s - t) :=
      flowCurve_periodic_of_eq (s := s) (t := t) hF hst
    have hbT : flowCurve F hF b (s - t) = b := by
      simpa [flowCurve_zero F hF b] using hper 0
    have hbint : b ∈ interior (Submission.Drive.unitBox m) := by
      rw [← hbT]
      exact H (s - t) (sub_pos.mpr hlt)
    exact not_mem_interior_unitBox_of_mem_bdyZeros hb hbint

theorem in_box_arc_right {m : ℕ} {F : Work.Drive.Amb m → Work.Drive.Tgt m}
    (hF : ContDiff ℝ Work.Drive.Ctop F)
    (hreg : ∀ x ∈ Submission.Drive.unitBox m, F x = 0 → Function.Surjective (fderiv ℝ F x))
    {b : Work.Drive.Amb m} (hb : b ∈ Work.Drive.bdyZeros F)
    (hface : ∃ i : Fin (m + 1), (b i = 0 ∨ b i = 1) ∧ (∀ j, j ≠ i → b j ∈ Set.Ioo (0 : ℝ) 1) ∧
      Work.Drive.flowField F b i ≠ 0)
    {ε : ℝ} (hε : 0 < ε)
    (hin : ∀ t ∈ Set.Ioo (0 : ℝ) ε,
      Work.Drive.flowCurve F hF b t ∈ interior (Submission.Drive.unitBox m)) :
    ∃ M : ℝ, ∀ t : ℝ,
      (∀ s ∈ Set.Ioo (0 : ℝ) t,
        Work.Drive.flowCurve F hF b s ∈ interior (Submission.Drive.unitBox m)) → t ≤ M := by
  by_contra hM
  push Not at hM
  -- If no bound existed, the whole positive arc would be inside the box.
  have hH : ∀ t : ℝ, 0 < t → flowCurve F hF b t ∈ interior (Submission.Drive.unitBox m) := by
    intro t ht
    obtain ⟨t', ht', htt'⟩ := hM t
    exact ht' t ⟨ht, htt'⟩
  have hγ : ∀ t : ℝ, HasDerivAt (flowCurve F hF b) (flowField F (flowCurve F hF b t)) t :=
    flowCurve_hasDerivAt F hF b
  have hinj : Function.Injective (flowCurve F hF b) := flowCurve_injective_of_interior hF hb hH
  have hF0 : ∀ t : ℝ, F (flowCurve F hF b t) = 0 := by
    intro t
    rw [F_flowCurve hF b t]
    exact ((mem_bdyZeros).mp hb).2
  have hflow : Continuous (flowField F) := (flowField_basic hF).1.continuous
  obtain ⟨N, p, C, hcover⟩ := exists_chart_cover hF hreg
  have hbdd : ∀ j : Fin N, ∃ B : ℝ, ∀ t : ℝ, flowCurve F hF b t ∈ (C j).region → t ≤ B :=
    fun j => chart_visit_bddAbove (C j) hγ hflow hinj hF0
  choose B hB using hbdd
  set S : ℝ := ∑ j : Fin N, max (B j) 0 with hSdef
  have hSnn : 0 ≤ S := by
    rw [hSdef]
    exact Finset.sum_nonneg fun j _ => le_max_right _ _
  -- the point `S + 1 > 0` is in the zero set, hence in some chart region, giving `S + 1 ≤ S`
  have ht0 : 0 < S + 1 := by linarith
  have hmem : flowCurve F hF b (S + 1) ∈ zeroSet F :=
    ⟨interior_subset (hH (S + 1) ht0), hF0 (S + 1)⟩
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hcover hmem)
  have hle : S + 1 ≤ B j := hB j (S + 1) hj
  have hleS : B j ≤ S := by
    rw [hSdef]
    refine le_trans (le_max_left (B j) 0) ?_
    exact Finset.single_le_sum (f := fun j : Fin N => max (B j) 0)
      (fun i _ => le_max_right (B i) 0) (Finset.mem_univ j)
  linarith

end

end Work.Drive
