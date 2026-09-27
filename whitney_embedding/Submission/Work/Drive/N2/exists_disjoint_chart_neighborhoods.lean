import Mathlib
import Submission.Work.Drive.Morse
import Submission.Work.Drive.N2.exists_chart_ball_noOtherCritical

namespace Work.Drive.N2

open scoped Manifold ContDiff in
/-- **Disjoint chart neighbourhoods of the critical points.**  Let `f` be a smooth function on a
compact surface all of whose critical points are nondegenerate, and let `p : Fin k → M` be an
injective listing of all its critical points.  Then the `p i` have open neighbourhoods `T i`, each
contained in the chart source at `p i` together with its closure, none of whose closures contains a
critical point of `f` other than its own centre, and with pairwise disjoint closures.

Route (corrected after review).  For each `i`, `Work.Drive.N2.exists_chart_ball_noOtherCritical`
applied to `p i` and the smoothness plus `hnd (p i) (hcrit i)` gives `r i > 0` with
`Metric.closedBall (c i) (r i) ⊆ (e i).target` (where `e i = extChartAt (𝓡 2) (p i)` and `c i = e i
(p i)`) and with no zero of `fderiv ℝ (f ∘ (e i).symm)` in that closed ball other than `c i`.  Put
`S i = (e i).source ∩ (e i) ⁻¹' Metric.ball (c i) (r i / 2)` (open, contains `p i`), so that
`closure (S i) ⊆ (e i).symm '' Metric.closedBall (c i) (r i / 2)`: the right-hand side is compact
(continuous image of a compact ball) and contained in `(e i).source`, whence `closure (S i)` is
contained in `(e i).source` and meets the critical set only in `p i`.  Also, for `j ≠ i`, the
critical point `p j` is not in `closure (S i)`, by the same isolation applied to `e i (p j)` (which
lies at distance `≤ r i / 2 < r i` from `c i`).  Now set `H i = closure (S i)`, and apply the
shrink in `U i = S i \ ⋃_{j ≠ i} H j` (open, since `S i` is open and the union of the compact `H j`
is closed; and `p i ∈ U i`).  Use the Mathlib lemma `IsCompact.exists_isOpen_closure_subset` with
`K = {p i}` and `U = U i` to get `T i` open with `p i ∈ T i` and `closure (T i) ⊆ U i`.  Then
`closure (T i) ⊆ closure (S i)`, so the chart-source, isolation and `hTnd` clauses follow, while
`closure (T i) ∩ H j = ∅` for `j ≠ i` together with `closure (T j) ⊆ H j` gives the disjointness of
the closures. -/
theorem exists_disjoint_chart_neighborhoods {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M] [T2Space M]
    [CompactSpace M] (f : M → ℝ) (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f)
    (hnd : ∀ x, Work.Drive.Morse.IsCritical f x → Work.Drive.Morse.NondegCrit f x)
    {k : ℕ} (p : Fin k → M) (hinj : Function.Injective p)
    (hcrit : ∀ i, Work.Drive.Morse.IsCritical f (p i))
    (hcover : ∀ x, Work.Drive.Morse.IsCritical f x → ∃ i, p i = x) :
    ∃ T : Fin k → Set M, (∀ i, IsOpen (T i)) ∧ (∀ i, p i ∈ T i) ∧
      (∀ i, closure (T i) ⊆ (extChartAt (𝓡 2) (p i)).source) ∧
      (∀ i x, Work.Drive.Morse.IsCritical f x → x ∈ closure (T i) → x = p i) ∧
      (∀ i j, i ≠ j → Disjoint (closure (T i)) (closure (T j))) := by
  classical
  have hex : ∀ i : Fin k, ∃ r : ℝ, 0 < r ∧
      Metric.closedBall (extChartAt (𝓡 2) (p i) (p i)) r ⊆ (extChartAt (𝓡 2) (p i)).target ∧
      ∀ y ∈ Metric.closedBall (extChartAt (𝓡 2) (p i) (p i)) r,
        fderiv ℝ (f ∘ (extChartAt (𝓡 2) (p i)).symm) y = 0 →
          y = extChartAt (𝓡 2) (p i) (p i) :=
    fun i => exists_chart_ball_noOtherCritical f hf (p i) (hnd (p i) (hcrit i))
  choose r hrpos hrtgt hriso using hex
  -- a small chart ball around each critical point
  let S : Fin k → Set M := fun i => (extChartAt (𝓡 2) (p i)).source ∩
    (extChartAt (𝓡 2) (p i)) ⁻¹' Metric.ball (extChartAt (𝓡 2) (p i) (p i)) (r i / 2)
  have hSopen : ∀ i, IsOpen (S i) := fun i =>
    isOpen_extChartAt_preimage' (p i) Metric.isOpen_ball
  have hball_sub : ∀ i, Metric.closedBall (extChartAt (𝓡 2) (p i) (p i)) (r i / 2) ⊆
      (extChartAt (𝓡 2) (p i)).target := fun i =>
    subset_trans (Metric.closedBall_subset_closedBall (le_of_lt (half_lt_self (hrpos i)))) (hrtgt i)
  -- `closure (S i)` sits inside the compact image of the half ball, hence in the chart source
  have hcl_sub_image : ∀ i, closure (S i) ⊆ (extChartAt (𝓡 2) (p i)).symm ''
      Metric.closedBall (extChartAt (𝓡 2) (p i) (p i)) (r i / 2) := by
    intro i
    have hclosed : IsClosed ((extChartAt (𝓡 2) (p i)).symm ''
        Metric.closedBall (extChartAt (𝓡 2) (p i) (p i)) (r i / 2)) :=
      ((isCompact_closedBall _ _).image_of_continuousOn
        ((continuousOn_extChartAt_symm (p i)).mono (hball_sub i))).isClosed
    refine closure_minimal (fun x hx => ⟨extChartAt (𝓡 2) (p i) x,
      Metric.ball_subset_closedBall hx.2, (extChartAt (𝓡 2) (p i)).left_inv hx.1⟩) hclosed
  -- the isolation: `closure (S i)` contains no critical point other than `p i`
  have hiso : ∀ i x, Work.Drive.Morse.IsCritical f x → x ∈ closure (S i) → x = p i := by
    intro i x hxcrit hx
    obtain ⟨y, hy, hyx⟩ := hcl_sub_image i hx
    have hyt : y ∈ (extChartAt (𝓡 2) (p i)).target := hball_sub i hy
    have hxsrc : x ∈ (extChartAt (𝓡 2) (p i)).source := by
      rw [← hyx]; exact (extChartAt (𝓡 2) (p i)).map_target hyt
    have hey : extChartAt (𝓡 2) (p i) x = y := by
      rw [← hyx]; exact (extChartAt (𝓡 2) (p i)).right_inv hyt
    have hzero : fderiv ℝ (f ∘ (extChartAt (𝓡 2) (p i)).symm) y = 0 := by
      rw [← hey]
      exact (isCritical_iff_chartRep f hf (p i) x hxsrc).mp hxcrit
    have hycrit : y ∈ Metric.closedBall (extChartAt (𝓡 2) (p i) (p i)) (r i) :=
      Metric.closedBall_subset_closedBall (le_of_lt (half_lt_self (hrpos i))) hy
    rw [← hyx, hriso i y hycrit hzero]
    exact (extChartAt (𝓡 2) (p i)).left_inv (mem_extChartAt_source (p i))
  let H : Fin k → Set M := fun j => closure (S j)
  let U : Fin k → Set M := fun i => S i \ ⋃ j ∈ ({j : Fin k | j ≠ i} : Set (Fin k)), H j
  have hpU : ∀ i, p i ∈ U i := by
    intro i
    refine ⟨⟨mem_extChartAt_source (p i), Metric.mem_ball_self (half_pos (hrpos i))⟩, ?_⟩
    intro hmem
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq] at hmem
    obtain ⟨j, hji, hpj⟩ := hmem
    exact hji (hinj (hiso j (p i) (hcrit i) hpj)).symm
  have hUopen : ∀ i, IsOpen (U i) := by
    intro i
    exact (hSopen i).sdiff
      (Set.Finite.isClosed_biUnion (Set.toFinite _) (fun j _ => isClosed_closure))
  have hexT : ∀ i, ∃ T : Set M, IsOpen T ∧ p i ∈ T ∧ closure T ⊆ U i := by
    intro i
    have hmem : ({p i} : Set M) ⊆ U i := by
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact hpU i
    obtain ⟨T, hTopen, hTK, hTcl⟩ :=
      (isCompact_singleton (x := p i)).exists_isOpen_closure_subset
        ((hUopen i).mem_nhdsSet.mpr hmem)
    exact ⟨T, hTopen, hTK (Set.mem_singleton (p i)), hTcl⟩
  choose T hTopen hTmem hTcl using hexT
  refine ⟨T, hTopen, hTmem, ?_, ?_, ?_⟩
  · intro i
    exact subset_trans (hTcl i) (fun x hx => hx.1.1)
  · intro i x hxcrit hx
    have hsub : closure (T i) ⊆ closure (S i) :=
      closure_mono (fun y hy => (hTcl i (subset_closure hy)).1)
    exact hiso i x hxcrit (hsub hx)
  · intro i j hij
    have hdisj : Disjoint (closure (T i)) (H j) := by
      rw [Set.disjoint_left]
      intro x hx hxj
      have hxU : x ∈ U i := hTcl i hx
      exact hxU.2 (by
        simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
        exact ⟨j, fun h => hij h.symm, hxj⟩)
    have hHj : closure (T j) ⊆ H j :=
      closure_mono (fun y hy => (hTcl j (subset_closure hy)).1)
    exact hdisj.mono_right hHj

end Work.Drive.N2
