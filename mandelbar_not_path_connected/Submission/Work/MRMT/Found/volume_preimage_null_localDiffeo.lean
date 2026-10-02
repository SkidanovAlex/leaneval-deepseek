import Mathlib
import Submission.Work.MRMT.Found.lintegral_comp_le_of_isCompact_disjoint

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Found

open MeasureTheory Filter Topology Complex Function
open scoped Topology ENNReal

noncomputable section

/-!
## Null sets pull back to null sets for an orientation-reversing `C¹` map, off a locally discrete set

The target lemma `volume_preimage_null_localDiffeo` says: if `f : ℂ → ℂ` is `C¹` and satisfies the
orientation-reversing condition `‖∂f z‖ < ‖∂̄f z‖` at every point outside a set `S` which meets every
compact set in a finite set, then `f ⁻¹' N` is Lebesgue-null for every Lebesgue-null set `N`.

The mathematical content is the classical *N-property* (Lusin condition) of such a map:

* Off `S` the Jacobian `det (fderiv ℝ f z) = ‖∂f z‖² - ‖∂̄f z‖²` is negative
  (`Work.MRMT.Sobolev.det_fderiv_eq`), in particular non-zero, so `f` is a local diffeomorphism
  there (`lintegral_comp_le_of_isCompact_disjoint` provides the resulting change-of-variables
  inequality on compacts disjoint from `S`);
* `S` meets every compact set in a finite set, hence is countable, hence null;
* the complement of `S` is exhausted by an increasing sequence of compact sets
  `K n = {z | ‖z‖ ≤ n ∧ ∀ y ∈ S, 1/(n+1) ≤ dist z y}` (the condition on the distances expresses
  that `z` stays at distance `≥ 1/(n+1)` from `S`; for `S = ∅` it is vacuous).

Applying the change-of-variables inequality `∫⁻_{z ∈ K} H (f z) ≤ C ∫⁻_{w ∈ f '' K} H w` with
`H = 1_M`, where `M ⊇ N` is a measurable null hull of `N`, shows that `K n ∩ f ⁻¹'N` is null for
every `n`; since `⋃ n K n ∪ S = ℂ` and `S` is null, `f ⁻¹'N` is null.
-/

/-- **Separation from a locally finite set.**  If `S` meets every compact set in finitely many
points, then every point `z ∉ S` has a positive distance from `S`. -/
private lemma exists_pos_le_dist_of_finite_inter_isCompact {S : Set ℂ}
    (hSfin : ∀ K : Set ℂ, IsCompact K → (S ∩ K).Finite) {z : ℂ} (hz : z ∉ S) :
    ∃ r : ℝ, 0 < r ∧ ∀ y ∈ S, r ≤ dist z y := by
  by_cases hne : (S ∩ Metric.closedBall z 1).Nonempty
  · have hfin : (S ∩ Metric.closedBall z 1).Finite := hSfin _ (isCompact_closedBall z 1)
    have hclosed : IsClosed (S ∩ Metric.closedBall z 1) := hfin.isClosed
    have hzT : z ∉ S ∩ Metric.closedBall z 1 := fun h => hz h.1
    have hpos : 0 < Metric.infDist z (S ∩ Metric.closedBall z 1) :=
      (Metric.infDist_pos_iff_notMem_closure hne).mp (by rw [hclosed.closure_eq]; exact hzT)
    refine ⟨min 1 (Metric.infDist z (S ∩ Metric.closedBall z 1)), lt_min one_pos hpos, ?_⟩
    intro y hy
    by_contra hlt
    push Not at hlt
    have hlt1 : dist z y < 1 := lt_of_lt_of_le hlt (min_le_left _ _)
    have hy1 : y ∈ S ∩ Metric.closedBall z 1 :=
      ⟨hy, by rw [Metric.mem_closedBall, dist_comm]; exact le_of_lt hlt1⟩
    have h1 := Metric.infDist_le_dist_of_mem (x := z) hy1
    have h2 : min 1 (Metric.infDist z (S ∩ Metric.closedBall z 1))
        ≤ Metric.infDist z (S ∩ Metric.closedBall z 1) := min_le_right _ _
    linarith
  · refine ⟨1, one_pos, ?_⟩
    intro y hy
    by_contra hlt
    push Not at hlt
    exact hne ⟨y, ⟨hy, by rw [Metric.mem_closedBall, dist_comm]; exact le_of_lt hlt⟩⟩

/-- A set meeting every compact set in finitely many points is countable (exhaust `ℂ` by the
closed balls of integral radius). -/
private lemma countable_of_finite_inter_isCompact {S : Set ℂ}
    (hSfin : ∀ K : Set ℂ, IsCompact K → (S ∩ K).Finite) : S.Countable := by
  have h : (⋃ n : ℕ, S ∩ Metric.closedBall (0 : ℂ) (n : ℝ)).Countable :=
    Set.countable_iUnion (fun n => (hSfin _ (isCompact_closedBall (0 : ℂ) (n : ℝ))).countable)
  have heq : S = ⋃ n : ℕ, S ∩ Metric.closedBall (0 : ℂ) (n : ℝ) := by
    ext z
    simp only [Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro hz
      obtain ⟨n, hn⟩ := exists_nat_ge ‖z‖
      exact ⟨n, hz, by rw [Metric.mem_closedBall, dist_zero_right]; exact hn⟩
    · rintro ⟨n, hz, -⟩
      exact hz
  rw [heq]; exact h

theorem volume_preimage_null_localDiffeo {f : ℂ → ℂ} (hf : ContDiff ℝ 1 f) {S : Set ℂ}
    (hSfin : ∀ K : Set ℂ, IsCompact K → (S ∩ K).Finite)
    (hrev : ∀ z ∉ S, ‖Work.MRMT.dz f z‖ < ‖Work.MRMT.dzbar f z‖) {N : Set ℂ}
    (hN : (MeasureTheory.volume : MeasureTheory.Measure ℂ) N = 0) :
    (MeasureTheory.volume : MeasureTheory.Measure ℂ) (f ⁻¹' N) = 0 := by
  -- enlarge `N` to a measurable null set `M`
  obtain ⟨M, hNM, hMmeas, hM0⟩ := MeasureTheory.exists_measurable_superset_of_null hN
  have hfmeas : Measurable f := hf.continuous.measurable
  -- `S` is countable, hence null
  have hScount : S.Countable := countable_of_finite_inter_isCompact hSfin
  have hSnull : (MeasureTheory.volume : MeasureTheory.Measure ℂ) S = 0 :=
    hScount.measure_zero _
  -- positive distance from `S`, off `S`
  have hsep : ∀ z : ℂ, z ∉ S → ∃ r : ℝ, 0 < r ∧ ∀ y ∈ S, r ≤ dist z y :=
    fun z hz => exists_pos_le_dist_of_finite_inter_isCompact hSfin hz
  -- the compact exhaustion `K n ↑ ℂ \ S`
  set K : ℕ → Set ℂ := fun n => {z : ℂ | ‖z‖ ≤ (n : ℝ)} ∩
    {z : ℂ | ∀ y ∈ S, 1 / ((n : ℝ) + 1) ≤ dist z y} with hKdef
  have hKclosed : ∀ n, IsClosed (K n) := by
    intro n
    refine IsClosed.inter ?_ ?_
    · exact isClosed_Iic.preimage continuous_norm
    · have heq : {z : ℂ | ∀ y ∈ S, 1 / ((n : ℝ) + 1) ≤ dist z y}
          = ⋂ y, ⋂ (_ : y ∈ S), {z : ℂ | 1 / ((n : ℝ) + 1) ≤ dist z y} := by
        ext z; simp
      rw [heq]
      refine isClosed_iInter fun y => isClosed_iInter fun _ => ?_
      exact isClosed_le continuous_const
        (continuous_id.dist (continuous_const : Continuous fun _ : ℂ => y))
  have hKcompact : ∀ n, IsCompact (K n) := by
    intro n
    refine IsCompact.of_isClosed_subset (isCompact_closedBall (0 : ℂ) (n : ℝ)) (hKclosed n) ?_
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hz.1
  have hKdisj : ∀ n, Disjoint (K n) S := by
    intro n
    rw [Set.disjoint_left]
    intro z hz hzS
    have h := hz.2 z hzS
    have hpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
    rw [dist_self] at h
    linarith
  have hKcov : ∀ z : ℂ, z ∉ S → z ∈ ⋃ n, K n := by
    intro z hzS
    obtain ⟨r, hrpos, hr⟩ := hsep z hzS
    obtain ⟨n, hn⟩ := exists_nat_ge (max ‖z‖ (1 / r))
    refine Set.mem_iUnion.mpr ⟨n, ⟨?_, ?_⟩⟩
    · exact le_trans (le_max_left _ _) hn
    · intro y hy
      have hnr : 1 / r ≤ (n : ℝ) := le_trans (le_max_right _ _) hn
      have hstep : 1 / ((n : ℝ) + 1) ≤ 1 / (1 / r) := by
        apply one_div_le_one_div_of_le
        · exact one_div_pos.mpr hrpos
        · linarith
      rw [one_div_one_div] at hstep
      exact le_trans hstep (hr y hy)
  -- each piece `K n ∩ f ⁻¹' N` is null, by the change-of-variables inequality
  have hKnull : ∀ n, (MeasureTheory.volume : MeasureTheory.Measure ℂ) (K n ∩ f ⁻¹' M) = 0 := by
    intro n
    obtain ⟨C, _hCpos, hC⟩ :=
      lintegral_comp_le_of_isCompact_disjoint hf hrev (hKcompact n) (hKdisj n)
    set H : ℂ → ENNReal := M.indicator (fun _ => 1) with hHdef
    have hstep : ∫⁻ z in K n, H (f z) ≤ ENNReal.ofReal C * ∫⁻ w in f '' K n, H w := hC H
    have hRHS : ∫⁻ w in f '' K n, H w = 0 := by
      have h1 : ∫⁻ w in f '' K n, H w ≤ ∫⁻ w, H w := by
        simpa using lintegral_mono_set (μ := (MeasureTheory.volume : MeasureTheory.Measure ℂ))
          (Set.subset_univ (f '' K n))
      have h2 : ∫⁻ w, H w = (MeasureTheory.volume : MeasureTheory.Measure ℂ) M := by
        rw [hHdef]; exact MeasureTheory.lintegral_indicator_one hMmeas
      rw [h2, hM0] at h1
      exact le_antisymm h1 zero_le
    have hL : ∫⁻ z in K n, H (f z)
        = (MeasureTheory.volume : MeasureTheory.Measure ℂ) (K n ∩ f ⁻¹' M) := by
      have hpt : Set.EqOn (fun z => H (f z)) ((f ⁻¹' M).indicator (fun _ => 1)) (K n) := by
        intro z _
        rw [hHdef]
        by_cases h : f z ∈ M <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]
      rw [setLIntegral_congr_fun (hKclosed n).measurableSet hpt,
        MeasureTheory.setLIntegral_indicator (hMmeas.preimage hfmeas) (fun _ => (1 : ENNReal)),
        show (f ⁻¹' M) ∩ K n = K n ∩ f ⁻¹' M from Set.inter_comm _ _,
        MeasureTheory.setLIntegral_one]
    have hle : (MeasureTheory.volume : MeasureTheory.Measure ℂ) (K n ∩ f ⁻¹' M) ≤ 0 :=
      calc (MeasureTheory.volume : MeasureTheory.Measure ℂ) (K n ∩ f ⁻¹' M)
          = ∫⁻ z in K n, H (f z) := hL.symm
        _ ≤ ENNReal.ofReal C * ∫⁻ w in f '' K n, H w := hstep
        _ = ENNReal.ofReal C * 0 := by rw [hRHS]
        _ = 0 := mul_zero _
    exact le_antisymm hle zero_le
  -- `⋃ n K n ∪ S = ℂ`, so `f ⁻¹' N ⊆ f ⁻¹' M` splits into a null part in `S` and a null part
  have hMfin : (MeasureTheory.volume : MeasureTheory.Measure ℂ) (f ⁻¹' M) = 0 := by
    have hcover : f ⁻¹' M ⊆ (f ⁻¹' M ∩ S) ∪ (⋃ n, (K n ∩ f ⁻¹' M)) := by
      intro z hz
      by_cases hzS : z ∈ S
      · exact Or.inl ⟨hz, hzS⟩
      · obtain ⟨n, hn⟩ := Set.mem_iUnion.mp (hKcov z hzS)
        exact Or.inr (Set.mem_iUnion.mpr ⟨n, ⟨hn, hz⟩⟩)
    have h1 : (MeasureTheory.volume : MeasureTheory.Measure ℂ) (⋃ n, (K n ∩ f ⁻¹' M)) = 0 :=
      MeasureTheory.measure_iUnion_null (fun n => hKnull n)
    have h2 : (MeasureTheory.volume : MeasureTheory.Measure ℂ) (f ⁻¹' M ∩ S) = 0 :=
      MeasureTheory.measure_mono_null Set.inter_subset_right hSnull
    have hle : (MeasureTheory.volume : MeasureTheory.Measure ℂ) (f ⁻¹' M) ≤ 0 :=
      calc (MeasureTheory.volume : MeasureTheory.Measure ℂ) (f ⁻¹' M)
          ≤ (MeasureTheory.volume : MeasureTheory.Measure ℂ)
              ((f ⁻¹' M ∩ S) ∪ (⋃ n, (K n ∩ f ⁻¹' M))) :=
            MeasureTheory.measure_mono hcover
        _ ≤ (MeasureTheory.volume : MeasureTheory.Measure ℂ) (f ⁻¹' M ∩ S)
              + (MeasureTheory.volume : MeasureTheory.Measure ℂ) (⋃ n, (K n ∩ f ⁻¹' M)) :=
            MeasureTheory.measure_union_le _ _
        _ = 0 := by rw [h2, h1, add_zero]
    exact le_antisymm hle zero_le
  exact MeasureTheory.measure_mono_null (Set.preimage_mono hNM) hMfin

end

end Work.MRMT.Found
