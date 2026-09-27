import Mathlib
import Submission.Work.Projection.exists_projection_transverse

namespace Work.Projection

open scoped Manifold ContDiff
open Topology MeasureTheory

set_option linter.style.haveILetI false

set_option maxHeartbeats 800000 in
/-- **General position for the projection of an embedded `n`-manifold in `ℝ^{2n+1}`, avoiding a
prescribed null set.**  This is `Work.Projection.exists_projection_transverse` enhanced with an
extra requirement: the direction `u` may be chosen so that its image under
`Work.Projection.pairEquiv n` avoids a given set `Z` of measure zero.  The proof is the same
Sard-type argument, with the union of the two bad sets enlarged by `Z`. -/
theorem exists_projection_transverse_avoiding {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [SecondCountableTopology M]
    (e : M → EuclideanSpace ℝ (Fin (2 * n + 1)))
    (he : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n + 1))))
      ((⊤ : ℕ∞) : WithTop ℕ∞) e)
    (hinj : Function.Injective e)
    (himm : ∀ x, Function.Injective (mfderiv
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n + 1)))) e x))
    (Z : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)))
    (hZ : MeasureTheory.volume Z = 0) :
    ∃ u : EuclideanSpace ℝ (Fin (2 * n)),
      Work.Projection.pairEquiv n u ∉ Z ∧
      (∀ x, Function.Injective (mfderiv
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n))))
        (fun x => Work.Projection.projVec u (e x)) x)) ∧
      ∀ x y, x ≠ y → Work.Projection.projVec u (e x) = Work.Projection.projVec u (e y) →
        (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n))))
          (fun x => Work.Projection.projVec u (e x)) x).range ⊔
        (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n))))
          (fun x => Work.Projection.projVec u (e x)) y).range = ⊤ := by
  rcases isEmpty_or_nonempty M with hM | hM
  · -- the empty manifold: only the avoidance condition is non-trivial
    haveI : IsEmpty M := hM
    obtain ⟨v, hv⟩ : ∃ v, v ∉ Z := by
      by_contra h
      push Not at h
      have hball : (Metric.ball (0 : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) 1) ⊆ Z :=
        fun w _ => h w
      have hpos : 0 < volume
          (Metric.ball (0 : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) 1) :=
        Metric.measure_ball_pos _ 0 (by norm_num)
      have hmono : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) 1)
          ≤ volume Z := measure_mono hball
      rw [hZ] at hmono
      exact absurd (le_antisymm hmono bot_le) (ne_of_gt hpos)
    refine ⟨(pairEquiv n).symm v, ?_, fun x => isEmptyElim x, fun x => isEmptyElim x⟩
    show pairEquiv n ((pairEquiv n).symm v) ∉ Z
    rw [(pairEquiv n).apply_symm_apply]
    exact hv
  · haveI := hM
    obtain ⟨p, hcov⟩ := exists_countable_chart_cover n M
    -- the two bad sets of directions, in the coordinates `ℝ^n × ℝ^n` of the direction space
    set S : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :=
      (⋃ i, immBadCoord e (p i)) ∪ (⋃ i, ⋃ j, transBadCoord e (p i) (p j)) with hS
    have hSnull : volume S = 0 := by
      rw [hS, measure_union_null_iff]
      exact ⟨measure_iUnion_null fun i => volume_image_immBadCoord_eq_zero_smooth e he (p i),
        measure_iUnion_null fun i => measure_iUnion_null fun j =>
          volume_image_pairCrit_eq_zero_smooth e he (p i) (p j)⟩
    -- enlarge the bad set by the prescribed null set `Z`
    have hS'null : volume (S ∪ Z) = 0 := measure_union_null hSnull hZ
    -- so there is a direction outside `S ∪ Z`
    obtain ⟨v, hv⟩ : ∃ v, v ∉ S ∪ Z := by
      by_contra h
      push Not at h
      have hball : (Metric.ball (0 : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) 1) ⊆
          S ∪ Z := fun w _ => h w
      have hpos : 0 < volume
          (Metric.ball (0 : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) 1) :=
        Metric.measure_ball_pos _ 0 (by norm_num)
      have hmono : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) 1)
          ≤ volume (S ∪ Z) := measure_mono hball
      rw [hS'null] at hmono
      exact absurd (le_antisymm hmono bot_le) (ne_of_gt hpos)
    have hvS : v ∉ S := fun h => hv (Set.mem_union_left _ h)
    have hvZ : v ∉ Z := fun h => hv (Set.mem_union_right _ h)
    obtain ⟨u, hu⟩ : ∃ u, pairEquiv n u = v := (pairEquiv n).surjective v
    have hv1 : v ∉ (⋃ i, immBadCoord e (p i)) := fun h => hvS (Set.mem_union_left _ h)
    have hv2 : v ∉ (⋃ i, ⋃ j, transBadCoord e (p i) (p j)) :=
      fun h => hvS (Set.mem_union_right _ h)
    refine ⟨u, ?_, ?_, ?_⟩
    · -- `pairEquiv n u` avoids `Z`
      rw [hu]
      exact hvZ
    · -- `g = projVec u ∘ e` is an immersion
      intro x
      have huBad : u ∉ badImmCharts (n := n) (k := 2*n) e p := by
        intro hmem
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (badImmCharts_subset e he p hmem)
        have : pairEquiv n u ∈ (⋃ i, immBadCoord e (p i)) :=
          Set.mem_iUnion.mpr ⟨i, ⟨u, hi, rfl⟩⟩
        rw [hu] at this
        exact hv1 this
      change Function.Injective (mfderiv (𝓡 n) (𝓡 (2*n)) (⇑(projVec u) ∘ e) x)
      rw [mfderiv_comp_clm (projVec u) e he x]
      exact injective_projVec_comp_mfderiv e he himm hcov huBad x
    · -- every double point is transverse
      intro x y hxy hgxy
      obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp (hcov (Set.mem_univ x))
      obtain ⟨j, hyj⟩ := Set.mem_iUnion.mp (hcov (Set.mem_univ y))
      set a : EuclideanSpace ℝ (Fin n) := (chartAt (EuclideanSpace ℝ (Fin n)) (p i)) x with ha_def
      set b : EuclideanSpace ℝ (Fin n) := (chartAt (EuclideanSpace ℝ (Fin n)) (p j)) y with hb_def
      have hZ' : pairZ e (p i) (p j) (a, b) = e y - e x := by
        simp only [pairZ, ha_def, hb_def]
        rw [chartRep_chart e (p j) y hyj, chartRep_chart e (p i) x hxi]
      have hz0 : e y - e x ≠ 0 := sub_ne_zero_of_ne fun h => hxy (hinj h.symm)
      have hproj : projVec u (e y - e x) = 0 := by
        change projVec u (e x) = projVec u (e y) at hgxy
        rw [map_sub, hgxy, sub_self]
      obtain ⟨c, hc⟩ := (projVec_eq_zero_iff u (e y - e x)).1 hproj
      have hc0 : c ≠ 0 := by
        intro h0
        exact hz0 (by rw [hc, h0, zero_smul])
      have hzlast : (e y - e x) (Fin.last (2*n)) ≠ 0 := by
        rw [hc, last_smul_vVec]
        exact hc0
      have huext : u = extract (e y - e x) := (extract_of_eq_smul_vVec u hc0 hc).symm
      have hu_eq : u = pairDirPt e (p i) (p j) x y := by
        have h1 : pairDirPt e (p i) (p j) x y = extract (pairZ e (p i) (p j) (a, b)) := rfl
        rw [h1, hZ']
        exact huext
      have hv_eq : v = pairParam e (p i) (p j) (a, b) := by
        rw [pairParam, pairDir, hZ', ← huext]
        exact hu.symm
      have hmemDom : (a, b) ∈ pairDom e (p i) (p j) := by
        refine ⟨?_, ?_, ?_⟩
        · exact (chartAt (EuclideanSpace ℝ (Fin n)) (p i)).map_source hxi
        · exact (chartAt (EuclideanSpace ℝ (Fin n)) (p j)).map_source hyj
        · rw [hZ']; exact hzlast
      have hdet : (fderiv ℝ (pairParam e (p i) (p j)) (a, b)).det ≠ 0 := by
        intro hzero
        have : v ∈ (⋃ i, ⋃ j, transBadCoord e (p i) (p j)) :=
          Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨j,
            ⟨(a, b), ⟨hmemDom, hzero⟩, hv_eq.symm⟩⟩⟩
        exact hv2 this
      rw [hu_eq]
      exact range_sup_eq_top_of_det_ne_zero_smooth e he (p i) (p j) x y hxi hyj
        (by rw [show ((chartAt (EuclideanSpace ℝ (Fin n)) (p i)) x,
            (chartAt (EuclideanSpace ℝ (Fin n)) (p j)) y) = (a, b) from rfl, hZ']; exact hzlast) hdet

end Work.Projection
