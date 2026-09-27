import Mathlib
import Submission.Work.Whitney.TripleLocusDefs
import Submission.Work.Whitney.TripleLocusSmooth
import Submission.Work.Projection.dimH_image_le_of_surjective
import Submission.Work.Projection.volume_prod_eq_zero_of_dimH_lt
import Submission.Work.Projection.fderiv_tripleParam_range_top
import Submission.Work.Projection.volume_image_immBadCoord_eq_zero_smooth
import Submission.Work.Projection.volume_image_pairCrit_eq_zero_smooth
import Submission.Work.Projection.dimH_badImmCharts
import Submission.Work.Projection.exists_good_direction
import Submission.Work.Projection.exists_countable_chart_cover
import Submission.Work.Projection.compact_embedding
import Submission.Work.Embedding.finite_double_points_of_transverse
import Submission.Work.Whitney.reduce_double_points_abstract

namespace Work.Whitney

open scoped Manifold ContDiff
open Topology MeasureTheory
open Work.Projection

/-- The function `Fin 3 → E` with values `a`, `b`, `c`. -/
noncomputable def tripleVec {n : ℕ} (a b c : EuclideanSpace ℝ (Fin n)) :
    Fin 3 → EuclideanSpace ℝ (Fin n) :=
  ![a, b, c]

@[simp] lemma tripleVec_zero {n : ℕ} (a b c : EuclideanSpace ℝ (Fin n)) :
    tripleVec a b c 0 = a := by simp [tripleVec]

@[simp] lemma tripleVec_one {n : ℕ} (a b c : EuclideanSpace ℝ (Fin n)) :
    tripleVec a b c 1 = b := by simp [tripleVec]

@[simp] lemma tripleVec_two {n : ℕ} (a b c : EuclideanSpace ℝ (Fin n)) :
    tripleVec a b c 2 = c := by simp [tripleVec]

section Main

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]

/-- **A bad triple direction is either a transverse triple point or a direction at which the pair
`(x,y)` fails to be transverse.** -/
theorem tripleBad_subset (e : M → EuclideanSpace ℝ (Fin (2 * n + 1))) (p q r : M) :
    tripleBad e p q r ⊆
      tripleBadTrans e p q r ∪
      ({u | pairEquiv n u ∈ transBadCoord e p q} ∪
        {u | pairEquiv n u ∈ transBadCoord e p r}) := by
  intro u hu
  obtain ⟨x, hxdom, hzero, rfl⟩ := hu
  by_cases hdet : (fderiv ℝ (pairParam e p q) (x.1 0, x.1 1)).det = 0
  · refine Or.inr (Or.inl ?_)
    have hproj : projVec x.2 (pairZ e p q (x.1 0, x.1 1)) = 0 :=
      (tripleParam_eq_zero_iff.mp hzero).1
    have hlast : (pairZ e p q (x.1 0, x.1 1)) (Fin.last (2 * n)) ≠ 0 := hxdom.2.2.2.1
    obtain ⟨c, hc⟩ := (projVec_eq_zero_iff x.2 (pairZ e p q (x.1 0, x.1 1))).1 hproj
    have hc0 : c ≠ 0 := by
      intro h0
      rw [hc, h0, zero_smul] at hlast
      exact hlast rfl
    have hdir : x.2 = pairDir e p q (x.1 0, x.1 1) := by
      show x.2 = extract (pairZ e p q (x.1 0, x.1 1))
      rw [hc, extract_smul_vVec x.2 hc0]
    refine ⟨(x.1 0, x.1 1), ⟨⟨hxdom.1, hxdom.2.1, hlast⟩, hdet⟩, ?_⟩
    show pairParam e p q (x.1 0, x.1 1) = pairEquiv n x.2
    rw [hdir]
    rfl
  · exact Or.inl ⟨x, ⟨hxdom, hdet⟩, hzero, rfl⟩

/-- **The image in the pair coordinates of the transverse triple point locus has Hausdorff
dimension at most `n`.** -/
theorem dimH_pairEquiv_tripleBadTrans_le (hn : 1 ≤ n)
    (e : M → EuclideanSpace ℝ (Fin (2 * n + 1)))
    (he : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n + 1)))) ((⊤ : ℕ∞) : WithTop ℕ∞) e)
    (p q r : M) :
    dimH (pairEquiv n '' tripleBadTrans e p q r) ≤ (n : ENNReal) := by
  have hφ : ∀ x ∈ tripleDomTrans e p q r,
      ContDiffAt ℝ 1 (fun y : (Fin 3 → EuclideanSpace ℝ (Fin n)) ×
        EuclideanSpace ℝ (Fin (2 * n)) => pairEquiv n y.2) x := by
    intro x hx
    have h1 : ContDiff ℝ 1 (fun y : (Fin 3 → EuclideanSpace ℝ (Fin n)) ×
        EuclideanSpace ℝ (Fin (2 * n)) => pairEquiv n y.2) :=
      ((LinearMap.toContinuousLinearMap ((pairEquiv n).toLinearMap)).comp
        (ContinuousLinearMap.snd ℝ ((Fin 3 → EuclideanSpace ℝ (Fin n)))
          (EuclideanSpace ℝ (Fin (2 * n))))).contDiff (n := (1 : ℕ∞ω))
    exact h1.contDiffAt
  have hmain := dimH_image_le_of_surjective (Φ := tripleParam e p q r)
    (D := tripleDomTrans e p q r)
    (fun x hx => contDiffAt_tripleParam e he p q r x hx)
    (fun x hx h0 => LinearMap.range_eq_top.mp (fderiv_tripleParam_range_top e he p q r x hx h0))
    (φ := fun y : (Fin 3 → EuclideanSpace ℝ (Fin n)) × EuclideanSpace ℝ (Fin (2 * n)) =>
      pairEquiv n y.2)
    hφ
  have hset : (fun y : (Fin 3 → EuclideanSpace ℝ (Fin n)) × EuclideanSpace ℝ (Fin (2 * n)) =>
        pairEquiv n y.2) '' (tripleDomTrans e p q r ∩ tripleParam e p q r ⁻¹' {0}) =
      pairEquiv n '' tripleBadTrans e p q r := by
    ext v
    constructor
    · rintro ⟨y, ⟨hyD, hy0⟩, rfl⟩
      exact ⟨y.2, ⟨y, hyD, hy0, rfl⟩, rfl⟩
    · rintro ⟨u, ⟨y, hyD, hy0, hyu⟩, rfl⟩
      refine ⟨y, ⟨hyD, hy0⟩, ?_⟩
      show pairEquiv n y.2 = pairEquiv n u
      rw [hyu]
  have h1 : Module.finrank ℝ ((Fin 3 → EuclideanSpace ℝ (Fin n)) ×
      EuclideanSpace ℝ (Fin (2 * n))) = 5 * n := by
    rw [Module.finrank_prod, Module.finrank_pi_fintype, finrank_euclideanSpace_fin]
    simp
    ring
  have h2 : Module.finrank ℝ (EuclideanSpace ℝ (Fin (2 * n)) ×
      EuclideanSpace ℝ (Fin (2 * n))) = 4 * n := by
    simp only [Module.finrank_prod, finrank_euclideanSpace_fin]
    ring
  calc dimH (pairEquiv n '' tripleBadTrans e p q r)
      = dimH ((fun y : (Fin 3 → EuclideanSpace ℝ (Fin n)) ×
            EuclideanSpace ℝ (Fin (2 * n)) => pairEquiv n y.2) ''
          (tripleDomTrans e p q r ∩ tripleParam e p q r ⁻¹' {0})) := by rw [hset]
    _ ≤ ((Module.finrank ℝ ((Fin 3 → EuclideanSpace ℝ (Fin n)) ×
          EuclideanSpace ℝ (Fin (2 * n))) - Module.finrank ℝ (EuclideanSpace ℝ (Fin (2 * n)) ×
          EuclideanSpace ℝ (Fin (2 * n))) : ℕ) : ENNReal) := hmain
    _ = (n : ENNReal) := by
        rw [h1, h2, show 5 * n - 4 * n = n from by omega]

/-- **The triple point locus is Lebesgue-null in the pair coordinates.** -/
theorem volume_pairEquiv_tripleBadTrans_eq_zero (hn : 1 ≤ n)
    (e : M → EuclideanSpace ℝ (Fin (2 * n + 1)))
    (he : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n + 1)))) ((⊤ : ℕ∞) : WithTop ℕ∞) e)
    (p q r : M) :
    volume (pairEquiv n '' tripleBadTrans e p q r) = 0 :=
  volume_prod_eq_zero_of_dimH_lt (n := n)
    (lt_of_le_of_lt (dimH_pairEquiv_tripleBadTrans_le hn e he p q r)
      (by exact_mod_cast (by omega : n < 2 * n)))

/-- **Existence of a direction whose projection is an immersion with simple transverse double
points.** -/
theorem exists_good_direction (hn : 1 ≤ n) [T2Space M] [SecondCountableTopology M]
    (e : M → EuclideanSpace ℝ (Fin (2 * n + 1)))
    (he : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n + 1)))) ((⊤ : ℕ∞) : WithTop ℕ∞) e)
    (hinj : Function.Injective e)
    (himm : ∀ y, Function.Injective
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n + 1)))) e y)) :
    ∃ u : EuclideanSpace ℝ (Fin (2 * n)),
      (∀ x, Function.Injective
        (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n))))
          (fun z => projVec u (e z)) x)) ∧
      (∀ x y : M, x ≠ y → (fun z => projVec u (e z)) x = (fun z => projVec u (e z)) y →
        (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n))))
          (fun z => projVec u (e z)) x).range ⊔
        (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n))))
          (fun z => projVec u (e z)) y).range = ⊤) ∧
      (∀ x y z : M, (fun z => projVec u (e z)) x = (fun z => projVec u (e z)) y →
        (fun z => projVec u (e z)) y = (fun z => projVec u (e z)) z →
        x = y ∨ y = z ∨ x = z) := by
  rcases isEmpty_or_nonempty M with hM | hM
  · haveI := hM
    exact ⟨0, fun x => isEmptyElim x, fun x => isEmptyElim x, fun x => isEmptyElim x⟩
  · haveI := hM
    obtain ⟨p, hcov⟩ := exists_countable_chart_cover n M
    set S : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :=
      ((⋃ i, immBadCoord e (p i)) ∪ (⋃ i, ⋃ j, transBadCoord e (p i) (p j))) ∪
      (⋃ i, ⋃ j, ⋃ l, pairEquiv n '' tripleBad e (p i) (p j) (p l)) with hS
    have hSnull : volume S = 0 := by
      rw [hS, measure_union_null_iff, measure_union_null_iff]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · exact measure_iUnion_null fun i => volume_image_immBadCoord_eq_zero_smooth e he (p i)
      · exact measure_iUnion_null fun i => measure_iUnion_null fun j =>
          volume_image_pairCrit_eq_zero_smooth e he (p i) (p j)
      · refine measure_iUnion_null fun i => measure_iUnion_null fun j =>
          measure_iUnion_null (fun l => ?_)
        refine measure_mono_null (t := ((pairEquiv n '' tripleBadTrans e (p i) (p j) (p l)) ∪
          transBadCoord e (p i) (p j)) ∪ transBadCoord e (p i) (p l)) ?_ ?_
        · rintro v ⟨u, hu, rfl⟩
          rcases tripleBad_subset e (p i) (p j) (p l) hu with h | h | h
          · exact Or.inl (Or.inl ⟨u, h, rfl⟩)
          · exact Or.inl (Or.inr h)
          · exact Or.inr h
        · rw [measure_union_null_iff, measure_union_null_iff]
          exact ⟨⟨volume_pairEquiv_tripleBadTrans_eq_zero hn e he (p i) (p j) (p l),
            volume_image_pairCrit_eq_zero_smooth e he (p i) (p j)⟩,
            volume_image_pairCrit_eq_zero_smooth e he (p i) (p l)⟩
    obtain ⟨v, hv⟩ : ∃ v, v ∉ S := by
      by_contra h
      push_neg at h
      have hball : Metric.ball (0 : EuclideanSpace ℝ (Fin n) ×
          EuclideanSpace ℝ (Fin n)) 1 ⊆ S := fun w _ => h w
      have hpos : 0 < volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n) ×
          EuclideanSpace ℝ (Fin n)) 1) := Metric.measure_ball_pos _ 0 (by norm_num)
      have hmono : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n) ×
          EuclideanSpace ℝ (Fin n)) 1) ≤ volume S := measure_mono hball
      rw [hSnull] at hmono
      exact absurd (le_antisymm hmono bot_le) (ne_of_gt hpos)
    have hv1 : ∀ i, v ∉ immBadCoord e (p i) := by
      intro i hi
      exact hv (Or.inl (Or.inl (Set.mem_iUnion.mpr ⟨i, hi⟩)))
    have hv2 : ∀ i j, v ∉ transBadCoord e (p i) (p j) := by
      intro i j hij
      exact hv (Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨j, hij⟩⟩)))
    have hv3 : ∀ i j l, v ∉ pairEquiv n '' tripleBad e (p i) (p j) (p l) := by
      intro i j l hijl
      exact hv (Or.inr (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr
        ⟨j, Set.mem_iUnion.mpr ⟨l, hijl⟩⟩⟩))
    refine ⟨(pairEquiv n).symm v, ?_, ?_, ?_⟩
    · -- the projection is an immersion
      intro x
      have hu_bad : (pairEquiv n).symm v ∉ badImmCharts (n := n) (k := 2 * n) e p := by
        intro hmem
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp
          (badImmCharts_subset (n := n) (k := 2 * n) e he p hmem)
        obtain ⟨yw, hyw, hyw2⟩ := hi
        exact hv1 i ⟨immParam e (p i) yw, ⟨yw, hyw, rfl⟩, by rw [hyw2]; simp⟩
      change Function.Injective
        (mfderiv (𝓡 n) (𝓡 (2 * n)) (⇑(projVec ((pairEquiv n).symm v)) ∘ e) x)
      rw [mfderiv_comp_clm (projVec ((pairEquiv n).symm v)) e he x]
      exact injective_projVec_comp_mfderiv (n := n) (k := 2 * n) e he himm hcov hu_bad x
    · -- the double points are transverse
      intro x y hxy hgxy
      obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp (hcov (Set.mem_univ x))
      obtain ⟨j, hyj⟩ := Set.mem_iUnion.mp (hcov (Set.mem_univ y))
      set a : EuclideanSpace ℝ (Fin n) := (chartAt (EuclideanSpace ℝ (Fin n)) (p i)) x
        with ha_def
      set b : EuclideanSpace ℝ (Fin n) := (chartAt (EuclideanSpace ℝ (Fin n)) (p j)) y
        with hb_def
      have hZ : pairZ e (p i) (p j) (a, b) = e y - e x := by
        simp only [pairZ, ha_def, hb_def]
        rw [chartRep_chart e (p j) y hyj, chartRep_chart e (p i) x hxi]
      have hz0 : e y - e x ≠ 0 := sub_ne_zero_of_ne fun h => hxy (hinj h.symm)
      have hproj : projVec ((pairEquiv n).symm v) (e y - e x) = 0 := by
        change projVec ((pairEquiv n).symm v) (e x) = projVec ((pairEquiv n).symm v) (e y)
          at hgxy
        rw [map_sub, hgxy, sub_self]
      obtain ⟨c, hc⟩ := (projVec_eq_zero_iff ((pairEquiv n).symm v) (e y - e x)).1 hproj
      have hc0 : c ≠ 0 := by
        intro h0
        exact hz0 (by rw [hc, h0, zero_smul])
      have hzlast : (e y - e x) (Fin.last (2 * n)) ≠ 0 := by
        rw [hc, last_smul_vVec]
        exact hc0
      have huext : (pairEquiv n).symm v = extract (e y - e x) :=
        (extract_of_eq_smul_vVec ((pairEquiv n).symm v) hc0 hc).symm
      have hu_eq : (pairEquiv n).symm v = pairDirPt e (p i) (p j) x y := by
        have h1 : pairDirPt e (p i) (p j) x y = extract (pairZ e (p i) (p j) (a, b)) := rfl
        rw [h1, hZ]
        exact huext
      have hv_eq : v = pairParam e (p i) (p j) (a, b) := by
        rw [pairParam, pairDir, hZ, ← huext]
        simp
      have hmemDom : (a, b) ∈ pairDom e (p i) (p j) := by
        refine ⟨?_, ?_, ?_⟩
        · exact (chartAt (EuclideanSpace ℝ (Fin n)) (p i)).map_source hxi
        · exact (chartAt (EuclideanSpace ℝ (Fin n)) (p j)).map_source hyj
        · rw [hZ]; exact hzlast
      have hdet : (fderiv ℝ (pairParam e (p i) (p j)) (a, b)).det ≠ 0 := by
        intro hzero
        exact hv2 i j ⟨(a, b), ⟨hmemDom, hzero⟩, hv_eq.symm⟩
      rw [hu_eq]
      exact range_sup_eq_top_of_det_ne_zero_smooth e he (p i) (p j) x y hxi hyj
        (by rw [show ((chartAt (EuclideanSpace ℝ (Fin n)) (p i)) x,
            (chartAt (EuclideanSpace ℝ (Fin n)) (p j)) y) = (a, b) from rfl, hZ]; exact hzlast)
        hdet
    · -- there are no triple points
      intro x y z hxy hyz
      by_contra hcon
      push_neg at hcon
      obtain ⟨hxy_ne, hyz_ne, hxz_ne⟩ := hcon
      have hxz : (fun z => projVec ((pairEquiv n).symm v) (e z)) x =
          (fun z => projVec ((pairEquiv n).symm v) (e z)) z := hxy.trans hyz
      obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp (hcov (Set.mem_univ x))
      obtain ⟨j, hyj⟩ := Set.mem_iUnion.mp (hcov (Set.mem_univ y))
      obtain ⟨l, hzl⟩ := Set.mem_iUnion.mp (hcov (Set.mem_univ z))
      set a : EuclideanSpace ℝ (Fin n) := (chartAt (EuclideanSpace ℝ (Fin n)) (p i)) x
        with ha_def
      set b : EuclideanSpace ℝ (Fin n) := (chartAt (EuclideanSpace ℝ (Fin n)) (p j)) y
        with hb_def
      set c : EuclideanSpace ℝ (Fin n) := (chartAt (EuclideanSpace ℝ (Fin n)) (p l)) z
        with hc_def
      have hZxy : pairZ e (p i) (p j) (a, b) = e y - e x := by
        simp only [pairZ, ha_def, hb_def]
        rw [chartRep_chart e (p j) y hyj, chartRep_chart e (p i) x hxi]
      have hZxz : pairZ e (p i) (p l) (a, c) = e z - e x := by
        simp only [pairZ, ha_def, hc_def]
        rw [chartRep_chart e (p l) z hzl, chartRep_chart e (p i) x hxi]
      have hxy_eq : projVec ((pairEquiv n).symm v) (e x) =
          projVec ((pairEquiv n).symm v) (e y) := hxy
      have hxz_eq : projVec ((pairEquiv n).symm v) (e x) =
          projVec ((pairEquiv n).symm v) (e z) := hxz
      have hprojxy : projVec ((pairEquiv n).symm v) (e y - e x) = 0 := by
        rw [map_sub, hxy_eq, sub_self]
      have hprojxz : projVec ((pairEquiv n).symm v) (e z - e x) = 0 := by
        rw [map_sub, hxz_eq, sub_self]
      obtain ⟨t₁, ht₁⟩ := (projVec_eq_zero_iff ((pairEquiv n).symm v)
        (pairZ e (p i) (p j) (a, b))).1 (by rw [hZxy]; exact hprojxy)
      obtain ⟨t₂, ht₂⟩ := (projVec_eq_zero_iff ((pairEquiv n).symm v)
        (pairZ e (p i) (p l) (a, c))).1 (by rw [hZxz]; exact hprojxz)
      have ht₁0 : t₁ ≠ 0 := by
        intro h0
        have h1 : pairZ e (p i) (p j) (a, b) = 0 := by rw [ht₁, h0, zero_smul]
        have h2 : e y - e x = 0 := by rw [← hZxy]; exact h1
        exact hxy_ne (hinj (sub_eq_zero.mp h2)).symm
      have ht₂0 : t₂ ≠ 0 := by
        intro h0
        have h1 : pairZ e (p i) (p l) (a, c) = 0 := by rw [ht₂, h0, zero_smul]
        have h2 : e z - e x = 0 := by rw [← hZxz]; exact h1
        exact hxz_ne (hinj (sub_eq_zero.mp h2)).symm
      have ht_ne : t₁ ≠ t₂ := by
        intro h
        have h1 : e y - e x = e z - e x := by rw [← hZxy, ← hZxz, ht₁, ht₂, h]
        have h2 : e y = e z := by
          have h3 := congrArg (fun w => w + e x) h1
          simpa using h3
        exact hyz_ne (hinj h2)
      have hlastxy : (pairZ e (p i) (p j) (a, b)) (Fin.last (2 * n)) ≠ 0 := by
        rw [ht₁, last_smul_vVec]; exact ht₁0
      have hlastxz : (pairZ e (p i) (p l) (a, c)) (Fin.last (2 * n)) ≠ 0 := by
        rw [ht₂, last_smul_vVec]; exact ht₂0
      have hlast_ne : (pairZ e (p i) (p j) (a, b)) (Fin.last (2 * n)) ≠
          (pairZ e (p i) (p l) (a, c)) (Fin.last (2 * n)) := by
        rw [ht₁, ht₂, last_smul_vVec, last_smul_vVec]
        exact ht_ne
      have hmem : (tripleVec a b c, (pairEquiv n).symm v) ∈ tripleDom e (p i) (p j) (p l) := by
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · show tripleVec a b c 0 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) (p i)).target
          rw [tripleVec_zero]
          exact (chartAt (EuclideanSpace ℝ (Fin n)) (p i)).map_source hxi
        · show tripleVec a b c 1 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) (p j)).target
          rw [tripleVec_one]
          exact (chartAt (EuclideanSpace ℝ (Fin n)) (p j)).map_source hyj
        · show tripleVec a b c 2 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) (p l)).target
          rw [tripleVec_two]
          exact (chartAt (EuclideanSpace ℝ (Fin n)) (p l)).map_source hzl
        · show (pairZ e (p i) (p j) (tripleVec a b c 0, tripleVec a b c 1))
              (Fin.last (2 * n)) ≠ 0
          rw [tripleVec_zero, tripleVec_one]
          exact hlastxy
        · show (pairZ e (p i) (p l) (tripleVec a b c 0, tripleVec a b c 2))
              (Fin.last (2 * n)) ≠ 0
          rw [tripleVec_zero, tripleVec_two]
          exact hlastxz
        · show (pairZ e (p i) (p j) (tripleVec a b c 0, tripleVec a b c 1))
              (Fin.last (2 * n)) ≠
            (pairZ e (p i) (p l) (tripleVec a b c 0, tripleVec a b c 2)) (Fin.last (2 * n))
          rw [tripleVec_zero, tripleVec_one, tripleVec_two]
          exact hlast_ne
      have hzero : tripleParam e (p i) (p j) (p l)
          (tripleVec a b c, (pairEquiv n).symm v) = 0 := by
        rw [tripleParam_eq_zero_iff]
        constructor
        · show projVec ((pairEquiv n).symm v)
            (pairZ e (p i) (p j) (tripleVec a b c 0, tripleVec a b c 1)) = 0
          rw [tripleVec_zero, tripleVec_one, hZxy]
          exact hprojxy
        · show projVec ((pairEquiv n).symm v)
            (pairZ e (p i) (p l) (tripleVec a b c 0, tripleVec a b c 2)) = 0
          rw [tripleVec_zero, tripleVec_two, hZxz]
          exact hprojxz
      exact hv3 i j l ⟨_, ⟨_, hmem, hzero, rfl⟩, by simp⟩

end Main

/-- **The last geometric input of the compact `n ≥ 3` case**: a smooth immersion of a compact
`n`-manifold into `ℝ^{2n}` in general position, i.e. with finitely many double points, all of
them simple (no value has three preimages) and transverse. -/
theorem exists_simple_transverse_immersion {n : ℕ} (hn : 3 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M] :
    ∃ g : M → EuclideanSpace ℝ (Fin (2 * n)),
      ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧
      (∀ x, Function.Injective
        (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) g x)) ∧
      (Work.Whitney.doubleSet g).Finite ∧
      Work.Whitney.SimpleDP g ∧
      (∀ p : M × M, p ∈ Work.Whitney.doubleSet g →
        (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) g p.1).range ⊔
        (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) g p.2).range = ⊤) := by
  -- Weak Whitney embedding into `ℝ^{2n+1}`, then a generic projection to `ℝ^{2n}`.
  obtain ⟨e, he, hemb, heinj⟩ := Work.Projection.exists_embedding_euclidean_of_compact n (M := M)
  obtain ⟨u, huimm, hutrans, hutriple⟩ :=
    Work.Whitney.exists_good_direction (n := n) (by omega : 1 ≤ n) e he hemb.injective heinj
  let g : M → EuclideanSpace ℝ (Fin (2 * n)) := fun x => projVec u (e x)
  have hg : ContMDiff (𝓡 n) (𝓡 (2 * n)) ∞ g := by
    change ContMDiff (𝓡 n) (𝓡 (2 * n)) ∞ (⇑(projVec u) ∘ e)
    exact contMDiff_comp_clm (projVec u) e he
  have himmg : ∀ x, Function.Injective (mfderiv (𝓡 n) (𝓡 (2 * n)) g x) := fun x => huimm x
  have htransg : ∀ x y : M, x ≠ y → g x = g y →
      (mfderiv (𝓡 n) (𝓡 (2 * n)) g x).range ⊔
        (mfderiv (𝓡 n) (𝓡 (2 * n)) g y).range = ⊤ :=
    fun x y hxy hgxy => hutrans x y hxy hgxy
  have hsimple : SimpleDP g := by
    intro p hp z hz
    obtain ⟨hne, heq⟩ := mem_doubleSet.mp hp
    rcases hutriple z p.1 p.2 hz heq with h | h | h
    · exact Or.inl h
    · exact absurd h hne
    · exact Or.inr h
  exact ⟨g, hg, himmg,
    Work.Embedding.finite_double_points_of_transverse g hg himmg htransg, hsimple,
    fun p hp => htransg p.1 p.2 (mem_doubleSet.mp hp).1 (mem_doubleSet.mp hp).2⟩

end Work.Whitney
