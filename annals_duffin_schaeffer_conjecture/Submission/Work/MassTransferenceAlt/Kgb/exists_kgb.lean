import Mathlib
import Submission.Work.MassTransferenceAlt.Basic
import Submission.Work.MassTransferenceAlt.Greedy.exists_disjoint_subfamily
import Submission.Work.MassTransferenceAlt.Greedy.measure_inter_iUnion_le_six_sum
import Submission.Work.MassTransferenceAlt.Kgb.eps_arith
import Submission.Work.MassTransferenceAlt.Geom.Iv_subset_thickening_of_not_disjoint

namespace Work.MassTransferenceAlt.Kgb

open MeasureTheory Set Metric
open scoped ENNReal NNReal

/-- **The `K_{G,B}` covering lemma** (Beresnevich–Velani, Lemma 1) in `ℝ`, `k = 1`,
`f(r) = r^d`.

Let the enlarged limsup set `LSenl d c ρ` (over indices with positive radius) have full
`1`-dimensional Hausdorff measure on every subinterval of `[0,1]`.  Let `J = Iv B r` be an
interval inside `[0,1]`, let `T` be a finite set of forbidden indices, let `U` be a forbidden
region (any set), and let `δ > 0`, `ε > 0` satisfy `16 δ ≤ r` and `ε ^ d ≤ δ / 2`, with the
measure hypothesis `H¹ (thickening δ U ∩ J) ≤ r / 4`.  Then there is a finite family `F` of
indices such that

* every `i ∈ F` is fresh (`i ∉ T`), has `0 < ρ i ≤ ε`, has its enlarged interval inside `J`,
  and its enlarged interval is disjoint from `U`;
* the enlarged intervals of the members of `F` are pairwise disjoint;
* `r / 16 ≤ ∑_{i ∈ F} (ρ i) ^ d`. -/
theorem exists_kgb (d : ℝ) (hd0 : 0 < d) (c ρ : ℕ → ℝ) (hρ : ∀ i, 0 ≤ ρ i)
    (hρfin : ∀ ε : ℝ, 0 < ε → {i : ℕ | ε ≤ ρ i}.Finite)
    (hfull : ∀ a b : ℝ, 0 ≤ a → b ≤ 1 →
      MeasureTheory.Measure.hausdorffMeasure 1
        (Set.Icc a b ∩ Work.MassTransferenceAlt.LSenl d c ρ)
        = MeasureTheory.Measure.hausdorffMeasure 1 (Set.Icc a b))
    (B r : ℝ) (hr : 0 < r) (hB0 : 0 ≤ B - r) (hB1 : B + r ≤ 1)
    (U : Set ℝ) (δ : ℝ) (hδ : 0 < δ) (hδr : 16 * δ ≤ r)
    (hU : MeasureTheory.Measure.hausdorffMeasure 1
        (Metric.thickening δ U ∩ Work.MassTransferenceAlt.Iv B r) ≤ ENNReal.ofReal (r / 4))
    (T : Finset ℕ) (ε : ℝ) (hε : 0 < ε) (hεδ : ε ^ d ≤ δ / 2) :
    ∃ F : Finset ℕ,
      (∀ i ∈ F, i ∉ T ∧ 0 < ρ i ∧ ρ i ≤ ε) ∧
      (∀ i ∈ F, Work.MassTransferenceAlt.Fenl d c ρ i ⊆ Work.MassTransferenceAlt.Iv B r) ∧
      (∀ i ∈ F, Disjoint (Work.MassTransferenceAlt.Fenl d c ρ i) U) ∧
      (∀ i ∈ F, ∀ j ∈ F, i ≠ j →
        Disjoint (Work.MassTransferenceAlt.Fenl d c ρ i) (Work.MassTransferenceAlt.Fenl d c ρ j)) ∧
      r / 16 ≤ ∑ i ∈ F, (ρ i) ^ d := by
  classical
  -- ## Step 1. The threshold `e = min (ε/2) ((δ/2)^(1/d)/2)` and its arithmetic.
  have harith := eps_arith d δ ε r hd0 hδ hε hr hδr
  set e : ℝ := min (ε / 2) (((δ / 2) ^ (1 / d)) / 2) with he
  have he0 : 0 < e := by rw [he]; exact harith.1
  have heε : e ≤ ε := by rw [he]; exact harith.2.1
  have hed : e ^ d ≤ δ / 2 ^ (d + 1) := by rw [he]; exact harith.2.2.1
  have he8 : 8 * e ^ d ≤ r / 4 := by rw [he]; exact harith.2.2.2
  set m : ℝ := e ^ d with hm
  have hm0 : 0 < m := by rw [hm]; exact Real.rpow_pos_of_pos he0 d
  have hm8 : 8 * m ≤ r / 4 := by rw [hm]; exact he8
  have hmd : m ≤ δ / 2 ^ (d + 1) := by rw [hm]; exact hed
  -- `2 m < δ`, and hence any enlarged interval of radius `≤ e` meeting `U` lies in the
  -- `δ`-thickening of `U`.
  have hmδ : 2 * m < δ := by
    have h4 : 2 * (δ / 2 ^ (d + 1)) = δ / 2 ^ d := by
      have h2 : (2 : ℝ) ^ (d + 1) = 2 ^ d * 2 := by
        rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
      rw [h2]
      have h2d : (2 : ℝ) ^ d ≠ 0 := by positivity
      field_simp
    have h3 : 2 * m ≤ δ / 2 ^ d := by rw [← h4]; linarith
    have h5 : δ / 2 ^ d < δ := by
      rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 2 ^ d)]
      have h2d : (1 : ℝ) < 2 ^ d := Real.one_lt_rpow (by norm_num) hd0
      nlinarith
    linarith
  have hr4 : 4 * m < r := by linarith
  -- ## Step 2. The shrunken interval `J2 = Iv B (r - 4 m)`.
  set J2 : Set ℝ := Iv B (r - 4 * m) with hJ2
  have hrJ2 : 0 < r - 4 * m := by linarith
  have hJ2le : r - 4 * m ≤ r := by linarith
  have hJ2sub : J2 ⊆ Iv B r := by rw [hJ2]; exact Iv_mono hJ2le
  have hJ2meas : MeasureTheory.Measure.hausdorffMeasure 1 J2
      = ENNReal.ofReal (2 * (r - 4 * m)) := by
    rw [hJ2]; exact hausdorffMeasure_one_Iv B (r - 4 * m) (le_of_lt hrJ2)
  have hfull2 : MeasureTheory.Measure.hausdorffMeasure 1 (J2 ∩ LSenl d c ρ)
      = MeasureTheory.Measure.hausdorffMeasure 1 J2 := by
    rw [hJ2]
    exact hfull (B - (r - 4 * m)) (B + (r - 4 * m)) (by linarith) (by linarith)
  -- ## Step 3. The forbidden indices and the bad region.
  set Ab : Set ℕ := {i : ℕ | 0 < ρ i ∧ ρ i ≤ e ∧ ¬ Disjoint (Fenl d c ρ i) U} with hAb
  set B1 : Set ℝ := ⋃ i ∈ Ab, Fenl d c ρ i with hB1
  set G : Set ℝ := (J2 ∩ LSenl d c ρ) \ B1 with hG
  have hB1meas : MeasurableSet B1 := by
    rw [hB1]
    exact MeasurableSet.biUnion (Set.to_countable Ab)
      (fun i _ => (isClosed_Iv (c i) ((ρ i) ^ d)).measurableSet)
  have hB1sub : B1 ⊆ Metric.thickening δ U := by
    intro z hz
    rw [hB1] at hz
    rw [Set.mem_iUnion₂] at hz
    obtain ⟨i, hi, hzF⟩ := hz
    obtain ⟨hi0, hie, hnd⟩ := hi
    have hpd : (ρ i) ^ d ≤ m := by
      rw [hm]
      exact Real.rpow_le_rpow (le_of_lt hi0) hie (le_of_lt hd0)
    exact Work.MassTransferenceAlt.Geom.Iv_subset_thickening_of_not_disjoint (Real.rpow_nonneg (hρ i) d)
      (by linarith) hnd hzF
  -- The measure of the exceptional set `B1 ∩ J` is at most `r/4`.
  have hXfin : MeasureTheory.Measure.hausdorffMeasure 1 ((J2 ∩ LSenl d c ρ) ∩ B1) ≠ ⊤ := by
    have hle : MeasureTheory.Measure.hausdorffMeasure 1 ((J2 ∩ LSenl d c ρ) ∩ B1)
        ≤ ENNReal.ofReal (2 * (r - 4 * m)) := by
      refine le_trans (measure_mono ?_) (le_of_eq hJ2meas)
      exact Set.inter_subset_left.trans Set.inter_subset_left
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  have hXle : MeasureTheory.Measure.hausdorffMeasure 1 ((J2 ∩ LSenl d c ρ) ∩ B1)
      ≤ ENNReal.ofReal (r / 4) := by
    refine le_trans (measure_mono ?_) hU
    rintro z ⟨hz1, hz2⟩
    exact ⟨hB1sub hz2, hJ2sub hz1.1⟩
  have hGadd : MeasureTheory.Measure.hausdorffMeasure 1 G
      + MeasureTheory.Measure.hausdorffMeasure 1 ((J2 ∩ LSenl d c ρ) ∩ B1)
      = MeasureTheory.Measure.hausdorffMeasure 1 (J2 ∩ LSenl d c ρ) := by
    rw [hG]
    exact measure_sdiff_add_inter _ hB1meas
  have hYge : ENNReal.ofReal (3 * r / 2)
      ≤ MeasureTheory.Measure.hausdorffMeasure 1 (J2 ∩ LSenl d c ρ) := by
    rw [hfull2, hJ2meas]
    apply ENNReal.ofReal_le_ofReal
    linarith
  -- Hence `G` has large measure.
  have hGlower : ENNReal.ofReal (5 * r / 4) ≤ MeasureTheory.Measure.hausdorffMeasure 1 G := by
    have hsub : ENNReal.ofReal (3 * r / 2) - ENNReal.ofReal (r / 4)
        ≤ MeasureTheory.Measure.hausdorffMeasure 1 (J2 ∩ LSenl d c ρ)
          - MeasureTheory.Measure.hausdorffMeasure 1 ((J2 ∩ LSenl d c ρ) ∩ B1) :=
      tsub_le_tsub hYge hXle
    have heq : ENNReal.ofReal (5 * r / 4)
        = ENNReal.ofReal (3 * r / 2) - ENNReal.ofReal (r / 4) := by
      rw [← ENNReal.ofReal_sub (3 * r / 2) (by positivity : (0 : ℝ) ≤ r / 4)]
      congr 1
      ring
    have hGeq : MeasureTheory.Measure.hausdorffMeasure 1 G
        = MeasureTheory.Measure.hausdorffMeasure 1 (J2 ∩ LSenl d c ρ)
          - MeasureTheory.Measure.hausdorffMeasure 1 ((J2 ∩ LSenl d c ρ) ∩ B1) :=
      ENNReal.eq_sub_of_add_eq hXfin hGadd
    rw [hGeq, heq]
    exact hsub
  -- ## Step 4. The admissible index set `A`.
  set A : Set ℕ := {i : ℕ | i ∉ T ∧ 0 < ρ i ∧ ρ i ≤ e ∧
      Disjoint (Fenl d c ρ i) U ∧ Fenl d c ρ i ⊆ Iv B r} with hA
  have hAmem : ∀ {i : ℕ}, i ∈ A → i ∉ T ∧ 0 < ρ i ∧ ρ i ≤ e ∧
      Disjoint (Fenl d c ρ i) U ∧ Fenl d c ρ i ⊆ Iv B r := by
    intro i hi
    rw [hA] at hi
    simpa using hi
  set W : Set ℝ := Iv B r ∩ ⋃ i ∈ A, Fenl d c ρ i with hW
  -- ## Step 5. `G` is covered by the admissible enlarged intervals.
  have hGcover : G ⊆ ⋃ i ∈ A, Fenl d c ρ i := by
    intro z hz
    have hz' : z ∈ (J2 ∩ LSenl d c ρ) \ B1 := by rw [← hG]; exact hz
    obtain ⟨hzJ2, hzB1⟩ := hz'
    obtain ⟨hzJ2', hzLS⟩ := hzJ2
    obtain ⟨i, hiT, hi0, hie, hicov⟩ :=
      exists_fresh_of_mem_LSenl hρfin he0 hzLS T
    have hzFi : z ∈ Fenl d c ρ i := mem_Iv.mpr hicov
    have hnd : Disjoint (Fenl d c ρ i) U := by
      by_contra hcon
      exact hzB1 (by
        rw [hB1]
        exact mem_iUnion₂.mpr ⟨i, ⟨hi0, le_of_lt hie, hcon⟩, hzFi⟩)
    have hsub : Fenl d c ρ i ⊆ Iv B r := by
      have hpd : (ρ i) ^ d ≤ m := by
        rw [hm]
        exact Real.rpow_le_rpow (le_of_lt hi0) (le_of_lt hie) (le_of_lt hd0)
      have hzB : |z - B| ≤ r - 4 * m := mem_Iv.mp hzJ2'
      have hcz : |c i - z| ≤ (ρ i) ^ d := by rw [abs_sub_comm]; exact hicov
      have htri : |c i - B| ≤ |c i - z| + |z - B| := by
        calc |c i - B| = |(c i - z) + (z - B)| := by ring_nf
          _ ≤ |c i - z| + |z - B| := abs_add_le _ _
      refine Iv_subset_Iv ?_
      linarith
    exact mem_iUnion₂.mpr ⟨i, ⟨hiT, hi0, le_of_lt hie, hnd, hsub⟩, hzFi⟩
  have hGW : G ⊆ W := by
    intro z hz
    have hzJ : z ∈ Iv B r := by
      have h1 : z ∈ J2 := by
        have h2 := hz
        rw [hG] at h2
        exact h2.1.1
      exact hJ2sub h1
    exact ⟨hzJ, hGcover hz⟩
  -- ## Step 6. `W` has measure at most `3r/8`.
  by_contra hcontra
  have hsmall : ∀ F : Finset ℕ, (F : Set ℕ) ⊆ A →
      (∀ i ∈ F, ∀ j ∈ F, i ≠ j → Disjoint (Fenl d c ρ i) (Fenl d c ρ j)) →
      ∑ i ∈ F, (ρ i) ^ d < r / 16 := by
    intro F hFA hdisj
    by_contra hle
    refine hcontra ⟨F, ?_, ?_, ?_, hdisj, not_lt.mp hle⟩
    · intro i hi
      exact ⟨(hAmem (hFA hi)).1, (hAmem (hFA hi)).2.1,
        le_trans (hAmem (hFA hi)).2.2.1 heε⟩
    · intro i hi
      exact (hAmem (hFA hi)).2.2.2.2
    · intro i hi
      exact (hAmem (hFA hi)).2.2.2.1
  have hbound : ∀ s : Finset ℕ, (s : Set ℕ) ⊆ A →
      MeasureTheory.Measure.hausdorffMeasure 1 (Iv B r ∩ ⋃ i ∈ s, Fenl d c ρ i)
        ≤ ENNReal.ofReal (3 * r / 8) := by
    intro s hs
    obtain ⟨F, hFs, hFdisj, hFbound⟩ :=
      Work.MassTransferenceAlt.Greedy.measure_inter_iUnion_le_six_sum d c ρ hρ (Iv B r) s
    have hsum := hsmall F (fun i hi => hs (hFs hi)) hFdisj
    have h6 : ∑ i ∈ F, ENNReal.ofReal (6 * (ρ i) ^ d)
        = ENNReal.ofReal (6 * ∑ i ∈ F, (ρ i) ^ d) := by
      rw [(ENNReal.ofReal_sum_of_nonneg (fun i _ =>
        mul_nonneg (by norm_num : (0 : ℝ) ≤ 6) (Real.rpow_nonneg (hρ i) d))).symm]
      congr 1
      rw [Finset.mul_sum]
    rw [h6] at hFbound
    have hlt : ENNReal.ofReal (6 * ∑ i ∈ F, (ρ i) ^ d) < ENNReal.ofReal (3 * r / 8) := by
      rw [ENNReal.ofReal_lt_ofReal_iff_of_nonneg
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 6)
          (Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (hρ i) d)))]
      nlinarith
    exact le_of_lt (lt_of_le_of_lt hFbound hlt)
  -- Continuity from below along the finite initial segments of `A`.
  have hWN : W = ⋃ N : ℕ,
      (Iv B r ∩ ⋃ i ∈ ((A ∩ {i : ℕ | i < N}) : Set ℕ), Fenl d c ρ i) := by
    rw [hW]
    ext z
    constructor
    · rintro ⟨hzJ, hzU⟩
      rw [Set.mem_iUnion₂] at hzU
      obtain ⟨i, hiA, hzF⟩ := hzU
      refine mem_iUnion.mpr ⟨i + 1, ?_⟩
      exact ⟨hzJ, mem_iUnion₂.mpr ⟨i, ⟨hiA, Nat.lt_succ_self i⟩, hzF⟩⟩
    · intro hz
      rw [Set.mem_iUnion] at hz
      obtain ⟨N, hN⟩ := hz
      obtain ⟨hzJ, hzU⟩ := hN
      rw [Set.mem_iUnion₂] at hzU
      obtain ⟨i, hiA, hzF⟩ := hzU
      exact ⟨hzJ, mem_iUnion₂.mpr ⟨i, hiA.1, hzF⟩⟩
  have hmono : Monotone (fun N : ℕ =>
      (Iv B r ∩ ⋃ i ∈ ((A ∩ {i : ℕ | i < N}) : Set ℕ), Fenl d c ρ i)) := by
    intro N M hNM z hz
    obtain ⟨hzJ, hzU⟩ := hz
    refine ⟨hzJ, ?_⟩
    rw [Set.mem_iUnion₂] at hzU
    obtain ⟨i, hiA, hzF⟩ := hzU
    exact mem_iUnion₂.mpr ⟨i, ⟨hiA.1, lt_of_lt_of_le hiA.2 hNM⟩, hzF⟩
  have hmuW : MeasureTheory.Measure.hausdorffMeasure 1 W
      = ⨆ N : ℕ, MeasureTheory.Measure.hausdorffMeasure 1
          (Iv B r ∩ ⋃ i ∈ ((A ∩ {i : ℕ | i < N}) : Set ℕ), Fenl d c ρ i) := by
    rw [hWN]
    exact Monotone.measure_iUnion hmono
  have hWle : MeasureTheory.Measure.hausdorffMeasure 1 W ≤ ENNReal.ofReal (3 * r / 8) := by
    rw [hmuW]
    refine iSup_le fun N => ?_
    have hcoe : ((Finset.filter (fun i => i ∈ A) (Finset.range N) : Finset ℕ) : Set ℕ)
        = A ∩ {i : ℕ | i < N} := by
      ext i
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range, Set.mem_inter_iff,
        Set.mem_ofPred_eq]
      exact and_comm
    rw [← hcoe]
    exact hbound _ (fun i hi => (Finset.mem_filter.mp hi).2)
  -- ## Step 7. Contradiction.
  have hfinal : ENNReal.ofReal (5 * r / 4) ≤ ENNReal.ofReal (3 * r / 8) :=
    le_trans hGlower (le_trans (measure_mono hGW) hWle)
  have hlt : ENNReal.ofReal (3 * r / 8) < ENNReal.ofReal (5 * r / 4) := by
    rw [ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)]
    linarith
  exact absurd hfinal (not_le.mpr hlt)

end Work.MassTransferenceAlt.Kgb
