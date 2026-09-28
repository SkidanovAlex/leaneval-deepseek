import Mathlib
import Submission.Work.HP.BCS.CLDefs

/-!
# Auxiliary lemmas for `Work.HP.BCS.count_from_layer`

All statements here are proved directly; they are the ingredients of `count_from_layer`.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped Pointwise

namespace Work.HP.BCS

variable {k : ℕ}

/-! ### The fundamental domain: covering and disjointness -/

/-- Every point of `ℝ^k` lies in exactly one translate `Ψ (toEk c) + fund Ψ`. -/
lemma fund_cover_aux (Ψ : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k))
    (hΨ : Function.Injective Ψ) (x : EuclideanSpace ℝ (Fin k)) :
    ∃! c : Fin k → ℤ, x - Ψ (toEk c) ∈ fund Ψ := by
  classical
  have hsurj : Function.Surjective Ψ := LinearMap.injective_iff_surjective.mp hΨ
  obtain ⟨y, hy⟩ := hsurj x
  have hyunit : (y - toEk (fun i => ⌊y.ofLp i⌋)) ∈ unitCube k := by
    intro i
    have h2 : (y - toEk (fun i => ⌊y.ofLp i⌋)).ofLp i = Int.fract (y.ofLp i) := by
      simp only [toEk, WithLp.ofLp_sub, WithLp.ofLp_toLp, Pi.sub_apply]
      linarith [Int.floor_add_fract (y.ofLp i)]
    rw [h2]
    exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  have hex : x - Ψ (toEk (fun i => ⌊y.ofLp i⌋)) ∈ fund Ψ :=
    ⟨y - toEk (fun i => ⌊y.ofLp i⌋), hyunit, by rw [map_sub, hy]⟩
  refine ⟨fun i => ⌊y.ofLp i⌋, hex, ?_⟩
  intro c' hc'
  obtain ⟨u, hu, huc⟩ := hex
  obtain ⟨u', hu', hu'c⟩ := hc'
  have key : u - u' = toEk (c' - fun i => ⌊y.ofLp i⌋) := by
    apply hΨ
    rw [map_sub, huc, hu'c, toEk_sub, map_sub]
    abel
  funext i
  have hi : (u - u').ofLp i = ((c' - fun i => ⌊y.ofLp i⌋) i : ℝ) := by
    rw [key]
    simp only [toEk, WithLp.ofLp_toLp]
  rw [WithLp.ofLp_sub, Pi.sub_apply] at hi
  have hlt : (c' - fun i => ⌊y.ofLp i⌋) i < 1 := by
    have h : ((c' - fun i => ⌊y.ofLp i⌋) i : ℝ) < 1 := by
      rw [← hi]; linarith [(hu i).2, (hu' i).1]
    exact_mod_cast h
  have hgt : -1 < (c' - fun i => ⌊y.ofLp i⌋) i := by
    have h : (-1 : ℝ) < ((c' - fun i => ⌊y.ofLp i⌋) i : ℝ) := by
      rw [← hi]; linarith [(hu i).1, (hu' i).2]
    exact_mod_cast h
  have hzero : (c' - fun i => ⌊y.ofLp i⌋) i = 0 := by omega
  have hfin : c' i - (fun i => ⌊y.ofLp i⌋) i = 0 := by simpa [Pi.sub_apply] using hzero
  exact sub_eq_zero.mp hfin

/-- Distinct translates of `fund Ψ` by lattice vectors are disjoint. -/
lemma fund_disjoint_aux (Ψ : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k))
    (hΨ : Function.Injective Ψ) {s s' : EuclideanSpace ℝ (Fin k)}
    (hs : s ∈ latImage Ψ) (hs' : s' ∈ latImage Ψ) (h : s ≠ s') :
    Disjoint ({s} + fund Ψ) ({s'} + fund Ψ) := by
  rw [Set.disjoint_iff_inter_eq_empty, Set.eq_empty_iff_forall_notMem]
  intro x hx
  simp only [Set.mem_inter_iff, Set.mem_add, Set.mem_singleton_iff] at hx
  obtain ⟨⟨a, ha, fa, hfa, hxfa⟩, ⟨b, hb, fb, hfb, hxfb⟩⟩ := hx
  subst ha
  subst hb
  obtain ⟨y, ⟨c, rfl⟩, hy⟩ := hs
  obtain ⟨y', ⟨c', rfl⟩, hy'⟩ := hs'
  have h1 : x - Ψ (toEk c) ∈ fund Ψ := by
    have : x - Ψ (toEk c) = fa := by rw [← hxfa, ← hy]; abel
    rw [this]; exact hfa
  have h2 : x - Ψ (toEk c') ∈ fund Ψ := by
    have : x - Ψ (toEk c') = fb := by rw [← hxfb, ← hy']; abel
    rw [this]; exact hfb
  exact h (by rw [← hy, ← hy', (fund_cover_aux Ψ hΨ x).unique h1 h2])

/-! ### The strict radius bound `fund Ψ ⊆ ball 0 (cellRad Ψ)` -/

lemma norm_lt_cellRad_aux (hk : 1 ≤ k)
    (Ψ : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k))
    (hΨ : Function.Injective Ψ) {y : EuclideanSpace ℝ (Fin k)} (hy : y ∈ unitCube k) :
    ‖Ψ y‖ < cellRad Ψ := by
  have hpos : ∀ i : Fin k, 0 < ‖Ψ (toEk (Pi.single i (1 : ℤ)) : EuclideanSpace ℝ (Fin k))‖ := by
    intro i
    rw [norm_pos_iff]
    intro h
    have hz : toEk (Pi.single i (1 : ℤ)) = (0 : EuclideanSpace ℝ (Fin k)) :=
      hΨ (by rw [h, map_zero])
    have h1 := congrFun (toEk_eq_zero_iff.mp hz) i
    simpa [Pi.single_eq_same] using h1
  have hkey : ∀ i : Fin k, Ψ ((y.ofLp i) • toEk (Pi.single i (1 : ℤ)))
      = (y.ofLp i) • Ψ (toEk (Pi.single i (1 : ℤ))) := fun i => map_smul Ψ _ _
  rw [← sum_smul_toEk_single_eq y, map_sum]
  simp only [hkey]
  refine lt_of_le_of_lt (norm_sum_le _ _) ?_
  rw [cellRad]
  refine Finset.sum_lt_sum ?hle ?hlt
  · intro i _
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hy i).1]
    exact mul_le_of_le_one_left (norm_nonneg _) (le_of_lt (hy i).2)
  · have hk0 : 0 < k := by omega
    refine ⟨⟨0, hk0⟩, Finset.mem_univ _, ?_⟩
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hy ⟨0, hk0⟩).1]
    exact mul_lt_of_lt_one_left (hpos ⟨0, hk0⟩) (hy ⟨0, hk0⟩).2

/-! ### Measurability and volume of the fundamental domain -/

lemma measurableSet_unitCube (k : ℕ) : MeasurableSet (unitCube k) := by
  have h2 : MeasurableSet (Set.pi Set.univ (fun _ : Fin k => Set.Ico (0 : ℝ) 1)) :=
    MeasurableSet.pi Set.countable_univ fun _ _ => measurableSet_Ico
  have h1 : Measurable (WithLp.ofLp : EuclideanSpace ℝ (Fin k) → (Fin k → ℝ)) :=
    WithLp.measurable_ofLp 2 (Fin k → ℝ)
  have hunit : unitCube k
      = WithLp.ofLp ⁻¹' (Set.pi Set.univ (fun _ : Fin k => Set.Ico (0 : ℝ) 1)) := by
    ext x; simp [unitCube, Set.mem_pi]
  rw [hunit]
  exact h2.preimage h1

lemma measurableSet_fund_aux (Ψ : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k))
    (hΨ : Function.Injective Ψ) : MeasurableSet (fund Ψ) := by
  have hsurj : Function.Surjective Ψ := LinearMap.injective_iff_surjective.mp hΨ
  have hbij : Function.Bijective Ψ := ⟨hΨ, hsurj⟩
  have hfund : fund Ψ
      = (fun x => (LinearEquiv.ofBijective Ψ hbij).symm x) ⁻¹' unitCube k := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      simpa using ht
    · intro hx
      exact ⟨(LinearEquiv.ofBijective Ψ hbij).symm x, hx, by simp⟩
  rw [hfund]
  refine MeasurableSet.preimage (measurableSet_unitCube k) ?_
  exact (LinearMap.continuous_of_finiteDimensional
    (LinearEquiv.ofBijective Ψ hbij).symm.toLinearMap).measurable

lemma measurableSet_add_fund (Ψ : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k))
    (hΨ : Function.Injective Ψ) (s : EuclideanSpace ℝ (Fin k)) :
    MeasurableSet ({s} + fund Ψ) := by
  rw [Set.singleton_add, Set.image_add_left]
  exact (measurableSet_fund_aux Ψ hΨ).preimage (measurable_const_add _)

lemma volume_unitCube (k : ℕ) : MeasureTheory.volume (unitCube k) = 1 := by
  set S : Set (Fin k → ℝ) := Set.pi Set.univ (fun _ : Fin k => Set.Ico (0 : ℝ) 1) with hSdef
  have hS : MeasurableSet S := MeasurableSet.pi Set.countable_univ fun _ _ => measurableSet_Ico
  have hMP : MeasurePreserving (WithLp.ofLp : EuclideanSpace ℝ (Fin k) → (Fin k → ℝ))
      (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin k)))
      (MeasureTheory.volume : Measure (Fin k → ℝ)) := PiLp.volume_preserving_ofLp (Fin k)
  have hunit : (WithLp.ofLp : EuclideanSpace ℝ (Fin k) → (Fin k → ℝ)) ⁻¹' S = unitCube k := by
    ext x; simp [hSdef, unitCube, Set.mem_pi]
  have hvolS : (MeasureTheory.volume : Measure (Fin k → ℝ)) S = 1 := by
    rw [hSdef, volume_pi, MeasureTheory.Measure.pi_pi]
    simp [Real.volume_Ico]
  rw [← hunit, hMP.measure_preimage hS.nullMeasurableSet, hvolS]

lemma volume_fund_aux (Ψ : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k))
    (hΨ : Function.Injective Ψ) :
    MeasureTheory.volume (fund Ψ) = ENNReal.ofReal Ψ.normDet := by
  have hfund : fund Ψ = Ψ '' unitCube k := rfl
  rw [hfund, MeasureTheory.Measure.addHaar_image_linearMap volume Ψ (unitCube k),
    LinearMap.normDet_eq_abs_det, volume_unitCube k, mul_one]

/-! ### The finite union of translates -/

lemma volume_biUnion_fund_aux (Ψ : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k))
    (hΨ : Function.Injective Ψ) (S : Finset (EuclideanSpace ℝ (Fin k)))
    (hS : ∀ s ∈ S, s ∈ latImage Ψ) :
    (MeasureTheory.volume (⋃ s ∈ S, ({s} + fund Ψ))).toReal = (S.card : ℝ) * Ψ.normDet := by
  have hpd : (↑S : Set (EuclideanSpace ℝ (Fin k))).PairwiseDisjoint (fun s => ({s} + fund Ψ)) := by
    intro s hs s' hs' hne
    exact fund_disjoint_aux Ψ hΨ (hS s (Finset.mem_coe.mp hs)) (hS s' (Finset.mem_coe.mp hs')) hne
  have hmeas : ∀ b ∈ S, MeasurableSet ({b} + fund Ψ) := fun b _ => measurableSet_add_fund Ψ hΨ b
  have hvol : ∀ p : EuclideanSpace ℝ (Fin k),
      MeasureTheory.volume ({p} + fund Ψ) = MeasureTheory.volume (fund Ψ) := by
    intro p
    simp only [Set.singleton_add, Set.image_add_left, measure_preimage_add]
  have hunion : MeasureTheory.volume (⋃ s ∈ S, ({s} + fund Ψ))
      = S.card • MeasureTheory.volume (fund Ψ) := by
    rw [measure_biUnion_finset hpd hmeas]
    rw [(Finset.sum_congr rfl fun p _ => hvol p), Finset.sum_const]
  rw [hunion, ENNReal.toReal_nsmul, volume_fund_aux Ψ hΨ,
    ENNReal.toReal_ofReal (LinearMap.normDet_nonneg Ψ), nsmul_eq_mul]

/-! ### The thickening / erosion / layer split -/

lemma add_ball_eq_thickening {K : Set (EuclideanSpace ℝ (Fin k))} {R : ℝ} :
    K + Metric.ball (0 : EuclideanSpace ℝ (Fin k)) R = Metric.thickening R K := by
  ext x
  rw [Set.mem_add, Metric.mem_thickening_iff]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨a, ha, by simpa [dist_eq_norm] using hb⟩
  · rintro ⟨z, hz, hd⟩
    exact ⟨z, hz, x - z, by simpa [dist_eq_norm] using hd, by abel⟩

lemma erode_eq_compl_thickening (K : Set (EuclideanSpace ℝ (Fin k))) (R : ℝ) :
    erode K (Metric.ball (0 : EuclideanSpace ℝ (Fin k)) R) = (Metric.thickening R Kᶜ)ᶜ := by
  ext x
  simp only [erode, Set.mem_ofPred_eq, Set.mem_compl_iff, Metric.mem_thickening_iff]
  constructor
  · intro h hx
    obtain ⟨z, hz, hd⟩ := hx
    have hbz : z - x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin k)) R := by
      simpa [dist_eq_norm, norm_sub_rev] using hd
    have := h (z - x) hbz
    rw [show x + (z - x) = z by abel] at this
    exact hz this
  · intro h b hb
    by_contra hcon
    exact h ⟨x + b, hcon, by simpa [dist_eq_norm] using hb⟩

lemma measurableSet_erode_ball (K : Set (EuclideanSpace ℝ (Fin k))) (R : ℝ) :
    MeasurableSet (erode K (Metric.ball (0 : EuclideanSpace ℝ (Fin k)) R)) := by
  rw [erode_eq_compl_thickening]
  exact Metric.isOpen_thickening.measurableSet.compl

lemma erode_subset_self {K : Set (EuclideanSpace ℝ (Fin k))} {R : ℝ} (hR : 0 < R) :
    erode K (Metric.ball (0 : EuclideanSpace ℝ (Fin k)) R) ⊆ K := by
  intro x hx
  have := hx 0 (by simpa using hR)
  simpa using this

lemma thickening_erode_layer_aux {K : Set (EuclideanSpace ℝ (Fin k))} {R : ℝ} (hR : 0 < R) :
    MeasureTheory.volume (Metric.thickening R K)
      = MeasureTheory.volume (erode K (Metric.ball (0 : EuclideanSpace ℝ (Fin k)) R))
        + MeasureTheory.volume (layer K R) := by
  have hmeas : MeasurableSet (erode K (Metric.ball (0 : EuclideanSpace ℝ (Fin k)) R)) :=
    measurableSet_erode_ball K R
  have hsub : erode K (Metric.ball (0 : EuclideanSpace ℝ (Fin k)) R) ⊆ Metric.thickening R K := by
    intro x hx
    exact Metric.mem_thickening_iff.mpr ⟨x, erode_subset_self hR hx, by simpa using hR⟩
  have hlayer : layer K R
      = Metric.thickening R K \ erode K (Metric.ball (0 : EuclideanSpace ℝ (Fin k)) R) := by
    rw [layer, add_ball_eq_thickening]
  have hunion : Metric.thickening R K
      = (Metric.thickening R K \ erode K (Metric.ball (0 : EuclideanSpace ℝ (Fin k)) R))
        ∪ erode K (Metric.ball (0 : EuclideanSpace ℝ (Fin k)) R) :=
    (Set.sdiff_union_of_subset hsub).symm
  rw [hunion, measure_union Set.disjoint_sdiff_left hmeas, ← hlayer]
  exact add_comm _ _

/-! ### Two elementary positivity facts -/

lemma cellRad_pos_aux (hk : 1 ≤ k) (Ψ : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k))
    (hΨ : Function.Injective Ψ) : 0 < cellRad Ψ := by
  rw [cellRad]
  refine Finset.sum_pos (fun i _ => ?_) ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  rw [norm_pos_iff]
  intro h
  have hz : toEk (Pi.single i (1 : ℤ)) = (0 : EuclideanSpace ℝ (Fin k)) :=
    hΨ (by rw [h, map_zero])
  have h1 := congrFun (toEk_eq_zero_iff.mp hz) i
  simpa [Pi.single_eq_same] using h1

lemma normDet_pos_aux (Ψ : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k))
    (hΨ : Function.Injective Ψ) : 0 < Ψ.normDet := by
  have hne : Ψ.normDet ≠ 0 := by
    intro h
    exact (LinearMap.normDet_eq_zero_iff_ker_ne_bot.mp h) ((LinearMap.ker_eq_bot).mpr hΨ)
  exact lt_of_le_of_ne (LinearMap.normDet_nonneg Ψ) (Ne.symm hne)

end Work.HP.BCS
