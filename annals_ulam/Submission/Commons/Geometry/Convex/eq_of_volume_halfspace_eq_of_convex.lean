import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

namespace Commons.Geometry.Convex

open MeasureTheory
open scoped RealInnerProductSpace

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

private lemma exists_mem_interior_Ioo_of_le_lt
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {K : Set E} (hK_conv : Convex ℝ K) (hK_int : (interior K).Nonempty)
    {f : E → ℝ} (hf_linear : ∀ (x y : E) (t : ℝ),
      f ((1 - t) • x + t • y) = (1 - t) * f x + t * f y)
    {a b : ℝ} (hab : a < b)
    {x y : E} (hx : x ∈ K) (hfx : f x ≤ a) (hy : y ∈ K) (hfy : b < f y) :
    ∃ z ∈ interior K, a < f z ∧ f z < b := by
  rcases hK_int with ⟨w, hw⟩
  by_cases hw_mid : a < f w ∧ f w < b
  · exact ⟨w, hw, hw_mid.1, hw_mid.2⟩
  have hw_le_or : f w ≤ a ∨ b ≤ f w := by
    by_cases hw_le : f w ≤ a
    · exact Or.inl hw_le
    · have hwa : a < f w := lt_of_not_ge hw_le
      by_cases hw_ge : b ≤ f w
      · exact Or.inr hw_ge
      · have hwb : f w < b := lt_of_not_ge hw_ge
        exact False.elim (hw_mid ⟨hwa, hwb⟩)
  rcases hw_le_or with hw_le | hw_ge
  · -- f w ≤ a, use the segment from w to y
    let d : ℝ := f y - f w
    have hd_pos : 0 < d := by linarith
    let t : ℝ := (a - f w + (b - a) / 2) / d
    have ht0 : 0 < t := by
      apply div_pos
      · linarith
      · exact hd_pos
    have ht1 : t < 1 := by
      rw [div_lt_one hd_pos]
      have hy_gt : a - f w + (b - a) / 2 < f y - f w := by linarith
      exact hy_gt
    let z : E := (1 - t) • w + t • y
    have hz_open : z ∈ openSegment ℝ w y := by
      rw [openSegment_eq_image]
      exact ⟨t, ⟨ht0, ht1⟩, rfl⟩
    have hz_int : z ∈ interior K :=
      hK_conv.openSegment_interior_self_subset_interior hw hy hz_open
    have hfz : f z = a + (b - a) / 2 := by
      dsimp [z, t, d]
      rw [hf_linear]
      have hd_ne : f y - f w ≠ 0 := by linarith
      field_simp [hd_ne]
      ring
    refine ⟨z, hz_int, ?_, ?_⟩
    · linarith
    · linarith
  · -- b ≤ f w, use the segment from w to x
    let d : ℝ := f w - f x
    have hd_pos : 0 < d := by linarith
    let t : ℝ := (f w - (a + (b - a) / 2)) / d
    have ht0 : 0 < t := by
      apply div_pos
      · linarith
      · exact hd_pos
    have ht1 : t < 1 := by
      rw [div_lt_one hd_pos]
      have hx_lt : f w - (a + (b - a) / 2) < f w - f x := by linarith
      exact hx_lt
    let z : E := (1 - t) • w + t • x
    have hz_open : z ∈ openSegment ℝ w x := by
      rw [openSegment_eq_image]
      exact ⟨t, ⟨ht0, ht1⟩, rfl⟩
    have hz_int : z ∈ interior K :=
      hK_conv.openSegment_interior_self_subset_interior hw hx hz_open
    have hfz : f z = a + (b - a) / 2 := by
      dsimp [z, t, d]
      rw [hf_linear]
      have hd_ne : f w - f x ≠ 0 := by linarith
      field_simp [hd_ne]
      ring
    refine ⟨z, hz_int, ?_, ?_⟩
    · linarith
    · linarith

private lemma volume_halfspace_ne_of_lt
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {K : Set E} (hK_meas : MeasurableSet K) (hK_conv : Convex ℝ K)
    (hK_int : (interior K).Nonempty) (hK_finite : volume K < ⊤)
    {ξ : E} {a b : ℝ} (hab : a < b)
    (ha_pos : 0 < volume.real (K ∩ {x | ⟪x, ξ⟫ ≤ a}))
    (ha_lt : volume.real (K ∩ {x | ⟪x, ξ⟫ ≤ a}) < volume.real K)
    (hb_pos : 0 < volume.real (K ∩ {x | ⟪x, ξ⟫ ≤ b}))
    (hb_lt : volume.real (K ∩ {x | ⟪x, ξ⟫ ≤ b}) < volume.real K) :
    volume.real (K ∩ {x | ⟪x, ξ⟫ ≤ a}) ≠ volume.real (K ∩ {x | ⟪x, ξ⟫ ≤ b}) := by
  intro hvol
  let f : E → ℝ := fun x => ⟪x, ξ⟫
  have hf_cont : Continuous f := by
    dsimp [f]
    exact continuous_id.inner continuous_const
  have hf_meas : Measurable f := hf_cont.measurable
  have hf_linear : ∀ (x y : E) (t : ℝ),
      f ((1 - t) • x + t • y) = (1 - t) * f x + t * f y := by
    intro x y t
    dsimp [f]
    rw [inner_add_left, inner_smul_left, inner_smul_left]
    simp
  let A : Set E := K ∩ {x | f x ≤ a}
  let B : Set E := K ∩ {x | f x ≤ b}
  have hA_meas : MeasurableSet A := hK_meas.inter (measurableSet_le hf_meas measurable_const)
  have hB_meas : MeasurableSet B := hK_meas.inter (measurableSet_le hf_meas measurable_const)
  have hA_sub_B : A ⊆ B := by
    intro x hx
    exact ⟨hx.1, le_trans hx.2 (le_of_lt hab)⟩
  have hA_sub_K : A ⊆ K := fun x hx => hx.1
  have hB_sub_K : B ⊆ K := fun x hx => hx.1
  have hA_lt_top : volume A < ⊤ := lt_of_le_of_lt (measure_mono hA_sub_K) hK_finite
  have hB_lt_top : volume B < ⊤ := lt_of_le_of_lt (measure_mono hB_sub_K) hK_finite
  have hA_fin : volume A ≠ ⊤ := hA_lt_top.ne
  have hB_fin : volume B ≠ ⊤ := hB_lt_top.ne
  -- Equality of the real halfspace volumes gives equality of the ENNReal measures.
  have hAB_enn : volume A = volume B := by
    rw [← ENNReal.ofReal_toReal hA_fin, ← ENNReal.ofReal_toReal hB_fin]
    simpa [Measure.real, A, B, f] using hvol
  have hBA_diff_zero : volume (B \ A) = 0 := by
    rw [measure_sdiff hA_sub_B hA_meas.nullMeasurableSet hA_fin]
    rw [hAB_enn]
    simp
  -- The hypotheses give a point of A and a point of K \ B.
  have hA_enn_pos : 0 < volume A := by
    have h := (ENNReal.toReal_pos_iff.mp (by simpa [Measure.real, A, f] using ha_pos)).1
    simpa [A] using h
  have hB_lt_K_enn : volume B < volume K := by
    have hK_fin' : volume K ≠ ⊤ := hK_finite.ne
    have hB_fin' : volume B ≠ ⊤ := hB_lt_top.ne
    exact (ENNReal.toReal_lt_toReal hB_fin' hK_fin').mp (by simpa [Measure.real, B, f] using hb_lt)
  have hKB_pos : 0 < volume (K \ B) := by
    have hBmeas : NullMeasurableSet B volume := hB_meas.nullMeasurableSet
    rw [measure_sdiff hB_sub_K hBmeas hB_fin]
    exact tsub_pos_iff_lt.mpr hB_lt_K_enn
  have hx_nonempty : A.Nonempty := nonempty_of_measure_ne_zero hA_enn_pos.ne'
  have hy_nonempty : (K \ B).Nonempty := nonempty_of_measure_ne_zero hKB_pos.ne'
  rcases hx_nonempty with ⟨x, hxA⟩
  rcases hy_nonempty with ⟨y, hyKB⟩
  have hxK : x ∈ K := hxA.1
  have hfx : f x ≤ a := hxA.2
  have hyK : y ∈ K := hyKB.1
  have hy_notB : y ∉ B := hyKB.2
  have hfy : b < f y := by
    by_contra hnot
    have hle : f y ≤ b := le_of_not_gt hnot
    exact hy_notB ⟨hyK, hle⟩
  -- Convexity gives an interior point with f-value strictly between a and b.
  obtain ⟨z, hz_int, hza, hzb⟩ :=
    exists_mem_interior_Ioo_of_le_lt hK_conv hK_int hf_linear hab hxK hfx hyK hfy
  let U : Set E := interior K ∩ {x | a < f x ∧ f x < b}
  have hU_open : IsOpen U := by
    dsimp [U]
    exact isOpen_interior.inter (hf_cont.isOpen_preimage (Set.Ioo a b) isOpen_Ioo)
  have hU_nonempty : U.Nonempty := by
    refine ⟨z, hz_int, ?_⟩
    exact ⟨hza, hzb⟩
  have hU_sub : U ⊆ B \ A := by
    intro x hxU
    rcases hxU with ⟨hx_int, hxa, hxb⟩
    refine ⟨⟨interior_subset hx_int, le_of_lt hxb⟩, ?_⟩
    intro hxA
    have hfx_le_a : f x ≤ a := hxA.2
    linarith
  have hU_pos : 0 < volume U := hU_open.measure_pos (μ := volume) hU_nonempty
  have hBA_pos : 0 < volume (B \ A) := hU_pos.trans_le (measure_mono hU_sub)
  exact (ne_of_gt hBA_pos) hBA_diff_zero

lemma eq_of_volume_halfspace_eq_of_convex
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {K : Set E} (hK_meas : MeasurableSet K) (hK_conv : Convex ℝ K)
    (hK_int : (interior K).Nonempty) (hK_finite : volume K < ⊤)
    {ξ : E} (hξ : ξ ≠ 0) {a b : ℝ}
    (ha_pos : 0 < volume.real (K ∩ {x | ⟪x, ξ⟫ ≤ a}))
    (ha_lt : volume.real (K ∩ {x | ⟪x, ξ⟫ ≤ a}) < volume.real K)
    (hb_pos : 0 < volume.real (K ∩ {x | ⟪x, ξ⟫ ≤ b}))
    (hb_lt : volume.real (K ∩ {x | ⟪x, ξ⟫ ≤ b}) < volume.real K)
    (hvol : volume.real (K ∩ {x | ⟪x, ξ⟫ ≤ a}) =
            volume.real (K ∩ {x | ⟪x, ξ⟫ ≤ b})) :
    a = b := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hab | hba
  · exact (volume_halfspace_ne_of_lt hK_meas hK_conv hK_int hK_finite hab
      ha_pos ha_lt hb_pos hb_lt) hvol
  · exact (volume_halfspace_ne_of_lt hK_meas hK_conv hK_int hK_finite hba
      hb_pos hb_lt ha_pos ha_lt) hvol.symm

end Commons.Geometry.Convex