import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mr_direct

open MeasureTheory Set

lemma integral_le_sum_cellSup (f : ℝ → ℝ) (hf : Continuous f) (hnn : ∀ x, 0 ≤ f x)
    {T₀ T : ℝ} (hT : T₀ ≤ T) {U : Set ℝ} (hU : MeasurableSet U)
    (hsub : U ⊆ Set.Icc T₀ T) :
    (∫ x in U, f x) ≤
      ∑ k ∈ Finset.Icc (⌊T₀⌋ - 1) (⌊T⌋ + 1),
        sSup (f '' (U ∩ Set.Ico (k : ℝ) ((k : ℝ) + 1))) := by
  set S : Finset ℤ := Finset.Icc (⌊T₀⌋ - 1) (⌊T⌋ + 1) with hS
  have hcell_meas : ∀ k : ℤ, MeasurableSet (U ∩ Set.Ico (k : ℝ) ((k : ℝ) + 1)) :=
    fun k => hU.inter measurableSet_Ico
  have hint : ∀ k ∈ S, Integrable ((U ∩ Set.Ico (k : ℝ) ((k : ℝ) + 1)).indicator f) := by
    intro k hk
    refine ((ContinuousOn.integrableOn_compact (K := Set.Icc (k:ℝ) ((k:ℝ)+1))
      isCompact_Icc hf.continuousOn).mono_set ?_).integrable_indicator (hcell_meas k)
    intro y hy
    exact ⟨hy.2.1, le_of_lt hy.2.2⟩
  have hpoint : ∀ x, U.indicator f x =
      ∑ k ∈ S, (U ∩ Set.Ico (k:ℝ) ((k:ℝ)+1)).indicator f x := by
    intro x
    by_cases hxU : x ∈ U
    · have hxIcc : x ∈ Set.Icc T₀ T := hsub hxU
      have hk_mem : ⌊x⌋ ∈ S := by
        rw [hS, Finset.mem_Icc]
        exact ⟨by have h1 : ⌊T₀⌋ ≤ ⌊x⌋ := Int.floor_le_floor hxIcc.1; omega,
               by have h2 : ⌊x⌋ ≤ ⌊T⌋ := Int.floor_le_floor hxIcc.2; omega⟩
      rw [Set.indicator_of_mem hxU f]
      rw [Finset.sum_eq_single_of_mem ⌊x⌋ hk_mem (by
        intro b hb hbne
        exact Set.indicator_of_notMem (fun hbx => hbne (Int.floor_eq_on_Ico b x hbx.2).symm) f)]
      rw [Set.indicator_of_mem (show x ∈ U ∩ Set.Ico ((⌊x⌋ : ℤ):ℝ) (((⌊x⌋ : ℤ):ℝ)+1) from
        ⟨hxU, Int.floor_le x, Int.lt_floor_add_one x⟩) f]
    · rw [Set.indicator_of_notMem hxU f]
      symm
      apply Finset.sum_eq_zero
      intro k hk
      exact Set.indicator_of_notMem (fun hx => hxU hx.1) f
  have hkey : (∫ x in U, f x) = ∑ k ∈ S, ∫ x in (U ∩ Set.Ico (k:ℝ) ((k:ℝ)+1)), f x := by
    rw [← MeasureTheory.integral_indicator hU]
    rw [MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all (volume : Measure ℝ) hpoint)]
    rw [MeasureTheory.integral_finsetSum S hint]
    exact Finset.sum_congr rfl (fun k hk => MeasureTheory.integral_indicator (hcell_meas k))
  have hstep : ∀ k ∈ S, ∫ x in (U ∩ Set.Ico (k:ℝ) ((k:ℝ)+1)), f x ≤
      sSup (f '' (U ∩ Set.Ico (k:ℝ) ((k:ℝ)+1))) := by
    intro k hk
    have hcell_sub : U ∩ Set.Ico (k:ℝ) ((k:ℝ)+1) ⊆ Set.Icc (k:ℝ) ((k:ℝ)+1) :=
      fun y hy => ⟨hy.2.1, le_of_lt hy.2.2⟩
    have hbdd : BddAbove (f '' (U ∩ Set.Ico (k:ℝ) ((k:ℝ)+1))) :=
      (isCompact_Icc.bddAbove_image hf.continuousOn).mono (Set.image_mono hcell_sub)
    have hvol : volume (U ∩ Set.Ico (k:ℝ) ((k:ℝ)+1)) ≤ 1 := by
      have h1 := MeasureTheory.measure_mono (μ := volume) hcell_sub
      rw [Real.volume_Icc] at h1
      have hsub1 : ((k:ℝ) + 1) - (k:ℝ) = 1 := by ring
      rw [hsub1, ENNReal.ofReal_one] at h1
      exact h1
    have hfin : volume (U ∩ Set.Ico (k:ℝ) ((k:ℝ)+1)) < ⊤ :=
      lt_of_le_of_lt hvol ENNReal.one_lt_top
    have hreal : volume.real (U ∩ Set.Ico (k:ℝ) ((k:ℝ)+1)) ≤ 1 := by
      rw [MeasureTheory.measureReal_def]
      have := ENNReal.toReal_mono (b := (1:ENNReal)) ENNReal.one_ne_top hvol
      simpa [ENNReal.toReal_one] using this
    have hCnn : 0 ≤ sSup (f '' (U ∩ Set.Ico (k:ℝ) ((k:ℝ)+1))) := by
      rcases Set.eq_empty_or_nonempty (f '' (U ∩ Set.Ico (k:ℝ) ((k:ℝ)+1))) with h | ⟨v, hv⟩
      · rw [h]; simp [Real.sSup_empty]
      · rcases hv with ⟨y, hy, rfl⟩
        exact le_trans (hnn y) (le_csSup hbdd (Set.mem_image_of_mem f hy))
    have hbound : ∀ x ∈ U ∩ Set.Ico (k:ℝ) ((k:ℝ)+1),
        ‖f x‖ ≤ sSup (f '' (U ∩ Set.Ico (k:ℝ) ((k:ℝ)+1))) := by
      intro x hx
      rw [Real.norm_of_nonneg (hnn x)]
      exact le_csSup hbdd (Set.mem_image_of_mem f hx)
    have hnorm := MeasureTheory.norm_setIntegral_le_of_norm_le_const hfin hbound
    have hnnint : 0 ≤ ∫ x in (U ∩ Set.Ico (k:ℝ) ((k:ℝ)+1)), f x :=
      MeasureTheory.setIntegral_nonneg (hcell_meas k) (fun x hx => hnn x)
    rw [Real.norm_of_nonneg hnnint] at hnorm
    calc ∫ x in (U ∩ Set.Ico (k:ℝ) ((k:ℝ)+1)), f x
        ≤ sSup (f '' (U ∩ Set.Ico (k:ℝ) ((k:ℝ)+1))) *
            volume.real (U ∩ Set.Ico (k:ℝ) ((k:ℝ)+1)) := hnorm
      _ ≤ sSup (f '' (U ∩ Set.Ico (k:ℝ) ((k:ℝ)+1))) * 1 :=
            mul_le_mul_of_nonneg_left hreal hCnn
      _ = sSup (f '' (U ∩ Set.Ico (k:ℝ) ((k:ℝ)+1))) := mul_one _
  calc (∫ x in U, f x)
      = ∑ k ∈ S, ∫ x in (U ∩ Set.Ico (k:ℝ) ((k:ℝ)+1)), f x := hkey
    _ ≤ ∑ k ∈ S, sSup (f '' (U ∩ Set.Ico (k:ℝ) ((k:ℝ)+1))) := Finset.sum_le_sum hstep

end Work.BMF.mr_direct
