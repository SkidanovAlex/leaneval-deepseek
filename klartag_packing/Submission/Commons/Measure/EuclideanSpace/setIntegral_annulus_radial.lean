import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Constructions.HaarToSphere

namespace Commons.Measure.EuclideanSpace

open MeasureTheory

theorem setIntegral_annulus_radial {n : ℕ} (hn : 1 ≤ n) {r R : ℝ} (hr : 0 ≤ r) (hR : r ≤ R)
    (g : ℝ → ℝ) :
    ∫ x in {x : EuclideanSpace ℝ (Fin n) | r ≤ ‖x‖ ∧ ‖x‖ < R}, g ‖x‖
      = (n : ℝ) * (MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal
        * ∫ ρ in r..R, ρ ^ (n - 1) * g ρ := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  set A : Set (EuclideanSpace ℝ (Fin n)) := {x | r ≤ ‖x‖ ∧ ‖x‖ < R} with hA
  let h : ℝ → ℝ := fun ρ => ρ ^ (n - 1) * g ρ
  let F : ℝ → ℝ := Set.indicator (Set.Ico r R) g
  have hAmeas : MeasurableSet A := by
    have : A = (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖) ⁻¹' (Set.Ico r R) := by
      rw [hA]; ext x; simp [Set.mem_Ico]
    rw [this]; exact measurableSet_Ico.preimage continuous_norm.measurable
  have hAiff : ∀ x : EuclideanSpace ℝ (Fin n), x ∈ A ↔ ‖x‖ ∈ Set.Ico r R := by
    intro x; rw [hA]; simp [Set.mem_Ico]
  -- Step A : rewrite the set integral as an integral over the whole space
  have stepA : ∫ x in A, g ‖x‖ = ∫ x : EuclideanSpace ℝ (Fin n), F ‖x‖ := by
    rw [← MeasureTheory.integral_indicator (μ := volume) (s := A)
      (f := fun x : EuclideanSpace ℝ (Fin n) => g ‖x‖) hAmeas]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ A
    · have hx' : ‖x‖ ∈ Set.Ico r R := (hAiff x).mp hx
      simp only [F, Set.indicator_of_mem hx, Set.indicator_of_mem hx']
    · have hx' : ‖x‖ ∉ Set.Ico r R := fun hh => hx ((hAiff x).mpr hh)
      simp only [F, Set.indicator_of_notMem hx, Set.indicator_of_notMem hx']
  -- Step B : polar coordinates over the whole space
  have stepB := MeasureTheory.integral_fun_norm_addHaar
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))) F
  rw [finrank_euclideanSpace_fin, Measure.real] at stepB
  -- Step C : the radial integral is supported on the annulus
  have hF_eq : ∀ y : ℝ, y ^ (n - 1) • F y = (Set.Ico r R).indicator h y := by
    intro y
    by_cases hy : y ∈ Set.Ico r R
    · simp only [F, h, Set.indicator_of_mem hy, smul_eq_mul]
    · simp only [F, h, Set.indicator_of_notMem hy, smul_zero]
  have hAe : (Set.Ioi (0 : ℝ) ∩ Set.Ico r R : Set ℝ) =ᵐ[volume] Set.Ico r R := by
    rw [MeasureTheory.ae_eq_set]
    refine ⟨?_, ?_⟩
    · rw [Set.sdiff_eq_empty.mpr Set.inter_subset_right, measure_empty]
    · apply measure_mono_null (t := {(0 : ℝ)})
      · intro x hx
        simp only [Set.mem_sdiff, Set.mem_singleton_iff] at hx ⊢
        obtain ⟨hx1, hx2⟩ := hx
        have hxlt : ¬ (0 < x) := fun h0 => hx2 ⟨h0, hx1⟩
        exact le_antisymm (le_of_not_gt hxlt) (hr.trans (Set.mem_Ico.mp hx1).1)
      · exact MeasureTheory.measure_singleton 0
  have stepC : ∫ y in Set.Ioi (0 : ℝ), y ^ (n - 1) • F y = ∫ ρ in r..R, h ρ := by
    simp_rw [hF_eq]
    rw [MeasureTheory.setIntegral_indicator (μ := volume) (t := Set.Ico r R) (f := h)
      measurableSet_Ico]
    rw [MeasureTheory.setIntegral_congr_set (μ := volume) hAe]
    rw [MeasureTheory.setIntegral_congr_set (μ := volume)
      (MeasureTheory.Ico_ae_eq_Ioc (μ := volume) (a := r) (b := R))]
    exact (intervalIntegral.integral_of_le hR).symm
  rw [stepA, stepB, stepC]
  simp only [nsmul_eq_mul, smul_eq_mul]
  ring

end Commons.Measure.EuclideanSpace