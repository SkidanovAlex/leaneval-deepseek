import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open _root_.MeasureTheory

namespace Commons.MeasureTheory.Integral

/-- The integrand of the target integral, as a standalone function. -/
private noncomputable def G (t : ℝ) : ℝ :=
  (Real.smoothTransition (t - 1) - Real.smoothTransition (t / 2 - 1)) * (t ^ 2)⁻¹

private lemma G_zero_of_lt_one {t : ℝ} (ht : t < 1) : G t = 0 := by
  have h1 : t - 1 ≤ 0 := by linarith
  have h2 : t / 2 - 1 ≤ 0 := by linarith
  simp only [G, Real.smoothTransition.zero_of_nonpos h1,
    Real.smoothTransition.zero_of_nonpos h2]
  ring

private lemma G_zero_of_four_lt {t : ℝ} (ht : 4 < t) : G t = 0 := by
  have h1 : 1 ≤ t - 1 := by linarith
  have h2 : 1 ≤ t / 2 - 1 := by linarith
  simp only [G, Real.smoothTransition.one_of_one_le h1, Real.smoothTransition.one_of_one_le h2]
  ring

private lemma G_zero_of_nonpos {t : ℝ} (ht : t ≤ 0) : G t = 0 :=
  G_zero_of_lt_one (by linarith)

private lemma G_nonneg : 0 ≤ G := by
  intro t
  rcases lt_or_ge t 0 with ht | ht
  · have h1 : t - 1 ≤ 0 := by linarith
    have h2 : t / 2 - 1 ≤ 0 := by linarith
    simp [G, Real.smoothTransition.zero_of_nonpos h1,
      Real.smoothTransition.zero_of_nonpos h2]
  · have hmono : Real.smoothTransition (t / 2 - 1) ≤ Real.smoothTransition (t - 1) :=
      Real.smoothTransition.monotone (by linarith)
    exact mul_nonneg (sub_nonneg.mpr hmono) (inv_nonneg.mpr (sq_nonneg t))

private lemma G_support_subset : Function.support G ⊆ Set.Icc 1 4 := by
  intro t ht
  by_contra h
  simp only [Set.mem_Icc, not_and_or, not_le] at h
  rcases h with h | h
  · exact ht (G_zero_of_lt_one h)
  · exact ht (G_zero_of_four_lt h)

private lemma G_pos_of_mem_Ioo {t : ℝ} (ht : t ∈ Set.Ioo 1 4) : 0 < G t := by
  obtain ⟨ht1, ht4⟩ := ht
  rcases lt_or_ge 2 t with h2 | h2
  · have h1 : Real.smoothTransition (t - 1) = 1 :=
      Real.smoothTransition.one_of_one_le (by linarith)
    have hlt : Real.smoothTransition (t / 2 - 1) < 1 :=
      Real.smoothTransition.lt_one_of_lt_one (by linarith)
    have hi : 0 < (t ^ 2)⁻¹ := inv_pos.mpr (pow_pos (by linarith) 2)
    simp only [G, h1]
    exact mul_pos (sub_pos.mpr hlt) hi
  · have hz : Real.smoothTransition (t / 2 - 1) = 0 :=
      Real.smoothTransition.zero_of_nonpos (by linarith)
    have hp : 0 < Real.smoothTransition (t - 1) :=
      Real.smoothTransition.pos_of_pos (by linarith)
    have hi : 0 < (t ^ 2)⁻¹ := inv_pos.mpr (pow_pos (by linarith) 2)
    simp only [G, hz, sub_zero]
    exact mul_pos hp hi

private lemma G_measurable : Measurable G := by
  unfold G
  measurability

private lemma G_norm_le_one_of_mem_Icc {x : ℝ} (hx : x ∈ Set.Icc 1 4) : ‖G x‖ ≤ 1 := by
  obtain ⟨hx1, hx4⟩ := hx
  have hnn : 0 ≤ G x := G_nonneg x
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  have hmono : Real.smoothTransition (x / 2 - 1) ≤ Real.smoothTransition (x - 1) :=
    Real.smoothTransition.monotone (by linarith)
  have hdiff_le : Real.smoothTransition (x - 1) - Real.smoothTransition (x / 2 - 1) ≤ 1 := by
    have hle := Real.smoothTransition.le_one (x - 1)
    have hnn2 := Real.smoothTransition.nonneg (x / 2 - 1)
    linarith
  have hinv_nn : 0 ≤ (x ^ 2)⁻¹ := inv_nonneg.mpr (sq_nonneg x)
  have hinv_le : (x ^ 2)⁻¹ ≤ 1 := by
    apply inv_le_one_of_one_le₀
    nlinarith [hx1]
  simp only [G]
  calc (Real.smoothTransition (x - 1) - Real.smoothTransition (x / 2 - 1)) * (x ^ 2)⁻¹
      ≤ 1 * 1 := mul_le_mul hdiff_le hinv_le hinv_nn (by norm_num)
    _ = 1 := by norm_num

theorem integral_smoothTransition_diff_div_sq_pos :
    0 < ∫ t in Set.Ioi (0 : ℝ),
      (Real.smoothTransition (t - 1) - Real.smoothTransition (t / 2 - 1)) * (t ^ 2)⁻¹ := by
  change 0 < ∫ t in Set.Ioi (0 : ℝ), G t
  have hG_int : Integrable G volume := by
    have hAE : AEStronglyMeasurable G (volume.restrict (Set.Icc 1 4)) :=
      (G_measurable.aestronglyMeasurable).mono_measure Measure.restrict_le_self
    have hbound : ∀ᵐ x ∂(volume.restrict (Set.Icc 1 4)), ‖G x‖ ≤ 1 := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      exact G_norm_le_one_of_mem_Icc hx
    have hfin : (volume : Measure ℝ) (Set.Icc 1 4) < ⊤ := by
      rw [Real.volume_Icc]
      exact ENNReal.ofReal_lt_top
    have hIntOn : IntegrableOn G (Set.Icc 1 4) volume :=
      IntegrableOn.of_bound hfin hAE 1 hbound
    have hzero_compl : ∀ x ∉ Set.Icc 1 4, G x = 0 := by
      intro x hx
      simp only [Set.mem_Icc, not_and_or, not_le] at hx
      rcases hx with h | h
      · exact G_zero_of_lt_one h
      · exact G_zero_of_four_lt h
    have hIntCompl : IntegrableOn G (Set.Icc 1 4)ᶜ volume :=
      IntegrableOn.congr_fun (f := fun _ : ℝ => (0 : ℝ)) (g := G)
        (s := (Set.Icc 1 4)ᶜ) integrableOn_zero
        (fun x hx => (hzero_compl x hx).symm) measurableSet_Icc.compl
    have hunion : IntegrableOn G (Set.Icc 1 4 ∪ (Set.Icc 1 4)ᶜ) volume :=
      (integrableOn_union (s := Set.Icc 1 4) (t := (Set.Icc 1 4)ᶜ) (f := G)
        (μ := volume)).mpr ⟨hIntOn, hIntCompl⟩
    rw [Set.union_compl_self] at hunion
    exact (integrableOn_univ (f := G) (μ := volume)).mp hunion
  have hsupp : 0 < (volume : Measure ℝ) (Function.support G) := by
    have hIoo_sub : Set.Ioo 1 4 ⊆ Function.support G := by
      intro t ht
      rw [Function.mem_support]
      exact ne_of_gt (G_pos_of_mem_Ioo ht)
    have h1 : (volume : Measure ℝ) (Set.Ioo 1 4) ≤
        (volume : Measure ℝ) (Function.support G) := measure_mono hIoo_sub
    have h2 : (volume : Measure ℝ) (Set.Ioo 1 4) = ENNReal.ofReal 3 := by
      rw [Real.volume_Ioo]
      norm_num
    have h3 : 0 < (volume : Measure ℝ) (Set.Ioo 1 4) := by
      rw [h2]
      exact ENNReal.ofReal_pos.mpr (by norm_num)
    exact lt_of_lt_of_le h3 h1
  have heq : ∫ t in Set.Ioi (0 : ℝ), G t = ∫ t, G t ∂volume :=
    setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx => G_zero_of_nonpos (le_of_not_gt hx))
  rw [heq]
  exact (integral_pos_iff_support_of_nonneg G_nonneg hG_int).mpr hsupp

end Commons.MeasureTheory.Integral