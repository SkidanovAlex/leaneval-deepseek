import Mathlib

namespace Work.TMComp.RealCartan

open MeasureTheory Set intervalIntegral
open scoped Real

set_option linter.unnecessarySimpa false

/-- The integral of `u ↦ log (ρ / u)` over `(0, ρ]` equals `ρ`. -/
private lemma integral_log_div_self_pos {ρ : ℝ} (hρ : 0 < ρ) :
    ∫ u in (0:ℝ)..ρ, Real.log (ρ / u) = ρ := by
  have hcongr : ∫ u in (0:ℝ)..ρ, Real.log (ρ / u)
      = ∫ u in (0:ℝ)..ρ, (Real.log ρ - Real.log u) := by
    apply intervalIntegral.integral_congr_ae
    refine Filter.Eventually.of_forall (fun u hu => ?_)
    rw [Set.uIoc_of_le hρ.le] at hu
    exact Real.log_div (ne_of_gt hρ) (ne_of_gt hu.1)
  rw [hcongr, intervalIntegral.integral_sub intervalIntegrable_const intervalIntegrable_log',
      intervalIntegral.integral_const, integral_log_from_zero]
  simp only [sub_zero, smul_eq_mul]
  ring

/-- `u ↦ log |u|` is interval integrable on every interval. -/
private lemma intervalIntegrable_log_abs (a b : ℝ) :
    IntervalIntegrable (fun u : ℝ => Real.log |u|) volume a b := by
  have h := (MeromorphicOn.id (U := Set.uIcc a b)).intervalIntegrable_log_norm
  simpa [Real.norm_eq_abs] using h

/-- `u ↦ log (ρ / |u|)` is interval integrable on intervals whose interior avoids `0`. -/
private lemma intervalIntegrable_log_div_abs {ρ : ℝ} (hρ : 0 < ρ) {a b : ℝ}
    (h0 : 0 ∉ Set.uIoo a b) :
    IntervalIntegrable (fun u : ℝ => Real.log (ρ / |u|)) volume a b := by
  refine (IntervalIntegrable.sub (intervalIntegrable_const (c := Real.log ρ))
    (intervalIntegrable_log_abs a b)).congr_uIoo ?_
  intro u hu
  have hne : u ≠ 0 := fun h => h0 (h ▸ hu)
  exact (Real.log_div (ne_of_gt hρ) (abs_ne_zero.mpr hne)).symm

/-- The integral of `u ↦ log (ρ / |u|)` over `[-ρ, ρ]` equals `2 ρ`. -/
private lemma integral_log_abs_div_self {ρ : ℝ} (hρ : 0 < ρ) :
    ∫ u in (-ρ)..ρ, Real.log (ρ / |u|) = 2 * ρ := by
  have hg0 : IntervalIntegrable (fun u : ℝ => Real.log (ρ / |u|)) volume (0:ℝ) ρ :=
    intervalIntegrable_log_div_abs hρ (by rw [Set.uIoo_of_le hρ.le]; simp)
  have hgm : IntervalIntegrable (fun u : ℝ => Real.log (ρ / |u|)) volume (-ρ) (0:ℝ) :=
    intervalIntegrable_log_div_abs hρ
      (by rw [Set.uIoo_of_le (by linarith : -ρ ≤ (0:ℝ))]; simp)
  have hadj := intervalIntegral.integral_add_adjacent_intervals hgm hg0
  have hsym : ∫ u in (0:ℝ)..ρ, Real.log (ρ / |u|) = ∫ u in (-ρ)..0, Real.log (ρ / |u|) := by
    have h := intervalIntegral.integral_comp_neg (fun u : ℝ => Real.log (ρ / |u|))
      (a := (0:ℝ)) (b := ρ)
    simp only [abs_neg, neg_zero] at h
    exact h
  have hC : ∫ u in (0:ℝ)..ρ, Real.log (ρ / |u|) = ρ := by
    have hcongr : ∫ u in (0:ℝ)..ρ, Real.log (ρ / |u|)
        = ∫ u in (0:ℝ)..ρ, Real.log (ρ / u) := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [Set.uIcc_of_le hρ.le] at hu
      change Real.log (ρ / |u|) = Real.log (ρ / u)
      rw [abs_of_nonneg hu.1]
    rw [hcongr]
    exact integral_log_div_self_pos hρ
  rw [hadj.symm, hsym.symm, hC]
  ring

theorem rcLogKernel_int {ρ s : ℝ} (hρ : 0 < ρ) :
    ∫ t : ℝ, max (Real.log (ρ / |t - s|)) 0 = 2 * ρ := by
  -- Translation invariance reduces the parameter `s` to `0`.
  have htrans : ∫ t : ℝ, max (Real.log (ρ / |t - s|)) 0
      = ∫ u : ℝ, max (Real.log (ρ / |u|)) 0 :=
    integral_sub_right_eq_self (fun u : ℝ => max (Real.log (ρ / |u|)) 0) s
  rw [htrans]
  -- The integrand vanishes off `(-ρ, ρ]`.
  have hvan : ∀ u : ℝ, u ∉ Set.Ioc (-ρ) ρ → max (Real.log (ρ / |u|)) 0 = 0 := by
    intro u hu
    have hu' : u ≤ -ρ ∨ ρ < u := by
      by_cases h : u ≤ -ρ
      · exact Or.inl h
      · by_cases h2 : u ≤ ρ
        · exact absurd (Set.mem_Ioc.mpr ⟨not_le.mp h, h2⟩) hu
        · exact Or.inr (not_le.mp h2)
    have hge : ρ ≤ |u| := by
      rcases hu' with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    have hpos : 0 < |u| := lt_of_lt_of_le hρ hge
    have hle1 : ρ / |u| ≤ 1 := (div_le_one hpos).mpr hge
    rw [max_eq_right (Real.log_nonpos (le_of_lt (div_pos hρ hpos)) hle1)]
  have h1 : ∫ u : ℝ, max (Real.log (ρ / |u|)) 0
      = ∫ u in (-ρ)..ρ, max (Real.log (ρ / |u|)) 0 :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero hvan).symm.trans
      (integral_of_le (by linarith : -ρ ≤ ρ)).symm
  rw [h1]
  -- On `[-ρ, ρ]` the truncated logarithm is the plain logarithm.
  have h2 : ∫ u in (-ρ)..ρ, max (Real.log (ρ / |u|)) 0
      = ∫ u in (-ρ)..ρ, Real.log (ρ / |u|) := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [Set.uIcc_of_le (by linarith : -ρ ≤ ρ)] at hu
    have hle : |u| ≤ ρ := abs_le.mpr ⟨hu.1, hu.2⟩
    by_cases h0 : u = 0
    · subst h0; simp
    · have hpos : 0 < |u| := abs_pos.mpr h0
      have hge1 : 1 ≤ ρ / |u| := (one_le_div hpos).mpr hle
      change max (Real.log (ρ / |u|)) 0 = Real.log (ρ / |u|)
      rw [max_eq_left (Real.log_nonneg hge1)]
  rw [h2]
  exact integral_log_abs_div_self hρ

end Work.TMComp.RealCartan
