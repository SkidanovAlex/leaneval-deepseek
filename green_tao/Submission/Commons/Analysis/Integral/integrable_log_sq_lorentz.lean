import Mathlib
import Submission.Commons.Analysis.Integral.log_pow_div_sq_integrableOn

open MeasureTheory Set
open scoped Topology

namespace Commons.Analysis.Integral

/-- On `[0, ∞)`, the function `t ↦ (log (t+2) + 1)^2 / (a^2 + (t-c)^2)` is integrable
for every `a > 0`.  This is the half-line reduction used for the full-line statement. -/
lemma integrableOn_log_sq_add_one_div_quad_aux (a c : ℝ) (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => (Real.log (t + 2) + 1) ^ 2 / (a ^ 2 + (t - c) ^ 2)) (Set.Ici 0) := by
  set R : ℝ := max 2 (max (2 * |c|) a) with hRdef
  have hR2 : (2 : ℝ) ≤ R := le_max_left _ _
  have hRc : 2 * |c| ≤ R := le_trans (le_max_left _ _) (le_max_right _ _)
  have hRa : a ≤ R := le_trans (le_max_right _ _) (le_max_right _ _)
  have hRpos : 0 < R := by linarith
  -- Continuity on the compact piece `[0, R]`.
  have hcont : ContinuousOn (fun t : ℝ => (Real.log (t + 2) + 1) ^ 2 / (a ^ 2 + (t - c) ^ 2))
      (Set.Icc 0 R) := by
    have hlin : ContinuousOn (fun t : ℝ => t + 2) (Set.Icc 0 R) :=
      (continuous_id.add continuous_const).continuousOn
    have hlog : ContinuousOn (fun t : ℝ => Real.log (t + 2)) (Set.Icc 0 R) :=
      hlin.log (fun t ht => ne_of_gt (by have := ht.1; linarith : (0 : ℝ) < t + 2))
    have hnum : ContinuousOn (fun t : ℝ => (Real.log (t + 2) + 1) ^ 2) (Set.Icc 0 R) :=
      (hlog.add continuousOn_const).pow 2
    have hsub : ContinuousOn (fun t : ℝ => t - c) (Set.Icc 0 R) :=
      (continuous_id.continuousOn).sub continuousOn_const
    have hden : ContinuousOn (fun t : ℝ => a ^ 2 + (t - c) ^ 2) (Set.Icc 0 R) :=
      continuousOn_const.add (hsub.pow 2)
    exact ContinuousOn.div hnum hden
      (fun t _ => ne_of_gt (by positivity : (0 : ℝ) < a ^ 2 + (t - c) ^ 2))
  have hIcc : IntegrableOn (fun t : ℝ => (Real.log (t + 2) + 1) ^ 2 / (a ^ 2 + (t - c) ^ 2))
      (Set.Icc 0 R) := hcont.integrableOn_Icc
  -- Continuity on the tail `(R, ∞)`.
  have hcontIoi : ContinuousOn (fun t : ℝ => (Real.log (t + 2) + 1) ^ 2 / (a ^ 2 + (t - c) ^ 2))
      (Set.Ioi R) := by
    have hlin : ContinuousOn (fun t : ℝ => t + 2) (Set.Ioi R) :=
      (continuous_id.add continuous_const).continuousOn
    have hlog : ContinuousOn (fun t : ℝ => Real.log (t + 2)) (Set.Ioi R) :=
      hlin.log (fun t ht => ne_of_gt (by have := Set.mem_Ioi.mp ht; linarith [hRpos] : (0 : ℝ) < t + 2))
    have hnum : ContinuousOn (fun t : ℝ => (Real.log (t + 2) + 1) ^ 2) (Set.Ioi R) :=
      (hlog.add continuousOn_const).pow 2
    have hsub : ContinuousOn (fun t : ℝ => t - c) (Set.Ioi R) :=
      (continuous_id.continuousOn).sub continuousOn_const
    have hden : ContinuousOn (fun t : ℝ => a ^ 2 + (t - c) ^ 2) (Set.Ioi R) :=
      continuousOn_const.add (hsub.pow 2)
    exact ContinuousOn.div hnum hden
      (fun t _ => ne_of_gt (by positivity : (0 : ℝ) < a ^ 2 + (t - c) ^ 2))
  -- Domination on the tail by `32 * (log (t+2))^2 / (t^2 + a^2)`.
  have hbase : IntegrableOn (fun t : ℝ => (Real.log (t + 2)) ^ 2 / (t ^ 2 + a ^ 2)) (Set.Ioi R) := by
    have h0 := (log_pow_div_sq_integrableOn 2 a (by norm_num) ha).mono_set
      (Set.Ioi_subset_Ioi (le_of_lt hRpos))
    refine h0.congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp only [Real.rpow_two]
  have hmaj : IntegrableOn (fun t : ℝ => 32 * ((Real.log (t + 2)) ^ 2 / (t ^ 2 + a ^ 2)))
      (Set.Ioi R) := hbase.const_mul 32
  have hpoint : ∀ t ∈ Set.Ioi R,
      ‖(Real.log (t + 2) + 1) ^ 2 / (a ^ 2 + (t - c) ^ 2)‖
        ≤ 32 * ((Real.log (t + 2)) ^ 2 / (t ^ 2 + a ^ 2)) := by
    intro t ht
    have htR : R < t := ht
    have ht2 : (2 : ℝ) < t := lt_of_le_of_lt hR2 htR
    have hta : a < t := lt_of_le_of_lt hRa htR
    have htc : 2 * |c| < t := lt_of_le_of_lt hRc htR
    have htpos : 0 < t := by linarith
    have hlog4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]; ring
    have hlt4 : Real.log 4 < Real.log (t + 2) := Real.log_lt_log (by norm_num) (by linarith)
    have h1 : (1 : ℝ) < Real.log 4 := by rw [hlog4]; nlinarith [Real.log_two_gt_d9]
    have hlog1 : 1 ≤ Real.log (t + 2) := le_of_lt (lt_trans h1 hlt4)
    -- numerator bound
    have hnum : (Real.log (t + 2) + 1) ^ 2 ≤ 4 * (Real.log (t + 2)) ^ 2 := by
      have hL1 : Real.log (t + 2) + 1 ≤ 2 * Real.log (t + 2) := by linarith
      have h0 : 0 ≤ Real.log (t + 2) + 1 := by linarith
      have := pow_le_pow_left₀ h0 hL1 2
      nlinarith [this]
    -- denominator bound
    have hcabs : |c| < t / 2 := by linarith [abs_nonneg c]
    have hdiff : t / 2 < t - c := by linarith [le_abs_self c]
    have hsq : (t / 2) ^ 2 ≤ (t - c) ^ 2 := pow_le_pow_left₀ (by positivity) hdiff.le 2
    have hden_ge : t ^ 2 / 4 ≤ a ^ 2 + (t - c) ^ 2 := by nlinarith [hsq, sq_nonneg a]
    have hdenpos : 0 < a ^ 2 + (t - c) ^ 2 := by nlinarith [hden_ge, htpos]
    have h_one : 1 / (a ^ 2 + (t - c) ^ 2) ≤ 4 / t ^ 2 := by
      have h := one_div_le_one_div_of_le (show (0 : ℝ) < t ^ 2 / 4 by positivity) hden_ge
      rwa [one_div_div] at h
    have h_two : 4 / t ^ 2 ≤ 8 / (t ^ 2 + a ^ 2) := by
      have ha2 : a ^ 2 < t ^ 2 := by nlinarith [hta, ha, htpos]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [ha2]
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) hdenpos.le)]
    calc (Real.log (t + 2) + 1) ^ 2 / (a ^ 2 + (t - c) ^ 2)
        = (Real.log (t + 2) + 1) ^ 2 * (1 / (a ^ 2 + (t - c) ^ 2)) := by
          rw [div_eq_mul_one_div]
      _ ≤ (4 * (Real.log (t + 2)) ^ 2) * (8 / (t ^ 2 + a ^ 2)) :=
          mul_le_mul hnum (le_trans h_one h_two) (by positivity) (by positivity)
      _ = 32 * ((Real.log (t + 2)) ^ 2 / (t ^ 2 + a ^ 2)) := by ring
  have hIoi : IntegrableOn (fun t : ℝ => (Real.log (t + 2) + 1) ^ 2 / (a ^ 2 + (t - c) ^ 2))
      (Set.Ioi R) :=
    hmaj.mono' (hcontIoi.aestronglyMeasurable measurableSet_Ioi)
      (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht; exact hpoint t ht)
  have hset : Set.Icc 0 R ∪ Set.Ioi R = Set.Ici 0 := by
    ext x
    simp only [Set.mem_union, Set.mem_Icc, Set.mem_Ioi, Set.mem_Ici]
    constructor
    · rintro (⟨h, _⟩ | h)
      · exact h
      · exact le_of_lt (lt_trans hRpos h)
    · intro h
      by_cases hx : x ≤ R
      · exact Or.inl ⟨h, hx⟩
      · exact Or.inr (lt_of_not_ge hx)
  rw [← hset]
  exact hIcc.union hIoi

theorem integrable_log_sq_lorentz (a b : ℝ) (ha : 0 < a) :
    MeasureTheory.Integrable
      (fun t : ℝ => (Real.log (|t| + 2) + 1) ^ 2 / (a ^ 2 + (t - b) ^ 2)) MeasureTheory.volume := by
  -- Half-line `(0, ∞)`: this is the `c = b` case of the auxiliary lemma.
  have hkeyb := integrableOn_log_sq_add_one_div_quad_aux a b ha
  have hgIoi : IntegrableOn (fun t : ℝ => (Real.log (|t| + 2) + 1) ^ 2 / (a ^ 2 + (t - b) ^ 2))
      (Set.Ioi 0) := by
    refine (hkeyb.mono_set Set.Ioi_subset_Ici_self).congr_fun (fun t ht => ?_) measurableSet_Ioi
    rw [abs_of_pos (Set.mem_Ioi.mp ht)]
  -- Half-line `(-∞, 0]`: substitute `t ↦ -t` and use the `c = -b` case.
  have hkeynb := integrableOn_log_sq_add_one_div_quad_aux a (-b) ha
  have hfun : IntegrableOn
      (fun x : ℝ => (Real.log (|-x| + 2) + 1) ^ 2 / (a ^ 2 + (-x - b) ^ 2)) (Set.Ici 0) := by
    refine hkeynb.congr_fun (fun x hx => ?_) measurableSet_Ici
    simp only [abs_neg, abs_of_nonneg (Set.mem_Ici.mp hx)]
    have hden : a ^ 2 + (x - (-b)) ^ 2 = a ^ 2 + (-x - b) ^ 2 := by ring
    rw [hden]
  have hcomp : IntegrableOn (fun t : ℝ => (Real.log (|t| + 2) + 1) ^ 2 / (a ^ 2 + (t - b) ^ 2))
      (Set.Iic 0) := by
    simpa using hfun.comp_neg
  have hunion := hgIoi.union hcomp
  have hset : Set.Ioi (0 : ℝ) ∪ Set.Iic 0 = Set.univ := by
    ext x
    simp only [Set.mem_union, Set.mem_Ioi, Set.mem_Iic, Set.mem_univ, iff_true]
    rcases lt_trichotomy x 0 with h | h | h
    · exact Or.inr (le_of_lt h)
    · exact Or.inr (le_of_eq h)
    · exact Or.inl h
  rw [hset] at hunion
  rwa [integrableOn_univ] at hunion

end Commons.Analysis.Integral
