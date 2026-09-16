import Mathlib.Tactic.NormNum.RealSqrt
import Submission.Commons.Analysis.SpecialFunctions.Log.half_curve_mm_bound

noncomputable section
open scoped Real

namespace Commons.Analysis.SpecialFunctions.Log

open half_curve_mm_bound

private def Lfun : ℝ → ℝ := fun y => Real.log (2 + 2 * y)
private def Bfun : ℝ → ℝ := fun y => (1 / 2 : ℝ) * Real.log (y ^ 2 + 1 / 4)
private def Tfun : ℝ → ℝ := fun y => Real.arctan (2 * y)
private def Gfun : ℝ → ℝ := fun y => (Lfun y) ^ 2 - (Bfun y) ^ 2 - (Tfun y) ^ 2

private lemma Lfun_hasDerivAt (t : ℝ) (ht : 0 ≤ t) : HasDerivAt Lfun ((1 + t)⁻¹) t := by
  have htpos : 0 < 2 + 2 * t := by nlinarith [ht]
  have harg : HasDerivAt (fun y : ℝ => 2 + 2 * y) 2 t := by
    simpa [two_mul] using (((hasDerivAt_id t).const_mul (2 : ℝ)).const_add (2 : ℝ))
  have hlog : HasDerivAt (fun y : ℝ => Real.log (2 + 2 * y)) (2 / (2 + 2 * t)) t := by
    simpa using harg.log (ne_of_gt htpos)
  have hval : 2 / (2 + 2 * t) = (1 + t)⁻¹ := by
    field_simp [show (1 : ℝ) + t ≠ 0 by nlinarith [ht]]
  unfold Lfun
  simpa [hval] using hlog

private lemma Bfun_hasDerivAt (t : ℝ) : HasDerivAt Bfun (t * (t ^ 2 + 1 / 4)⁻¹) t := by
  have hne : t ^ 2 + 1 / 4 ≠ 0 := by positivity
  have hsq : HasDerivAt (fun y : ℝ => y ^ 2 + 1 / 4) (2 * t) t := by
    convert! ((hasDerivAt_id t).pow 2).const_add (1 / 4 : ℝ) using 1
    · ext y; simp [pow_two]; ring
    · norm_num [pow_one]
  have hlog : HasDerivAt (fun y : ℝ => Real.log (y ^ 2 + 1 / 4))
      (2 * t * (t ^ 2 + 1 / 4)⁻¹) t := by
    simpa [div_eq_mul_inv] using hsq.log hne
  have hhalf : HasDerivAt (fun y : ℝ => (1 / 2 : ℝ) * Real.log (y ^ 2 + 1 / 4))
      (t * (t ^ 2 + 1 / 4)⁻¹) t := by
    convert! hlog.const_mul (1 / 2 : ℝ) using 1
    field_simp [hne]
  unfold Bfun
  simpa using hhalf

private lemma Tfun_hasDerivAt (t : ℝ) : HasDerivAt Tfun (2 * (1 + 4 * t ^ 2)⁻¹) t := by
  have harg : HasDerivAt (fun y : ℝ => 2 * y) 2 t := by
    simpa using (hasDerivAt_id t).const_mul (2 : ℝ)
  have hat : HasDerivAt (fun y : ℝ => Real.arctan (2 * y)) (2 * (1 + 4 * t ^ 2)⁻¹) t := by
    convert! (Real.hasDerivAt_arctan (2 * t)).comp t harg using 1
    field_simp [show (1 + 4 * t ^ 2 : ℝ) ≠ 0 by positivity, show (1 + (2*t)^2 : ℝ) ≠ 0 by positivity]
    all_goals ring
  unfold Tfun
  simpa using hat

private lemma Gfun_hasDerivAt_raw (t : ℝ) (ht : 0 ≤ t) :
    HasDerivAt Gfun
      (2 * Lfun t * (1 + t)⁻¹ - 2 * Bfun t * (t * (t ^ 2 + 1 / 4)⁻¹) -
        2 * Tfun t * (2 * (1 + 4 * t ^ 2)⁻¹)) t := by
  have hL2 : HasDerivAt (fun y : ℝ => (Lfun y) ^ 2) (2 * Lfun t * (1 + t)⁻¹) t := by
    convert! (Lfun_hasDerivAt t ht).pow 2 using 1
    norm_num [pow_one]
  have hB2 : HasDerivAt (fun y : ℝ => (Bfun y) ^ 2)
      (2 * Bfun t * (t * (t ^ 2 + 1 / 4)⁻¹)) t := by
    convert! (Bfun_hasDerivAt t).pow 2 using 1
    norm_num [pow_one]
  have hT2 : HasDerivAt (fun y : ℝ => (Tfun y) ^ 2)
      (2 * Tfun t * (2 * (1 + 4 * t ^ 2)⁻¹)) t := by
    convert! (Tfun_hasDerivAt t).pow 2 using 1
    norm_num [pow_one]
  have hsub : HasDerivAt (fun y : ℝ => (Lfun y) ^ 2 - (Bfun y) ^ 2)
      (2 * Lfun t * (1 + t)⁻¹ - 2 * Bfun t * (t * (t ^ 2 + 1 / 4)⁻¹)) t := by
    convert! hL2.sub hB2 using 1
  have htot : HasDerivAt (fun y : ℝ => (Lfun y) ^ 2 - (Bfun y) ^ 2 - (Tfun y) ^ 2)
      (2 * Lfun t * (1 + t)⁻¹ - 2 * Bfun t * (t * (t ^ 2 + 1 / 4)⁻¹) -
        2 * Tfun t * (2 * (1 + 4 * t ^ 2)⁻¹)) t := by
    convert! hsub.sub hT2 using 1
  unfold Gfun
  simpa using htot


-- positivity of the derivative of G via mm_bound
private lemma Gfun_deriv_nonneg (t : ℝ) (ht : 0 ≤ t) : 0 ≤ deriv Gfun t := by
  have hd := Gfun_hasDerivAt_raw t ht
  rw [hd.deriv]
  -- convert mm_bound into the "mm' ≥ 0" form with Bfun
  have hmm := half_curve_mm_bound t ht
  have hlogeq : Real.log (Real.sqrt (t ^ 2 + 1 / 4)) = Bfun t := by
    rw [Bfun]
    rw [Real.log_sqrt]
    · ring
    · positivity
  have hmm0 : 0 ≤ (1 + 4 * t ^ 2) * Real.log (2 + 2 * t) -
      4 * t * (1 + t) * Real.log (Real.sqrt (t ^ 2 + 1 / 4)) - 2 * (1 + t) * Real.arctan (2 * t) := by
    nlinarith
  have hmm' : 0 ≤ (1 + 4 * t ^ 2) * Lfun t - 4 * t * (1 + t) * Bfun t - 2 * (1 + t) * Tfun t := by
    rw [show Real.log (2 + 2 * t) = Lfun t by rfl] at hmm0
    rw [hlogeq] at hmm0
    rw [show Real.arctan (2 * t) = Tfun t by rfl] at hmm0
    exact hmm0
  -- algebra: raw derivative = 2 * mm' / ((1+t)*(1+4t²))
  have hne1 : (1 : ℝ) + t ≠ 0 := by nlinarith [ht]
  have hne2 : (1 : ℝ) + 4 * t ^ 2 ≠ 0 := by positivity
  have hne3 : t ^ 2 + 1 / 4 ≠ 0 := by positivity
  have hraw : 0 ≤ 2 * Lfun t * (1 + t)⁻¹ - 2 * Bfun t * (t * (t ^ 2 + 1 / 4)⁻¹) -
      2 * Tfun t * (2 * (1 + 4 * t ^ 2)⁻¹) := by
    have heq : 2 * Lfun t * (1 + t)⁻¹ - 2 * Bfun t * (t * (t ^ 2 + 1 / 4)⁻¹) -
          2 * Tfun t * (2 * (1 + 4 * t ^ 2)⁻¹) =
        2 * ((1 + 4 * t ^ 2) * Lfun t - 4 * t * (1 + t) * Bfun t - 2 * (1 + t) * Tfun t) /
          ((1 + t) * (1 + 4 * t ^ 2)) := by
      have hrel : (1 : ℝ) + 4 * t ^ 2 = 4 * (t ^ 2 + 1 / 4) := by ring
      rw [hrel]
      field_simp [hne1, hne2, hne3, mul_comm, mul_left_comm, mul_assoc]
    rw [heq]
    have hposd : 0 < ((1 : ℝ) + t) * (1 + 4 * t ^ 2) := by positivity
    exact div_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hmm') (le_of_lt hposd)
  exact hraw

-- component values at 0
private lemma Lfun_zero : Lfun 0 = Real.log 2 := by simp [Lfun]

private lemma Tfun_zero : Tfun 0 = 0 := by simp [Tfun]

private lemma Bfun_zero : Bfun 0 = -Real.log 2 := by
  unfold Bfun
  have h1 : (0 : ℝ) ^ 2 + 1 / 4 = (4 : ℝ)⁻¹ := by norm_num
  rw [h1, Real.log_inv]
  have h4 : (4 : ℝ) = 2 ^ 2 := by norm_num
  rw [h4, Real.log_pow]
  ring

private lemma Gfun_zero : Gfun 0 = 0 := by
  unfold Gfun
  rw [Lfun_zero, Bfun_zero, Tfun_zero]
  ring

-- G ≥ 0 on [0,∞)
private lemma Gfun_nonneg (t : ℝ) (ht : 0 ≤ t) : 0 ≤ Gfun t := by
  by_cases ht0 : t = 0
  · rw [ht0, Gfun_zero]
  · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
    have hcont : ContinuousOn Gfun (Set.Icc (0 : ℝ) t) := by
      intro y hy
      exact (Gfun_hasDerivAt_raw y hy.1).continuousAt.continuousWithinAt
    have hdiff : DifferentiableOn ℝ Gfun (interior (Set.Icc (0 : ℝ) t)) := by
      intro y hy
      have hyi : y ∈ Set.Ioo (0 : ℝ) t := by simpa [interior_Icc, htpos] using hy
      exact (Gfun_hasDerivAt_raw y (le_of_lt hyi.1)).differentiableAt.differentiableWithinAt
    have hnonneg : ∀ y ∈ interior (Set.Icc (0 : ℝ) t), 0 ≤ deriv Gfun y := by
      intro y hy
      have hyi : y ∈ Set.Ioo (0 : ℝ) t := by simpa [interior_Icc, htpos] using hy
      exact Gfun_deriv_nonneg y (le_of_lt hyi.1)
    have hmono := monotoneOn_of_deriv_nonneg (convex_Icc (0 : ℝ) t) hcont hdiff hnonneg
    have hmem0 : (0 : ℝ) ∈ Set.Icc 0 t := by exact ⟨le_rfl, ht⟩
    have hmemt : t ∈ Set.Icc 0 t := by exact ⟨ht, le_rfl⟩
    have hle := hmono hmem0 hmemt ht
    rw [Gfun_zero] at hle
    exact hle



-- KEY inequality: sqrt(B²+T²) ≤ L, from G ≥ 0
private lemma half_curve_key_local (t : ℝ) (ht : 0 ≤ t) :
    Real.sqrt (((1 / 2 : ℝ) * Real.log (t ^ 2 + 1 / 4)) ^ 2 + (Real.arctan (2 * t)) ^ 2) ≤
      Real.log (2 + 2 * t) := by
  have hG := Gfun_nonneg t ht
  have hsq : (Bfun t) ^ 2 + (Tfun t) ^ 2 ≤ (Lfun t) ^ 2 := by
    unfold Gfun at hG
    nlinarith
  have hL : 0 ≤ Lfun t := by
    unfold Lfun
    exact Real.log_nonneg (by linarith)
  have hs : Real.sqrt ((Bfun t) ^ 2 + (Tfun t) ^ 2) ≤ Lfun t := by
    exact (Real.sqrt_le_iff).2 ⟨hL, hsq⟩
  unfold Bfun Tfun Lfun at hs
  simpa [pow_two] using hs

-- ============ assembly ============
lemma log_two_le_one : Real.log 2 ≤ (1:ℝ) := by
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
  linarith

lemma sqrt_sq_add_quarter_ge_half (t : ℝ) : (1 / 2 : ℝ) ≤ Real.sqrt (t ^ 2 + 1 / 4) := by
  have hs : (1:ℝ)/4 ≤ t ^ 2 + 1/4 := by nlinarith [sq_nonneg t]
  have hs' : Real.sqrt (1 / 4 : ℝ) ≤ Real.sqrt (t ^ 2 + 1 / 4) := Real.sqrt_le_sqrt hs
  norm_num at hs'
  exact hs'

lemma sqrt_sq_add_quarter_ge_one (t : ℝ) (ht1 : 1 ≤ t) : (1 : ℝ) ≤ Real.sqrt (t ^ 2 + 1 / 4) := by
  have hs : (1:ℝ) ≤ t ^ 2 + 1/4 := by nlinarith [sq_nonneg (t - 1), ht1]
  have hs' : Real.sqrt (1:ℝ) ≤ Real.sqrt (t ^ 2 + 1 / 4) := Real.sqrt_le_sqrt hs
  have hs1 : Real.sqrt (1 : ℝ) = 1 := by norm_num
  rwa [hs1] at hs'

lemma inv_two_sqrt_le_half (t : ℝ) (ht1 : 1 ≤ t) :
    ((1 : ℝ) / 2) * (Real.sqrt (t ^ 2 + 1 / 4))⁻¹ ≤ 1 / 2 := by
  have hu1 : 1 ≤ Real.sqrt (t ^ 2 + 1 / 4) := sqrt_sq_add_quarter_ge_one t ht1
  have h : (Real.sqrt (t ^ 2 + 1 / 4))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hu1
  nlinarith

lemma inv_two_sqrt_le_one (t : ℝ) (_ht : 0 ≤ t) :
    ((1 : ℝ) / 2) * (Real.sqrt (t ^ 2 + 1 / 4))⁻¹ ≤ 1 := by
  have hu : 0 < Real.sqrt (t ^ 2 + 1 / 4) := Real.sqrt_pos.2 (by positivity)
  have huh : 1 / 2 ≤ Real.sqrt (t ^ 2 + 1 / 4) := sqrt_sq_add_quarter_ge_half t
  have h : (Real.sqrt (t ^ 2 + 1 / 4))⁻¹ ≤ 2 := by
    rw [inv_eq_one_div]
    exact (one_div_le hu (by norm_num : (0:ℝ) < 2)).2 huh
  nlinarith

theorem half_curve_log_le (t : ℝ) (ht : 0 ≤ t) :
    Real.sqrt ((((1 : ℝ) / 2) * Real.log (t ^ 2 + (1 : ℝ) / 4)) ^ 2 + (Real.arctan (2 * t)) ^ 2) +
        ((1 : ℝ) / 2) * (Real.sqrt (t ^ 2 + (1 : ℝ) / 4))⁻¹ ≤
      Real.log (2 + t) + (3 : ℝ) / 2 := by
  have hkey := half_curve_key_local t ht
  by_cases h1 : t ≤ 1
  · have hsq : ((1 : ℝ) / 2) * (Real.sqrt (t ^ 2 + 1 / 4))⁻¹ ≤ 1 := inv_two_sqrt_le_one t ht
    have hmon : 2 + 2 * t ≤ (4 / 3) * (2 + t) := by nlinarith [h1]
    have hle43 : Real.log (2 + 2 * t) ≤ Real.log ((4 / 3) * (2 + t)) :=
      Real.log_le_log (by positivity) hmon
    have hsplit : Real.log ((4 / 3) * (2 + t)) = Real.log (4 / 3) + Real.log (2 + t) := by
      rw [Real.log_mul]
      · norm_num
      · positivity
    have h43 : Real.log (4 / 3) ≤ 1 / 3 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4 / 3)
      linarith
    have hlog : Real.log (2 + 2 * t) ≤ Real.log (2 + t) + 1 / 3 := by
      rw [hsplit] at hle43
      linarith
    nlinarith
  · have ht1 : 1 ≤ t := by linarith
    have hsq : ((1 : ℝ) / 2) * (Real.sqrt (t ^ 2 + 1 / 4))⁻¹ ≤ 1 / 2 := inv_two_sqrt_le_half t ht1
    have hmon : 2 + 2 * t ≤ 2 * (2 + t) := by nlinarith
    have hle2 : Real.log (2 + 2 * t) ≤ Real.log (2 * (2 + t)) :=
      Real.log_le_log (by positivity) hmon
    have hsplit : Real.log (2 * (2 + t)) = Real.log 2 + Real.log (2 + t) := by
      rw [Real.log_mul]
      · norm_num
      · positivity
    have hlog : Real.log (2 + 2 * t) ≤ Real.log (2 + t) + Real.log 2 := by
      rw [hsplit] at hle2
      linarith
    have hl2 : Real.log 2 ≤ 1 := log_two_le_one
    nlinarith

end Commons.Analysis.SpecialFunctions.Log