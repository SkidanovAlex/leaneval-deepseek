/-
# The upper-profile mass beyond `3.99`

Target: `∫_{Ici (399/100)} riPhi ≤ 499/12500`, i.e. `riPsi (499/100) ≤ 1/125`.

Route (all quantities explicit):

* `riPsi (499/100) = (∫_{Ici (399/100)} riPhi) / (499/100)` (the delay identity `4.99·riPsi = …`);
* `∫_{Ici (399/100)} riPhi = ∫_{Ici 3} riPhi - ∫_3^{399/100} riPhi = Ttot - ∫_3^{399/100} riPhi`;
* `Ttot = 4 - 3 log 3 - Ctot·log 3 ≤ 4 - 3·l₃ - c·l₃` where `c := 551/1000 ≤ Ctot` and `l₃` is a
  rational lower bound for `log 3` (`Ctot_lower_lim` + the mass-moment identity);
* for `s ∈ [3, 399/100]`, `s·riPhi s = ∫_{Ici (s-1)} riPsi = Ctot - ∫_2^{s-1} riPsi`, and
  `∫_2^x riPsi ≤ PsiUp x` where (`x = s-1 ∈ [2, 299/100]`)
  `PsiUp x = (x-2) - 2(3+c)·(2(x-2)/(x+2) + 2/x - 1) ≥ ∫_2^x riPsi`,
  because on `[2,3]` (`riPsi_eq_of_mem_Icc`) `riPsi u = 1 - (3+Ctot) log(u-1)/u` and
  `log y ≥ 2(y-1)/(y+1)`;
* hence `∫_3^{399/100} riPhi ≥ c·log(399/300) - ∫_2^{299/100} PsiUp x/(x+1) dx`, and the last
  integral is elementary (the integrand has the antiderivative
  `x - 2K log x + (9K-3) log(x+1) - 8K log(x+2)`, `K = 2(3+c)`).

The final numerical chain gives `≈ 0.0284 ≤ 0.03992`.
-/
import Mathlib
import Submission.Work.NumberTheory.Chen.APSwitchUpper.prof
import Submission.Work.NumberTheory.Chen.APSwitchUpper.profC_intervalIntegrable
import Submission.Work.NumberTheory.Chen.APSwitchUpper.riPhiDelay
import Submission.Work.NumberTheory.Chen.APSwitchUpper.riPhiLevelCore
import Submission.Work.NumberTheory.Chen.APSwitchUpper.riPhi_le_env
import Submission.Work.NumberTheory.Chen.APSwitchUpper.riPhiEnvBasic
import Submission.Work.NumberTheory.Chen.ApSumTenth.TailAux
import Submission.Work.NumberTheory.Chen.ApSumTenth.riPhi_delay_identity
import Submission.Work.NumberTheory.Chen.ApSumTenth.riPhi_delay_system
import Submission.Work.NumberTheory.Chen.ApSumTenth.integral_riPhi_Ici_one
import Submission.Work.NumberTheory.Chen.Ttot_eq_integral_riPhi

set_option maxHeartbeats 1000000

namespace Work.NumberTheory.Chen

open MeasureTheory intervalIntegral
open Work.NumberTheory.Chen.APSwitchUpper
open Work.NumberTheory.Chen.ApSumTenth

namespace RiPhiTail499

noncomputable section

/-- The numerical lower bound for the total mass `Ctot`. -/
def cmin : ℝ := 551 / 1000

/-- `K = 2(3+c)`. -/
def capK : ℝ := 2 * (3 + cmin)

/-- The explicit majorant of `∫_2^x riPsi` on `[2, 3]`. -/
def PsiUp (x : ℝ) : ℝ := (x - 2) - capK * (2 * (x - 2) / (x + 2) + 2 / x - 1)

lemma cmin_pos : (0 : ℝ) < cmin := by norm_num [cmin]

lemma capK_eq : capK = 7102 / 1000 := by norm_num [capK, cmin]

/-- **The mass `Ctot` is at least `0.551`.**  From `Cv_lower_lim` and the mass-moment identity. -/
theorem Ctot_ge_cmin : cmin ≤ Ctot := by
  have h1 := Cv_lower_lim
  have h2 : Ttot = 4 - 3 * Real.log 3 - Ctot * Real.log 3 := by
    linarith [mass_moment_eq]
  rw [h2] at h1
  have hk : (0.35379 : ℝ) ≤ mKap := by
    have h2' := Real.log_two_gt_d9
    have h3' := Real.log_three_lt_d9
    rw [mKap]; linarith
  have hl2 : Real.log 2 ≤ 0.6931471808 := Real.log_two_lt_d9.le
  have hl3 : Real.log 3 ≤ 1.0986122888 := Real.log_three_lt_d9.le
  have hl2nn : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hl3nn : (0 : ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hCnn : (0 : ℝ) ≤ Ctot := tsum_nonneg (fun i => P_nonneg i)
  have hprod : Real.log 3 * Real.log 2 ≤ 0.761501 := by
    have h := mul_le_mul hl3 hl2 hl2nn (le_trans hl3nn hl3)
    norm_num at h
    linarith
  set L := Real.log 3 * Real.log 2 with hL
  have hprod' : L ≤ 0.761501 := by rw [hL]; linarith [hprod]
  have hexp : (3 + Ctot) * mKap + (4 - 3 * Real.log 3 - Ctot * Real.log 3 - 4) * Real.log 2 + 2
      = 3 * mKap - 3 * L + 2 + Ctot * (mKap - L) := by
    rw [hL]; ring
  rw [hexp] at h1
  have hkey : Ctot * (1 - mKap + L) ≥ 3 * mKap - 3 * L + 2 := by nlinarith [h1]
  have hDpos : (0 : ℝ) < 1 - mKap + L := by nlinarith [hk, hprod']
  have hN : (0.7768 : ℝ) ≤ 3 * mKap - 3 * L + 2 := by nlinarith [hk, hprod']
  have hDup : 1 - mKap + L ≤ 1.40772 := by nlinarith [hk, hprod']
  have hlinc : Ctot * 1.40772 ≥ 0.7768 := by nlinarith [hkey, hN, hDup, hCnn, hDpos]
  rw [cmin]
  nlinarith [hlinc]

/-- **`Ttot` is bounded by the explicit upper bound.** -/
theorem Ttot_le_cmin : Ttot ≤ 4 - 3 * logLowRat 3 - cmin * logLowRat 3 := by
  have h2 : Ttot = 4 - 3 * Real.log 3 - Ctot * Real.log 3 := by linarith [mass_moment_eq]
  have hl3 : logLowRat 3 ≤ Real.log 3 := logLowRat_le (by norm_num)
  have hnl3 : (0 : ℝ) ≤ logLowRat 3 := by norm_num [logLowRat]
  have h3 : (0 : ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hCnn : (0 : ℝ) ≤ Ctot := tsum_nonneg (fun i => P_nonneg i)
  have hc : cmin ≤ Ctot := Ctot_ge_cmin
  have hprod : cmin * logLowRat 3 ≤ Ctot * Real.log 3 := mul_le_mul hc hl3 hnl3 hCnn
  have h3' : 3 * Real.log 3 ≥ 3 * logLowRat 3 := by linarith
  rw [h2]
  linarith

/-- `log y ≥ 2(y-1)/(y+1)` for `y ≥ 1`. -/
theorem two_mul_sub_div_le_log {y : ℝ} (hy : 1 ≤ y) :
    2 * (y - 1) / (y + 1) ≤ Real.log y := by
  rcases eq_or_lt_of_le hy with h | h
  · rw [← h]; simp
  have hy0 : 0 < y := by linarith
  set t : ℝ := (y - 1) / (y + 1) with ht
  have ht0 : 0 ≤ t := by rw [ht]; positivity
  have ht1 : t < 1 := by
    rw [ht, div_lt_one (by linarith)]; linarith
  have hkey : (1 + t) / (1 - t) = y := by
    rw [ht]; field_simp; ring
  have hsum := Real.sum_range_le_log_div ht0 ht1 1
  rw [hkey] at hsum
  have hsum' : t ≤ 1 / 2 * Real.log y := by simpa using hsum
  have h2 : 2 * ((y - 1) / (y + 1)) ≤ Real.log y := by linarith [hsum']
  calc 2 * (y - 1) / (y + 1) = 2 * ((y - 1) / (y + 1)) := by ring
    _ ≤ Real.log y := h2


/-- **`riPsi` is dominated by the rational majorant on `[2, 299/100]`.** -/
theorem riPsi_le_Bup {u : ℝ} (h2 : 2 ≤ u) (h3 : u ≤ 299 / 100) :
    riPsi u ≤ 1 - (3 + cmin) * (2 * (u - 2) / u ^ 2) := by
  have hu3 : u ≤ 3 := by linarith
  have hpsi : riPsi u = 1 - (3 + Ctot) * Real.log (u - 1) / u := riPsi_eq_of_mem_Icc h2 hu3
  have hu0 : 0 < u := by linarith
  have hlog : 2 * (u - 2) / u ≤ Real.log (u - 1) := by
    have h := two_mul_sub_div_le_log (y := u - 1) (by linarith)
    have e : 2 * (u - 1 - 1) / (u - 1 + 1) = 2 * (u - 2) / u := by ring
    rwa [e] at h
  have hnn : (0 : ℝ) ≤ 2 * (u - 2) / u := by positivity
  have hc : cmin ≤ Ctot := Ctot_ge_cmin
  have hCnn : (0 : ℝ) ≤ 3 + Ctot := by
    have h : (0 : ℝ) < cmin := by norm_num [cmin]
    linarith
  have hA : (3 + cmin) * (2 * (u - 2) / u) ≤ (3 + Ctot) * (2 * (u - 2) / u) :=
    mul_le_mul_of_nonneg_right (show (3 + cmin) ≤ 3 + Ctot by linarith) hnn
  have hB : (3 + Ctot) * (2 * (u - 2) / u) ≤ (3 + Ctot) * Real.log (u - 1) :=
    mul_le_mul_of_nonneg_left hlog hCnn
  have h1 : (3 + cmin) * (2 * (u - 2) / u) ≤ (3 + Ctot) * Real.log (u - 1) := le_trans hA hB
  have h2' : (3 + cmin) * (2 * (u - 2) / u ^ 2) ≤ (3 + Ctot) * Real.log (u - 1) / u := by
    have h := div_le_div_of_nonneg_right h1 hu0.le
    have e : (3 + cmin) * (2 * (u - 2) / u) / u = (3 + cmin) * (2 * (u - 2) / u ^ 2) := by
      rw [mul_div_assoc, div_div, pow_two]
    rwa [e] at h
  rw [hpsi]
  linarith

lemma derivval_eq {u : ℝ} (hu : 0 < u) :
    1 - 2 * (3 + cmin) * (u⁻¹ + -(2 / u ^ 2)) = 1 - (3 + cmin) * (2 * (u - 2) / u ^ 2) := by
  have hu' : u ≠ 0 := ne_of_gt hu
  have h1 : u⁻¹ = u / u ^ 2 := by
    rw [eq_div_iff (pow_ne_zero 2 hu'), pow_two, ← mul_assoc, inv_mul_cancel₀ hu', one_mul]
  rw [h1]
  ring

/-- The antiderivative of `1 - (3+c)·2(u-2)/u²`. -/
theorem hasDerivAt_PsiUpIntegrand {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun v : ℝ => v - 2 * (3 + cmin) * (Real.log v + 2 / v))
      (1 - 2 * (3 + cmin) * (u⁻¹ + -(2 / u ^ 2))) u := by
  have h1 : HasDerivAt (fun v : ℝ => v) 1 u := hasDerivAt_id u
  have h2 : HasDerivAt (fun v : ℝ => Real.log v) u⁻¹ u := Real.hasDerivAt_log (ne_of_gt hu)
  have h3 : HasDerivAt (fun v : ℝ => 2 / v) (-(2 / u ^ 2)) u := by
    have h := (hasDerivAt_inv (x := u) (ne_of_gt hu)).const_mul (2 : ℝ)
    have h4 : 2 * (-(u ^ 2)⁻¹) = -(2 / u ^ 2) := by ring
    rw [h4] at h
    exact h
  have h5 : HasDerivAt (fun v : ℝ => Real.log v + 2 / v) (u⁻¹ + -(2 / u ^ 2)) u := h2.add h3
  have h6 : HasDerivAt (fun v : ℝ => 2 * (3 + cmin) * (Real.log v + 2 / v))
      (2 * (3 + cmin) * (u⁻¹ + -(2 / u ^ 2))) u := h5.const_mul _
  exact h1.sub h6

/-- **`∫_2^x riPsi ≤ PsiUp x`** for `x ∈ [2, 299/100]`. -/
theorem integral_riPsi_le_PsiUp {x : ℝ} (h2 : 2 ≤ x) (hx : x ≤ 299 / 100) :
    (∫ u in (2 : ℝ)..x, riPsi u) ≤ PsiUp x := by
  have hcont : ContinuousOn (fun u : ℝ => 1 - (3 + cmin) * (2 * (u - 2) / u ^ 2))
      (Set.uIcc (2 : ℝ) x) := by
    rw [Set.uIcc_of_le h2]
    refine ContinuousOn.sub continuousOn_const ?_
    refine (ContinuousOn.div (by fun_prop) (by fun_prop) ?_).const_mul (3 + cmin)
    intro u hu
    rw [Set.mem_Icc] at hu
    exact pow_ne_zero 2 (ne_of_gt (by linarith [hu.1] : (0:ℝ) < u))
  have hint : IntervalIntegrable (fun u : ℝ => 1 - (3 + cmin) * (2 * (u - 2) / u ^ 2))
      volume (2 : ℝ) x := hcont.intervalIntegrable
  have hmono : (∫ u in (2 : ℝ)..x, riPsi u)
      ≤ ∫ u in (2 : ℝ)..x, (1 - (3 + cmin) * (2 * (u - 2) / u ^ 2)) := by
    refine intervalIntegral.integral_mono_on h2 ?_ hint ?_
    · refine IntegrableOn.intervalIntegrable (μ := volume) ?_
      rw [Set.uIcc_of_le h2]
      exact integrableOn_riPsi_Ici_two.mono_set Set.Icc_subset_Ici_self
    · intro u hu
      rw [Set.mem_Icc] at hu
      exact riPsi_le_Bup hu.1 (by linarith [hu.2])
  have hval : (∫ u in (2 : ℝ)..x, (1 - (3 + cmin) * (2 * (u - 2) / u ^ 2)))
      = (x - 2) - 2 * (3 + cmin) * (Real.log (x / 2) + 2 / x - 1) := by
    have hderiv : ∀ u ∈ Set.uIcc (2 : ℝ) x,
        HasDerivAt (fun v : ℝ => v - 2 * (3 + cmin) * (Real.log v + 2 / v))
          (1 - (3 + cmin) * (2 * (u - 2) / u ^ 2)) u := by
      intro u hu
      rw [Set.uIcc_of_le h2] at hu
      rw [← derivval_eq (by linarith [hu.1] : (0:ℝ) < u)]
      exact hasDerivAt_PsiUpIntegrand (by linarith [hu.1])
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
    have h2pos : (0 : ℝ) < 2 := by norm_num
    have hlogdiv : Real.log (x / 2) = Real.log x - Real.log 2 :=
      Real.log_div (ne_of_gt (by linarith : (0:ℝ) < x)) (ne_of_gt h2pos)
    rw [hlogdiv]
    ring
  rw [hval] at hmono
  have hlog : 2 * (x / 2 - 1) / (x / 2 + 1) ≤ Real.log (x / 2) :=
    two_mul_sub_div_le_log (y := x / 2) (by linarith)
  have hlog' : 2 * (x - 2) / (x + 2) ≤ Real.log (x / 2) := by
    have e : 2 * (x / 2 - 1) / (x / 2 + 1) = 2 * (x - 2) / (x + 2) := by
      have h1 : (x / 2 + 1) ≠ 0 := by positivity
      have h2' : x + 2 ≠ 0 := by linarith
      field_simp
    rwa [e] at hlog
  rw [PsiUp, capK]
  have hK : (0 : ℝ) ≤ 2 * (3 + cmin) := by norm_num [cmin]
  nlinarith [hmono, hlog', hK]

/-- The shift `u ↦ u-1` inside the integral. -/
lemma integral_shift_PsiUp :
    (∫ u in (3 : ℝ)..(399 / 100), PsiUp (u - 1) / u)
      = ∫ x in (2 : ℝ)..(299 / 100), PsiUp x / (x + 1) := by
  have h := intervalIntegral.integral_comp_add_right (a := (2:ℝ)) (b := 299/100)
    (fun y : ℝ => PsiUp (y - 1) / y) 1
  rw [show (2:ℝ) + 1 = 3 by norm_num,
    show (299:ℝ)/100 + 1 = 399/100 by norm_num] at h
  rw [← h]
  refine intervalIntegral.integral_congr (fun x hx => ?_)
  congr 2
  ring

/-- **Lower bound for `∫_3^{399/100} riPhi`.** -/
theorem LB3_riPhi :
    cmin * logLowRat (133 / 100) - (∫ x in (2 : ℝ)..(299 / 100), PsiUp x / (x + 1))
      ≤ ∫ u in (3 : ℝ)..(399 / 100), riPhi u := by
  have hpt : ∀ s ∈ Set.Icc (3 : ℝ) (399 / 100), (cmin - PsiUp (s - 1)) / s ≤ riPhi s := by
    intro s hs
    rw [Set.mem_Icc] at hs
    obtain ⟨hs1, hs2⟩ := hs
    have hs0 : 0 < s := by linarith
    have hid := riPhi_delay_identity s (by linarith)
    have hmax : max (s - 1) 2 = s - 1 := max_eq_left (by linarith)
    have hz : (3 - s) * (if s ≤ 3 then (1 : ℝ) else 0) = 0 := by
      by_cases h : s ≤ 3
      · rw [if_pos h]
        have h3 : s = 3 := le_antisymm h hs1
        rw [h3]; ring
      · rw [if_neg h]; ring
    rw [hmax, hz, zero_add] at hid
    have hsplit : (∫ u in Set.Ici (s - 1), riPsi u) = Ctot - ∫ u in (2 : ℝ)..(s - 1), riPsi u := by
      have h2' : IntegrableOn riPsi (Set.Ici (2 : ℝ)) := integrableOn_riPsi_Ici_two
      have hs2' : IntegrableOn riPsi (Set.Ici (s - 1)) :=
        h2'.mono_set (Set.Ici_subset_Ici.mpr (by linarith))
      have hrec := intervalIntegral.integral_Ici_sub_Ici' h2' hs2'
      rw [riSys_integral_Ici_two_riPsi] at hrec
      linarith
    have hle : (∫ u in (2 : ℝ)..(s - 1), riPsi u) ≤ PsiUp (s - 1) :=
      integral_riPsi_le_PsiUp (by linarith) (by linarith)
    have hcmin := Ctot_ge_cmin
    rw [div_le_iff₀ hs0]
    have h := hid
    rw [hsplit] at h
    linarith
  have hpsiCont : ContinuousOn (fun u : ℝ => PsiUp (u - 1)) (Set.Icc (3:ℝ) (399/100)) := by
    have h1 : ContinuousOn (fun u : ℝ => (u - 1) - 2) (Set.Icc (3:ℝ) (399/100)) := by
      have hsub : ContinuousOn (fun u : ℝ => u - 1) (Set.Icc (3:ℝ) (399/100)) :=
        ContinuousOn.sub continuousOn_id continuousOn_const
      exact hsub.sub continuousOn_const
    have hnum : ContinuousOn (fun u : ℝ => 2 * ((u - 1) - 2)) (Set.Icc (3:ℝ) (399/100)) :=
      ContinuousOn.const_mul h1 2
    have hden : ContinuousOn (fun u : ℝ => (u - 1) + 2) (Set.Icc (3:ℝ) (399/100)) := by
      have hsub : ContinuousOn (fun u : ℝ => u - 1) (Set.Icc (3:ℝ) (399/100)) :=
        ContinuousOn.sub continuousOn_id continuousOn_const
      exact hsub.add continuousOn_const
    have hterm1 : ContinuousOn (fun u : ℝ => 2 * ((u - 1) - 2) / ((u - 1) + 2))
        (Set.Icc (3:ℝ) (399/100)) :=
      ContinuousOn.div hnum hden (fun u hu => ne_of_gt (by linarith [hu.1] : (0:ℝ) < (u - 1) + 2))
    have hterm2 : ContinuousOn (fun u : ℝ => 2 / (u - 1)) (Set.Icc (3:ℝ) (399/100)) := by
      have hsub : ContinuousOn (fun u : ℝ => u - 1) (Set.Icc (3:ℝ) (399/100)) :=
        ContinuousOn.sub continuousOn_id continuousOn_const
      exact ContinuousOn.div continuousOn_const hsub
        (fun u hu => ne_of_gt (by linarith [hu.1] : (0:ℝ) < u - 1))
    have hsum : ContinuousOn (fun u : ℝ => 2 * ((u - 1) - 2) / ((u - 1) + 2) + 2 / (u - 1))
        (Set.Icc (3:ℝ) (399/100)) := hterm1.add hterm2
    have hbr : ContinuousOn (fun u : ℝ =>
        2 * ((u - 1) - 2) / ((u - 1) + 2) + 2 / (u - 1) - 1) (Set.Icc (3:ℝ) (399/100)) :=
      hsum.sub continuousOn_const
    have hc : ContinuousOn (fun u : ℝ =>
        capK * (2 * ((u - 1) - 2) / ((u - 1) + 2) + 2 / (u - 1) - 1)) (Set.Icc (3:ℝ) (399/100)) :=
      ContinuousOn.const_mul hbr capK
    exact h1.sub hc
  have hcont : ContinuousOn (fun u : ℝ => (cmin - PsiUp (u - 1)) / u) (Set.uIcc (3:ℝ) (399/100)) := by
    rw [Set.uIcc_of_le (by norm_num)]
    exact ContinuousOn.div (continuousOn_const.sub hpsiCont) continuousOn_id
      (fun u hu => ne_of_gt (by linarith [hu.1] : (0:ℝ) < u))
  have hminor_int : IntervalIntegrable (fun u : ℝ => (cmin - PsiUp (u - 1)) / u)
      volume (3:ℝ) (399/100) := hcont.intervalIntegrable
  have hri_int : IntervalIntegrable riPhi volume (3:ℝ) (399/100) := by
    refine IntegrableOn.intervalIntegrable (μ := volume) ?_
    rw [Set.uIcc_of_le (by norm_num)]
    exact integrableOn_riPhi_Ici_one.mono_set (fun x hx => by
      rw [Set.mem_Icc] at hx
      exact le_trans (by norm_num : (1:ℝ) ≤ 3) hx.1)
  have hmono : (∫ u in (3 : ℝ)..(399 / 100), (cmin - PsiUp (u - 1)) / u)
      ≤ ∫ u in (3 : ℝ)..(399 / 100), riPhi u :=
    intervalIntegral.integral_mono_on (by norm_num) hminor_int hri_int hpt
  have hInt1 : IntervalIntegrable (fun u : ℝ => (1:ℝ)/u) volume (3:ℝ) (399/100) := by
    have h : IntervalIntegrable (fun u : ℝ => u⁻¹) volume (3:ℝ) (399/100) :=
      (continuousOn_id.inv₀ (fun u hu => by
        rw [Set.uIcc_of_le (by norm_num)] at hu
        exact ne_of_gt (by linarith [hu.1] : (0:ℝ) < u))).intervalIntegrable
    simpa only [one_div] using h
  have hInt2 : IntervalIntegrable (fun u : ℝ => PsiUp (u - 1)/u) volume (3:ℝ) (399/100) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le (by norm_num)]
    exact ContinuousOn.div hpsiCont continuousOn_id
      (fun u hu => ne_of_gt (by linarith [hu.1] : (0:ℝ) < u))
  have hlog : (∫ u in (3 : ℝ)..(399 / 100), (1:ℝ)/u) = Real.log (399/100) - Real.log 3 := by
    have h1 : (fun u : ℝ => (1:ℝ)/u) = fun u : ℝ => u⁻¹ := by funext u; rw [one_div]
    have h0 : (0:ℝ) ∉ Set.uIcc (3:ℝ) (399/100) := by
      rw [Set.uIcc_of_le (by norm_num : (3:ℝ) ≤ 399/100)]
      rintro ⟨h1', h2'⟩
      linarith
    rw [h1, integral_inv (a := (3:ℝ)) (b := 399/100) h0,
      Real.log_div (by norm_num : (399:ℝ)/100 ≠ 0) (by norm_num : (3:ℝ) ≠ 0)]
  have hval : (∫ u in (3 : ℝ)..(399 / 100), (cmin - PsiUp (u - 1)) / u)
      = cmin * (Real.log (399/100) - Real.log 3)
        - ∫ x in (2 : ℝ)..(299 / 100), PsiUp x / (x + 1) := by
    have hcongr : (∫ u in (3 : ℝ)..(399 / 100), (cmin - PsiUp (u - 1)) / u)
        = cmin * (∫ u in (3 : ℝ)..(399 / 100), (1:ℝ)/u)
          - ∫ u in (3 : ℝ)..(399 / 100), PsiUp (u - 1)/u := by
      rw [← intervalIntegral.integral_const_mul cmin (fun u : ℝ => (1:ℝ)/u),
        ← intervalIntegral.integral_sub (hInt1.const_mul cmin) hInt2]
      refine intervalIntegral.integral_congr (fun u hu => ?_)
      rw [Set.uIcc_of_le (by norm_num)] at hu
      field_simp
    rw [hcongr, integral_shift_PsiUp, hlog]
  rw [hval] at hmono
  have hlog2 : Real.log (133/100) = Real.log (399/100) - Real.log 3 := by
    rw [← Real.log_div (by norm_num : (399:ℝ)/100 ≠ 0) (by norm_num : (3:ℝ) ≠ 0)]
    norm_num
  have hLR : logLowRat (133/100) ≤ Real.log (399/100) - Real.log 3 := by
    rw [← hlog2]
    exact logLowRat_le (by norm_num)
  have hc : (0:ℝ) ≤ cmin := le_of_lt cmin_pos
  have hstep : cmin * logLowRat (133/100) ≤ cmin * (Real.log (399/100) - Real.log 3) :=
    mul_le_mul_of_nonneg_left hLR hc
  linarith

/-- The explicit upper bound for `∫_2^{299/100} PsiUp x/(x+1) dx`. -/
def IupBound : ℝ := 99/100 - (2*capK)*(logLowRat (1495/1000))
  + (9*capK - 3)*(logUpRat (133/100)) - (8*capK)*(logLowRat (12475/10000))

lemma PsiUp_div_eq {x : ℝ} (hx : 0 < x) :
    PsiUp x / (x + 1) = 1 - (2*capK)/x + (9*capK - 3)/(x + 1) - (8*capK)/(x + 2) := by
  have h1 : x ≠ 0 := ne_of_gt hx
  have h2 : x + 1 ≠ 0 := by linarith
  have h3 : x + 2 ≠ 0 := by linarith
  unfold PsiUp
  field_simp
  ring

lemma derivval_eq2 {x : ℝ} :
    (1 - (2*capK)*x⁻¹ + (9*capK - 3)*(x+1)⁻¹) - (8*capK)*(x+2)⁻¹
      = 1 - (2*capK)/x + (9*capK - 3)/(x + 1) - (8*capK)/(x + 2) := by
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]

theorem hasDerivAt_IupForm {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => y - (2*capK)*Real.log y + (9*capK - 3)*Real.log (y + 1)
        - (8*capK)*Real.log (y + 2))
      ((1 - (2*capK)*x⁻¹ + (9*capK - 3)*(x+1)⁻¹) - (8*capK)*(x+2)⁻¹) x := by
  have h1 : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id x
  have h2 : HasDerivAt (fun y : ℝ => Real.log y) x⁻¹ x := Real.hasDerivAt_log (ne_of_gt hx)
  have h3 : HasDerivAt (fun y : ℝ => Real.log (y + 1)) (x + 1)⁻¹ x := by
    have hsub : HasDerivAt (fun y : ℝ => y + 1) 1 x := (hasDerivAt_id x).add_const 1
    have h := hsub.log (by linarith : x + 1 ≠ 0)
    convert h using 1
    rw [one_div]
  have h4 : HasDerivAt (fun y : ℝ => Real.log (y + 2)) (x + 2)⁻¹ x := by
    have hsub : HasDerivAt (fun y : ℝ => y + 2) 1 x := (hasDerivAt_id x).add_const 2
    have h := hsub.log (by linarith : x + 2 ≠ 0)
    convert h using 1
    rw [one_div]
  have hA : HasDerivAt (fun y : ℝ => y - (2*capK)*Real.log y) (1 - (2*capK)*x⁻¹) x :=
    h1.sub (h2.const_mul (2*capK))
  have hB : HasDerivAt (fun y : ℝ => (9*capK - 3)*Real.log (y + 1))
      ((9*capK - 3)*(x+1)⁻¹) x := h3.const_mul (9*capK - 3)
  have hC : HasDerivAt (fun y : ℝ => (8*capK)*Real.log (y + 2)) ((8*capK)*(x+2)⁻¹) x :=
    h4.const_mul (8*capK)
  exact (hA.add hB).sub hC

lemma continuousOn_PsiUp_div {a b : ℝ} (ha : (2:ℝ) ≤ a) :
    ContinuousOn (fun x : ℝ => PsiUp x / (x + 1)) (Set.Icc a b) := by
  have h2 : ContinuousOn (fun x : ℝ => x - 2) (Set.Icc a b) :=
    ContinuousOn.sub continuousOn_id continuousOn_const
  have hnum : ContinuousOn (fun x : ℝ => 2 * (x - 2)) (Set.Icc a b) :=
    ContinuousOn.const_mul h2 2
  have hden : ContinuousOn (fun x : ℝ => x + 2) (Set.Icc a b) :=
    ContinuousOn.add continuousOn_id continuousOn_const
  have hterm1 : ContinuousOn (fun x : ℝ => 2 * (x - 2) / (x + 2)) (Set.Icc a b) :=
    ContinuousOn.div hnum hden (fun x hx => ne_of_gt (by linarith [hx.1] : (0:ℝ) < x + 2))
  have hterm2 : ContinuousOn (fun x : ℝ => 2 / x) (Set.Icc a b) :=
    ContinuousOn.div continuousOn_const continuousOn_id
      (fun x hx => ne_of_gt (by linarith [hx.1] : (0:ℝ) < x))
  have hsum : ContinuousOn (fun x : ℝ => 2 * (x - 2) / (x + 2) + 2 / x) (Set.Icc a b) :=
    hterm1.add hterm2
  have hbr : ContinuousOn (fun x : ℝ => 2 * (x - 2) / (x + 2) + 2 / x - 1) (Set.Icc a b) :=
    hsum.sub continuousOn_const
  have hpsi : ContinuousOn PsiUp (Set.Icc a b) := by
    unfold PsiUp
    exact h2.sub (ContinuousOn.const_mul hbr capK)
  exact ContinuousOn.div hpsi (ContinuousOn.add continuousOn_id continuousOn_const)
    (fun x hx => ne_of_gt (by linarith [hx.1] : (0:ℝ) < x + 1))

/-- **The explicit bound for the auxiliary integral.** -/
theorem Iup_le :
    (∫ x in (2 : ℝ)..(299 / 100), PsiUp x / (x + 1)) ≤ IupBound := by
  have hderiv : ∀ x ∈ Set.uIcc (2:ℝ) (299/100),
      HasDerivAt (fun y : ℝ => y - (2*capK)*Real.log y + (9*capK - 3)*Real.log (y + 1)
        - (8*capK)*Real.log (y + 2)) (PsiUp x / (x + 1)) x := by
    intro x hx
    rw [Set.uIcc_of_le (by norm_num)] at hx
    rw [PsiUp_div_eq (by linarith [hx.1]), ← derivval_eq2]
    exact hasDerivAt_IupForm (by linarith [hx.1])
  have hint : IntervalIntegrable (fun x : ℝ => PsiUp x / (x + 1)) volume (2:ℝ) (299/100) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le (by norm_num : (2:ℝ) ≤ 299/100)]
    exact continuousOn_PsiUp_div (by norm_num)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  -- evaluate and bound
  have hlogdiv1 : Real.log (1495/1000) = Real.log (299/100) - Real.log 2 := by
    rw [← Real.log_div (by norm_num : (299:ℝ)/100 ≠ 0) (by norm_num : (2:ℝ) ≠ 0)]
    norm_num
  have hlogdiv2 : Real.log (133/100) = Real.log (399/100) - Real.log 3 := by
    rw [← Real.log_div (by norm_num : (399:ℝ)/100 ≠ 0) (by norm_num : (3:ℝ) ≠ 0)]
    norm_num
  have hlogdiv3 : Real.log (12475/10000) = Real.log (499/100) - Real.log 4 := by
    rw [← Real.log_div (by norm_num : (499:ℝ)/100 ≠ 0) (by norm_num : (4:ℝ) ≠ 0)]
    norm_num
  have hKpos : (0:ℝ) < capK := by norm_num [capK, cmin]
  have hK2 : (0:ℝ) < 9*capK - 3 := by norm_num [capK, cmin]
  have hb1 := logLowRat_le (z := 1495/1000) (by norm_num)
  have hb2 := le_logUpRat (z := 133/100) (by norm_num)
  have hb3 := logLowRat_le (z := 12475/10000) (by norm_num)
  rw [hlogdiv1, hlogdiv2, hlogdiv3] at *
  rw [IupBound]
  nlinarith [hb1, hb2, hb3, hKpos, hK2]

/-- **The upper-profile mass beyond `399/100`.** -/
theorem riPhi_Ici_399_le : (∫ u in Set.Ici ((399:ℝ)/100), riPhi u) ≤ 499/12500 := by
  have hT := Ttot_eq_integral_riPhi
  have hsplit : (∫ u in Set.Ici ((399:ℝ)/100), riPhi u)
      = Ttot - ∫ u in (3:ℝ)..(399/100), riPhi u := by
    have h1 : IntegrableOn riPhi (Set.Ici (3:ℝ)) :=
      integrableOn_riPhi_Ici_one.mono_set (fun x hx => by
        rw [Set.mem_Ici] at hx ⊢
        linarith)
    have h2' : IntegrableOn riPhi (Set.Ici ((399:ℝ)/100)) :=
      h1.mono_set (Set.Ici_subset_Ici.mpr (by norm_num))
    have hrec := intervalIntegral.integral_Ici_sub_Ici' h1 h2'
    rw [hT] at hrec
    linarith
  rw [hsplit]
  have hLB := LB3_riPhi
  have hIup := Iup_le
  have hTup := Ttot_le_cmin
  have hnum : (4 - 3 * logLowRat 3 - cmin * logLowRat 3)
      - (cmin * logLowRat (133/100) - IupBound) ≤ 499/12500 := by
    norm_num [IupBound, capK, cmin, logLowRat, logUpRat]
  linarith

/-- **`riPsi (499/100) ≤ 1/125`.** -/
theorem riPsi_499_le : riPsi ((499:ℝ)/100) ≤ 1/125 := by
  have hid := riPhi_delay_system.2 ((499:ℝ)/100) (by norm_num)
  have hbound := riPhi_Ici_399_le
  have hpos : (0:ℝ) < (499:ℝ)/100 := by norm_num
  have harg : (499:ℝ)/100 - 1 = 399/100 := by norm_num
  rw [harg] at hid
  have h2 : riPsi ((499:ℝ)/100) ≤ (499/12500)/((499:ℝ)/100) := by
    rw [le_div_iff₀ hpos]
    nlinarith [hid, hbound]
  have h3 : (499/12500)/((499:ℝ)/100) = 1/125 := by norm_num
  linarith

end

end RiPhiTail499

end Work.NumberTheory.Chen
