import Mathlib
import Submission.Work.NumberTheory.Chen.APSwitchUpper.prof
import Submission.Work.NumberTheory.Chen.APSwitchUpper.riPhiDelay
import Submission.Work.NumberTheory.Chen.riPhi_tail_499
import Submission.Work.NumberTheory.Chen.BTermCount.riSys_antitone_continuous
import Submission.Work.NumberTheory.Chen.ApSumTenth.riPhi_delay_identity
import Submission.Work.NumberTheory.Chen.ApSumTenth.riPhi_delay_system
import Submission.Work.NumberTheory.Chen.ApSumTenth.TailAux
import Submission.Work.NumberTheory.Chen.ApSumTenth.integral_riPhi_Ici_one
import Submission.Work.NumberTheory.Chen.Ttot_eq_integral_riPhi

/-!
# `riPsi s ≤ 7/1000` for `s ≥ 49/10`

The Rosser–Iwaniec lower profile `riPsi = 1 - f` is antitone on `[2,∞)`, so it suffices to
bound it at `s = 49/10`.  The delay identity `s * riPsi s = ∫_{Ici (s-1)} riPhi` turns this
into the tail-mass bound `∫_{Ici (39/10)} riPhi ≤ (49/10)·(7/1000) = 343/10000`.

The tail is split as `Ttot - ∫_3^{39/10} riPhi` (`Ttot_eq_integral_riPhi`), `Ttot` is bounded
above by `Ttot_le_cmin : Ttot ≤ 4 - 3 log 3 - (551/1000) log 3`, and `∫_3^{39/10} riPhi` is
bounded below by integrating the pointwise lower bound

`(cmin - PsiUp (s-1))/s ≤ riPhi s`   (`s ∈ [3, 39/10]`),

which comes from the delay identity `s riPhi s = Ctot - ∫_2^{s-1} riPsi`, `Ctot ≥ cmin` and the
rational majorant `∫_2^x riPsi ≤ PsiUp x` of `RiPhiTail499`.  The remaining integral
`∫_2^{29/10} PsiUp x/(x+1) dx` has the explicit antiderivative
`x - 2K log x + (9K-3) log(x+1) - 8K log(x+2)`, giving the rational bound `IupBound29`.
-/

namespace Work.ChenPlan.LinearSieve.Numerics

open MeasureTheory intervalIntegral
open Work.NumberTheory.Chen.APSwitchUpper
open Work.NumberTheory.Chen.ApSumTenth
open Work.NumberTheory.Chen.RiPhiTail499

noncomputable section

/-! ## 1. The pointwise lower bound for `riPhi` on `[3, 39/10]` -/

theorem riPhi_ge_of_mem_Icc39 {s : ℝ} (hs : s ∈ Set.Icc (3:ℝ) (39/10)) :
    (cmin - PsiUp (s - 1)) / s ≤ riPhi s := by
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
  rw [hsplit] at hid
  rw [div_le_iff₀ hs0, mul_comm (riPhi s) s]
  linarith

/-! ## 2. Shifting `∫_3^{39/10} PsiUp (u-1)/u` to `∫_2^{29/10} PsiUp x/(x+1)` -/

lemma integral_shift_PsiUp29 :
    (∫ u in (3 : ℝ)..(39/10), PsiUp (u - 1) / u)
      = ∫ x in (2 : ℝ)..(29/10), PsiUp x / (x + 1) := by
  have h := intervalIntegral.integral_comp_add_right (a := (2:ℝ)) (b := 29/10)
    (fun y : ℝ => PsiUp (y - 1) / y) 1
  rw [show (2:ℝ) + 1 = 3 by norm_num, show (29:ℝ)/10 + 1 = 39/10 by norm_num] at h
  rw [← h]
  refine intervalIntegral.integral_congr (fun x hx => ?_)
  congr 2
  ring

/-! ## 3. The explicit upper bound for `∫_2^{29/10} PsiUp x/(x+1) dx` -/

/-- The rational upper bound for `∫_2^{29/10} PsiUp x/(x+1) dx`. -/
def IupBound29 : ℝ := 9/10 - (2*capK)*(logLowRat (29/20))
  + (9*capK - 3)*(logUpRat (13/10)) - (8*capK)*(logLowRat (49/40))

theorem Iup_le29 :
    (∫ x in (2 : ℝ)..(29/10), PsiUp x / (x + 1)) ≤ IupBound29 := by
  have hderiv : ∀ x ∈ Set.uIcc (2:ℝ) (29/10),
      HasDerivAt (fun y : ℝ => y - (2*capK)*Real.log y + (9*capK - 3)*Real.log (y + 1)
        - (8*capK)*Real.log (y + 2)) (PsiUp x / (x + 1)) x := by
    intro x hx
    rw [Set.uIcc_of_le (by norm_num)] at hx
    rw [PsiUp_div_eq (by linarith [hx.1]), ← derivval_eq2]
    exact hasDerivAt_IupForm (by linarith [hx.1])
  have hint : IntervalIntegrable (fun x : ℝ => PsiUp x / (x + 1)) volume (2:ℝ) (29/10) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le (by norm_num : (2:ℝ) ≤ 29/10)]
    exact continuousOn_PsiUp_div (a := 2) (b := 29/10) (by norm_num)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  have hlogdiv1 : Real.log (29/20) = Real.log (29/10) - Real.log 2 := by
    rw [← Real.log_div (by norm_num : (29:ℝ)/10 ≠ 0) (by norm_num : (2:ℝ) ≠ 0)]; norm_num
  have hlogdiv2 : Real.log (13/10) = Real.log (39/10) - Real.log 3 := by
    rw [← Real.log_div (by norm_num : (39:ℝ)/10 ≠ 0) (by norm_num : (3:ℝ) ≠ 0)]; norm_num
  have hlogdiv3 : Real.log (49/40) = Real.log (49/10) - Real.log 4 := by
    rw [← Real.log_div (by norm_num : (49:ℝ)/10 ≠ 0) (by norm_num : (4:ℝ) ≠ 0)]; norm_num
  have hKpos : (0:ℝ) < capK := by norm_num [capK, cmin]
  have hK2 : (0:ℝ) < 9*capK - 3 := by norm_num [capK, cmin]
  have hb1 := logLowRat_le (z := 29/20) (by norm_num)
  have hb2 := le_logUpRat (z := 13/10) (by norm_num)
  have hb3 := logLowRat_le (z := 49/40) (by norm_num)
  rw [hlogdiv1, hlogdiv2, hlogdiv3] at *
  rw [IupBound29]
  nlinarith [hb1, hb2, hb3, hKpos, hK2]

/-! ## 4. The lower bound for `∫_3^{39/10} riPhi` -/

theorem LB39_riPhi :
    cmin * logLowRat (13/10) - (∫ x in (2 : ℝ)..(29/10), PsiUp x / (x + 1))
      ≤ ∫ u in (3 : ℝ)..(39/10), riPhi u := by
  have hpt : ∀ s ∈ Set.Icc (3:ℝ) (39/10), (cmin - PsiUp (s - 1)) / s ≤ riPhi s :=
    fun s hs => riPhi_ge_of_mem_Icc39 hs
  have hpsiCont : ContinuousOn (fun u : ℝ => PsiUp (u - 1) / u) (Set.Icc (3:ℝ) (39/10)) := by
    have hcomp : ContinuousOn ((fun x : ℝ => PsiUp x / (x + 1)) ∘ (fun u : ℝ => u - 1))
        (Set.Icc (3:ℝ) (39/10)) :=
      (continuousOn_PsiUp_div (a := 2) (b := 29/10) (by norm_num)).comp
        (continuousOn_id.sub continuousOn_const)
        (fun u hu => ⟨by linarith [hu.1], by linarith [hu.2]⟩)
    refine hcomp.congr (fun u hu => ?_)
    simp only [Function.comp_apply]
    rw [show (u - 1) + 1 = u by ring]
  have hpsi : ContinuousOn (fun u : ℝ => PsiUp (u - 1)) (Set.Icc (3:ℝ) (39/10)) := by
    have hmul : ContinuousOn (fun u : ℝ => PsiUp (u - 1) / u * u) (Set.Icc (3:ℝ) (39/10)) :=
      hpsiCont.mul continuousOn_id
    refine hmul.congr (fun u hu => ?_)
    simp only
    rw [Set.mem_Icc] at hu
    rw [div_mul_cancel₀ _ (ne_of_gt (by linarith [hu.1] : (0:ℝ) < u))]
  have hcont : ContinuousOn (fun u : ℝ => (cmin - PsiUp (u - 1)) / u)
      (Set.uIcc (3:ℝ) (39/10)) := by
    rw [Set.uIcc_of_le (by norm_num)]
    exact ContinuousOn.div (ContinuousOn.sub continuousOn_const hpsi) continuousOn_id
      (fun u hu => by
        rw [Set.mem_Icc] at hu
        exact ne_of_gt (by linarith [hu.1] : (0:ℝ) < u))
  have hminor_int : IntervalIntegrable (fun u : ℝ => (cmin - PsiUp (u - 1)) / u)
      volume (3:ℝ) (39/10) := hcont.intervalIntegrable
  have hri_int : IntervalIntegrable riPhi volume (3:ℝ) (39/10) := by
    refine IntegrableOn.intervalIntegrable (μ := volume) ?_
    rw [Set.uIcc_of_le (by norm_num)]
    exact integrableOn_riPhi_Ici_one.mono_set (fun x hx => by
      rw [Set.mem_Icc] at hx
      exact le_trans (by norm_num : (1:ℝ) ≤ 3) hx.1)
  have hmono : (∫ u in (3 : ℝ)..(39/10), (cmin - PsiUp (u - 1)) / u)
      ≤ ∫ u in (3 : ℝ)..(39/10), riPhi u :=
    intervalIntegral.integral_mono_on (by norm_num) hminor_int hri_int hpt
  have hInt1 : IntervalIntegrable (fun u : ℝ => (1:ℝ)/u) volume (3:ℝ) (39/10) := by
    have h : IntervalIntegrable (fun u : ℝ => u⁻¹) volume (3:ℝ) (39/10) :=
      (continuousOn_id.inv₀ (fun u hu => by
        rw [Set.uIcc_of_le (by norm_num)] at hu
        exact ne_of_gt (by linarith [hu.1] : (0:ℝ) < u))).intervalIntegrable
    simpa only [one_div] using h
  have hInt2 : IntervalIntegrable (fun u : ℝ => PsiUp (u - 1)/u) volume (3:ℝ) (39/10) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le (by norm_num)]
    exact hpsiCont
  have hlog : (∫ u in (3 : ℝ)..(39/10), (1:ℝ)/u) = Real.log (39/10) - Real.log 3 := by
    have h1 : (fun u : ℝ => (1:ℝ)/u) = fun u : ℝ => u⁻¹ := by funext u; rw [one_div]
    have h0 : (0:ℝ) ∉ Set.uIcc (3:ℝ) (39/10) := by
      rw [Set.uIcc_of_le (by norm_num : (3:ℝ) ≤ 39/10)]
      rintro ⟨h1', h2'⟩
      linarith
    rw [h1, integral_inv (a := (3:ℝ)) (b := 39/10) h0,
      Real.log_div (by norm_num : (39:ℝ)/10 ≠ 0) (by norm_num : (3:ℝ) ≠ 0)]
  have hval : (∫ u in (3 : ℝ)..(39/10), (cmin - PsiUp (u - 1)) / u)
      = cmin * (Real.log (39/10) - Real.log 3)
        - ∫ x in (2 : ℝ)..(29/10), PsiUp x / (x + 1) := by
    have hcongr : (∫ u in (3 : ℝ)..(39/10), (cmin - PsiUp (u - 1)) / u)
        = cmin * (∫ u in (3 : ℝ)..(39/10), (1:ℝ)/u)
          - ∫ u in (3 : ℝ)..(39/10), PsiUp (u - 1)/u := by
      rw [← intervalIntegral.integral_const_mul cmin (fun u : ℝ => (1:ℝ)/u),
        ← intervalIntegral.integral_sub (hInt1.const_mul cmin) hInt2]
      refine intervalIntegral.integral_congr (fun u hu => ?_)
      rw [Set.uIcc_of_le (by norm_num)] at hu
      field_simp
    rw [hcongr, integral_shift_PsiUp29, hlog]
  rw [hval] at hmono
  have hlog2 : Real.log (13/10) = Real.log (39/10) - Real.log 3 := by
    rw [← Real.log_div (by norm_num : (39:ℝ)/10 ≠ 0) (by norm_num : (3:ℝ) ≠ 0)]
    norm_num
  have hLR : logLowRat (13/10) ≤ Real.log (39/10) - Real.log 3 := by
    rw [← hlog2]
    exact logLowRat_le (by norm_num)
  have hc : (0:ℝ) ≤ cmin := le_of_lt cmin_pos
  have hstep : cmin * logLowRat (13/10) ≤ cmin * (Real.log (39/10) - Real.log 3) :=
    mul_le_mul_of_nonneg_left hLR hc
  linarith

/-! ## 5. The tail mass beyond `39/10` -/

theorem riPhi_Ici_39_le :
    (∫ u in Set.Ici ((39:ℝ)/10), riPhi u) ≤ 343/10000 := by
  have hT := Work.NumberTheory.Chen.Ttot_eq_integral_riPhi
  have hsplit : (∫ u in Set.Ici ((39:ℝ)/10), riPhi u)
      = Ttot - ∫ u in (3:ℝ)..(39/10), riPhi u := by
    have h1 : IntegrableOn riPhi (Set.Ici (3:ℝ)) :=
      integrableOn_riPhi_Ici_one.mono_set (fun x hx => by
        rw [Set.mem_Ici] at hx ⊢
        linarith)
    have h2' : IntegrableOn riPhi (Set.Ici ((39:ℝ)/10)) :=
      h1.mono_set (Set.Ici_subset_Ici.mpr (by norm_num))
    have hrec := intervalIntegral.integral_Ici_sub_Ici' h1 h2'
    rw [hT] at hrec
    linarith
  rw [hsplit]
  have hLB := LB39_riPhi
  have hIup := Iup_le29
  have hTup := Ttot_le_cmin
  have hnum : (4 - 3 * logLowRat 3 - cmin * logLowRat 3)
      - (cmin * logLowRat (13/10) - IupBound29) ≤ 343/10000 := by
    norm_num [IupBound29, capK, cmin, logLowRat, logUpRat]
  linarith

/-! ## 6. `riPsi (49/10) ≤ 7/1000` -/

theorem riPsi_49_10_le :
    Work.NumberTheory.Chen.APSwitchUpper.riPsi (49/10) ≤ 7/1000 := by
  have hid := riPhi_delay_system.2 ((49:ℝ)/10) (by norm_num)
  have hbound := riPhi_Ici_39_le
  have hpos : (0:ℝ) < (49:ℝ)/10 := by norm_num
  have harg : (49:ℝ)/10 - 1 = 39/10 := by norm_num
  rw [harg] at hid
  have h2 : riPsi ((49:ℝ)/10) ≤ (343/10000)/((49:ℝ)/10) := by
    rw [le_div_iff₀ hpos]
    nlinarith [hid, hbound]
  have h3 : (343/10000)/((49:ℝ)/10) = 7/1000 := by norm_num
  linarith

/-! ## 7. The target -/

theorem riPsi_le (s : ℝ) (hs : 49/10 ≤ s) :
    Work.NumberTheory.Chen.APSwitchUpper.riPsi s ≤ 7/1000 := by
  have hs2 : s ∈ Set.Ici (2:ℝ) := by rw [Set.mem_Ici]; linarith
  have h49 : (49/10 : ℝ) ∈ Set.Ici (2:ℝ) := by rw [Set.mem_Ici]; norm_num
  have hanti := Work.NumberTheory.Chen.BTermCount.riPsi_antitone h49 hs2 hs
  linarith [hanti, riPsi_49_10_le]

end

end Work.ChenPlan.LinearSieve.Numerics
