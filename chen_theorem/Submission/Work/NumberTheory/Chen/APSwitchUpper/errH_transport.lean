import Mathlib
import Submission.Work.NumberTheory.Chen.APSwitchUpper.ErrProfile

/-!
# Transport inequalities for the exponential error profile `errH`

This file proves the three structural transport inequalities of the explicit profile

`errH s = e^{-2}` on `(-∞,2]`,  `errH s = e^{-s}` on `[2,3]`,  `errH s = 3e^{-s}/s` on `[3,∞)`:

* the tail (Rosser–Iwaniec `Λ`-type) bound `∫_{s}^{∞} errH (t-1) dt ≤ (97/100) s errH s` for `s ≥ 2`;
* the shift inequality `errH (s-1) ≤ (4e/3) errH s` for `s ≥ 3`;
* the small-`s` comparison `(3/s) errH 2 ≤ 3 errH s` for `1 ≤ s ≤ 3`.

The only non-elementary input is the numerical bound
`∫_3^∞ e^{-u}/u du ≤ e^{-3}(4 + e^{-2})/15`, obtained by comparing `1/u` with the chord
through `(3,1/3)`, `(5,1/5)` on `[3,5]` and by `1/5` on `[5,∞)`.
-/

namespace Work.NumberTheory.Chen.APSwitchUpper

open MeasureTheory Set

noncomputable section

/-! ## §0  Pointwise descriptions of `errH` -/

/-- On `[2,3]` (endpoints included) the profile is `exp (-s)`. -/
lemma errH_eq_exp_neg {u : ℝ} (h2 : 2 ≤ u) (h3 : u ≤ 3) : errH u = Real.exp (-u) := by
  rcases eq_or_lt_of_le h2 with h | h
  · subst h; exact errH_of_le_two le_rfl
  · exact errH_of_between h h3

/-- On `[3,∞)` the profile is `3 exp (-s) / s` (including the endpoint `3`). -/
lemma errH_of_ge_three {u : ℝ} (h : 3 ≤ u) : errH u = 3 * Real.exp (-u) / u := by
  rcases eq_or_lt_of_le h with h' | h'
  · subst h'; rw [errH_eq_exp_neg (by norm_num) le_rfl]; ring
  · exact errH_of_three_lt h'

/-- Dominance of the profile by `3e^{-s}/2` on `[1,∞)`. -/
lemma errH_le_three_halves {u : ℝ} (_hu : 1 ≤ u) : errH u ≤ 3 * Real.exp (-u) / 2 := by
  by_cases h2 : u ≤ 2
  · rw [errH_of_le_two h2]
    have h : Real.exp (-2) ≤ Real.exp (-u) := Real.exp_le_exp.mpr (by linarith)
    linarith [Real.exp_pos (-u)]
  · have h2' : (2:ℝ) < u := not_le.mp h2
    by_cases h3 : u ≤ 3
    · rw [errH_of_between h2' h3]; nlinarith [Real.exp_pos (-u)]
    · have h3' : (3:ℝ) < u := not_le.mp h3
      rw [errH_of_three_lt h3']
      exact div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)

lemma measurable_errH : Measurable errH := by
  unfold errH
  refine Measurable.ite (measurableSet_le measurable_id measurable_const) measurable_const ?_
  refine Measurable.ite (measurableSet_le measurable_id measurable_const) ?_ ?_
  · fun_prop
  · fun_prop

/-- `errH` is integrable on any `Ioi a` with `a ≥ 1`. -/
lemma integrableOn_errH_Ioi {a : ℝ} (ha : 1 ≤ a) : IntegrableOn errH (Set.Ioi a) := by
  refine Integrable.mono' (g := fun u : ℝ => 3 * Real.exp (-u) / 2) ?_ ?_ ?_
  · exact ((integrableOn_exp_neg_Ioi a).integrable.const_mul 3).div_const 2
  · exact measurable_errH.aestronglyMeasurable
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
    have hu1 : (1:ℝ) ≤ u := le_trans ha (le_of_lt (Set.mem_Ioi.mp hu))
    rw [Real.norm_eq_abs, abs_of_nonneg (errH_nonneg u)]
    exact errH_le_three_halves hu1

/-! ## §1  Translation of a set integral over `Ioi` -/

/-- Translation invariance of the Bochner integral on `Ioi`:
`∫_{s}^{∞} G (t - c) dt = ∫_{s-c}^{∞} G u du`. -/
lemma setIntegral_Ioi_comp_sub (G : ℝ → ℝ) (s c : ℝ) :
    (∫ t in Set.Ioi s, G (t - c)) = ∫ u in Set.Ioi (s - c), G u := by
  have h1 : (∫ t in Set.Ioi s, G (t - c))
      = ∫ t, (Set.Ioi s).indicator (fun t => G (t - c)) t :=
    (integral_indicator (s := Set.Ioi s) (f := fun t => G (t - c)) measurableSet_Ioi).symm
  rw [h1]
  have h2 : (fun t : ℝ => (Set.Ioi s).indicator (fun t => G (t - c)) t)
      = fun t : ℝ => (Set.Ioi (s - c)).indicator G (t - c) := by
    funext t
    simp only [Set.indicator_apply, Set.mem_Ioi]
    by_cases h : s < t
    · rw [if_pos h, if_pos (by linarith)]
    · rw [if_neg h, if_neg (by linarith)]
  rw [h2]
  have h3 : (∫ t : ℝ, (Set.Ioi (s - c)).indicator G (t - c))
      = ∫ u : ℝ, (Set.Ioi (s - c)).indicator G u := by
    simpa only [sub_eq_add_neg] using
      integral_add_right_eq_self (fun u : ℝ => (Set.Ioi (s - c)).indicator G u) (-c)
  rw [h3]
  exact integral_indicator (s := Set.Ioi (s - c)) (f := G) measurableSet_Ioi

/-! ## §2  The exponential-integral bound -/

/-- `u ↦ e^{-u}/u` is integrable on `Ioi a` for `a ≥ 3`. -/
lemma integrableOn_expNeg_div_Ioi {a : ℝ} (ha : 3 ≤ a) :
    IntegrableOn (fun u : ℝ => Real.exp (-u) / u) (Set.Ioi a) := by
  refine Integrable.mono' (g := fun u : ℝ => Real.exp (-u) / 3) ?_ ?_ ?_
  · exact (integrableOn_exp_neg_Ioi a).integrable.div_const 3
  · apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    apply ContinuousOn.div
    · fun_prop
    · fun_prop
    · intro u hu
      exact ne_of_gt (by linarith [Set.mem_Ioi.mp hu] : (0:ℝ) < u)
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
    have hu3 : (3:ℝ) < u := lt_of_le_of_lt ha (Set.mem_Ioi.mp hu)
    rw [Real.norm_eq_abs, abs_of_pos (div_pos (Real.exp_pos _) (by linarith))]
    exact div_le_div_of_nonneg_left (Real.exp_pos _).le (by norm_num) (le_of_lt hu3)

/-- `∫_3^∞ e^{-u}/u du ≤ e^{-3}(4 + e^{-2})/15`:
on `[3,5]` compare `1/u` with its chord `8/15 - u/15`, on `[5,∞)` with `1/5`. -/
lemma E1_three_le :
    (∫ u in Set.Ioi (3:ℝ), Real.exp (-u)/u) ≤ Real.exp (-3)*(4 + Real.exp (-2))/15 := by
  have hf : IntegrableOn (fun u : ℝ => Real.exp (-u)/u) (Set.Ioi (3:ℝ)) :=
    integrableOn_expNeg_div_Ioi le_rfl
  have hsplit : (∫ u in Set.Ioi (3:ℝ), Real.exp (-u)/u)
      = (∫ u in (3:ℝ)..5, Real.exp (-u)/u) + ∫ u in Set.Ioi (5:ℝ), Real.exp (-u)/u := by
    have h := intervalIntegral.integral_Ioi_sub_Ioi (f := fun u : ℝ => Real.exp (-u)/u)
      (a := 3) (b := 5) hf (by norm_num)
    linarith
  rw [hsplit]
  have hmid : (∫ u in (3:ℝ)..5, Real.exp (-u)/u) ≤ (4*Real.exp (-3) - 2*Real.exp (-5))/15 := by
    have hcont1 : ContinuousOn (fun u : ℝ => Real.exp (-u)/u) (Set.uIcc (3:ℝ) 5) := by
      apply ContinuousOn.div
      · fun_prop
      · fun_prop
      · intro u hu
        rw [Set.uIcc_of_le (by norm_num : (3:ℝ) ≤ 5)] at hu
        exact ne_of_gt (by linarith [hu.1] : (0:ℝ) < u)
    have hcont2 : ContinuousOn (fun u : ℝ => Real.exp (-u) * (8/15 - u/15)) (Set.uIcc (3:ℝ) 5) := by
      fun_prop
    have hstep : (∫ u in (3:ℝ)..5, Real.exp (-u)/u)
        ≤ ∫ u in (3:ℝ)..5, Real.exp (-u) * (8/15 - u/15) := by
      refine intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num) hcont1.intervalIntegrable
        hcont2.intervalIntegrable ?_
      intro u hu
      have hu0 : (0:ℝ) < u := by linarith [hu.1]
      have hchord : 1/u ≤ 8/15 - u/15 := by
        rw [div_le_iff₀ hu0]
        nlinarith [hu.1, hu.2]
      rw [div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_left hchord (Real.exp_pos _).le
    have hderiv : ∀ x ∈ Set.Ioo (3:ℝ) 5,
        HasDerivAt (fun u : ℝ => (1/15)*(Real.exp (-u)*(u-7)))
          (Real.exp (-x)*(8/15 - x/15)) x := by
      intro x hx
      have h1 : HasDerivAt (fun u : ℝ => Real.exp (-u) * (u - 7))
          (Real.exp (-x) * (-1) * (x-7) + Real.exp (-x) * 1) x :=
        (((hasDerivAt_id x).neg).exp).mul ((hasDerivAt_id x).sub_const 7)
      refine (h1.const_mul (1/15)).congr_deriv ?_
      ring
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (a := (3:ℝ)) (b := 5) (by norm_num)
      (by fun_prop : ContinuousOn (fun u : ℝ => (1/15)*(Real.exp (-u)*(u-7))) (Set.Icc (3:ℝ) 5))
      hderiv hcont2.intervalIntegrable
    have hval : (∫ u in (3:ℝ)..5, Real.exp (-u) * (8/15 - u/15))
        = (4*Real.exp (-3) - 2*Real.exp (-5))/15 := by
      rw [hFTC]; ring
    linarith [hstep, hval]
  have htail : (∫ u in Set.Ioi (5:ℝ), Real.exp (-u)/u) ≤ Real.exp (-5)/5 := by
    have hf5 : IntegrableOn (fun u : ℝ => Real.exp (-u)/u) (Set.Ioi (5:ℝ)) :=
      integrableOn_expNeg_div_Ioi (by norm_num)
    have hg5 : IntegrableOn (fun u : ℝ => Real.exp (-u)/5) (Set.Ioi (5:ℝ)) :=
      (integrableOn_exp_neg_Ioi (5:ℝ)).integrable.div_const 5
    calc (∫ u in Set.Ioi (5:ℝ), Real.exp (-u)/u)
        ≤ ∫ u in Set.Ioi (5:ℝ), Real.exp (-u)/5 := by
          refine setIntegral_mono_on hf5 hg5 measurableSet_Ioi ?_
          intro u hu
          exact div_le_div_of_nonneg_left (Real.exp_pos _).le (by norm_num)
            (by linarith [Set.mem_Ioi.mp hu])
      _ = Real.exp (-5)/5 := by
          rw [MeasureTheory.integral_div, integral_exp_neg_Ioi]
  have hexp5 : Real.exp (-5) = Real.exp (-3)*Real.exp (-2) := by
    rw [← Real.exp_add]; norm_num
  linarith [hmid, htail, hexp5]

/-- Numerical input: `e^{-2} + (3/10) e ≤ 1`. -/
lemma exp_neg_two_add_three_tenths_le_one : Real.exp (-2) + (3/10)*Real.exp 1 ≤ 1 := by
  have hge : (2.7:ℝ) ≤ Real.exp 1 := by
    refine le_trans ?_ (Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ (1:ℝ)) 5)
    norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  have hxle : Real.exp 1 ≤ 2.719 := le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))
  have hexp2 : Real.exp (-2) = ((Real.exp 1)^2)⁻¹ := by
    rw [Real.exp_neg, show (2:ℝ) = ((2:ℕ):ℝ)*1 by norm_num, Real.exp_nat_mul]
  have h7 : (7.29:ℝ) ≤ (Real.exp 1)^2 := by
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2.7) hge 2
    norm_num at h ⊢
    exact h
  have hle : Real.exp (-2) ≤ 1/7.29 := by
    rw [hexp2, one_div]
    exact inv_anti₀ (by norm_num : (0:ℝ) < 7.29) h7
  linarith [hle, hxle]

/-- The `Ioi 3` tail of the profile, i.e. `∫_3^∞ 3e^{-u}/u du ≤ e^{-3} - (3/50)e^{-2}`. -/
lemma tail3_le :
    (∫ u in Set.Ioi (3:ℝ), 3 * Real.exp (-u)/u) ≤ Real.exp (-3) - (3/50)*Real.exp (-2) := by
  have hconst : (∫ u in Set.Ioi (3:ℝ), 3 * Real.exp (-u)/u)
      = 3 * ∫ u in Set.Ioi (3:ℝ), Real.exp (-u)/u := by
    rw [← MeasureTheory.integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioi (fun u hu => by ring)
  rw [hconst]
  refine le_trans (mul_le_mul_of_nonneg_left E1_three_le (by norm_num)) ?_
  have hexp : Real.exp (-2) = Real.exp (-3) * Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  have h1 : 4 + Real.exp (-2) ≤ 5 - (3/10)*Real.exp 1 := by
    linarith [exp_neg_two_add_three_tenths_le_one]
  nlinarith [hexp, h1, Real.exp_pos (-3), Real.exp_pos (-2)]

/-! ## §3  The three transport inequalities -/

theorem errH_transport :
    (∀ s : ℝ, 2 ≤ s → (∫ t in Set.Ioi s,
        Work.NumberTheory.Chen.APSwitchUpper.errH (t - 1)) ≤ (97/100) * s *
          Work.NumberTheory.Chen.APSwitchUpper.errH s)
    ∧ (∀ s : ℝ, 3 ≤ s → Work.NumberTheory.Chen.APSwitchUpper.errH (s - 1) ≤
        (4 * Real.exp 1 / 3) * Work.NumberTheory.Chen.APSwitchUpper.errH s)
    ∧ (∀ s : ℝ, 1 ≤ s → s ≤ 3 → (3 / s) * Work.NumberTheory.Chen.APSwitchUpper.errH 2 ≤
        3 * Work.NumberTheory.Chen.APSwitchUpper.errH s) := by
  -- the sharp `Ioi 3` bound for `errH`
  have hI3 : (∫ u in Set.Ioi (3:ℝ), errH u) ≤ Real.exp (-3) - (3/50)*Real.exp (-2) := by
    have hcong : (∫ u in Set.Ioi (3:ℝ), errH u) = ∫ u in Set.Ioi (3:ℝ), 3*Real.exp (-u)/u :=
      setIntegral_congr_fun measurableSet_Ioi (fun u hu => errH_of_three_lt hu)
    rw [hcong]
    exact tail3_le
  refine ⟨?_, ?_, ?_⟩
  · -- #### claim 1: the tail transport
    intro s hs2
    rw [setIntegral_Ioi_comp_sub errH s 1]
    by_cases hs3 : s ≤ 3
    · -- #### case `2 ≤ s ≤ 3`
      have hInt : IntegrableOn errH (Set.Ioi (s-1)) := integrableOn_errH_Ioi (by linarith)
      have hInt2 : IntegrableOn errH (Set.Ioi (2:ℝ)) := integrableOn_errH_Ioi (by norm_num)
      have hdecomp1 : (∫ u in Set.Ioi (s-1), errH u)
          = (∫ u in (s-1)..2, errH u) + ∫ u in Set.Ioi (2:ℝ), errH u := by
        have h := intervalIntegral.integral_Ioi_sub_Ioi (f := errH) (a := s-1) (b := 2) hInt
          (by linarith)
        linarith
      have hdecomp2 : (∫ u in Set.Ioi (2:ℝ), errH u)
          = (∫ u in (2:ℝ)..3, errH u) + ∫ u in Set.Ioi (3:ℝ), errH u := by
        have h := intervalIntegral.integral_Ioi_sub_Ioi (f := errH) (a := 2) (b := 3) hInt2
          (by norm_num)
        linarith
      have h12 : (∫ u in (s-1)..2, errH u) = (3-s)*Real.exp (-2) := by
        have hcong : (∫ u in (s-1)..2, errH u) = ∫ u in (s-1)..2, Real.exp (-2) := by
          refine intervalIntegral.integral_congr ?_
          intro u hu
          rw [Set.uIcc_of_le (by linarith : s-1 ≤ 2)] at hu
          exact errH_of_le_two hu.2
        rw [hcong, intervalIntegral.integral_const]
        simp only [smul_eq_mul]
        ring
      have h23 : (∫ u in (2:ℝ)..3, errH u) = Real.exp (-2) - Real.exp (-3) := by
        have hcong : (∫ u in (2:ℝ)..3, errH u) = ∫ u in (2:ℝ)..3, Real.exp (-u) := by
          refine intervalIntegral.integral_congr ?_
          intro u hu
          rw [Set.uIcc_of_le (by norm_num : (2:ℝ) ≤ 3)] at hu
          exact errH_eq_exp_neg hu.1 hu.2
        rw [hcong]
        have h := intervalIntegral.integral_Ioi_sub_Ioi (f := fun u : ℝ => Real.exp (-u))
          (a := 2) (b := 3) (integrableOn_exp_neg_Ioi 2) (by norm_num)
        rw [integral_exp_neg_Ioi, integral_exp_neg_Ioi] at h
        linarith
      have hstep : (∫ u in Set.Ioi (s-1), errH u) ≤ Real.exp (-2)*(3.94 - s) := by
        have hp : (0:ℝ) < Real.exp (-2) := Real.exp_pos _
        linarith [hdecomp1, hdecomp2, h12, h23, hI3]
      have hnum : Real.exp (-2)*(3.94 - s) ≤ (97/100)*s*errH s := by
        rw [errH_eq_exp_neg hs2 hs3]
        have hpos : (0:ℝ) < Real.exp (-2) := Real.exp_pos _
        have hσ0 : 0 ≤ s - 2 := by linarith
        have hσ1 : s - 2 ≤ 1 := by linarith
        have hexp : Real.exp (s - 2) ≤ 1 + (s-2) + (s-2)^2/2 + (2/9)*(s-2)^3 := by
          have h := Real.exp_bound' (x := s - 2) hσ0 hσ1 (n := 3) (by norm_num)
          simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
          convert h using 3 <;> ring
        have hPpos : 0 < 1 + (s-2) + (s-2)^2/2 + (2/9)*(s-2)^3 := by positivity
        have hpoly : (1.94 - (s-2)) * (1 + (s-2) + (s-2)^2/2 + (2/9)*(s-2)^3)
            ≤ (97/100)*(2 + (s-2)) := by
          have h1 : (0:ℝ) ≤ s - 2 := hσ0
          nlinarith [sq_nonneg (s-2), mul_nonneg h1 h1, mul_nonneg (mul_nonneg h1 h1) h1,
            mul_nonneg (mul_nonneg (mul_nonneg h1 h1) h1) h1]
        have hD : (1.94 - (s-2))
            ≤ (97/100)*(2 + (s-2)) / (1 + (s-2) + (s-2)^2/2 + (2/9)*(s-2)^3) := by
          rw [le_div_iff₀ hPpos]; exact hpoly
        have hinv : (1 + (s-2) + (s-2)^2/2 + (2/9)*(s-2)^3)⁻¹ ≤ Real.exp (-(s-2)) := by
          rw [Real.exp_neg]
          exact inv_anti₀ (Real.exp_pos _) hexp
        have hexpneg : (97/100)*(2 + (s-2)) / (1 + (s-2) + (s-2)^2/2 + (2/9)*(s-2)^3)
            ≤ (97/100)*(2 + (s-2))*Real.exp (-(s-2)) := by
          rw [div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_left hinv (by nlinarith)
        have hrewrite : Real.exp (-s) = Real.exp (-2) * Real.exp (-(s-2)) := by
          rw [← Real.exp_add]; congr 1; ring
        have hmain : (3.94 - s) ≤ (97/100)*s*Real.exp (-(s-2)) := by
          have h1 : (3.94 - s) = 1.94 - (s-2) := by ring
          have h2 : (97/100)*(2+(s-2)) = (97/100)*s := by ring
          rw [h1, ← h2]
          exact le_trans hD hexpneg
        calc Real.exp (-2) * (3.94 - s) ≤ Real.exp (-2) * ((97/100)*s*Real.exp (-(s-2))) :=
              mul_le_mul_of_nonneg_left hmain hpos.le
          _ = (97/100)*s*Real.exp (-s) := by rw [hrewrite]; ring
      linarith [hstep, hnum]
    · -- #### case `3 < s`
      have hs3' : 3 < s := not_le.mp hs3
      by_cases hs4 : s ≤ 4
      · -- #### case `3 < s ≤ 4`
        have hInt : IntegrableOn errH (Set.Ioi (s-1)) := integrableOn_errH_Ioi (by linarith)
        have hdecomp : (∫ u in Set.Ioi (s-1), errH u)
            = (∫ u in (s-1)..3, errH u) + ∫ u in Set.Ioi (3:ℝ), errH u := by
          have h := intervalIntegral.integral_Ioi_sub_Ioi (f := errH) (a := s-1) (b := 3) hInt
            (by linarith)
          linarith
        have h23 : (∫ u in (s-1)..3, errH u) = Real.exp (-(s-1)) - Real.exp (-3) := by
          have hcong : (∫ u in (s-1)..3, errH u) = ∫ u in (s-1)..3, Real.exp (-u) := by
            refine intervalIntegral.integral_congr ?_
            intro u hu
            rw [Set.uIcc_of_le (by linarith : s-1 ≤ 3)] at hu
            exact errH_eq_exp_neg (by linarith [hu.1]) hu.2
          rw [hcong]
          have h := intervalIntegral.integral_Ioi_sub_Ioi (f := fun u : ℝ => Real.exp (-u))
            (a := s-1) (b := 3) (integrableOn_exp_neg_Ioi (s-1)) (by linarith)
          rw [integral_exp_neg_Ioi, integral_exp_neg_Ioi] at h
          linarith
        have hstep : (∫ u in Set.Ioi (s-1), errH u) ≤ Real.exp (-(s-1)) := by
          have hp : (0:ℝ) < Real.exp (-2) := Real.exp_pos _
          linarith [hdecomp, h23, hI3]
        have hgoal : Real.exp (-(s-1)) ≤ (97/100)*s*errH s := by
          rw [errH_of_ge_three (le_of_lt hs3')]
          have he : Real.exp 1 ≤ 2.91 := le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))
          have hkey : Real.exp (-(s-1)) = Real.exp 1 * Real.exp (-s) := by
            rw [show -(s-1) = 1 + (-s) by ring, Real.exp_add]
          rw [hkey]
          have hR : (97/100)*s*(3*Real.exp (-s)/s) = (97/100)*3*Real.exp (-s) := by
            field_simp
          rw [hR]
          have hE : (0:ℝ) < Real.exp (-s) := Real.exp_pos _
          nlinarith [hE, he, mul_nonneg hE.le (by linarith : (0:ℝ) ≤ 2.91 - Real.exp 1)]
        linarith [hstep, hgoal]
      · -- #### case `s > 4`
        have hs4' : 4 < s := not_le.mp hs4
        have hD : (0:ℝ) < s - 1 := by linarith
        have hcong : (∫ u in Set.Ioi (s-1), errH u)
            = ∫ u in Set.Ioi (s-1), 3 * Real.exp (-u)/u :=
          setIntegral_congr_fun measurableSet_Ioi
            (fun u hu => errH_of_three_lt (by linarith [Set.mem_Ioi.mp hu]))
        rw [hcong]
        have hfF : IntegrableOn (fun u : ℝ => 3 * Real.exp (-u)/u) (Set.Ioi (s-1)) := by
          refine Integrable.mono' (g := fun u : ℝ => 3 * Real.exp (-u) / 3) ?_ ?_ ?_
          · exact ((integrableOn_exp_neg_Ioi (s-1)).integrable.const_mul 3).div_const 3
          · apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
            apply ContinuousOn.div
            · fun_prop
            · fun_prop
            · intro u hu
              exact ne_of_gt (by linarith [Set.mem_Ioi.mp hu] : (0:ℝ) < u)
          · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
            have hu3 : (3:ℝ) < u := by linarith [Set.mem_Ioi.mp hu]
            rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ 3*Real.exp (-u)/u)]
            rw [div_le_div_iff₀ (by linarith : (0:ℝ) < u) (by norm_num : (0:ℝ) < 3)]
            nlinarith [Real.exp_pos (-u)]
        have hgF : IntegrableOn (fun u : ℝ => 3 * Real.exp (-u)/(s-1)) (Set.Ioi (s-1)) :=
          ((integrableOn_exp_neg_Ioi (s-1)).integrable.const_mul 3).div_const (s-1)
        have hmono : (∫ u in Set.Ioi (s-1), 3 * Real.exp (-u)/u)
            ≤ ∫ u in Set.Ioi (s-1), 3 * Real.exp (-u)/(s-1) := by
          refine setIntegral_mono_on hfF hgF measurableSet_Ioi (fun u hu => ?_)
          have hu0 : (0:ℝ) < u := by linarith [Set.mem_Ioi.mp hu]
          exact div_le_div_of_nonneg_left (by positivity) hD (by linarith [Set.mem_Ioi.mp hu])
        have hval : (∫ u in Set.Ioi (s-1), 3 * Real.exp (-u)/(s-1))
            = 3 * Real.exp (-(s-1))/(s-1) := by
          rw [MeasureTheory.integral_div]
          congr 1
          rw [MeasureTheory.integral_const_mul, integral_exp_neg_Ioi]
        have hgoal : 3 * Real.exp (-(s-1))/(s-1) ≤ (97/100)*s*errH s := by
          rw [errH_of_ge_three (by linarith : (3:ℝ) ≤ s)]
          have he : Real.exp 1 ≤ 2.91 := le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))
          have hkey : 3 * Real.exp (-(s-1)) = 3 * Real.exp 1 * Real.exp (-s) := by
            rw [show -(s-1) = 1 + (-s) by ring, Real.exp_add]; ring
          rw [hkey]
          have hR : (97/100)*s*(3*Real.exp (-s)/s) = (97/100)*3*Real.exp (-s) := by
            field_simp
          rw [hR, div_le_iff₀ hD]
          have hE : (0:ℝ) ≤ Real.exp (-s) := (Real.exp_pos _).le
          have h2 : (0:ℝ) ≤ 2.91*(s-1) - 3*Real.exp 1 := by nlinarith [he, hs4']
          nlinarith [mul_nonneg hE h2]
        linarith [hmono, hval, hgoal]
  · -- #### claim 2: the shift inequality
    intro s hs3
    by_cases hs4 : s ≤ 4
    · -- `3 ≤ s ≤ 4`
      have h1 : errH (s-1) = Real.exp (-(s-1)) := errH_eq_exp_neg (by linarith) (by linarith)
      have h2 : errH s = 3 * Real.exp (-s)/s := errH_of_ge_three hs3
      rw [h1, h2]
      have hs0 : (0:ℝ) < s := by linarith
      have hR : (4 * Real.exp 1 / 3) * (3 * Real.exp (-s) / s) = 4 * Real.exp 1 * Real.exp (-s)/s := by
        field_simp
      rw [hR,
        show Real.exp (-(s-1)) = Real.exp 1 * Real.exp (-s) by
          rw [show -(s-1) = 1 + (-s) by ring, Real.exp_add]]
      rw [le_div_iff₀ hs0]
      nlinarith [Real.exp_pos (-s), Real.exp_pos 1, hs4,
        mul_pos (Real.exp_pos 1) (Real.exp_pos (-s))]
    · -- `s > 4`
      have hs4' : 4 < s := not_le.mp hs4
      have h1 : errH (s-1) = 3 * Real.exp (-(s-1))/(s-1) := errH_of_ge_three (by linarith)
      have h2 : errH s = 3 * Real.exp (-s)/s := errH_of_ge_three hs3
      rw [h1, h2]
      rw [show Real.exp (-(s-1)) = Real.exp 1 * Real.exp (-s) by
        rw [show -(s-1) = 1 + (-s) by ring, Real.exp_add]]
      have hs0 : (0:ℝ) < s := by linarith
      have hp : (0:ℝ) < s - 1 := by linarith
      have hR : (4 * Real.exp 1 / 3) * (3 * Real.exp (-s) / s) = 4 * Real.exp 1 * Real.exp (-s)/s := by
        field_simp
      rw [hR, div_le_div_iff₀ hp hs0]
      nlinarith [Real.exp_pos (-s), Real.exp_pos 1, hs4',
        mul_pos (Real.exp_pos 1) (Real.exp_pos (-s))]
  · -- #### claim 3: the small-`s` comparison
    intro s hs1 hs3
    have h2 : errH 2 = Real.exp (-2) := errH_of_le_two le_rfl
    rw [h2]
    by_cases hs2 : s ≤ 2
    · -- `1 ≤ s ≤ 2`
      rw [errH_of_le_two hs2]
      have hs0 : (0:ℝ) < s := by linarith
      have hle : (3:ℝ)/s ≤ 3 := by
        rw [div_le_iff₀ hs0]; nlinarith
      calc (3/s)*Real.exp (-2) = (3/s)*Real.exp (-2) := rfl
        _ ≤ 3*Real.exp (-2) := mul_le_mul_of_nonneg_right hle (Real.exp_pos _).le
    · -- `2 < s ≤ 3`
      have hs2' : 2 < s := not_le.mp hs2
      rw [errH_of_between hs2' hs3]
      have hs0 : (0:ℝ) < s := by linarith
      have hexp : Real.exp (s-2) ≤ s := by
        have ht0 : (0:ℝ) ≤ s-2 := by linarith
        have ht1 : s-2 ≤ 1 := by linarith
        have hb := Real.exp_bound' (x := s-2) ht0 ht1 (n := 1) (by norm_num)
        simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hb
        nlinarith [hb]
      have hmain : Real.exp (-2)/s ≤ Real.exp (-s) := by
        rw [div_le_iff₀ hs0]
        have h : Real.exp (-2) = Real.exp (-s) * Real.exp (s-2) := by
          rw [← Real.exp_add]; congr 1; ring
        rw [h]
        exact mul_le_mul_of_nonneg_left hexp (Real.exp_pos _).le
      have h3 : (3:ℝ)*(Real.exp (-2)/s) ≤ 3*Real.exp (-s) :=
        mul_le_mul_of_nonneg_left hmain (by norm_num)
      calc (3/s)*Real.exp (-2) = 3*(Real.exp (-2)/s) := by ring
        _ ≤ 3*Real.exp (-s) := h3

end

end Work.NumberTheory.Chen.APSwitchUpper
