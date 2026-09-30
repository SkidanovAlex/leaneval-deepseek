import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.parseval.Defs
import Submission.Work.BMF.parseval.Basics
import Submission.Work.BMF.Phi_norm_bounds
import Submission.Work.BMF.mwt_transform_bound
import Submission.Work.BMF.frozen_l2_bound
import Submission.Work.BMF.dirP_weighted_integral_le
import Submission.Work.BMF.window_decomposition
import Submission.Work.BMF.perron_reduction_single
import Submission.Work.BMF.tail_integrable
import Submission.Work.BMF.dyadic
import Submission.Work.BMF.frozen_l2_bound_proof
import Submission.Work.BMF.window_J1_bound
import Submission.Work.BMF.window_J2_bound
import Submission.Work.BMF.perronP_l2_via_parts

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The single-window Parseval bound (`mr_parseval_direct`)

For every `1`-bounded sequence `a : ℕ → ℂ` and every `1 ≤ H ≤ Y`,

`Y⁻¹ ∫_Y^{2Y} ‖H⁻¹ Σ_{y ≤ n ≤ y+H} a n‖² ≤ C ( ‖Y⁻¹ Σ_{Y ≤ n ≤ 2Y} a n‖² + (log Y)^{-2/15}
     + ∫_{|t| ≤ Y/H} ‖A(1+it)‖² + ⨆_{T ≥ Y/H} (Y/H)/T ∫_{|t| ≤ 2T} ‖A(1+it)‖² )`,

where `A(1+it) = Σ_{Y ≤ n ≤ 3Y} a n n^{-1-it} = dirP a Y t`.  This is the "direct Parseval"
reduction of Matomäki–Radziwiłł (Annals 2016, Lemma `lem:shortintsumtoDirpols`) in the
single-window form used by the Matomäki–Radziwiłł node of the MRTTZ project.
-/

set_option maxHeartbeats 4000000

open scoped BigOperators
open MeasureTheory intervalIntegral

namespace Work.BMF

noncomputable section

/-- The constant in the Fourier decay of the logarithmic weight `mwt`. -/
def mpC0 : ℝ := Real.exp (-4) * (1 + Real.exp 5 + Real.exp 20 + Real.exp 15)

lemma mpC0_pos : 0 < mpC0 := by unfold mpC0; positivity

/-- A crude numerical bound for the constant `mpC0`. -/
lemma mpC0_le : mpC0 ≤ 4 * 10^9 := by
  unfold mpC0
  have he : Real.exp 1 ≤ 3 := le_of_lt Real.exp_one_lt_three
  have h4 : Real.exp (-4) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  have h5 : Real.exp 5 ≤ 243 := by
    have h : Real.exp 5 = (Real.exp 1)^5 := by
      rw [show (5:ℝ) = ((5:ℕ) : ℝ) * 1 by norm_num, Real.exp_nat_mul]
    rw [h]
    have h2 : ((Real.exp 1)^5 : ℝ) ≤ 3^5 :=
      pow_le_pow_left₀ (Real.exp_pos 1).le he 5
    norm_num at h2 ⊢
    linarith
  have h15 : Real.exp 15 ≤ 14348907 := by
    have h : Real.exp 15 = (Real.exp 1)^15 := by
      rw [show (15:ℝ) = ((15:ℕ) : ℝ) * 1 by norm_num, Real.exp_nat_mul]
    rw [h]
    have h2 : ((Real.exp 1)^15 : ℝ) ≤ 3^15 :=
      pow_le_pow_left₀ (Real.exp_pos 1).le he 15
    norm_num at h2 ⊢
    exact h2
  have h20 : Real.exp 20 ≤ 3486784401 := by
    have h : Real.exp 20 = (Real.exp 1)^20 := by
      rw [show (20:ℝ) = ((20:ℕ) : ℝ) * 1 by norm_num, Real.exp_nat_mul]
    rw [h]
    have h2 : ((Real.exp 1)^20 : ℝ) ≤ 3^20 :=
      pow_le_pow_left₀ (Real.exp_pos 1).le he 20
    norm_num at h2 ⊢
    exact h2
  have hsum : 1 + Real.exp 5 + Real.exp 20 + Real.exp 15
      ≤ 1 + 243 + 3486784401 + 14348907 := by linarith
  have hprod : Real.exp (-4) * (1 + Real.exp 5 + Real.exp 20 + Real.exp 15)
      ≤ 1 * (1 + 243 + 3486784401 + 14348907) := by
    refine mul_le_mul h4 hsum (by linarith [Real.exp_pos 5, Real.exp_pos 20, Real.exp_pos 15])
      (by norm_num)
  linarith

/-! ## Continuity of the elementary kernels -/

lemma mp_continuous_Phi_u (u : ℝ) : Continuous (fun t : ℝ => Phi t u) := by
  have h1 : Continuous (fun t : ℝ => (1 : ℂ) + Complex.I * (t : ℂ)) := by fun_prop
  have h2 : Continuous fun t : ℝ => ((1 + u : ℝ) : ℂ) ^ (1 + Complex.I * (t : ℂ)) :=
    h1.const_cpow (Or.inr (fun t => by
      intro h; have := congrArg Complex.re h; simp at this))
  exact (h2.sub continuous_const).div h1 (fun t => by
    intro h; have := congrArg Complex.re h; simp at this)

lemma mp_continuous_weight (c : ℝ) : Continuous (fun t : ℝ => min 1 (c / (1 + |t|))) :=
  Continuous.min continuous_const
    (Continuous.div continuous_const (continuous_const.add continuous_abs) (fun t => by
      positivity))

/-- The trapezoid weight `kappa` is continuous: it is `min 1 (max 0 (min w (4-w)))`. -/
lemma mp_continuous_kappa : Continuous kappa := by
  have hfun : kappa = fun w : ℝ => min 1 (max 0 (min w (4 - w))) := by
    funext w
    unfold kappa
    by_cases h0 : w ≤ 0
    · rw [if_pos h0, min_eq_left (by linarith : w ≤ 4 - w),
        max_eq_left (by linarith : w ≤ 0), min_eq_right (by norm_num : (0:ℝ) ≤ 1)]
    · rw [if_neg h0]
      have hw0 : (0:ℝ) ≤ w := le_of_lt (not_le.mp h0)
      by_cases h1 : w ≤ 1
      · rw [if_pos h1, min_eq_left (by linarith : w ≤ 4 - w), max_eq_right hw0,
          min_eq_right h1]
      · rw [if_neg h1]
        have hw1 : (1:ℝ) ≤ w := le_of_lt (not_le.mp h1)
        by_cases h3 : w ≤ 3
        · rw [if_pos h3]
          have hmin : (1:ℝ) ≤ min w (4 - w) := le_min (by linarith) (by linarith)
          rw [max_eq_right (le_trans (by norm_num) hmin), min_eq_left hmin]
        · rw [if_neg h3]
          have hw3 : (3:ℝ) ≤ w := le_of_lt (not_le.mp h3)
          by_cases h4 : w ≤ 4
          · rw [if_pos h4, min_eq_right (by linarith : 4 - w ≤ w),
              max_eq_right (by linarith : (0:ℝ) ≤ 4 - w),
              min_eq_right (by linarith : 4 - w ≤ 1)]
          · rw [if_neg h4, min_eq_right (by linarith : 4 - w ≤ w),
              max_eq_left (by linarith : 4 - w ≤ 0),
              min_eq_right (by norm_num : (0:ℝ) ≤ 1)]
  rw [hfun]; fun_prop

lemma mp_continuous_mwt_of_pos {X : ℝ} (hX : 0 < X) :
    ContinuousOn (fun x : ℝ => mwt X x) {x | 0 < x} := by
  have h1 : ContinuousOn (fun x : ℝ => Real.log (x/X) + 1) {x | 0 < x} :=
    ContinuousOn.add
      (ContinuousOn.log (continuousOn_id.div continuousOn_const (fun x hx => by
          simp only [Set.mem_setOf_eq] at hx; exact ne_of_gt hX))
        (fun x hx => ne_of_gt (div_pos hx hX))) continuousOn_const
  simpa only [mwt, Function.comp_def] using mp_continuous_kappa.comp_continuousOn h1

/-- `(x,t) ↦ x^{2+it}` is jointly continuous. -/
lemma mp_continuous_cpow_pair :
    Continuous fun q : ℝ × ℝ => ((q.1 : ℝ) : ℂ) ^ (2 + Complex.I * ((q.2 : ℝ) : ℂ)) := by
  rw [continuous_iff_continuousAt]
  intro p
  have hg : ContinuousAt (fun q : ℝ × ℝ => ((q.1 : ℝ), 2 + Complex.I * ((q.2 : ℝ) : ℂ))) p := by
    fun_prop
  have hf := Complex.continuousAt_ofReal_cpow p.1 (2 + Complex.I * ((p.2 : ℝ) : ℂ))
    (Or.inl (by simp : 0 < (2 + Complex.I * ((p.2 : ℝ) : ℂ)).re))
  exact ContinuousAt.comp (x := p)
    (f := fun q : ℝ × ℝ => ((q.1 : ℝ), 2 + Complex.I * ((q.2 : ℝ) : ℂ))) hf hg

/-- `Φ` is jointly continuous in its two arguments. -/
lemma mp_continuous_Phi_pair : Continuous fun q : ℝ × ℝ => Phi q.1 q.2 := by
  rw [continuous_iff_continuousAt]
  intro p
  unfold Phi
  refine ContinuousAt.div ?_ (by fun_prop) ?_
  · refine ContinuousAt.sub ?_ continuousAt_const
    have hg : ContinuousAt (fun q : ℝ × ℝ =>
        ((1 + q.2 : ℝ), 1 + Complex.I * ((q.1 : ℝ) : ℂ))) p := by fun_prop
    have hf := Complex.continuousAt_ofReal_cpow (1 + p.2) (1 + Complex.I * ((p.1 : ℝ) : ℂ))
      (Or.inl (by simp : 0 < (1 + Complex.I * ((p.1 : ℝ) : ℂ)).re))
    exact ContinuousAt.comp (x := p)
      (f := fun q : ℝ × ℝ => ((1 + q.2 : ℝ), 1 + Complex.I * ((q.1 : ℝ) : ℂ))) hf hg
  · intro h; have := congrArg Complex.re h; simp at this

/-- Continuity in `x` of the frozen transform at fixed `u`. -/
lemma mp_continuous_frozen_int (a : ℕ → ℂ) (X T u : ℝ) :
    Continuous (fun x : ℝ => ∫ t in (-T)..T,
      (dirP a X t * Phi t u) * (x : ℂ) ^ (2 + Complex.I * (t : ℂ))) := by
  have hPhi : Continuous fun p : ℝ × ℝ => Phi p.2 u :=
    mp_continuous_Phi_pair.comp (continuous_snd.prodMk continuous_const)
  have hpair : Continuous fun p : ℝ × ℝ =>
      (dirP a X p.2 * Phi p.2 u) * ((p.1 : ℝ) : ℂ) ^ (2 + Complex.I * ((p.2 : ℝ) : ℂ)) :=
    (((continuous_dirP a X).comp continuous_snd).mul hPhi).mul mp_continuous_cpow_pair
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hpair (-T) T

/-! ## Pointwise size of `Φ` against the logarithmic weight -/

lemma mp_Phi_norm_le_weight (X h t u : ℝ) (hX : 0 < X) (hh : 0 < h) (hhX : h ≤ X)
    (hu : 0 ≤ u) (hu2 : u ≤ 3*h/X) :
    ‖Phi t u‖ ≤ 8 * (h/X) * min 1 (8*(X/h)/(1+|t|)) := by
  have hden : (0:ℝ) < 1 + |t| := by positivity
  have hu3 : u ≤ 3 := by
    have h3 : 3*h/X ≤ 3 := by rw [div_le_iff₀ hX]; nlinarith
    linarith
  have hkey : ‖Phi t u‖ ≤ min (8/(1+|t|)) (3*h/X) :=
    le_min (Phi_norm_bounds.2 t u hu hu3) (le_trans (Phi_norm_bounds.1 t u hu) hu2)
  refine le_trans hkey ?_
  by_cases hc : 8*(X/h)/(1+|t|) ≤ 1
  · rw [min_eq_right hc]
    have hcalc : 8 * (h/X) * (8*(X/h)/(1+|t|)) = 64/(1+|t|) := by
      field_simp; ring
    rw [hcalc]
    refine le_trans (min_le_left _ _) ?_
    rw [div_le_div_iff_of_pos_right hden]; linarith
  · rw [min_eq_left (by linarith : (1:ℝ) ≤ 8*(X/h)/(1+|t|)), mul_one]
    refine le_trans (min_le_right _ _) ?_
    rw [show (8:ℝ)*(h/X) = 8*h/X by ring]
    exact div_le_div_of_nonneg_right (by linarith) hX.le

/-! ## The interval version of the weighted frequency bound -/

lemma mp_dirP_weighted_interval_le (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) (X R T S : ℝ)
    (hX : 1 ≤ X) (hR : 0 < R) (hS : 0 ≤ S)
    (hsup : ∀ T' : ℝ, R ≤ T' → R/T' * (∫ t in (-(2*T'))..(2*T'), ‖dirP a X t‖^2) ≤ S) :
    ∫ t in (-T)..T, ‖dirP a X t‖^2 * (min 1 (8*R/(1+|t|)))^2
      ≤ (∫ t in (-R)..R, ‖dirP a X t‖^2) + 128*S := by
  rcases lt_or_ge T 0 with hTneg | hTge
  · rw [intervalIntegral.integral_of_ge (by linarith : T ≤ -T)]
    have h1 : -(∫ t in Set.Ioc T (-T), ‖dirP a X t‖^2 * (min 1 (8*R/(1+|t|)))^2) ≤ 0 :=
      neg_nonpos.mpr (MeasureTheory.setIntegral_nonneg measurableSet_Ioc
        (fun t _ => mul_nonneg (by positivity) (sq_nonneg _)))
    have h2 : (0:ℝ) ≤ (∫ t in (-R)..R, ‖dirP a X t‖^2) + 128*S :=
      add_nonneg (intervalIntegral.integral_nonneg (by linarith) (fun t _ => by positivity))
        (by linarith)
    linarith
  · set F : ℝ → ℝ := fun t => ‖dirP a X t‖^2 with hFdef
    set B : ℝ := ∑ n ∈ natIcc X (3*X), (1:ℝ)/(n:ℝ) with hBdef
    have hFnn : ∀ t, 0 ≤ F t := fun t => by rw [hFdef]; positivity
    have hFmeas : Measurable F := ((continuous_dirP a X).norm.pow 2).measurable
    have hFcont : Continuous F := ((continuous_dirP a X).norm).pow 2
    have hFbd : ∀ t, F t ≤ B^2 := by
      intro t
      rw [hFdef, hBdef]
      exact pow_le_pow_left₀ (norm_nonneg _) (dirP_norm_le_sum a ha X t) 2
    have htail : ∫ t in {t : ℝ | R < |t|}, F t * (R^2/t^2) ≤ 2*S :=
      dyadicTail_le F hFnn hFmeas (B^2) hFbd R S hR hS hsup
    have hIntTail : IntegrableOn (fun t : ℝ => F t * (R^2/t^2)) {t : ℝ | R < |t|} :=
      tail_integrable F hFnn hFmeas (B^2) hFbd R hR
    have hIntIcc : IntegrableOn F (Set.Icc (-R) R) :=
      ContinuousOn.integrableOn_compact isCompact_Icc hFcont.continuousOn
    have hmaj : Integrable (fun t : ℝ => (Set.Icc (-R) R).indicator F t
        + 64 * ({t : ℝ | R < |t|}.indicator (fun t => F t * (R^2/t^2)) t)) :=
      Integrable.add (hIntIcc.integrable_indicator measurableSet_Icc)
        ((hIntTail.integrable_indicator
          (measurableSet_lt measurable_const measurable_id.abs)).const_mul 64)
    have hmajnn : ∀ t : ℝ, 0 ≤ (Set.Icc (-R) R).indicator F t
        + 64 * ({t : ℝ | R < |t|}.indicator (fun t => F t * (R^2/t^2)) t) := by
      intro t
      refine add_nonneg ?_ ?_
      · by_cases h : t ∈ Set.Icc (-R) R
        · rw [Set.indicator_of_mem h]; exact hFnn t
        · rw [Set.indicator_of_notMem h]
      · refine mul_nonneg (by norm_num) ?_
        by_cases h : t ∈ {t : ℝ | R < |t|}
        · rw [Set.indicator_of_mem h]; exact mul_nonneg (hFnn t) (by positivity)
        · rw [Set.indicator_of_notMem h]
    have hpt : ∀ t : ℝ, F t * (min 1 (8*R/(1+|t|)))^2
        ≤ (Set.Icc (-R) R).indicator F t
          + 64 * ({t : ℝ | R < |t|}.indicator (fun t => F t * (R^2/t^2)) t) := by
      intro t
      have hWnn : (0:ℝ) ≤ min 1 (8*R/(1+|t|)) := le_min (by norm_num) (by positivity)
      by_cases h : |t| ≤ R
      · have habs := abs_le.mp h
        have hmem : t ∈ Set.Icc (-R) R := by rw [Set.mem_Icc]; exact ⟨habs.1, habs.2⟩
        have hnot : t ∉ {t : ℝ | R < |t|} := by simp only [Set.mem_setOf_eq, not_lt]; exact h
        rw [Set.indicator_of_mem hmem, Set.indicator_of_notMem hnot]
        simp only [mul_zero, add_zero]
        have hW1 : (min 1 (8*R/(1+|t|)))^2 ≤ 1 := pow_le_one₀ hWnn (min_le_left _ _)
        calc F t * (min 1 (8*R/(1+|t|)))^2 ≤ F t * 1 :=
              mul_le_mul_of_nonneg_left hW1 (hFnn t)
          _ = F t := mul_one _
      · have hnot : t ∉ Set.Icc (-R) R := by
          intro hc; exact h (abs_le.mpr (by rwa [Set.mem_Icc] at hc))
        have hmem : t ∈ {t : ℝ | R < |t|} := by simpa using h
        rw [Set.indicator_of_notMem hnot, Set.indicator_of_mem hmem]
        simp only [zero_add]
        have htpos : 0 < |t| := lt_trans hR (not_le.mp h)
        have hb : min 1 (8*R/(1+|t|)) ≤ 8*R/|t| :=
          le_trans (min_le_right _ _) (by
            apply div_le_div_of_nonneg_left (by positivity) htpos
            linarith)
        have h2 : (min 1 (8*R/(1+|t|)))^2 ≤ (8*R/t)^2 := by
          have h3 : (8*R/|t|)^2 = (8*R/t)^2 := by rw [div_pow, div_pow, sq_abs]
          rw [← h3]
          exact pow_le_pow_left₀ hWnn hb 2
        calc F t * (min 1 (8*R/(1+|t|)))^2 ≤ F t * (8*R/t)^2 :=
              mul_le_mul_of_nonneg_left h2 (hFnn t)
          _ = 64 * (F t * (R^2/t^2)) := by ring
    have hIntIocL : IntegrableOn (fun t : ℝ => F t * (min 1 (8*R/(1+|t|)))^2)
        (Set.Ioc (-T) T) :=
      (ContinuousOn.integrableOn_compact isCompact_Icc
        ((hFcont.mul ((mp_continuous_weight (8*R)).pow 2)).continuousOn)).mono_set
        Set.Ioc_subset_Icc_self
    have hstep1 : ∫ t in Set.Ioc (-T) T, F t * (min 1 (8*R/(1+|t|)))^2
        ≤ ∫ t in Set.Ioc (-T) T, ((Set.Icc (-R) R).indicator F t
          + 64 * ({t : ℝ | R < |t|}.indicator (fun t => F t * (R^2/t^2)) t)) :=
      MeasureTheory.setIntegral_mono hIntIocL hmaj.integrableOn (fun t => hpt t)
    have hstep2 : ∫ t in Set.Ioc (-T) T, ((Set.Icc (-R) R).indicator F t
          + 64 * ({t : ℝ | R < |t|}.indicator (fun t => F t * (R^2/t^2)) t))
        ≤ ∫ t : ℝ, ((Set.Icc (-R) R).indicator F t
          + 64 * ({t : ℝ | R < |t|}.indicator (fun t => F t * (R^2/t^2)) t)) :=
      MeasureTheory.setIntegral_le_integral hmaj (by filter_upwards with t; exact hmajnn t)
    have hA : ∫ t : ℝ, (Set.Icc (-R) R).indicator F t = ∫ t in Set.Icc (-R) R, F t := by
      rw [MeasureTheory.integral_indicator]
      exact measurableSet_Icc
    have hB : ∫ t : ℝ, ({t : ℝ | R < |t|}.indicator (fun t => F t * (R^2/t^2)) t)
        = ∫ t in {t : ℝ | R < |t|}, F t * (R^2/t^2) := by
      rw [MeasureTheory.integral_indicator]
      exact measurableSet_lt measurable_const measurable_id.abs
    have hstep3 : ∫ t : ℝ, ((Set.Icc (-R) R).indicator F t
          + 64 * ({t : ℝ | R < |t|}.indicator (fun t => F t * (R^2/t^2)) t))
        = (∫ t in Set.Icc (-R) R, F t)
          + 64 * (∫ t in {t : ℝ | R < |t|}, F t * (R^2/t^2)) := by
      rw [MeasureTheory.integral_add (f := fun t : ℝ => (Set.Icc (-R) R).indicator F t)
          (g := fun t : ℝ => 64 * ({t : ℝ | R < |t|}.indicator
            (fun t => F t * (R^2/t^2)) t))
          (hIntIcc.integrable_indicator measurableSet_Icc)
          ((hIntTail.integrable_indicator
            (measurableSet_lt measurable_const measurable_id.abs)).const_mul 64),
        MeasureTheory.integral_const_mul, hA, hB]
    have hstep4 : (∫ t in Set.Icc (-R) R, F t)
          + 64 * (∫ t in {t : ℝ | R < |t|}, F t * (R^2/t^2))
        ≤ (∫ t in (-R)..R, F t) + 128*S := by
      have h3 : ∫ t in Set.Icc (-R) R, F t = ∫ t in (-R)..R, F t := by
        rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
          intervalIntegral.integral_of_le (by linarith : -R ≤ R)]
      rw [h3]
      linarith [htail]
    rw [intervalIntegral.integral_of_le (by linarith : -T ≤ T)]
    linarith [hstep1, hstep2, hstep3, hstep4]

/-! ## The mass of `dirP · Φ(·,u)` against `I` and `S` -/

lemma mp_dirP_Phi_mass_le (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) (X h T S : ℝ)
    (hX : 1 ≤ X) (hh : 0 < h) (hhX : h ≤ X) (hT : 0 ≤ T) (hS : 0 ≤ S)
    (hsup : ∀ T' : ℝ, X/h ≤ T' → (X/h)/T' * (∫ t in (-(2*T'))..(2*T'), ‖dirP a X t‖^2) ≤ S)
    (u : ℝ) (hu : 0 ≤ u) (hu2 : u ≤ 3*h/X) :
    ∫ t in (-T)..T, ‖dirP a X t * Phi t u‖^2
      ≤ 6400 * (h/X)^2 * ((∫ t in (-(X/h))..(X/h), ‖dirP a X t‖^2) + 128*S) := by
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hRpos : 0 < X/h := div_pos hXpos hh
  have hW := mp_dirP_weighted_interval_le a ha X (X/h) T S hX hRpos hS hsup
  have hpt : ∀ t : ℝ, ‖dirP a X t * Phi t u‖^2
      ≤ 64*(h/X)^2 * (‖dirP a X t‖^2 * (min 1 (8*(X/h)/(1+|t|)))^2) := by
    intro t
    have hb := mp_Phi_norm_le_weight X h t u hXpos hh hhX hu hu2
    rw [norm_mul, mul_pow]
    have hb2 : ‖Phi t u‖^2 ≤ (8 * (h/X) * min 1 (8*(X/h)/(1+|t|)))^2 :=
      pow_le_pow_left₀ (norm_nonneg _) hb 2
    have hw8 : (8 * (h/X) * min 1 (8*(X/h)/(1+|t|)))^2
        = 64*(h/X)^2 * (min 1 (8*(X/h)/(1+|t|)))^2 := by ring
    calc ‖dirP a X t‖^2 * ‖Phi t u‖^2
        ≤ ‖dirP a X t‖^2 * (8 * (h/X) * min 1 (8*(X/h)/(1+|t|)))^2 :=
          mul_le_mul_of_nonneg_left hb2 (by positivity)
      _ = 64*(h/X)^2 * (‖dirP a X t‖^2 * (min 1 (8*(X/h)/(1+|t|)))^2) := by
          rw [hw8]; ring
  have hcontL : Continuous (fun t : ℝ => ‖dirP a X t * Phi t u‖^2) :=
    (((continuous_dirP a X).mul (mp_continuous_Phi_u u)).norm).pow 2
  have hcontR : Continuous (fun t : ℝ => 64*(h/X)^2
      * (‖dirP a X t‖^2 * (min 1 (8*(X/h)/(1+|t|)))^2)) :=
    ((((continuous_dirP a X).norm).pow 2).mul ((mp_continuous_weight (8*(X/h))).pow 2)).const_mul _
  have htarget : (0:ℝ) ≤ 6400 * (h/X)^2 * ((∫ t in (-(X/h))..(X/h), ‖dirP a X t‖^2) + 128*S) := by
    refine mul_nonneg (by positivity) (add_nonneg ?_ (by linarith))
    exact intervalIntegral.integral_nonneg
      (by have hp : 0 < X/h := div_pos (lt_of_lt_of_le zero_lt_one hX) hh; linarith)
      (fun t _ => by positivity)
  rcases lt_or_ge T 0 with hTneg | hTge
  · rw [intervalIntegral.integral_of_ge (by linarith : T ≤ -T)]
    have h1 : -(∫ t in Set.Ioc T (-T), ‖dirP a X t * Phi t u‖^2) ≤ 0 :=
      neg_nonpos.mpr (MeasureTheory.setIntegral_nonneg measurableSet_Ioc
        (fun t _ => by positivity))
    linarith
  · have hmono : ∫ t in (-T)..T, ‖dirP a X t * Phi t u‖^2
        ≤ ∫ t in (-T)..T, 64*(h/X)^2 * (‖dirP a X t‖^2
          * (min 1 (8*(X/h)/(1+|t|)))^2) :=
      intervalIntegral.integral_mono_on (by linarith : -T ≤ T) (hcontL.intervalIntegrable _ _)
        (hcontR.intervalIntegrable _ _) (fun t _ => hpt t)
    rw [intervalIntegral.integral_const_mul] at hmono
    refine le_trans hmono ?_
    have hstep1 : 64*(h/X)^2 * (∫ t in (-T)..T, ‖dirP a X t‖^2
          * (min 1 (8*(X/h)/(1+|t|)))^2)
        ≤ 64*(h/X)^2 * ((∫ t in (-(X/h))..(X/h), ‖dirP a X t‖^2) + 128*S) :=
      mul_le_mul_of_nonneg_left hW (by positivity)
    have hI : 0 ≤ (∫ t in (-(X/h))..(X/h), ‖dirP a X t‖^2) + 128*S := by
      refine add_nonneg ?_ (by linarith)
      exact intervalIntegral.integral_nonneg
        (by have hp : 0 < X/h := div_pos (lt_of_lt_of_le zero_lt_one hX) hh; linarith)
        (fun t _ => by positivity)
    have hstep2 : 64*(h/X)^2 * ((∫ t in (-(X/h))..(X/h), ‖dirP a X t‖^2) + 128*S)
        ≤ 6400*(h/X)^2 * ((∫ t in (-(X/h))..(X/h), ‖dirP a X t‖^2) + 128*S) := by
      nlinarith [mul_nonneg (sq_nonneg (h/X)) hI]
    linarith [hstep1, hstep2]


/-- The `u`-integrated form of `mp_dirP_Phi_mass_le`. -/
lemma mp_dirP_Phi_mass_int (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) (X h T S c d : ℝ)
    (hX : 1 ≤ X) (hh : 0 < h) (hhX : h ≤ X) (hT : 0 ≤ T) (hS : 0 ≤ S)
    (hsup : ∀ T' : ℝ, X/h ≤ T' → (X/h)/T' * (∫ t in (-(2*T'))..(2*T'), ‖dirP a X t‖^2) ≤ S)
    (hc : 0 ≤ c) (hd : d ≤ 3*h/X) (hcd : c ≤ d) :
    ∫ u in c..d, (∫ t in (-T)..T, ‖dirP a X t * Phi t u‖^2)
      ≤ (d - c) * (6400 * (h/X)^2 * ((∫ t in (-(X/h))..(X/h), ‖dirP a X t‖^2) + 128*S)) := by
  set C : ℝ := 6400 * (h/X)^2 * ((∫ t in (-(X/h))..(X/h), ‖dirP a X t‖^2) + 128*S) with hC
  have hCnn : 0 ≤ C := by
    rw [hC]
    refine mul_nonneg (by positivity) (add_nonneg ?_ (by linarith))
    exact intervalIntegral.integral_nonneg
      (by have hp : 0 < X/h := div_pos (lt_of_lt_of_le zero_lt_one hX) hh; linarith)
      (fun t _ => by positivity)
  rw [intervalIntegral.integral_of_le hcd]
  have hmaj : Integrable ((Set.Ioc c d).indicator (fun _ : ℝ => C)) :=
    (integrableOn_const (ne_of_lt (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top))).integrable_indicator
      measurableSet_Ioc
  have hcmp : (∫ u : ℝ, (Set.Ioc c d).indicator
        (fun u => ∫ t in (-T)..T, ‖dirP a X t * Phi t u‖^2) u)
      ≤ ∫ u : ℝ, (Set.Ioc c d).indicator (fun _ : ℝ => C) u := by
    refine MeasureTheory.integral_mono_of_nonneg ?_ hmaj ?_
    · filter_upwards with u
      by_cases hu : u ∈ Set.Ioc c d
      · rw [Set.indicator_of_mem hu]
        exact intervalIntegral.integral_nonneg (by linarith) (fun t _ => by positivity)
      · simp only [Set.indicator_of_notMem hu, Pi.zero_apply, le_refl]
    · filter_upwards with u
      by_cases hu : u ∈ Set.Ioc c d
      · rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu]
        exact mp_dirP_Phi_mass_le a ha X h T S hX hh hhX hT hS hsup u
          (le_trans hc (le_of_lt hu.1)) (le_trans hu.2 hd)
      · simp only [Set.indicator_of_notMem hu, Pi.zero_apply, le_refl]
  have hconst : (∫ u : ℝ, (Set.Ioc c d).indicator (fun _ : ℝ => C) u) = C * (d - c) := by
    rw [MeasureTheory.integral_indicator measurableSet_Ioc, MeasureTheory.setIntegral_const,
      smul_eq_mul]
    change (volume (Set.Ioc c d)).toReal * C = C * (d - c)
    rw [Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]
    ring
  rw [hconst] at hcmp
  have hid : ∫ u in Set.Ioc c d, (∫ t in (-T)..T, ‖dirP a X t * Phi t u‖^2)
      = ∫ u : ℝ, (Set.Ioc c d).indicator (fun u => ∫ t in (-T)..T, ‖dirP a X t * Phi t u‖^2) u :=
    (MeasureTheory.integral_indicator measurableSet_Ioc).symm
  rw [hid]
  refine le_trans hcmp ?_
  rw [hC]
  ring_nf
  exact le_rfl

/-! ## The frozen bound on the positive window `[X,d]` -/

lemma mp_frozen_window (a : ℕ → ℂ) (X T d : ℝ) (hX : 1 ≤ X) (hT : 0 ≤ T) (hXd : X ≤ d)
    (hd : d ≤ 3*X) :
    ∀ u : ℝ, (∫ x in X..d, ‖∫ t in (-T)..T,
          (dirP a X t * Phi t u) * (x : ℂ) ^ (2 + Complex.I * (t : ℂ))‖^2)
        ≤ (mpC0 * Real.pi) * X^5 * (∫ t in (-T)..T, ‖dirP a X t * Phi t u‖^2) := by
  intro u
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hxe : X * Real.exp (-1) ≤ X := by
    have h1 : Real.exp (-1) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    nlinarith
  have hxe2 : 3 * X ≤ X * Real.exp 3 := by
    have h1 : (3:ℝ) ≤ Real.exp 3 := by
      have h2 : (2:ℝ) < Real.exp 1 := Real.exp_one_gt_two
      have h3 : Real.exp 3 = (Real.exp 1)^3 := by
        rw [show (3:ℝ) = ((3:ℕ) : ℝ) * 1 by norm_num, Real.exp_nat_mul]
      have h4 : (3:ℝ) ≤ (Real.exp 1)^3 := by
        have h5 : (2:ℝ) ≤ Real.exp 1 := le_of_lt h2
        have h6 : (2:ℝ)^3 ≤ (Real.exp 1)^3 := pow_le_pow_left₀ (by norm_num) h5 3
        have h7 : (8:ℝ) ≤ (2:ℝ)^3 := by norm_num
        linarith
      rw [h3]; exact h4
    nlinarith
  have htrans : ∀ Δ : ℝ, ‖∫ x in X * Real.exp (-1)..X * Real.exp 3,
      (mwt X x : ℂ) * (x : ℂ) ^ (4 + Complex.I * (Δ : ℂ))‖ ≤ mpC0 * X^5/(1+Δ^2) := by
    intro Δ
    simpa [mpC0] using mwt_transform_bound X Δ hXpos
  have hcont : Continuous (fun t : ℝ => dirP a X t * Phi t u) :=
    (continuous_dirP a X).mul (mp_continuous_Phi_u u)
  have hfr := frozen_l2_bound_proof X T mpC0 mpC0_pos hX hT htrans
    (fun t : ℝ => dirP a X t * Phi t u) hcont
  have hFcont : Continuous (fun x : ℝ => ‖∫ t in (-T)..T,
      (dirP a X t * Phi t u) * (x : ℂ) ^ (2 + Complex.I * (t : ℂ))‖^2) :=
    (mp_continuous_frozen_int a X T u).norm.pow 2
  have huicc : Set.uIcc (X * Real.exp (-1)) (X * Real.exp 3)
      = Set.Icc (X * Real.exp (-1)) (X * Real.exp 3) :=
    Set.uIcc_of_le (by
      have h1 : Real.exp (-1) ≤ Real.exp 3 := Real.exp_le_exp.mpr (by norm_num)
      nlinarith [hXpos.le])
  have hmwtct : ContinuousOn (fun x : ℝ => mwt X x)
      (Set.uIcc (X * Real.exp (-1)) (X * Real.exp 3)) := by
    rw [huicc]
    exact (mp_continuous_mwt_of_pos hXpos).mono (fun x hx => by
      have h0 : X * Real.exp (-1) > 0 := by positivity
      exact lt_of_lt_of_le h0 hx.1)
  have hprod : ContinuousOn (fun x : ℝ => mwt X x * ‖∫ t in (-T)..T,
      (dirP a X t * Phi t u) * (x : ℂ) ^ (2 + Complex.I * (t : ℂ))‖^2)
      (Set.uIcc (X * Real.exp (-1)) (X * Real.exp 3)) :=
    ContinuousOn.mul hmwtct (Continuous.continuousOn hFcont)
  have hint : IntervalIntegrable (fun x : ℝ => mwt X x * ‖∫ t in (-T)..T,
      (dirP a X t * Phi t u) * (x : ℂ) ^ (2 + Complex.I * (t : ℂ))‖^2) volume
      (X * Real.exp (-1)) (X * Real.exp 3) :=
    hprod.intervalIntegrable
  have heq : (∫ x in X..d, ‖∫ t in (-T)..T,
        (dirP a X t * Phi t u) * (x : ℂ) ^ (2 + Complex.I * (t : ℂ))‖^2)
      = ∫ x in X..d, mwt X x * ‖∫ t in (-T)..T,
        (dirP a X t * Phi t u) * (x : ℂ) ^ (2 + Complex.I * (t : ℂ))‖^2 :=
    intervalIntegral.integral_congr (fun x hx => by
      have hx' : X ≤ x ∧ x ≤ d := by simpa [Set.uIcc_of_le hXd] using hx
      rw [mwt_eq_one hXpos hx'.1 (by linarith)]
      ring)
  have hmono : (∫ x in X..d, mwt X x * ‖∫ t in (-T)..T,
        (dirP a X t * Phi t u) * (x : ℂ) ^ (2 + Complex.I * (t : ℂ))‖^2)
      ≤ ∫ x in X * Real.exp (-1)..X * Real.exp 3, mwt X x * ‖∫ t in (-T)..T,
        (dirP a X t * Phi t u) * (x : ℂ) ^ (2 + Complex.I * (t : ℂ))‖^2 :=
    intervalIntegral.integral_mono_interval hxe hXd (le_trans hd hxe2)
      (by filter_upwards with x; exact mul_nonneg (mwt_nonneg X x) (by positivity)) hint
  have hfin : (∫ x in X * Real.exp (-1)..X * Real.exp 3, mwt X x * ‖∫ t in (-T)..T,
        (dirP a X t * Phi t u) * (x : ℂ) ^ (2 + Complex.I * (t : ℂ))‖^2)
      ≤ (mpC0 * Real.pi) * X^5 * (∫ t in (-T)..T, ‖dirP a X t * Phi t u‖^2) := by
    have h1 := mul_le_mul_of_nonneg_left hfr hXpos.le
    have h2 : X * ((1/X) * (∫ x in X * Real.exp (-1)..X * Real.exp 3,
        mwt X x * ‖∫ t in (-T)..T,
          (dirP a X t * Phi t u) * (x : ℂ) ^ (2 + Complex.I * (t : ℂ))‖^2))
        = ∫ x in X * Real.exp (-1)..X * Real.exp 3,
          mwt X x * ‖∫ t in (-T)..T,
            (dirP a X t * Phi t u) * (x : ℂ) ^ (2 + Complex.I * (t : ℂ))‖^2 := by
      field_simp
    rw [h2] at h1
    have h3 : X * (mpC0 * Real.pi * X^4 * (∫ t in (-T)..T, ‖dirP a X t * Phi t u‖^2))
        = (mpC0 * Real.pi) * X^5 * (∫ t in (-T)..T, ‖dirP a X t * Phi t u‖^2) := by ring
    rwa [h3] at h1
  rw [heq]
  exact le_trans hmono hfin

/-! ## The main theorem -/

theorem mr_parseval_direct :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℕ → ℂ), (∀ n, ‖a n‖ ≤ 1) →
      ∀ (Y H : ℝ), 4 ≤ Y → 1 ≤ H → H ≤ Y →
        1 / Y * (∫ y in Y..(2*Y), ‖(1/H) * ∑ n ∈ Work.BMF.natIcc y (y+H), a n‖^2)
          ≤ C * (‖(1/Y) * ∑ n ∈ Work.BMF.natIcc Y (2*Y), a n‖^2
              + (Real.log Y)^(-(2/15:ℝ))
              + (∫ t in -(Y/H)..(Y/H), ‖∑ n ∈ Work.BMF.natIcc Y (3*Y), a n * (n:ℂ)^(-(1+Complex.I*t))‖^2)
              + ⨆ (T : {T : ℝ // Y/H ≤ T}),
                  (Y/H)/T * ∫ t in -(2*T)..(2*T), ‖∑ n ∈ Work.BMF.natIcc Y (3*Y), a n * (n:ℂ)^(-(1+Complex.I*t))‖^2) := by
  refine ⟨10^16, by norm_num, ?_⟩
  intro a ha Y H hY hH hHY
  have hY1 : 1 ≤ Y := by linarith
  have hYpos : 0 < Y := by linarith
  have hHpos : 0 < H := by linarith
  have hRpos : 0 < Y/H := div_pos hYpos hHpos
  have hRnn : 0 ≤ Y/H := le_of_lt hRpos
  -- the supremum S
  have hbdd := bddAbove_dirP_sup a ha Y (Y/H) hY1 hRpos
  have hSnn := dirP_sup_nonneg a ha Y (Y/H) hY1 hRpos
  set I : ℝ := ∫ t in (-(Y/H))..(Y/H), ‖dirP a Y t‖^2 with hIdef
  set S : ℝ := ⨆ (T : {T : ℝ // Y/H ≤ T}),
      (Y/H)/T * (∫ t in (-(2*T.1))..(2*T.1), ‖dirP a Y t‖^2) with hSdef
  have hInn : 0 ≤ I := by
    rw [hIdef]
    exact intervalIntegral.integral_nonneg (by
      have hp : 0 < Y/H := div_pos hYpos hHpos
      linarith) (fun t _ => by positivity)
  have hSnn' : 0 ≤ S := by rw [hSdef]; exact hSnn
  have hsup : ∀ T' : ℝ, Y/H ≤ T' → (Y/H)/T' * (∫ t in (-(2*T'))..(2*T'), ‖dirP a Y t‖^2) ≤ S :=
    fun T' hT' => hSdef ▸ le_ciSup hbdd ⟨T', hT'⟩
  -- the Perron reduction
  have hred := perron_reduction_single a ha Y H hY1 hH hHY
  -- uniform bound for the truncated Perron integral
  set k : ℝ := (mpC0 * Real.pi) * Y^5 with hkdef
  have hknn : 0 ≤ k := by
    rw [hkdef]
    have h1 := mpC0_pos; have h2 := Real.pi_pos; positivity
  have hAI : (0:ℝ) ≤ I + 128*S := add_nonneg hInn (by linarith)
  have hstep : (⨆ (T : {T : ℝ // 1 ≤ T}),
      (1/Y) * (∫ x in Y..(2*Y), ‖perronP a Y H T.1 x‖^2)) ≤ 10^16 * (I + S) := by
    refine ciSup_le (fun T => ?_)
    have hT1 : 1 ≤ T.1 := T.2
    have hT0 : 0 ≤ T.1 := le_trans zero_le_one hT1
    have hPV := perronP_l2_via_parts a Y H T.1 hY1 hH hHY hT1
    have hfr2 := mp_frozen_window a Y T.1 (2*Y) hY1 hT0 (by linarith) (by linarith)
    have hfr3 := mp_frozen_window a Y T.1 (3*Y) hY1 hT0 (by linarith) (by linarith)
    have hC0nn : (0:ℝ) ≤ mpC0 * Real.pi := le_of_lt (mul_pos mpC0_pos Real.pi_pos)
    have hJ1 := window_J1_bound a Y H T.1 (mpC0 * Real.pi) hYpos hHpos hHY hT0 hC0nn hfr2
    have hJ2 := window_J2_bound a Y H T.1 (mpC0 * Real.pi) hYpos hHpos hHY hT0 hC0nn hfr3
    have hc1 : (0:ℝ) ≤ H/(2*Y) := div_nonneg hHpos.le (by positivity)
    have hd1 : 3*H/Y ≤ 3*H/Y := le_rfl
    have hcd1 : H/(2*Y) ≤ 3*H/Y := by
      rw [div_le_div_iff₀ (by positivity : (0:ℝ) < 2*Y) hYpos]
      nlinarith [mul_pos hHpos hYpos]
    have hc2 : (0:ℝ) ≤ 0 := le_refl 0
    have hd2 : 2*H/Y ≤ 3*H/Y := by rw [div_le_div_iff_of_pos_right hYpos]; linarith
    have hcd2 : (0:ℝ) ≤ 2*H/Y := div_nonneg (by positivity) (by positivity)
    have hm1 := mp_dirP_Phi_mass_int a ha Y H T.1 S (H/(2*Y)) (3*H/Y) hY1 hHpos hHY hT0
      hSnn' hsup hc1 hd1 hcd1
    have hm2 := mp_dirP_Phi_mass_int a ha Y H T.1 S (0:ℝ) (2*H/Y) hY1 hHpos hHY hT0
      hSnn' hsup hc2 hd2 hcd2
    -- the two window bounds with the weight `k` made explicit
    have hJ1b : (∫ u in (H/(2*Y))..(3*H/Y),
          k * (∫ t in (-T.1)..T.1, ‖dirP a Y t * Phi t u‖^2))
        ≤ k * ((3*H/Y - H/(2*Y)) * (6400 * (H/Y)^2 * (I + 128*S))) := by
      rw [intervalIntegral.integral_const_mul]
      exact mul_le_mul_of_nonneg_left hm1 hknn
    have hJ2b : (∫ u in (0:ℝ)..(2*H/Y),
          k * (∫ t in (-T.1)..T.1, ‖dirP a Y t * Phi t u‖^2))
        ≤ k * ((2*H/Y) * (6400 * (H/Y)^2 * (I + 128*S))) := by
      rw [intervalIntegral.integral_const_mul]
      refine le_trans (mul_le_mul_of_nonneg_left hm2 hknn) (le_of_eq (by ring))
    have hA1 : (0:ℝ) ≤ 2*H/Y := div_nonneg (by positivity) (by positivity)
    -- the two pieces of the `x`-integral
    have hJ1d : (1/Y) * (∫ x in Y..(2*Y), ‖∫ t in (-T.1)..T.1, dirP a Y t
          * ((x:ℂ)^(2 + Complex.I*(t:ℂ))) * (∫ u in (H/x)..(3*H/x), Phi t u)‖^2)
        ≤ (32000 * mpC0 * Real.pi) * (H^4 * (I + 128*S)) := by
      have h1 : (1/Y) * (∫ x in Y..(2*Y), ‖∫ t in (-T.1)..T.1, dirP a Y t
            * ((x:ℂ)^(2 + Complex.I*(t:ℂ))) * (∫ u in (H/x)..(3*H/x), Phi t u)‖^2)
          ≤ (1/Y) * ((2*H/Y) * (k * ((3*H/Y - H/(2*Y)) * (6400 * (H/Y)^2 * (I + 128*S))))) :=
        mul_le_mul_of_nonneg_left (le_trans hJ1 (by rw [hkdef]; exact mul_le_mul_of_nonneg_left hJ1b hA1))
          (by positivity)
      refine le_trans h1 ?_
      have e1 : (1/Y) * ((2*H/Y) * ((mpC0 * Real.pi) * Y^5 * ((3*H/Y - H/(2*Y))
            * (6400 * (H/Y)^2 * (I + 128*S)))))
          = (32000 * mpC0 * Real.pi) * (H^4 * (I + 128*S)) := by
        field_simp
        ring
      rw [hkdef, e1]
    have hJ2d : (1/Y) * (∫ x in Y..(2*Y), ‖∫ t in (-T.1)..T.1, dirP a Y t
          * (((x+H):ℂ)^(2 + Complex.I*(t:ℂ))) * (∫ u in (0:ℝ)..(2*H/(x+H)), Phi t u)‖^2)
        ≤ (25600 * mpC0 * Real.pi) * (H^4 * (I + 128*S)) := by
      have h1 : (1/Y) * (∫ x in Y..(2*Y), ‖∫ t in (-T.1)..T.1, dirP a Y t
            * (((x+H):ℂ)^(2 + Complex.I*(t:ℂ))) * (∫ u in (0:ℝ)..(2*H/(x+H)), Phi t u)‖^2)
          ≤ (1/Y) * ((2*H/Y) * (k * ((2*H/Y) * (6400 * (H/Y)^2 * (I + 128*S))))) :=
        mul_le_mul_of_nonneg_left (le_trans hJ2 (by rw [hkdef]; exact mul_le_mul_of_nonneg_left hJ2b hA1))
          (by positivity)
      refine le_trans h1 ?_
      have e1 : (1/Y) * ((2*H/Y) * ((mpC0 * Real.pi) * Y^5 * ((2*H/Y)
            * (6400 * (H/Y)^2 * (I + 128*S)))))
          = (25600 * mpC0 * Real.pi) * (H^4 * (I + 128*S)) := by
        field_simp
        ring
      rw [hkdef, e1]
    -- assemble
    refine le_trans hPV ?_
    have hsum : (1/(8*Real.pi^2*H^4)) *
          ((1/Y) * (∫ x in Y..(2*Y), ‖∫ t in (-T.1)..T.1, dirP a Y t
              * ((x:ℂ)^(2 + Complex.I*(t:ℂ))) * (∫ u in (H/x)..(3*H/x), Phi t u)‖^2)
         + (1/Y) * (∫ x in Y..(2*Y), ‖∫ t in (-T.1)..T.1, dirP a Y t
              * (((x+H):ℂ)^(2 + Complex.I*(t:ℂ))) * (∫ u in (0:ℝ)..(2*H/(x+H)), Phi t u)‖^2))
        ≤ (1/(8*Real.pi^2*H^4)) *
          ((32000 * mpC0 * Real.pi) * (H^4 * (I + 128*S))
            + (25600 * mpC0 * Real.pi) * (H^4 * (I + 128*S))) :=
      mul_le_mul_of_nonneg_left (add_le_add hJ1d hJ2d) (by positivity)
    refine le_trans hsum ?_
    have h4 : (0:ℝ) ≤ H^4 * (I + 128*S) := mul_nonneg (by positivity) hAI
    have h32000 : (0:ℝ) ≤ 32000 * mpC0 * Real.pi := by
      have := mpC0_pos; have := Real.pi_pos; positivity
    have h25600 : (0:ℝ) ≤ 25600 * mpC0 * Real.pi := by
      have := mpC0_pos; have := Real.pi_pos; positivity
    have hval : (1/(8*Real.pi^2*H^4)) *
          ((32000 * mpC0 * Real.pi) * (H^4 * (I + 128*S))
            + (25600 * mpC0 * Real.pi) * (H^4 * (I + 128*S)))
        = (7200 * mpC0 / Real.pi) * (I + 128*S) := by
      field_simp
      ring
    rw [hval]
    have h128 : I + 128*S ≤ 128 * (I + S) := by linarith [hInn, hSnn']
    have hb : 7200 * mpC0 / Real.pi ≤ 7200 * (4*10^9) / 3 := by
      rw [div_le_div_iff₀ Real.pi_pos (by norm_num : (0:ℝ) < 3)]
      nlinarith [mpC0_le, Real.pi_gt_three, Real.pi_pos]
    calc (7200 * mpC0 / Real.pi) * (I + 128*S)
        ≤ (7200 * (4*10^9) / 3) * (128 * (I + S)) :=
          mul_le_mul hb h128 hAI (by positivity)
      _ ≤ 10^16 * (I + S) := by nlinarith [hInn, hSnn']
  -- final comparison with the target's bracket
  have hmain : 1 / Y * (∫ y in Y..(2*Y), ‖(1/H) * ∑ n ∈ Work.BMF.natIcc y (y+H), a n‖^2)
      ≤ 10^16 * (‖(1/Y) * ∑ n ∈ Work.BMF.natIcc Y (2*Y), a n‖^2
            + (Real.log Y)^(-(2/15:ℝ))
            + (∫ t in -(Y/H)..(Y/H), ‖∑ n ∈ Work.BMF.natIcc Y (3*Y),
                a n * (n:ℂ)^(-(1+Complex.I*t))‖^2)
            + ⨆ (T : {T : ℝ // Y/H ≤ T}), (Y/H)/T * ∫ t in -(2*T)..(2*T),
                ‖∑ n ∈ Work.BMF.natIcc Y (3*Y), a n * (n:ℂ)^(-(1+Complex.I*t))‖^2) := by
    have h1 : 1 / Y * (∫ y in Y..(2*Y), ‖(1/H) * ∑ n ∈ Work.BMF.natIcc y (y+H), a n‖^2)
        ≤ 10^16 * (I + S) :=
      le_trans (le_trans hred hstep) (le_refl _)
    refine le_trans h1 ?_
    have hdir : I = (∫ t in -(Y/H)..(Y/H), ‖∑ n ∈ Work.BMF.natIcc Y (3*Y),
        a n * (n:ℂ)^(-(1+Complex.I*t))‖^2) := rfl
    have hsup2 : S = (⨆ (T : {T : ℝ // Y/H ≤ T}), (Y/H)/T * ∫ t in -(2*T)..(2*T),
        ‖∑ n ∈ Work.BMF.natIcc Y (3*Y), a n * (n:ℂ)^(-(1+Complex.I*t))‖^2) := rfl
    have hlog : 0 ≤ (Real.log Y)^(-(2/15:ℝ)) :=
      Real.rpow_nonneg (Real.log_nonneg hY1) _
    have hm : 0 ≤ ‖(1/Y) * ∑ n ∈ Work.BMF.natIcc Y (2*Y), a n‖^2 := by positivity
    rw [hdir, hsup2]
    nlinarith [hInn, hSnn', hlog, hm]
  exact hmain

end

end Work.BMF
