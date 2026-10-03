import Mathlib
import Submission.Work.A3.OscPhase
import Submission.Work.A3.exists_band_split_mono
import Submission.Commons.Analysis.ExponentialSums.second_derivative_test

set_option autoImplicit false

namespace Work.A3

open MeasureTheory Set
open scoped Interval

noncomputable section

/-! # The van der Corput first-derivative test with a level set

For `f : ℝ → ℝ` that is `C²` on `[a,b]` with `f'' ≥ 0` there and `a ≤ b`, `m > 0`:

  `‖∫_a^b e^{-2πi f(x)} dx‖ ≤ |{t ∈ [a,b] : |f'(t)| ≤ m}| + 16/m`.

The monotone function `f'` splits `[a,b]` into a left band where `f' ≤ -m`, a middle
band where `|f'| ≤ m`, and a right band where `f' ≥ m`.  On each outer band the
first-derivative test `exp_integral_first_deriv_le` gives `8/m`; the middle band is
bounded by its length, which is at most the measure of the level set.
-/

/-- **Monotonicity of the one-sided derivative.**  If `f` is `C²` on `[a,b]` and
`f'' ≥ 0` on the interior, then `derivWithin f [a,b]` is monotone on `[a,b]`
(the interval is convex and its interior is `(a,b)`). -/
lemma oscInt_monotoneOn_derivWithin {a b : ℝ} (f : ℝ → ℝ)
    (hf : ContDiffOn ℝ 2 f (Set.Icc a b))
    (hpp : ∀ x : ℝ, x ∈ Set.Ioo a b → 0 ≤ deriv (deriv f) x) :
    MonotoneOn (fun x : ℝ => derivWithin f (Set.Icc a b) x) (Set.Icc a b) := by
  have hd2 : (2 : WithTop ℕ∞) ≠ 0 := by norm_num
  have hdiff : DifferentiableOn ℝ f (interior (Set.Icc a b)) :=
    (hf.differentiableOn hd2).mono interior_subset
  have hdiff' : DifferentiableOn ℝ (deriv f) (interior (Set.Icc a b)) := by
    intro x hx
    rw [interior_Icc] at hx
    exact (Submission.SdtOscB.differentiableAt_deriv_F_of_Ioo f hf hx).differentiableWithinAt
  have h2 : ∀ x ∈ interior (Set.Icc a b), 0 ≤ (deriv^[2]) f x := by
    intro x hx
    rw [interior_Icc] at hx
    have hval : (deriv^[2]) f x = deriv (deriv f) x := rfl
    rw [hval]
    exact hpp x hx
  have hconv : ConvexOn ℝ (Set.Icc a b) f :=
    convexOn_of_deriv2_nonneg (convex_Icc a b) hf.continuousOn hdiff hdiff' h2
  exact hconv.monotoneOn_derivWithin (hf.differentiableOn hd2)

/-- **Norm transfer.**  On an interval, the norm of the oscillatory integral of
`oscPhase f = e^{-2πi f}` equals that of `ephase f = e^{2πi f}` (the two phases are
complex conjugates of each other). -/
lemma oscInt_norm_integral_eq_ephase {f : ℝ → ℝ} {c d : ℝ}
    (hf : ContinuousOn f (Set.uIcc c d)) :
    ‖∫ x in c..d, oscPhase f x‖ = ‖∫ x in c..d, Submission.SdtOscB.ephase f x‖ := by
  have hcont : ContinuousOn (Submission.SdtOscB.ephase f) (Set.uIcc c d) := by
    have hrepr : Submission.SdtOscB.ephase f
        = fun x => Complex.exp ((((2 * Real.pi : ℝ) : ℂ) * Complex.I) * (f x : ℂ)) := by
      funext x; rw [Submission.SdtOscB.ephase]; congr 1; push_cast; ring
    rw [hrepr]
    have hfC : ContinuousOn (fun x : ℝ => (f x : ℂ)) (Set.uIcc c d) :=
      Complex.continuous_ofReal.comp_continuousOn hf
    have h1 : ContinuousOn (fun x : ℝ => (((2 * Real.pi : ℝ) : ℂ) * Complex.I) * (f x : ℂ))
        (Set.uIcc c d) := hfC.const_mul _
    exact Complex.continuous_exp.comp_continuousOn h1
  have hpoint : ∀ x : ℝ, oscPhase f x = (starRingEnd ℂ) (Submission.SdtOscB.ephase f x) := by
    intro x
    rw [Submission.SdtOscB.ephase, oscPhase, ← Complex.exp_conj]
    congr 1
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
    push_cast
    ring
  calc ‖∫ x in c..d, oscPhase f x‖
      = ‖∫ x in c..d, (starRingEnd ℂ) (Submission.SdtOscB.ephase f x)‖ := by
        rw [intervalIntegral.integral_congr (fun x _ => hpoint x)]
    _ = ‖(starRingEnd ℂ) (∫ x in c..d, Submission.SdtOscB.ephase f x)‖ := by
        rw [intervalIntegral_star (fun x => Submission.SdtOscB.ephase f x) c d
          hcont.intervalIntegrable]
    _ = ‖∫ x in c..d, Submission.SdtOscB.ephase f x‖ := by
        rw [starRingEnd_apply, norm_star]

/-- **The middle band is inside the level set.**  If `a ≤ p ≤ q ≤ b` and
`|f'| ≤ m` on `(p,q)`, then the length of `[p,q]` is at most the (Lebesgue) measure
of the level set `{t ∈ [a,b] : |f'(t)| ≤ m}`. -/
lemma oscInt_le_volume_levelSet {f : ℝ → ℝ} {a b m p q : ℝ} (hpq : p ≤ q)
    (hp : a ≤ p) (hq : q ≤ b) (hmid : ∀ x : ℝ, x ∈ Set.Ioo p q → |deriv f x| ≤ m) :
    q - p ≤ (MeasureTheory.volume {t ∈ Set.Icc a b | |deriv f t| ≤ m}).toReal := by
  have hsub : Set.Ioo p q ⊆ {t ∈ Set.Icc a b | |deriv f t| ≤ m} := by
    intro x hx
    exact ⟨⟨le_trans hp (le_of_lt hx.1), le_trans (le_of_lt hx.2) hq⟩, hmid x hx⟩
  have hvol : ENNReal.ofReal (q - p)
      ≤ MeasureTheory.volume {t ∈ Set.Icc a b | |deriv f t| ≤ m} := by
    rw [← Real.volume_Ioo]
    exact MeasureTheory.measure_mono hsub
  have hfin : MeasureTheory.volume {t ∈ Set.Icc a b | |deriv f t| ≤ m} ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (MeasureTheory.measure_mono
      (fun t ht => ht.1 : _ ⊆ Set.Icc a b))
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  calc q - p = (ENNReal.ofReal (q - p)).toReal :=
        (ENNReal.toReal_ofReal (sub_nonneg.mpr hpq)).symm
    _ ≤ (MeasureTheory.volume {t ∈ Set.Icc a b | |deriv f t| ≤ m}).toReal :=
        ENNReal.toReal_mono hfin hvol

/-- **van der Corput first-derivative test with level set.** -/
lemma oscInt_levelSet_le (f : ℝ → ℝ) {a b m : ℝ} (hab : a ≤ b) (hm : 0 < m)
    (hf : ContDiffOn ℝ 2 f (Set.Icc a b))
    (hpp : ∀ x : ℝ, x ∈ Set.Ioo a b → 0 ≤ deriv (deriv f) x) :
    ‖∫ x in a..b, Work.A3.oscPhase f x‖
      ≤ (MeasureTheory.volume {t ∈ Set.Icc a b | |deriv f t| ≤ m}).toReal + 16 / m := by
  by_cases hab' : a = b
  · subst hab'
    rw [intervalIntegral.integral_same, norm_zero]
    have h1 : (0 : ℝ) ≤ (MeasureTheory.volume {t ∈ Set.Icc a a | |deriv f t| ≤ m}).toReal :=
      ENNReal.toReal_nonneg
    have h2 : (0 : ℝ) ≤ 16 / m := div_nonneg (by norm_num) hm.le
    linarith
  · have hablt : a < b := lt_of_le_of_ne hab hab'
    have hgcont : ContinuousOn (fun x : ℝ => derivWithin f (Set.Icc a b) x) (Set.Icc a b) :=
      (Submission.SdtOscB.contDiffOn_derivWithin_one hablt f hf).continuousOn
    have hgmono : MonotoneOn (fun x : ℝ => derivWithin f (Set.Icc a b) x) (Set.Icc a b) :=
      oscInt_monotoneOn_derivWithin f hf hpp
    obtain ⟨p, q, hap, hpq, hqb, hleft, hright, hmid⟩ :=
      exists_band_split_mono hab hm (fun x : ℝ => derivWithin f (Set.Icc a b) x)
        hgcont hgmono
    have hpb : p ≤ b := le_trans hpq hqb
    have haq : a ≤ q := le_trans hap hpq
    have hleft' : ∀ x : ℝ, x ∈ Set.Ioo a p → deriv f x ≤ -m := by
      intro x hx
      have hxab : x ∈ Set.Ioo a b := ⟨hx.1, lt_of_lt_of_le hx.2 hpb⟩
      have h := hleft x hx
      rwa [Submission.SdtOscB.derivWithin_eq_deriv_of_Ioo f hxab] at h
    have hright' : ∀ x : ℝ, x ∈ Set.Ioo q b → m ≤ deriv f x := by
      intro x hx
      have hxab : x ∈ Set.Ioo a b := ⟨lt_of_le_of_lt haq hx.1, hx.2⟩
      have h := hright x hx
      rwa [Submission.SdtOscB.derivWithin_eq_deriv_of_Ioo f hxab] at h
    have hmid' : ∀ x : ℝ, x ∈ Set.Ioo p q → |deriv f x| ≤ m := by
      intro x hx
      have hxab : x ∈ Set.Ioo a b := ⟨lt_of_le_of_lt hap hx.1, lt_of_lt_of_le hx.2 hqb⟩
      have h := hmid x hx
      rwa [Submission.SdtOscB.derivWithin_eq_deriv_of_Ioo f hxab] at h
    have hosc : ContinuousOn (oscPhase f) (Set.Icc a b) := by
      have hrepr : oscPhase f
          = fun x => Complex.exp ((((-2 * Real.pi : ℝ) : ℂ) * Complex.I) * (f x : ℂ)) := by
        funext x; rw [oscPhase]; congr 1; push_cast; ring
      rw [hrepr]
      have hfC : ContinuousOn (fun x : ℝ => (f x : ℂ)) (Set.Icc a b) :=
        Complex.continuous_ofReal.comp_continuousOn hf.continuousOn
      have h1 : ContinuousOn (fun x : ℝ => (((-2 * Real.pi : ℝ) : ℂ) * Complex.I) * (f x : ℂ))
          (Set.Icc a b) := hfC.const_mul _
      exact Complex.continuous_exp.comp_continuousOn h1
    have hint : ∀ (x y : ℝ), a ≤ x → x ≤ y → y ≤ b →
        IntervalIntegrable (oscPhase f) volume x y := by
      intro x y hax hxy hyb
      refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le hxy]
      exact hosc.mono (Set.Icc_subset_Icc hax hyb)
    have hin_ap : IntervalIntegrable (oscPhase f) volume a p := hint a p le_rfl hap hpb
    have hin_pq : IntervalIntegrable (oscPhase f) volume p q := hint p q hap hpq hqb
    have hin_aq : IntervalIntegrable (oscPhase f) volume a q := hint a q le_rfl haq hqb
    have hin_qb : IntervalIntegrable (oscPhase f) volume q b := hint q b haq hqb le_rfl
    have hI1 : ‖∫ x in a..p, oscPhase f x‖ ≤ 8 / m := by
      rcases eq_or_lt_of_le hap with hpaeq | hpalt
      · rw [← hpaeq, intervalIntegral.integral_same, norm_zero]
        exact div_nonneg (by norm_num) hm.le
      · have hsl : ∀ x : ℝ, x ∈ Set.Ioo a p → m ≤ |deriv f x| := by
          intro x hx
          have h := hleft' x hx
          rw [abs_of_nonpos (by linarith)]
          linarith
        have hF : ContDiffOn ℝ 2 f (Set.Icc a p) := hf.mono (Set.Icc_subset_Icc le_rfl hpb)
        have hbd := Submission.SdtOscB.exp_integral_first_deriv_le hpalt f hm hF hsl
          (fun x hx => hpp x ⟨hx.1, lt_of_lt_of_le hx.2 hpb⟩)
        have heq : ‖∫ x in a..p, oscPhase f x‖ =
            ‖∫ x in a..p, Submission.SdtOscB.ephase f x‖ :=
          oscInt_norm_integral_eq_ephase (by
            rw [Set.uIcc_of_le hap]
            exact hf.continuousOn.mono (Set.Icc_subset_Icc le_rfl hpb))
        rw [heq]; exact hbd
    have hI2 : ‖∫ x in p..q, oscPhase f x‖ ≤ q - p := by
      have h := intervalIntegral.norm_integral_le_of_norm_le_const
        (f := fun x : ℝ => oscPhase f x) (a := p) (b := q) (C := 1)
        (fun x _ => (oscPhase_norm f x).le)
      rwa [one_mul, abs_of_nonneg (sub_nonneg.mpr hpq)] at h
    have hI3 : ‖∫ x in q..b, oscPhase f x‖ ≤ 8 / m := by
      rcases eq_or_lt_of_le hqb with hqbeq | hqblt
      · rw [hqbeq, intervalIntegral.integral_same, norm_zero]
        exact div_nonneg (by norm_num) hm.le
      · have hsl : ∀ x : ℝ, x ∈ Set.Ioo q b → m ≤ |deriv f x| := by
          intro x hx
          have h := hright' x hx
          rw [abs_of_nonneg (le_trans hm.le h)]
          exact h
        have hF : ContDiffOn ℝ 2 f (Set.Icc q b) := hf.mono (Set.Icc_subset_Icc haq le_rfl)
        have hbd := Submission.SdtOscB.exp_integral_first_deriv_le hqblt f hm hF hsl
          (fun x hx => hpp x ⟨lt_of_le_of_lt haq hx.1, hx.2⟩)
        have heq : ‖∫ x in q..b, oscPhase f x‖ =
            ‖∫ x in q..b, Submission.SdtOscB.ephase f x‖ :=
          oscInt_norm_integral_eq_ephase (by
            rw [Set.uIcc_of_le hqb]
            exact hf.continuousOn.mono (Set.Icc_subset_Icc haq le_rfl))
        rw [heq]; exact hbd
    have hI4 : q - p ≤ (MeasureTheory.volume {t ∈ Set.Icc a b | |deriv f t| ≤ m}).toReal :=
      oscInt_le_volume_levelSet hpq hap hqb hmid'
    have hsum : (∫ x in a..b, oscPhase f x)
        = (∫ x in a..p, oscPhase f x) + (∫ x in p..q, oscPhase f x)
          + (∫ x in q..b, oscPhase f x) := by
      rw [← intervalIntegral.integral_add_adjacent_intervals hin_aq hin_qb,
          ← intervalIntegral.integral_add_adjacent_intervals hin_ap hin_pq]
    rw [hsum]
    calc ‖(∫ x in a..p, oscPhase f x) + (∫ x in p..q, oscPhase f x)
            + (∫ x in q..b, oscPhase f x)‖
        ≤ ‖(∫ x in a..p, oscPhase f x) + (∫ x in p..q, oscPhase f x)‖
            + ‖∫ x in q..b, oscPhase f x‖ := norm_add_le _ _
      _ ≤ ‖∫ x in a..p, oscPhase f x‖ + ‖∫ x in p..q, oscPhase f x‖
            + ‖∫ x in q..b, oscPhase f x‖ := by
          linarith [norm_add_le (∫ x in a..p, oscPhase f x) (∫ x in p..q, oscPhase f x)]
      _ ≤ 8 / m + (q - p) + 8 / m := by linarith [hI1, hI2, hI3]
      _ = (q - p) + 16 / m := by ring
      _ ≤ (MeasureTheory.volume {t ∈ Set.Icc a b | |deriv f t| ≤ m}).toReal + 16 / m := by
          linarith [hI4]

end

end Work.A3
