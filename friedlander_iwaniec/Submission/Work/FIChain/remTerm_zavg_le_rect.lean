import Mathlib
import Submission.Work.FIChain.s3RemPlus_maj_le_defs
import Submission.Work.FIChain.inner_Fsub_measurable

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIChain

open Finset MeasureTheory
open scoped BigOperators Interval

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## Elementary facts about the two integrands -/

/-- `s3RemSub` is a sum of absolute values, hence nonnegative. -/
lemma s3RemSub_nonneg (x Cm ℓ : ℕ) (sc v t : ℝ) : 0 ≤ s3RemSub x Cm ℓ sc v t := by
  unfold s3RemSub
  exact Finset.sum_nonneg (fun d _ => add_nonneg (abs_nonneg _) (abs_nonneg _))

/-- On the rectangle (where the `ℓ`-indicators hold and `v ≤ x`) the integrand `Fsub = τ(ℓ)²·s3RemSubF`
is `τ(ℓ)²` times the `w`-indicator times `s3RemSubF/(v·w)`. -/
lemma Fsub_div_eq_of_mem (x Cm : ℕ) (B : ℝ) (ℓ : ℕ) {v : ℝ}
    (hv1 : (ℓ : ℝ) * zc x B ≤ v) (hv2 : v ≤ (ℓ : ℝ) * (Real.exp 1 * zc x B))
    (hvx : v ≤ (x : ℝ)) (w : ℝ) :
    Fsub x Cm B ℓ v w / (v * w)
      = ((ℓ.divisors.card : ℝ)) ^ 2 *
        ((if (ℓ : ℝ) ≤ w then s3RemSubF x Cm x ℓ (sc x B) v w else 0) / (v * w)) := by
  unfold Fsub
  by_cases hw : (ℓ : ℝ) ≤ w
  · rw [if_pos ⟨hv1, hv2, hw, hvx⟩, if_pos hw]
    ring
  · rw [if_neg (fun h => hw h.2.2.1), if_neg hw]
    simp

/-! ## The pointwise comparison of the two inner `w`-integrals -/

/-- **The relaxation of one `ℓ`-slice of the substituted REM integral to the common rectangle.**

For `v` in the `ℓ`-th `v`-window `[ℓ·zc, ℓ·e·zc]` the `ℓ`-th substituted integral over
`[ℓ, min (s·v/Cm) (x/Cm)]` (of the raw `s3RemSub` majorant, killed for `v > x`) is at most the
integral of the corresponding slice of `Fsub` over the whole `w`-range `[1, x/Cm]`.

This is a pure relaxation: `s3RemSub` agrees with `s3RemSubF` on the range (because `w ≤ x ≤ x·ℓ`),
the `w`-range `[ℓ, min (…)]` sits inside `[1, x/Cm]` (because `1 ≤ ℓ` and `min ≤ x/Cm`), and on the
latter the `w`-indicator `ℓ ≤ w` is automatically satisfied.  If `min (…) < ℓ` the left integral is
over a reversed interval of a nonnegative function, hence `≤ 0 ≤` the right integral. -/
lemma rect_inner_le (x Cm : ℕ) (B : ℝ) (ℓ : ℕ) (hCm1 : 1 ≤ Cm) (hℓ1 : 1 ≤ ℓ)
    (hℓM : (ℓ : ℝ) ≤ ((⌊(x : ℝ) / (Cm : ℝ)⌋₊ : ℕ) : ℝ))
    (hzcp : 0 < zc x B) (hc1 : 1 ≤ (x : ℝ) / (Cm : ℝ))
    {v : ℝ} (hv : v ∈ Set.Ioc ((ℓ : ℝ) * zc x B) ((ℓ : ℝ) * (Real.exp 1 * zc x B))) :
    ((ℓ.divisors.card : ℝ)) ^ 2 *
        (∫ w in (ℓ : ℝ)..(min (sc x B * v / (Cm : ℝ)) ((x : ℝ) / (Cm : ℝ))),
          (if v ≤ (x : ℝ) then s3RemSub x Cm ℓ (sc x B) v w else 0) / (v * w))
      ≤ ∫ w in (1 : ℝ)..((x : ℝ) / (Cm : ℝ)), Fsub x Cm B ℓ v w / (v * w) := by
  have hCmp : (0 : ℝ) < (Cm : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hCm1)
  have hℓp : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hℓ1)
  have hℓ1R : (1 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hℓ1
  have hvpos : 0 < v := by nlinarith [hv.1, hℓp, hzcp]
  have hxnn : (0 : ℝ) ≤ (x : ℝ) := Nat.cast_nonneg x
  have hxcpos : (0 : ℝ) < (x : ℝ) / (Cm : ℝ) := lt_of_lt_of_le zero_lt_one hc1
  have hAnn : (0 : ℝ) ≤ AcountAtilC x := AcountAtilC_nonneg x
  set U : ℝ := min (sc x B * v / (Cm : ℝ)) ((x : ℝ) / (Cm : ℝ)) with hUdef
  have hUle : U ≤ (x : ℝ) / (Cm : ℝ) := min_le_right _ _
  set g : ℝ → ℝ :=
    fun w => (if (ℓ : ℝ) ≤ w then s3RemSubF x Cm x ℓ (sc x B) v w else 0) / (v * w) with hgdef
  have hgeq : ∀ w : ℝ,
      g w = (if (ℓ : ℝ) ≤ w then s3RemSubF x Cm x ℓ (sc x B) v w else 0) / (v * w) :=
    fun w => rfl
  have hgnn : ∀ w : ℝ, 0 < w → 0 ≤ g w := by
    intro w hw0
    rw [hgeq w]
    by_cases h : (ℓ : ℝ) ≤ w
    · rw [if_pos h]
      exact div_nonneg (s3RemSubF_nonneg x Cm x ℓ (sc x B) v w) (mul_pos hvpos hw0).le
    · rw [if_neg h]; simp
  by_cases hvx : v ≤ (x : ℝ)
  · -- main case: `v ≤ x`
    have hRHS : (∫ w in (1 : ℝ)..((x : ℝ) / (Cm : ℝ)), Fsub x Cm B ℓ v w / (v * w))
        = ((ℓ.divisors.card : ℝ)) ^ 2 * (∫ w in (1 : ℝ)..((x : ℝ) / (Cm : ℝ)), g w) := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr (fun w hw => ?_)
      rw [Set.uIcc_of_le hc1] at hw
      exact Fsub_div_eq_of_mem x Cm B ℓ (le_of_lt hv.1) hv.2 hvx w
    rw [hRHS]
    have hLHS : ((ℓ.divisors.card : ℝ)) ^ 2 *
          (∫ w in (ℓ : ℝ)..U,
            (if v ≤ (x : ℝ) then s3RemSub x Cm ℓ (sc x B) v w else 0) / (v * w))
        = ((ℓ.divisors.card : ℝ)) ^ 2 *
          (∫ w in (ℓ : ℝ)..U, s3RemSub x Cm ℓ (sc x B) v w / (v * w)) := by
      congr 1
      refine intervalIntegral.integral_congr (fun w _ => ?_)
      rw [if_pos hvx]
    rw [hLHS]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    by_cases hℓU : (ℓ : ℝ) ≤ U
    · -- `ℓ ≤ U`: the `w`-window sits inside `[1, x/Cm]`
      have hIntG : IntervalIntegrable g volume (1 : ℝ) ((x : ℝ) / (Cm : ℝ)) := by
        rw [show g = (fun w : ℝ =>
            (if (ℓ : ℝ) ≤ w then s3RemSubF x Cm x ℓ (sc x B) v w else 0) / (v * w)) from rfl]
        rw [intervalIntegrable_iff, Set.uIoc_of_le hc1]
        have hmeas : Measurable (fun w : ℝ =>
            (if (ℓ : ℝ) ≤ w then s3RemSubF x Cm x ℓ (sc x B) v w else 0) / (v * w)) := by
          refine Measurable.div ?_ (measurable_const.mul measurable_id)
          refine Measurable.ite measurableSet_Ici ?_ measurable_const
          exact (measurable_s3RemSubF x Cm x ℓ (sc x B)).comp
            (Measurable.prodMk measurable_const measurable_id)
        refine Measure.integrableOn_of_bounded (s_finite := (measure_Ioc_lt_top).ne)
          (f_mble := hmeas.aestronglyMeasurable) (M := (x : ℝ) * (4 * AcountAtilC x) / v) ?_
        apply ae_restrict_of_forall_mem measurableSet_Ioc
        intro w hw
        have hw0 : 0 < w := lt_of_lt_of_le zero_lt_one (le_of_lt hw.1)
        have hwle : w ≤ (x : ℝ) / (Cm : ℝ) := hw.2
        have hCw : (Cm : ℝ) * w ≤ (x : ℝ) := by
          calc (Cm : ℝ) * w ≤ (Cm : ℝ) * ((x : ℝ) / (Cm : ℝ)) :=
                mul_le_mul_of_nonneg_left hwle hCmp.le
            _ = (x : ℝ) := by field_simp
        have hF : |(if (ℓ : ℝ) ≤ w then s3RemSubF x Cm x ℓ (sc x B) v w else 0)|
            ≤ (x : ℝ) * (4 * AcountAtilC x) := by
          by_cases h : (ℓ : ℝ) ≤ w
          · rw [if_pos h]
            exact abs_s3RemSubF_le x Cm x ℓ (sc x B) v w hvx hCw
          · rw [if_neg h, abs_zero]
            exact mul_nonneg hxnn (by linarith)
        rw [Real.norm_eq_abs, abs_div, abs_of_pos (mul_pos hvpos hw0)]
        have h1 : |(if (ℓ : ℝ) ≤ w then s3RemSubF x Cm x ℓ (sc x B) v w else 0)| / (v * w)
            ≤ ((x : ℝ) * (4 * AcountAtilC x)) / (v * w) :=
          div_le_div_of_nonneg_right hF (mul_pos hvpos hw0).le
        have h2 : ((x : ℝ) * (4 * AcountAtilC x)) / (v * w)
            ≤ ((x : ℝ) * (4 * AcountAtilC x)) / v := by
          have hA : (0 : ℝ) ≤ (x : ℝ) * (4 * AcountAtilC x) :=
            mul_nonneg hxnn (by linarith)
          have hvle : v ≤ v * w := by
            calc v = v * 1 := (mul_one v).symm
              _ ≤ v * w := mul_le_mul_of_nonneg_left hw.1.le hvpos.le
          exact div_le_div_of_nonneg_left hA hvpos hvle
        linarith
      have hEq : (∫ w in (ℓ : ℝ)..U, s3RemSub x Cm ℓ (sc x B) v w / (v * w))
          = ∫ w in (ℓ : ℝ)..U, g w := by
        refine intervalIntegral.integral_congr (fun w hw => ?_)
        rw [Set.uIcc_of_le hℓU] at hw
        have hwU : w ≤ U := hw.2
        have hwℓ : (ℓ : ℝ) ≤ w := hw.1
        rw [hgeq w, if_pos hwℓ]
        have hwxl : w ≤ (x : ℝ) * (ℓ : ℝ) := by
          have h1 : w ≤ (x : ℝ) / (Cm : ℝ) := le_trans hwU hUle
          have h2 : (x : ℝ) / (Cm : ℝ) ≤ (x : ℝ) := by
            rw [div_le_iff₀ hCmp]
            calc (x : ℝ) = (x : ℝ) * 1 := (mul_one _).symm
              _ ≤ (x : ℝ) * (Cm : ℝ) :=
                  mul_le_mul_of_nonneg_left (by exact_mod_cast hCm1) hxnn
          have h3 : (x : ℝ) ≤ (x : ℝ) * (ℓ : ℝ) := by
            calc (x : ℝ) = (x : ℝ) * 1 := (mul_one _).symm
              _ ≤ (x : ℝ) * (ℓ : ℝ) := mul_le_mul_of_nonneg_left hℓ1R hxnn
          linarith
        rw [s3RemSub_eq_s3RemSubF x Cm x ℓ (sc x B) hℓ1 hwxl]
      have hmono : (∫ w in (ℓ : ℝ)..U, g w)
          ≤ ∫ w in (1 : ℝ)..((x : ℝ) / (Cm : ℝ)), g w :=
        intervalIntegral.integral_mono_interval hℓ1R hℓU hUle
          (ae_restrict_of_forall_mem measurableSet_Ioc
            (fun w hw => hgnn w (lt_of_lt_of_le zero_lt_one (le_of_lt hw.1))))
          hIntG
      linarith
    · -- `U < ℓ`: the left integral is over a reversed interval of a nonnegative function
      have hUℓ : U < (ℓ : ℝ) := lt_of_not_ge hℓU
      have hleft : (∫ w in (ℓ : ℝ)..U, s3RemSub x Cm ℓ (sc x B) v w / (v * w)) ≤ 0 := by
        rw [intervalIntegral.integral_symm]
        refine neg_nonpos.mpr ?_
        refine intervalIntegral.integral_nonneg hUℓ.le (fun w hw => ?_)
        have hUpos : 0 < U := lt_min (div_pos (mul_pos (sc_pos x B) hvpos) hCmp) hxcpos
        have hw0 : 0 < w := lt_of_lt_of_le hUpos hw.1
        exact div_nonneg (s3RemSub_nonneg x Cm ℓ (sc x B) v w) (mul_pos hvpos hw0).le
      have hright : 0 ≤ ∫ w in (1 : ℝ)..((x : ℝ) / (Cm : ℝ)), g w :=
        intervalIntegral.integral_nonneg hc1
          (fun w hw => hgnn w (lt_of_lt_of_le zero_lt_one hw.1))
      linarith
  · -- `x < v`: both sides vanish
    have hzero : ((ℓ.divisors.card : ℝ)) ^ 2 *
          (∫ w in (ℓ : ℝ)..U,
            (if v ≤ (x : ℝ) then s3RemSub x Cm ℓ (sc x B) v w else 0) / (v * w)) = 0 := by
      have hfun : (fun w : ℝ =>
            (if v ≤ (x : ℝ) then s3RemSub x Cm ℓ (sc x B) v w else 0) / (v * w))
          = fun _ => (0 : ℝ) := by
        funext w
        rw [if_neg hvx, zero_div]
      rw [hfun, intervalIntegral.integral_zero, mul_zero]
    rw [hzero]
    refine intervalIntegral.integral_nonneg hc1 (fun w hw => ?_)
    have hw0 : 0 < w := lt_of_lt_of_le zero_lt_one hw.1
    exact div_nonneg (Fsub_nonneg x Cm B ℓ v w) (mul_pos hvpos hw0).le

/-! ## Integrability of the inner `w`-integral over the `v`-window -/

/-- The inner `w`-integral of `Fsub` (over the rectangle's `w`-range `[1, x/Cm]`) is integrable as
a function of `v` on the rectangle's `v`-range `[zc, M·e·zc]`.  It is measurable
(`inner_Fsub_measurable`) and bounded: the `v ≤ x`-indicator in `Fsub` and `Cm·w ≤ x` give the
global bound `abs_Fsub_le_global`, while `v > zc > 0` and `w ≥ 1` bound `1/(v·w)` by `1/zc`. -/
lemma inner_Fsub_integrable (x Cm : ℕ) (B : ℝ) (ℓ : ℕ) (hCm1 : 1 ≤ Cm) (hℓ1 : 1 ≤ ℓ)
    (hℓM : (ℓ : ℝ) ≤ ((⌊(x : ℝ) / (Cm : ℝ)⌋₊ : ℕ) : ℝ)) (hzcp : 0 < zc x B)
    (hc1 : 1 ≤ (x : ℝ) / (Cm : ℝ)) :
    IntegrableOn (fun v : ℝ => ∫ w in Set.Ioc (1 : ℝ) ((x : ℝ) / (Cm : ℝ)),
        Fsub x Cm B ℓ v w / (v * w))
      (Set.Ioc (zc x B) (((⌊(x : ℝ) / (Cm : ℝ)⌋₊ : ℕ) : ℝ) * (Real.exp 1 * zc x B)))
      volume := by
  have hCmp : (0 : ℝ) < (Cm : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hCm1)
  have hxnn : (0 : ℝ) ≤ (x : ℝ) := Nat.cast_nonneg x
  have hAnn : (0 : ℝ) ≤ AcountAtilC x := AcountAtilC_nonneg x
  have hCnn : (0 : ℝ) ≤ (x : ℝ) ^ 2 * ((x : ℝ) * (4 * AcountAtilC x)) :=
    mul_nonneg (by positivity) (mul_nonneg hxnn (by linarith))
  have hℓxR : (ℓ : ℝ) ≤ (x : ℝ) := by
    have h2 : ((⌊(x : ℝ) / (Cm : ℝ)⌋₊ : ℕ) : ℝ) ≤ (x : ℝ) / (Cm : ℝ) :=
      Nat.floor_le (by positivity)
    have h3 : (x : ℝ) / (Cm : ℝ) ≤ (x : ℝ) := by
      rw [div_le_iff₀ hCmp]
      calc (x : ℝ) = (x : ℝ) * 1 := (mul_one _).symm
        _ ≤ (x : ℝ) * (Cm : ℝ) :=
            mul_le_mul_of_nonneg_left (by exact_mod_cast hCm1) hxnn
    linarith
  have hℓx : ℓ ≤ x := by exact_mod_cast hℓxR
  refine Measure.integrableOn_of_bounded (s_finite := (measure_Ioc_lt_top).ne)
    (f_mble := (inner_Fsub_measurable x Cm B ℓ).aestronglyMeasurable)
    (M := (x : ℝ) ^ 2 * ((x : ℝ) * (4 * AcountAtilC x)) / zc x B * ((x : ℝ) / (Cm : ℝ))) ?_
  apply ae_restrict_of_forall_mem measurableSet_Ioc
  intro v hv
  have hvzc : zc x B < v := hv.1
  have hvpos : 0 < v := lt_trans hzcp hv.1
  have hbound : ‖∫ w in Set.Ioc (1 : ℝ) ((x : ℝ) / (Cm : ℝ)), Fsub x Cm B ℓ v w / (v * w)‖
      ≤ ((x : ℝ) ^ 2 * ((x : ℝ) * (4 * AcountAtilC x)) / zc x B)
        * (volume.real (Set.Ioc (1 : ℝ) ((x : ℝ) / (Cm : ℝ)))) := by
    refine norm_setIntegral_le_of_norm_le_const measure_Ioc_lt_top (fun w hw => ?_)
    have hw0 : 0 < w := lt_of_lt_of_le zero_lt_one (le_of_lt hw.1)
    have hwle : w ≤ (x : ℝ) / (Cm : ℝ) := hw.2
    have hCw : (Cm : ℝ) * w ≤ (x : ℝ) := by
      calc (Cm : ℝ) * w ≤ (Cm : ℝ) * ((x : ℝ) / (Cm : ℝ)) :=
            mul_le_mul_of_nonneg_left hwle hCmp.le
        _ = (x : ℝ) := by field_simp
    have hF : |Fsub x Cm B ℓ v w| ≤ (x : ℝ) ^ 2 * ((x : ℝ) * (4 * AcountAtilC x)) := by
      by_cases hvx : v ≤ (x : ℝ)
      · exact abs_Fsub_le_global x Cm B ℓ v w hℓx hvx hCw
      · have hzero : Fsub x Cm B ℓ v w = 0 := by
          unfold Fsub
          rw [if_neg]
          rintro ⟨-, -, -, h⟩
          exact hvx h
        rw [hzero, abs_zero]
        exact hCnn
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (mul_pos hvpos hw0)]
    have h1 : |Fsub x Cm B ℓ v w| / (v * w)
        ≤ ((x : ℝ) ^ 2 * ((x : ℝ) * (4 * AcountAtilC x))) / (v * w) :=
      div_le_div_of_nonneg_right hF (mul_pos hvpos hw0).le
    have h2 : ((x : ℝ) ^ 2 * ((x : ℝ) * (4 * AcountAtilC x))) / (v * w)
        ≤ ((x : ℝ) ^ 2 * ((x : ℝ) * (4 * AcountAtilC x))) / zc x B := by
      have hvw : zc x B ≤ v * w := by
        have h1 : v ≤ v * w := by
          calc v = v * 1 := (mul_one v).symm
            _ ≤ v * w := mul_le_mul_of_nonneg_left hw.1.le hvpos.le
        linarith [hvzc.le, h1]
      exact div_le_div_of_nonneg_left hCnn hzcp hvw
    linarith
  refine le_trans hbound ?_
  have hvol : volume.real (Set.Ioc (1 : ℝ) ((x : ℝ) / (Cm : ℝ))) = (x : ℝ) / (Cm : ℝ) - 1 := by
    rw [MeasureTheory.Measure.real, Real.volume_Ioc,
      ENNReal.toReal_ofReal (by linarith)]
  rw [hvol]
  have hKnn : 0 ≤ (x : ℝ) ^ 2 * ((x : ℝ) * (4 * AcountAtilC x)) / zc x B := by
    exact div_nonneg hCnn hzcp.le
  have hle1 : (x : ℝ) / (Cm : ℝ) - 1 ≤ (x : ℝ) / (Cm : ℝ) := by linarith
  calc ((x : ℝ) ^ 2 * ((x : ℝ) * (4 * AcountAtilC x)) / zc x B)
        * ((x : ℝ) / (Cm : ℝ) - 1)
      ≤ ((x : ℝ) ^ 2 * ((x : ℝ) * (4 * AcountAtilC x)) / zc x B)
        * ((x : ℝ) / (Cm : ℝ)) := mul_le_mul_of_nonneg_left hle1 hKnn
    _ = (x : ℝ) ^ 2 * ((x : ℝ) * (4 * AcountAtilC x)) / zc x B * ((x : ℝ) / (Cm : ℝ)) := rfl

/-! ## The target: the `z`-average of the `ℓ`-th REM summand against the rectangle integral -/

theorem remTerm_zavg_le_rect (x Cm : ℕ) (B : ℝ) (ℓ : ℕ) (hCm1 : 1 ≤ Cm) (hℓ1 : 1 ≤ ℓ)
    (hℓM : (ℓ : ℝ) ≤ ((⌊(x : ℝ) / (Cm : ℝ)⌋₊ : ℕ) : ℝ))
    (hCmzc : (Cm : ℝ) ≤ sc x B * zc x B)
    (hzcp : 0 < zc x B) (hzle : zc x B ≤ Real.exp 1 * zc x B)
    (hc1 : 1 ≤ (x : ℝ) / (Cm : ℝ)) :
    (∫ z in zc x B..(Real.exp 1 * zc x B), remTerm x Cm (sc x B) ℓ z / z)
      ≤ ∫ v in zc x B..(((⌊(x : ℝ) / (Cm : ℝ)⌋₊ : ℕ) : ℝ) * (Real.exp 1 * zc x B)),
          ∫ w in (1 : ℝ)..((x : ℝ) / (Cm : ℝ)), Fsub x Cm B ℓ v w / (v * w) := by
  have hCmp : (0 : ℝ) < (Cm : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hCm1)
  have hℓp : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hℓ1)
  have hℓ1R : (1 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hℓ1
  have hEpos : 0 < Real.exp 1 * zc x B := by
    have : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
    positivity
  set M : ℝ := ((⌊(x : ℝ) / (Cm : ℝ)⌋₊ : ℕ) : ℝ) with hMdef
  set E : ℝ := Real.exp 1 * zc x B with hEdef
  set G : ℝ → ℝ := fun v : ℝ => ∫ w in Set.Ioc (1 : ℝ) ((x : ℝ) / (Cm : ℝ)),
      Fsub x Cm B ℓ v w / (v * w) with hGdef
  have hEll : (ℓ : ℝ) ≤ M := by rw [hMdef]; exact hℓM
  have hab : (ℓ : ℝ) * zc x B ≤ (ℓ : ℝ) * E := by
    rw [hEdef]; exact mul_le_mul_of_nonneg_left hzle hℓp.le
  have hca : zc x B ≤ (ℓ : ℝ) * zc x B := by
    have h := mul_le_mul_of_nonneg_right hℓ1R hzcp.le
    simpa using h
  have hbd : (ℓ : ℝ) * E ≤ M * E := by
    rw [hEdef] at *
    exact mul_le_mul_of_nonneg_right hEll hEpos.le
  have hcd : zc x B ≤ M * E := le_trans hca (le_trans hab hbd)
  -- the per-`ℓ` substitution bound
  have hsub := remTerm_zavg_le_sub x Cm B ℓ hCm1 hℓ1 hℓM hCmzc hzcp hzle
  -- the pointwise relaxation on the `v`-window
  have hpt : ∀ v ∈ Set.Ioc ((ℓ : ℝ) * zc x B) ((ℓ : ℝ) * E),
      ((ℓ.divisors.card : ℝ)) ^ 2 *
        (∫ w in (ℓ : ℝ)..(min (sc x B * v / (Cm : ℝ)) ((x : ℝ) / (Cm : ℝ))),
          (if v ≤ (x : ℝ) then s3RemSub x Cm ℓ (sc x B) v w else 0) / (v * w)) ≤ G v := by
    intro v hv
    rw [show G v = ∫ w in Set.Ioc (1 : ℝ) ((x : ℝ) / (Cm : ℝ)),
        Fsub x Cm B ℓ v w / (v * w) from rfl]
    rw [← intervalIntegral.integral_of_le hc1]
    rw [hEdef] at hv
    exact rect_inner_le x Cm B ℓ hCm1 hℓ1 hℓM hzcp hc1 hv
  -- the relaxed integrand is nonnegative on the `v`-window
  have hUnn : ∀ v ∈ Set.Ioc ((ℓ : ℝ) * zc x B) ((ℓ : ℝ) * E),
      (ℓ : ℝ) ≤ min (sc x B * v / (Cm : ℝ)) ((x : ℝ) / (Cm : ℝ)) := by
    intro v hv
    rw [hEdef] at hv
    refine le_min ?_ ?_
    · rw [le_div_iff₀ hCmp]
      have h1 : (ℓ : ℝ) * (Cm : ℝ) ≤ (ℓ : ℝ) * (sc x B * zc x B) :=
        mul_le_mul_of_nonneg_left hCmzc hℓp.le
      have h2 : (ℓ : ℝ) * (sc x B * zc x B) ≤ (sc x B) * v := by
        have hscp : 0 < sc x B := sc_pos x B
        calc (ℓ : ℝ) * (sc x B * zc x B) = (sc x B) * ((ℓ : ℝ) * zc x B) := by ring
          _ ≤ (sc x B) * v := mul_le_mul_of_nonneg_left hv.1.le hscp.le
      exact le_trans h1 h2
    · exact le_trans hℓM (Nat.floor_le (by positivity))
  have hLnn : ∀ v ∈ Set.Ioc ((ℓ : ℝ) * zc x B) ((ℓ : ℝ) * E),
      0 ≤ ((ℓ.divisors.card : ℝ)) ^ 2 *
        (∫ w in (ℓ : ℝ)..(min (sc x B * v / (Cm : ℝ)) ((x : ℝ) / (Cm : ℝ))),
          (if v ≤ (x : ℝ) then s3RemSub x Cm ℓ (sc x B) v w else 0) / (v * w)) := by
    intro v hv
    refine mul_nonneg (by positivity) ?_
    refine intervalIntegral.integral_nonneg (hUnn v hv) (fun w hw => ?_)
    have hw0 : 0 < w := lt_of_lt_of_le hℓp hw.1
    have hv0 : 0 < v := by
      rw [hEdef] at hv
      nlinarith [hv.1, hℓp, hzcp]
    by_cases h : v ≤ (x : ℝ)
    · rw [if_pos h]
      exact div_nonneg (s3RemSub_nonneg x Cm ℓ (sc x B) v w) (mul_pos hv0 hw0).le
    · rw [if_neg h]; simp
  -- `G ≥ 0` on the big `v`-interval
  have hGnn : ∀ v ∈ Set.Ioc (zc x B) (M * E), 0 ≤ G v := by
    intro v hv
    rw [show G v = ∫ w in Set.Ioc (1 : ℝ) ((x : ℝ) / (Cm : ℝ)),
        Fsub x Cm B ℓ v w / (v * w) from rfl]
    rw [← intervalIntegral.integral_of_le hc1]
    refine intervalIntegral.integral_nonneg hc1 (fun w hw => ?_)
    have hv0 : 0 < v := lt_of_lt_of_le hzcp (le_of_lt hv.1)
    have hw0 : 0 < w := lt_of_lt_of_le zero_lt_one hw.1
    exact div_nonneg (Fsub_nonneg x Cm B ℓ v w) (mul_pos hv0 hw0).le
  -- integrability of `G`
  have hME : M * E = ((⌊(x : ℝ) / (Cm : ℝ)⌋₊ : ℕ) : ℝ) * (Real.exp 1 * zc x B) := by
    rw [hMdef, hEdef]
  have hGint : IntegrableOn G (Set.Ioc (zc x B) (M * E)) volume := by
    rw [show G = (fun v : ℝ => ∫ w in Set.Ioc (1 : ℝ) ((x : ℝ) / (Cm : ℝ)),
        Fsub x Cm B ℓ v w / (v * w)) from rfl, hME]
    exact inner_Fsub_integrable x Cm B ℓ hCm1 hℓ1 hℓM hzcp hc1
  have hGint' : IntegrableOn G (Set.Ioc ((ℓ : ℝ) * zc x B) ((ℓ : ℝ) * E)) volume :=
    hGint.mono_set (by
      intro v hv
      exact ⟨lt_of_le_of_lt hca hv.1, le_trans hv.2 hbd⟩)
  have hGintI : IntervalIntegrable G volume (zc x B) (M * E) := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le hcd]; exact hGint
  -- the two monotonicity steps
  have hmono1 : (∫ v in Set.Ioc ((ℓ : ℝ) * zc x B) ((ℓ : ℝ) * E),
      ((ℓ.divisors.card : ℝ)) ^ 2 *
        (∫ w in (ℓ : ℝ)..(min (sc x B * v / (Cm : ℝ)) ((x : ℝ) / (Cm : ℝ))),
          (if v ≤ (x : ℝ) then s3RemSub x Cm ℓ (sc x B) v w else 0) / (v * w)))
      ≤ ∫ v in Set.Ioc ((ℓ : ℝ) * zc x B) ((ℓ : ℝ) * E), G v :=
    integral_mono_of_nonneg (ae_restrict_of_forall_mem measurableSet_Ioc hLnn) hGint'
      (ae_restrict_of_forall_mem measurableSet_Ioc hpt)
  have hmono2I : (∫ v in ((ℓ : ℝ) * zc x B)..((ℓ : ℝ) * E), G v)
      ≤ ∫ v in zc x B..(M * E), G v :=
    intervalIntegral.integral_mono_interval hca hab hbd
      (ae_restrict_of_forall_mem measurableSet_Ioc hGnn) hGintI
  have hmono2 : (∫ v in Set.Ioc ((ℓ : ℝ) * zc x B) ((ℓ : ℝ) * E), G v)
      ≤ ∫ v in Set.Ioc (zc x B) (M * E), G v := by
    have h := hmono2I
    rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hcd] at h
    exact h
  have hconst : (∫ v in ((ℓ : ℝ) * zc x B)..((ℓ : ℝ) * E),
      ((ℓ.divisors.card : ℝ)) ^ 2 *
        (∫ w in (ℓ : ℝ)..(min (sc x B * v / (Cm : ℝ)) ((x : ℝ) / (Cm : ℝ))),
          (if v ≤ (x : ℝ) then s3RemSub x Cm ℓ (sc x B) v w else 0) / (v * w)))
      = ((ℓ.divisors.card : ℝ)) ^ 2 *
        (∫ v in ((ℓ : ℝ) * zc x B)..((ℓ : ℝ) * E),
          ∫ w in (ℓ : ℝ)..(min (sc x B * v / (Cm : ℝ)) ((x : ℝ) / (Cm : ℝ))),
            (if v ≤ (x : ℝ) then s3RemSub x Cm ℓ (sc x B) v w else 0) / (v * w)) :=
    intervalIntegral.integral_const_mul _ _
  have hfinal : (∫ v in zc x B..(M * E), G v)
      = ∫ v in zc x B..(M * E), ∫ w in (1 : ℝ)..((x : ℝ) / (Cm : ℝ)),
          Fsub x Cm B ℓ v w / (v * w) := by
    refine intervalIntegral.integral_congr (fun v _ => ?_)
    rw [show G v = ∫ w in Set.Ioc (1 : ℝ) ((x : ℝ) / (Cm : ℝ)),
        Fsub x Cm B ℓ v w / (v * w) from rfl]
    rw [← intervalIntegral.integral_of_le hc1]
  calc (∫ z in zc x B..(Real.exp 1 * zc x B), remTerm x Cm (sc x B) ℓ z / z)
      ≤ ((ℓ.divisors.card : ℝ)) ^ 2 *
        (∫ v in ((ℓ : ℝ) * zc x B)..((ℓ : ℝ) * E),
          ∫ w in (ℓ : ℝ)..(min (sc x B * v / (Cm : ℝ)) ((x : ℝ) / (Cm : ℝ))),
            (if v ≤ (x : ℝ) then s3RemSub x Cm ℓ (sc x B) v w else 0) / (v * w)) := hsub
    _ = ∫ v in ((ℓ : ℝ) * zc x B)..((ℓ : ℝ) * E),
          ((ℓ.divisors.card : ℝ)) ^ 2 *
            (∫ w in (ℓ : ℝ)..(min (sc x B * v / (Cm : ℝ)) ((x : ℝ) / (Cm : ℝ))),
              (if v ≤ (x : ℝ) then s3RemSub x Cm ℓ (sc x B) v w else 0) / (v * w)) :=
        hconst.symm
    _ = ∫ v in Set.Ioc ((ℓ : ℝ) * zc x B) ((ℓ : ℝ) * E),
          ((ℓ.divisors.card : ℝ)) ^ 2 *
            (∫ w in (ℓ : ℝ)..(min (sc x B * v / (Cm : ℝ)) ((x : ℝ) / (Cm : ℝ))),
              (if v ≤ (x : ℝ) then s3RemSub x Cm ℓ (sc x B) v w else 0) / (v * w)) :=
        intervalIntegral.integral_of_le hab
    _ ≤ ∫ v in Set.Ioc ((ℓ : ℝ) * zc x B) ((ℓ : ℝ) * E), G v := hmono1
    _ ≤ ∫ v in Set.Ioc (zc x B) (M * E), G v := hmono2
    _ = ∫ v in zc x B..(M * E), G v := (intervalIntegral.integral_of_le hcd).symm
    _ = ∫ v in zc x B..(M * E), ∫ w in (1 : ℝ)..((x : ℝ) / (Cm : ℝ)),
          Fsub x Cm B ℓ v w / (v * w) := hfinal

end

end Work.FIChain
