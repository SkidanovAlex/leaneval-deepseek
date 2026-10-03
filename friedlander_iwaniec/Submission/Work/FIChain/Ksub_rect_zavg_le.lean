/-
# `Submission.Work.FIChain.Ksub_rect_zavg_le`

The measure-theoretic step (4)–(5) of the route recorded in `s3RemPlus_maj_le`: after the
per-`ℓ` `z`-substitution and the relaxation to the COMMON rectangle
`[zc, ⌊x/Cm⌋₊·e·zc] × [1, x/Cm]`, the joint integrand `Ksub` is bounded pointwise by
`Ksub_le` (the `(R′)` fibre bound), and the resulting two-fold integral is evaluated exactly:

    ∫_{zc}^{⌊x/Cm⌋₊·e·zc} dv/v ∫_1^{x/Cm} dw/w · Ksub(v,w)
      ≤ 2·Ã(x)·(log x)^{-3} · log(⌊x/Cm⌋₊·e) · log(x/Cm)
      ≤ 4·Ã(x)·(log x)^{-1} ,

using only `log(x/Cm) ≤ log x` and `log(⌊x/Cm⌋₊·e) = log⌊x/Cm⌋₊ + 1 ≤ 2 log x`.

All measure-theoretic bookkeeping is isolated in `iterated_integral_div_bound` (a general
two-variable interval-integral monotonicity lemma) and all arithmetic in `Ksub_rect_arith`.
-/
import Mathlib
import Submission.Work.FIChain.s3RemPlus_maj_le_defs

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIChain

open Finset MeasureTheory
open scoped BigOperators Interval

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. Elementary nonnegativity of the integrand -/

lemma Ksub_rect_s3RemSub_nonneg (x Cm ℓ : ℕ) (sc v t : ℝ) :
    0 ≤ s3RemSub x Cm ℓ sc v t := by
  unfold s3RemSub
  refine Finset.sum_nonneg (fun d _ => ?_)
  exact add_nonneg (abs_nonneg _) (abs_nonneg _)

lemma Ksub_rect_Ksub_nonneg (x Cm : ℕ) (B : ℝ) (v w : ℝ) :
    0 ≤ Ksub x Cm B v w := by
  unfold Ksub
  refine Finset.sum_nonneg (fun ℓ _ => ?_)
  by_cases h : (ℓ : ℝ) * zc x B ≤ v ∧ v ≤ (ℓ : ℝ) * (Real.exp 1 * zc x B) ∧
      (ℓ : ℝ) ≤ w ∧ v ≤ (x : ℝ)
  · rw [if_pos h]
    exact mul_nonneg (by positivity) (Ksub_rect_s3RemSub_nonneg x Cm ℓ (sc x B) v w)
  · rw [if_neg h]

/-! ## 2. The general two-variable interval-integral bound -/

/-- For a kernel `F` that is nonnegative and bounded by `C/(v·w)` on
`(a,b] × [c,d]`, the iterated integral is at most `C·log(b/a)·log(d/c)`.

The proof uses `integral_mono_of_nonneg`, which only asks for integrability of the *dominating*
function `C/(v·w)` (shown with `IntegrableOn.of_bound`), so no measurability of `F` is needed. -/
theorem iterated_integral_div_bound (F : ℝ → ℝ → ℝ) {a b c d C : ℝ}
    (hab : a ≤ b) (ha : 0 < a) (hc : 0 < c) (hcd : c ≤ d)
    (hFnn : ∀ v ∈ Set.Ioc a b, ∀ w ∈ Set.Icc c d, 0 ≤ F v w)
    (hbound : ∀ v ∈ Set.Ioc a b, ∀ w ∈ Set.Icc c d, F v w ≤ C / (v * w)) :
    (∫ v in a..b, ∫ w in c..d, F v w) ≤ C * Real.log (b / a) * Real.log (d / c) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hd : 0 < d := lt_of_lt_of_le hc hcd
  -- Step 1: a uniform bound for the inner integral, for every `v ∈ (a,b]`.
  have hinner : ∀ v ∈ Set.Ioc a b, (∫ w in c..d, F v w) ≤ (C / v) * Real.log (d / c) := by
    intro v hv
    have hv0 : 0 < v := lt_trans ha hv.1
    rw [intervalIntegral.integral_of_le hcd]
    have hg : Integrable (fun w : ℝ => C / (v * w)) (volume.restrict (Set.Ioc c d)) := by
      refine IntegrableOn.of_bound (measure_Ioc_lt_top (a := c) (b := d)) ?_
        (|C| / (v * c)) ?_
      · exact (measurable_const.div (measurable_const.mul measurable_id)).aestronglyMeasurable
      · rw [ae_restrict_iff' measurableSet_Ioc]
        refine Filter.Eventually.of_forall (fun w hw => ?_)
        have hw0 : 0 < w := lt_trans hc hw.1
        have hcw : c ≤ w := le_of_lt hw.1
        rw [Real.norm_eq_abs, abs_div, abs_of_pos (mul_pos hv0 hw0)]
        exact div_le_div_of_nonneg_left (abs_nonneg C) (mul_pos hv0 hc)
          (mul_le_mul_of_nonneg_left hcw hv0.le)
    have h1 : (0 : ℝ → ℝ) ≤ᵐ[volume.restrict (Set.Ioc c d)] (fun w : ℝ => F v w) := by
      rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
      exact Filter.Eventually.of_forall
        (fun w hw => hFnn v hv w (Set.Ioc_subset_Icc_self hw))
    have h2 : (fun w : ℝ => F v w) ≤ᵐ[volume.restrict (Set.Ioc c d)]
        (fun w : ℝ => C / (v * w)) := by
      rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
      exact Filter.Eventually.of_forall
        (fun w hw => hbound v hv w (Set.Ioc_subset_Icc_self hw))
    calc ∫ w in Set.Ioc c d, F v w ≤ ∫ w in Set.Ioc c d, C / (v * w) :=
          integral_mono_of_nonneg h1 hg h2
      _ = ∫ w in c..d, C / (v * w) := by rw [intervalIntegral.integral_of_le hcd]
      _ = (C / v) * Real.log (d / c) := by
          have hfun : (fun w : ℝ => C / (v * w)) = fun w => (C / v) * w⁻¹ := by
            funext w
            rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv]
            ring
          rw [hfun, intervalIntegral.integral_const_mul, integral_inv_of_pos hc hd]
  -- Step 2: replace the inner integral by its bound and integrate `dv/v`.
  have hmain : (∫ v in a..b, ∫ w in c..d, F v w)
      ≤ ∫ v in a..b, (C / v) * Real.log (d / c) := by
    rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
    refine integral_mono_of_nonneg ?_ ?_ ?_
    · rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
      exact Filter.Eventually.of_forall
        (fun v hv => intervalIntegral.integral_nonneg hcd (fun w hw => hFnn v hv w hw))
    · refine IntegrableOn.of_bound (measure_Ioc_lt_top (a := a) (b := b)) ?_
        (|C| * |Real.log (d / c)| / a) ?_
      · exact ((measurable_const.div measurable_id).mul_const _).aestronglyMeasurable
      · rw [ae_restrict_iff' measurableSet_Ioc]
        refine Filter.Eventually.of_forall (fun v hv => ?_)
        have hv0 : 0 < v := lt_trans ha hv.1
        rw [Real.norm_eq_abs, abs_mul, abs_div, abs_of_pos hv0, div_mul_eq_mul_div]
        exact div_le_div_of_nonneg_left (by positivity) ha hv.1.le
    · rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
      exact Filter.Eventually.of_forall (fun v hv => hinner v hv)
  -- Step 3: exact evaluation of the comparison integral.
  have hval : (∫ v in a..b, (C / v) * Real.log (d / c))
      = C * Real.log (d / c) * Real.log (b / a) := by
    have hfun : (fun v : ℝ => (C / v) * Real.log (d / c))
        = fun v => (C * Real.log (d / c)) * v⁻¹ := by
      funext v
      rw [div_eq_mul_inv]
      ring
    rw [hfun, intervalIntegral.integral_const_mul, integral_inv_of_pos ha hb]
  calc (∫ v in a..b, ∫ w in c..d, F v w)
      ≤ ∫ v in a..b, (C / v) * Real.log (d / c) := hmain
    _ = C * Real.log (d / c) * Real.log (b / a) := hval
    _ = C * Real.log (b / a) * Real.log (d / c) := by ring

/-! ## 3. The final real arithmetic -/

/-- With `L = log x ≥ 1`, `1 ≤ M ≤ x`, `1 ≤ dd ≤ x` and `A ≥ 0`:
`2A L^{-3} · log(M·e) · log dd ≤ 4 A L^{-1}`. -/
theorem Ksub_rect_arith (A x M dd L : ℝ) (hA : 0 ≤ A) (hx1 : 1 ≤ x) (hL : L = Real.log x)
    (hL1 : 1 ≤ L) (hM1 : 1 ≤ M) (hMx : M ≤ x) (hdd1 : 1 ≤ dd) (hddx : dd ≤ x) :
    (2 * A * L ^ (-(3 : ℤ))) * Real.log (M * Real.exp 1) * Real.log dd
      ≤ 4 * A * L ^ (-(1 : ℤ)) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  have hM0 : 0 < M := lt_of_lt_of_le zero_lt_one hM1
  have hdd0 : 0 < dd := lt_of_lt_of_le zero_lt_one hdd1
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL1
  have hLne : L ≠ 0 := ne_of_gt hL0
  have hlogM : Real.log M ≤ L := by
    rw [hL]; exact Real.log_le_log hM0 hMx
  have hlogdd : Real.log dd ≤ L := by
    rw [hL]; exact Real.log_le_log hdd0 hddx
  have hlogdd0 : 0 ≤ Real.log dd := Real.log_nonneg hdd1
  have hexp : Real.log (M * Real.exp 1) = Real.log M + 1 := by
    rw [Real.log_mul (ne_of_gt hM0) (ne_of_gt (Real.exp_pos 1)), Real.log_exp]
  have hlogMe : Real.log (M * Real.exp 1) ≤ 2 * L := by
    rw [hexp]; linarith
  have hCx0 : 0 ≤ 2 * A * L ^ (-(3 : ℤ)) :=
    mul_nonneg (mul_nonneg (by norm_num) hA) (zpow_pos hL0 _).le
  have hpow : L ^ (-(3 : ℤ)) * L * L = L ^ (-(1 : ℤ)) := by
    rw [mul_assoc, ← pow_two, ← zpow_natCast, ← zpow_add₀ hLne,
      show (-(3 : ℤ) + ((2 : ℕ) : ℤ)) = (-(1 : ℤ)) by norm_num]
  calc (2 * A * L ^ (-(3 : ℤ))) * Real.log (M * Real.exp 1) * Real.log dd
      ≤ (2 * A * L ^ (-(3 : ℤ))) * (2 * L) * L := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left hlogMe hCx0) hlogdd hlogdd0 ?_
        exact mul_nonneg hCx0 (by linarith)
    _ = 4 * A * L ^ (-(1 : ℤ)) := by
        rw [show (2 * A * L ^ (-(3 : ℤ))) * (2 * L) * L
            = 4 * A * (L ^ (-(3 : ℤ)) * L * L) by ring, hpow]

/-! ## 4. The rectangle `z`-average bound -/

theorem Ksub_rect_zavg_le (Xf x Cm : ℕ) (B : ℝ)
    (hf : ∀ y : ℕ, Xf ≤ y → ∀ N m₁ m₂ : ℕ,
      N ≤ ⌈(y : ℝ) ^ ((7 : ℝ) / 10)⌉₊ → m₁ ≤ y → m₂ ≤ y →
      ∀ w : ℕ → ℝ, (∀ ℓ : ℕ, 0 ≤ w ℓ) →
        (∀ ℓ : ℕ, w ℓ ≤ ((ℓ.divisors.card : ℝ)) ^ 2) →
      (∑ ℓ ∈ Finset.Icc 1 y, ∑ d ∈ Finset.Icc 1 y,
          (if ℓ * d ≤ N then w ℓ * (|cfR (ℓ * d) m₁| + |cfR (ℓ * d) m₂|) else 0))
        ≤ 2 * AcountAtilC y * (Real.log (y : ℝ)) ^ (-(3 : ℤ)))
    (hXf : Xf ≤ x)
    (hxc : (x : ℝ) / (Cm : ℝ) ≤ ((⌈(x : ℝ) ^ ((7 : ℝ) / 10)⌉₊ : ℕ) : ℝ))
    (hc1 : 1 ≤ (x : ℝ) / (Cm : ℝ)) (hCm1 : 1 ≤ Cm)
    (hzcp : 0 < zc x B)
    (hV : zc x B ≤ ((⌊(x : ℝ) / (Cm : ℝ)⌋₊ : ℕ) : ℝ) * (Real.exp 1 * zc x B))
    (hx1 : 1 ≤ (x : ℝ)) (hlog1 : 1 ≤ Real.log (x : ℝ)) :
    (∫ v in zc x B..(((⌊(x : ℝ) / (Cm : ℝ)⌋₊ : ℕ) : ℝ) * (Real.exp 1 * zc x B)),
        ∫ w in (1 : ℝ)..((x : ℝ) / (Cm : ℝ)), Ksub x Cm B v w / (v * w))
      ≤ 4 * AcountAtilC x * (Real.log (x : ℝ)) ^ (-(1 : ℤ)) := by
  set A : ℝ := AcountAtilC x with hA
  set L : ℝ := Real.log (x : ℝ) with hL
  set M : ℝ := ((⌊(x : ℝ) / (Cm : ℝ)⌋₊ : ℕ) : ℝ) with hM
  set dd : ℝ := (x : ℝ) / (Cm : ℝ) with hdd
  set a : ℝ := zc x B with ha
  set b : ℝ := M * (Real.exp 1 * a) with hb
  have hA0 : 0 ≤ A := by rw [hA]; exact AcountAtilC_nonneg x
  have hL1' : 1 ≤ L := by rw [hL]; exact hlog1
  have hx0 : 0 < (x : ℝ) := lt_of_lt_of_le zero_lt_one hx1
  have hCm0 : 0 < (Cm : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hCm1)
  have hCm1' : (1 : ℝ) ≤ (Cm : ℝ) := by exact_mod_cast hCm1
  have ha0 : 0 < a := by rw [ha]; exact hzcp
  have hab : a ≤ b := by
    simp only [ha, hb, hM]
    exact hV
  have hdd1 : 1 ≤ dd := by rw [hdd]; exact hc1
  have hddx : dd ≤ (x : ℝ) := by
    rw [hdd, div_le_iff₀ hCm0]
    exact le_mul_of_one_le_right (le_of_lt hx0) hCm1'
  have hM1 : 1 ≤ M := by
    rw [hM]
    have h1le : ((1 : ℕ) : ℝ) ≤ dd := by exact_mod_cast hc1
    exact_mod_cast (Nat.le_floor h1le)
  have hM0 : 0 < M := lt_of_lt_of_le zero_lt_one hM1
  have hMx : M ≤ (x : ℝ) := by
    rw [hM]
    have h1 : (((⌊(x : ℝ) / (Cm : ℝ)⌋₊ : ℕ)) : ℝ) ≤ (x : ℝ) / (Cm : ℝ) :=
      Nat.floor_le (by positivity)
    have h2 : (x : ℝ) / (Cm : ℝ) ≤ (x : ℝ) := by
      rw [div_le_iff₀ hCm0]
      exact le_mul_of_one_le_right (le_of_lt hx0) hCm1'
    linarith
  -- the pointwise `(R′)` bound on the rectangle
  have hKsub_le : ∀ v ∈ Set.Ioc a b, ∀ w ∈ Set.Icc (1 : ℝ) dd,
      Ksub x Cm B v w ≤ 2 * A * L ^ (-(3 : ℤ)) := by
    intro v hv w hw
    have hw0 : 0 ≤ w := le_trans zero_le_one hw.1
    have hwx : ⌊w⌋₊ ≤ ⌈(x : ℝ) ^ ((7 : ℝ) / 10)⌉₊ := by
      have h2 : ⌊dd⌋₊ ≤ ⌈(x : ℝ) ^ ((7 : ℝ) / 10)⌉₊ := by
        have h3 : dd ≤ ((⌈(x : ℝ) ^ ((7 : ℝ) / 10)⌉₊ : ℕ) : ℝ) := by
          rw [hdd]; exact hxc
        calc ⌊dd⌋₊ ≤ ⌊((⌈(x : ℝ) ^ ((7 : ℝ) / 10)⌉₊ : ℕ) : ℝ)⌋₊ := Nat.floor_mono h3
          _ = ⌈(x : ℝ) ^ ((7 : ℝ) / 10)⌉₊ := Nat.floor_natCast _
      exact le_trans (Nat.floor_mono hw.2) h2
    have hCmw : (Cm : ℝ) * w ≤ (x : ℝ) := by
      have h1 : (Cm : ℝ) * w ≤ (Cm : ℝ) * dd := mul_le_mul_of_nonneg_left hw.2 hCm0.le
      have h2 : (Cm : ℝ) * dd = (x : ℝ) := by
        rw [hdd, mul_comm, div_mul_cancel₀ (x : ℝ) (ne_of_gt hCm0)]
      linarith
    have hwle : w ≤ (x : ℝ) := le_trans hw.2 hddx
    by_cases hvx : v ≤ (x : ℝ)
    · rw [hA, hL]
      exact Ksub_le Xf x Cm B v w hf hXf hwx hvx hCmw hw0 hwle
    · have hzero : Ksub x Cm B v w = 0 := by
        unfold Ksub
        refine Finset.sum_eq_zero (fun ℓ _ => ?_)
        rw [if_neg]
        intro h
        exact hvx h.2.2.2
      rw [hzero]
      exact mul_nonneg (mul_nonneg (by norm_num) hA0)
        (zpow_pos (lt_of_lt_of_le zero_lt_one hL1') _).le
  -- the two hypotheses of `iterated_integral_div_bound`
  have hpoint : ∀ v ∈ Set.Ioc a b, ∀ w ∈ Set.Icc (1 : ℝ) dd,
      Ksub x Cm B v w / (v * w) ≤ (2 * A * L ^ (-(3 : ℤ))) / (v * w) := by
    intro v hv w hw
    have hv0 : 0 < v := lt_trans ha0 hv.1
    have hw0 : 0 < w := lt_of_lt_of_le zero_lt_one hw.1
    exact div_le_div_of_nonneg_right (hKsub_le v hv w hw) (le_of_lt (mul_pos hv0 hw0))
  have hnn : ∀ v ∈ Set.Ioc a b, ∀ w ∈ Set.Icc (1 : ℝ) dd,
      0 ≤ Ksub x Cm B v w / (v * w) := by
    intro v hv w hw
    have hv0 : 0 < v := lt_trans ha0 hv.1
    have hw0 : 0 < w := lt_of_lt_of_le zero_lt_one hw.1
    exact div_nonneg (Ksub_rect_Ksub_nonneg x Cm B v w) (le_of_lt (mul_pos hv0 hw0))
  have hub := iterated_integral_div_bound (F := fun v w => Ksub x Cm B v w / (v * w))
    hab ha0 zero_lt_one hdd1 hnn hpoint
  have hbda : b / a = M * Real.exp 1 := by
    rw [hb, mul_div_assoc, mul_div_assoc, div_self (ne_of_gt ha0), mul_one]
  calc (∫ v in a..b, ∫ w in (1 : ℝ)..dd, Ksub x Cm B v w / (v * w))
      ≤ (2 * A * L ^ (-(3 : ℤ))) * Real.log (b / a) * Real.log (dd / 1) := hub
    _ = (2 * A * L ^ (-(3 : ℤ))) * Real.log (M * Real.exp 1) * Real.log dd := by
        rw [hbda, div_one]
    _ ≤ 4 * A * L ^ (-(1 : ℤ)) :=
        Ksub_rect_arith A x M dd L hA0 hx1 hL hL1' hM1 hMx hdd1 hddx

end

end Work.FIChain
