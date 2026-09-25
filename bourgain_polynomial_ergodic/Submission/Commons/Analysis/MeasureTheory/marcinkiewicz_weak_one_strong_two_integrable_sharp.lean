import Mathlib
import Submission.Commons.Analysis.MeasureTheory.marcinkiewicz_weak_one_strong_two_integrable

/-!
# Marcinkiewicz interpolation, integrable form, sharp (geometric-mean) constant

The lemma `marcinkiewicz_weak_one_strong_two_integrable` in the commons proves that an operator
`T` (additive on integrable functions) which is weak type `(1,1)` with constant `A₀` and strong
type `(2,2)` with constant `A₁` is strong type `(p,p)` for `1 < p < 2`, but with a constant
depending on `A₀, A₁` in a non-interpolatory way.

Here we prove the *sharp* form: the constant can be taken to depend on `p` only, with the
`L^p` operator norm bounded by a universal multiple of `A₀ ^ (2/p - 1) * A₁ ^ (2 - 2/p)`, i.e.
the geometric mean of the endpoint constants.

The proof is the same truncation/layer-cake argument as in the commons file, but the level at
which `f` is truncated is decoupled from the level at which the distribution of `T f` is
measured: for a parameter `d > 0` one splits `f` at level `d * t` while measuring the tail of
`T f` at level `t`.  This produces the one-parameter family of bounds

`∫ ‖T f‖^p ≤ (c₁ A₀ d^{1-p} + c₂ A₁² d^{2-p}) ∫ ‖f‖^p`,

and choosing `d = A₀ / A₁²` balances the two terms and yields the geometric mean.
-/

open MeasureTheory Measure Filter Set
open scoped ENNReal

namespace Commons.Analysis.MeasureTheory

/-! ## Pointwise truncation bounds with decoupled levels -/

/-- The weak-type bound for the high truncation, with the truncation level `d * t` decoupled
from the measuring level `t / 2`, multiplied by `t ^ (p - 1)`. -/
lemma sharp_high_pointwise {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace E] [NormedAddCommGroup E] {μ : Measure α} {ν : Measure β} {A0 : ℝ}
    (hA0 : 0 < A0) {p d : ℝ} (hp1 : 1 < p) (hd : 0 < d)
    {T : (α → E) → (β → E)} {f : α → E} (hf : Integrable f μ)
    (hweak : ∀ (g : α → E) (lam : ℝ), Integrable g μ → 0 < lam →
      ν {x : β | lam < ‖T g x‖} ≤ ENNReal.ofReal (A0 / lam) * eLpNorm g 1 μ)
    {t : ℝ} (ht : 0 < t) :
    ENNReal.ofReal (t ^ (p - 1)) *
      ν {a : β | t / 2 < ‖T (Set.indicator {x : α | ENNReal.ofReal (d * t) < ‖f x‖ₑ} f) a‖}
      ≤ ENNReal.ofReal (6 * A0 * t ^ (p - 2)) *
          (∫⁻ s in Set.Ioi (d * t / 2), innerTail μ (fun x => ‖f x‖ₑ) s) := by
  have hdt : 0 < d * t := mul_pos hd ht
  set g : α → E := Set.indicator {x : α | ENNReal.ofReal (d * t) < ‖f x‖ₑ} f with hg
  have hgi : Integrable g μ := by
    rw [hg]; exact integrable_indicator_ofReal_lt_enorm hf (d * t)
  have h1 : ν {a : β | t / 2 < ‖T g a‖} ≤ ENNReal.ofReal (A0 / (t/2)) * eLpNorm g 1 μ :=
    hweak g (t/2) hgi (by positivity)
  have h2 : eLpNorm g 1 μ
      = ∫⁻ x, Set.indicator {x : α | ENNReal.ofReal (d * t) < ‖f x‖ₑ} (fun x => ‖f x‖ₑ) x ∂μ := by
    rw [eLpNorm_one_eq_lintegral_enorm hgi.aestronglyMeasurable]
    refine lintegral_congr fun x => ?_
    have h3 : ‖g x‖ₑ
        = Set.indicator {x : α | ENNReal.ofReal (d * t) < ‖f x‖ₑ} (fun x => ‖f x‖ₑ) x := by
      show ‖Set.indicator {x : α | ENNReal.ofReal (d * t) < ‖f x‖ₑ} f x‖ₑ = _
      exact enorm_indicator_eq_indicator_enorm f x
    rw [h3]
  have h4 : (∫⁻ x, Set.indicator {x : α | ENNReal.ofReal (d * t) < ‖f x‖ₑ} (fun x => ‖f x‖ₑ) x ∂μ)
      ≤ 3 * ∫⁻ s in Set.Ioi (d * t / 2), innerTail μ (fun x => ‖f x‖ₑ) s :=
    lintegral_indicator_high_le (fun x => enorm_ne_top) hdt
  have hreal : t ^ (p - 1) * (A0 / (t / 2)) = 2 * A0 * t ^ (p - 2) := by
    have htp1 : t ^ (p-1) = t ^ (p-2) * t := by
      nth_rewrite 3 [← Real.rpow_one t]
      rw [← Real.rpow_add ht (p-2) 1, show p - 2 + 1 = p - 1 by ring]
    rw [htp1]
    have hstep : t * (A0 / (t/2)) = 2 * A0 := by field_simp
    calc t ^ (p-2) * t * (A0 / (t / 2)) = t ^ (p-2) * (t * (A0 / (t / 2))) := by ring
      _ = t ^ (p-2) * (2 * A0) := by rw [hstep]
      _ = 2 * A0 * t ^ (p - 2) := by ring
  have h5 : ENNReal.ofReal (t ^ (p - 1)) * ENNReal.ofReal (A0 / (t / 2))
      = ENNReal.ofReal (2 * A0 * t ^ (p - 2)) := by
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg ht.le (p-1)), hreal]
  have h6 : ENNReal.ofReal (2 * A0 * t ^ (p - 2)) * 3 = ENNReal.ofReal (6 * A0 * t ^ (p - 2)) := by
    rw [show (3 : ℝ≥0∞) = ENNReal.ofReal 3 by norm_num,
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  calc ENNReal.ofReal (t ^ (p - 1)) * ν {a : β | t / 2 < ‖T g a‖}
      ≤ ENNReal.ofReal (t ^ (p - 1)) *
          (ENNReal.ofReal (A0 / (t/2)) * eLpNorm g 1 μ) := mul_le_mul_right h1 _
    _ = ENNReal.ofReal (t ^ (p - 1)) *
          (ENNReal.ofReal (A0 / (t/2)) *
            ∫⁻ x, Set.indicator {x : α | ENNReal.ofReal (d * t) < ‖f x‖ₑ} (fun x => ‖f x‖ₑ) x ∂μ) := by
        rw [h2]
    _ = (ENNReal.ofReal (t ^ (p - 1)) * ENNReal.ofReal (A0 / (t/2))) *
            ∫⁻ x, Set.indicator {x : α | ENNReal.ofReal (d * t) < ‖f x‖ₑ} (fun x => ‖f x‖ₑ) x ∂μ := by
        rw [mul_assoc]
    _ = ENNReal.ofReal (2 * A0 * t ^ (p - 2)) *
            ∫⁻ x, Set.indicator {x : α | ENNReal.ofReal (d * t) < ‖f x‖ₑ} (fun x => ‖f x‖ₑ) x ∂μ := by
        rw [h5]
    _ ≤ ENNReal.ofReal (2 * A0 * t ^ (p - 2)) *
          (3 * ∫⁻ s in Set.Ioi (d * t / 2), innerTail μ (fun x => ‖f x‖ₑ) s) := mul_le_mul_right h4 _
    _ = ENNReal.ofReal (6 * A0 * t ^ (p - 2)) *
          (∫⁻ s in Set.Ioi (d * t / 2), innerTail μ (fun x => ‖f x‖ₑ) s) := by
        rw [← mul_assoc, h6]

/-- The strong-type bound for the low truncation, with the truncation level `d * t` decoupled
from the measuring level `t / 2`, multiplied by `t ^ (p - 1)`. -/
lemma sharp_low_pointwise {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace E] [NormedAddCommGroup E] {μ : Measure α} {ν : Measure β} {A1 : ℝ}
    (hA1 : 0 < A1) {p d : ℝ} (hp1 : 1 < p) (hd : 0 < d)
    {T : (α → E) → (β → E)} {f : α → E} (hf : Integrable f μ)
    (hstrong : ∀ g : α → E, Integrable g μ → eLpNorm (T g) 2 ν ≤ ENNReal.ofReal A1 * eLpNorm g 2 μ)
    {t : ℝ} (ht : 0 < t) :
    ENNReal.ofReal (t ^ (p - 1)) *
      innerTail ν (fun a => ‖T (Set.indicator {x : α | ENNReal.ofReal (d * t) < ‖f x‖ₑ}ᶜ f) a‖ₑ) (t / 2)
      ≤ ENNReal.ofReal (4 * A1 ^ 2 * t ^ (p - 3)) *
          (∫⁻ s in Set.Ioc (0:ℝ) ((d * t) ^ 2), innerTail μ (fun x => ‖f x‖ₑ) (Real.sqrt s)) := by
  have hdt : 0 < d * t := mul_pos hd ht
  set h : α → E := Set.indicator {x : α | ENNReal.ofReal (d * t) < ‖f x‖ₑ}ᶜ f with hh
  have hhi : Integrable h μ := by
    rw [hh]; exact integrable_indicator_ofReal_lt_enorm_compl hf (d * t)
  have h2t : (2:ℝ≥0∞).toReal = (2:ℝ) := by norm_num
  have hcheb : ENNReal.ofReal (t/2)^(2:ℝ) * innerTail ν (fun x => ‖T h x‖ₑ) (t/2)
      ≤ ∫⁻ x, ‖T h x‖ₑ ^ (2:ℝ) ∂ν :=
    pow_mul_innerTail_le (μ := ν) (W := fun x => ‖T h x‖ₑ) (u := t/2) (p := 2)
      (by positivity) (by norm_num)
  have hsquare : ENNReal.ofReal (t/2) ^ (2:ℝ) = ENNReal.ofReal ((t/2)^2) := by
    rw [rpow_two_eq, ← ENNReal.ofReal_pow (by positivity)]
  have heLph : (eLpNorm h 2 μ) ^ (2:ℝ) = ∫⁻ x, ‖h x‖ₑ ^ (2:ℝ) ∂μ := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (p := (2:ℝ≥0∞)) (by norm_num) (by norm_num)
      hhi.aestronglyMeasurable]
    simp_rw [h2t]
    rw [← ENNReal.rpow_mul, show (1:ℝ)/2 * 2 = 1 by norm_num, ENNReal.rpow_one]
  have heLpTh : ∫⁻ x, ‖T h x‖ₑ ^ (2:ℝ) ∂ν ≤ (eLpNorm (T h) 2 ν) ^ (2:ℝ) := by
    by_cases hTh : AEStronglyMeasurable (T h) ν
    · rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (p := (2:ℝ≥0∞)) (by norm_num) (by norm_num) hTh]
      simp_rw [h2t]
      rw [← ENNReal.rpow_mul, show (1:ℝ)/2 * 2 = 1 by norm_num, ENNReal.rpow_one]
    · rw [eLpNorm_of_not_aestronglyMeasurable hTh, ENNReal.top_rpow_of_pos (by norm_num)]
      exact le_top
  have hne0 : ENNReal.ofReal ((t/2)^2) ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    positivity
  have hnetop : ENNReal.ofReal ((t/2)^2) ≠ ∞ := ENNReal.ofReal_ne_top
  have hcheb' : ENNReal.ofReal ((t/2)^2) * innerTail ν (fun x => ‖T h x‖ₑ) (t/2)
      ≤ eLpNorm (T h) 2 ν ^ (2:ℝ) := by
    rw [← hsquare]
    exact hcheb.trans heLpTh
  have hstrong' : (eLpNorm (T h) 2 ν) ^ (2:ℝ)
      ≤ ENNReal.ofReal (A1^2) * (∫⁻ x, ‖h x‖ₑ ^ (2:ℝ) ∂μ) := by
    calc (eLpNorm (T h) 2 ν) ^ (2:ℝ) ≤ (ENNReal.ofReal A1 * eLpNorm h 2 μ) ^ (2:ℝ) :=
          ENNReal.rpow_le_rpow (hstrong h hhi) (by norm_num)
      _ = (ENNReal.ofReal A1) ^ (2:ℝ) * (eLpNorm h 2 μ) ^ (2:ℝ) :=
          ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
      _ = ENNReal.ofReal (A1^2) * ∫⁻ x, ‖h x‖ₑ ^ (2:ℝ) ∂μ := by rw [heLph, ofReal_sq A1 hA1.le]
  have hmain : innerTail ν (fun x => ‖T h x‖ₑ) (t/2)
      ≤ (ENNReal.ofReal ((t/2)^2))⁻¹ *
          (ENNReal.ofReal (A1^2) * ∫⁻ x, ‖h x‖ₑ ^ (2:ℝ) ∂μ) := by
    have hkey : ENNReal.ofReal ((t/2)^2) * innerTail ν (fun x => ‖T h x‖ₑ) (t/2)
        ≤ ENNReal.ofReal ((t/2)^2) *
            ((ENNReal.ofReal ((t/2)^2))⁻¹ *
              (ENNReal.ofReal (A1^2) * ∫⁻ x, ‖h x‖ₑ ^ (2:ℝ) ∂μ)) := by
      calc ENNReal.ofReal ((t/2)^2) * innerTail ν (fun x => ‖T h x‖ₑ) (t/2)
          ≤ ENNReal.ofReal (A1^2) * (∫⁻ x, ‖h x‖ₑ ^ (2:ℝ) ∂μ) := hcheb'.trans hstrong'
        _ = ENNReal.ofReal ((t/2)^2) *
              ((ENNReal.ofReal ((t/2)^2))⁻¹ *
                (ENNReal.ofReal (A1^2) * ∫⁻ x, ‖h x‖ₑ ^ (2:ℝ) ∂μ)) := by
            nth_rewrite 1 [← mul_assoc]
            rw [ENNReal.mul_inv_cancel hne0 hnetop, one_mul]
    calc innerTail ν (fun x => ‖T h x‖ₑ) (t/2)
        = (ENNReal.ofReal ((t/2)^2))⁻¹ *
            (ENNReal.ofReal ((t/2)^2) * innerTail ν (fun x => ‖T h x‖ₑ) (t/2)) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hne0 hnetop, one_mul]
      _ ≤ (ENNReal.ofReal ((t/2)^2))⁻¹ *
            (ENNReal.ofReal ((t/2)^2) *
              ((ENNReal.ofReal ((t/2)^2))⁻¹ *
                (ENNReal.ofReal (A1^2) * ∫⁻ x, ‖h x‖ₑ ^ (2:ℝ) ∂μ))) :=
          mul_le_mul_right hkey _
      _ = _ := by
          nth_rewrite 1 [← mul_assoc]
          rw [ENNReal.inv_mul_cancel hne0 hnetop, one_mul]
  have hL : (∫⁻ x, ‖h x‖ₑ ^ (2:ℝ) ∂μ)
      = ∫⁻ x, Set.indicator {x : α | ‖f x‖ₑ ≤ ENNReal.ofReal (d * t)} (fun x => ‖f x‖ₑ ^ 2) x ∂μ := by
    refine lintegral_congr fun x => ?_
    have hset : {x : α | ENNReal.ofReal (d * t) < ‖f x‖ₑ}ᶜ
        = {x : α | ‖f x‖ₑ ≤ ENNReal.ofReal (d * t)} := by
      ext y
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt]
    have h1 : ‖h x‖ₑ
        = Set.indicator {x : α | ENNReal.ofReal (d * t) < ‖f x‖ₑ}ᶜ (fun x => ‖f x‖ₑ) x := by
      show ‖Set.indicator {x : α | ENNReal.ofReal (d * t) < ‖f x‖ₑ}ᶜ f x‖ₑ = _
      exact enorm_indicator_eq_indicator_enorm f x
    rw [h1, hset]
    exact banach_trunc_sq (fun x => ‖f x‖ₑ) _ x
  have hlow := lintegral_indicator_low_le (μ := μ) (W := fun x => ‖f x‖ₑ) hdt
  have hcoef : ENNReal.ofReal (t ^ (p-1)) * (ENNReal.ofReal ((t/2)^2))⁻¹
      = ENNReal.ofReal (4 * t ^ (p-3)) := by
    rw [← ENNReal.ofReal_inv_of_pos (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have h1 : ((t/2)^2)⁻¹ = 4 * t^(-2:ℝ) := by
      have ha : t^(-2:ℝ) = (t^(2:ℝ))⁻¹ := by
        rw [show (-2:ℝ) = -(2:ℝ) by norm_num, Real.rpow_neg ht.le]
      have hb : t^(2:ℝ) = t^2 := by norm_num
      rw [ha, hb]
      field_simp
      ring
    rw [h1]
    have h2 : t ^ (p-1) * t^(-2:ℝ) = t^(p-3) := by
      rw [← Real.rpow_add ht (p-1) (-2), show p - 1 + (-2) = p - 3 by ring]
    calc t ^ (p-1) * (4 * t^(-2:ℝ)) = 4 * (t^(p-1) * t^(-2:ℝ)) := by ring
      _ = 4 * t^(p-3) := by rw [h2]
  have hcoef2 : ENNReal.ofReal (4 * t ^ (p-3)) * ENNReal.ofReal (A1^2)
      = ENNReal.ofReal (4 * A1^2 * t ^ (p-3)) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  calc ENNReal.ofReal (t ^ (p - 1)) * innerTail ν (fun x => ‖T h x‖ₑ) (t/2)
      ≤ ENNReal.ofReal (t ^ (p-1)) *
          ((ENNReal.ofReal ((t/2)^2))⁻¹ *
            (ENNReal.ofReal (A1^2) * ∫⁻ x, ‖h x‖ₑ ^ (2:ℝ) ∂μ)) := mul_le_mul_right hmain _
    _ = (ENNReal.ofReal (t ^ (p-1)) * (ENNReal.ofReal ((t/2)^2))⁻¹) *
          (ENNReal.ofReal (A1^2) * ∫⁻ x, ‖h x‖ₑ ^ (2:ℝ) ∂μ) := by rw [mul_assoc]
    _ = (ENNReal.ofReal (4 * t ^ (p-3)) * ENNReal.ofReal (A1^2)) *
          ∫⁻ x, ‖h x‖ₑ ^ (2:ℝ) ∂μ := by rw [hcoef, mul_assoc]
    _ = ENNReal.ofReal (4 * A1^2 * t ^ (p-3)) *
          ∫⁻ x, ‖h x‖ₑ ^ (2:ℝ) ∂μ := by rw [hcoef2]
    _ = ENNReal.ofReal (4 * A1^2 * t ^ (p-3)) *
          (∫⁻ x, Set.indicator {x : α | ‖f x‖ₑ ≤ ENNReal.ofReal (d * t)} (fun x => ‖f x‖ₑ ^ 2) x ∂μ) := by
        rw [hL]
    _ ≤ ENNReal.ofReal (4 * A1^2 * t ^ (p-3)) *
          (∫⁻ s in Set.Ioc (0:ℝ) ((d * t) ^ 2), innerTail μ (fun x => ‖f x‖ₑ) (Real.sqrt s)) :=
        mul_le_mul_right hlow _


/-! ## Rescaling and constant identities -/

lemma rpow_scale_high {s d p : ℝ} (hs : 0 ≤ s) (hd : 0 < d) :
    (2 / d) ^ (p - 1) / (p - 1) * s ^ (p - 1) = (2 * s / d) ^ (p - 1) / (p - 1) := by
  rw [div_mul_eq_mul_div, ← Real.mul_rpow (by positivity : (0:ℝ) ≤ 2/d) hs]
  have h : (2/d) * s = 2 * s / d := by ring
  rw [h]

lemma rpow_scale_low {s d p : ℝ} (hs : 0 ≤ s) (hd : 0 < d) :
    (Real.sqrt s / d) ^ (p - 2) / (2 - p)
      = d ^ (2 - p) * ((Real.sqrt s) ^ (p - 2) / (2 - p)) := by
  have h : (Real.sqrt s / d) ^ (p - 2) = d ^ (2 - p) * (Real.sqrt s) ^ (p - 2) := by
    rw [div_eq_mul_inv, Real.mul_rpow (Real.sqrt_nonneg s) (inv_nonneg.2 hd.le),
      Real.inv_rpow hd.le,
      show (d ^ (p - 2))⁻¹ = d ^ (2 - p) by
        rw [← Real.rpow_neg hd.le]; congr 1; ring]
    ring
  rw [h, mul_div_assoc]

lemma sharp_const_high {A0 A1 p : ℝ} (hA0 : 0 < A0) (hA1 : 0 < A1) :
    12 * A0 * (2 / (A0 / A1^2)) ^ (p-1) / (p-1)
      = 12 * 2^(p-1) / (p-1) * A0^(2-p) * A1^(2*p-2) := by
  have hA1sq : (A1^2 : ℝ) = A1^(2:ℝ) := (Real.rpow_natCast A1 2).symm
  have hquot : 2 / (A0 / A1^2) = 2 * (A1^2 / A0) := by field_simp
  rw [hquot, Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (by positivity : (0:ℝ) ≤ A1^2 / A0),
      Real.div_rpow (by positivity : (0:ℝ) ≤ A1^2) hA0.le]
  rw [hA1sq]
  rw [show (A1^(2:ℝ))^(p-1) = A1^(2*p-2) by
        rw [← Real.rpow_mul hA1.le]; congr 1; ring]
  have hdiv : A1 ^ (2*p-2) / A0 ^ (p-1) = A1 ^ (2*p-2) * A0^(1-p) := by
    rw [show A0^(1-p) = (A0 ^ (p-1))⁻¹ by
          rw [show 1-p = -(p-1) by ring, Real.rpow_neg hA0.le]]
    ring
  have hA0mul : A0 * A0^(1-p) = A0^(2-p) := by
    rw [show (2:ℝ)-p = 1 + (1-p) by ring, Real.rpow_add hA0, Real.rpow_one]
  rw [hdiv]
  calc 12 * A0 * (2 ^ (p - 1) * (A1 ^ (2*p-2) * A0 ^ (1 - p))) / (p - 1)
      = 12 * 2^(p-1) * (A0 * A0^(1-p)) * A1^(2*p-2) / (p-1) := by ring
    _ = 12 * 2^(p-1) * A0^(2-p) * A1^(2*p-2) / (p-1) := by rw [hA0mul]
    _ = 12 * 2^(p-1) / (p-1) * A0^(2-p) * A1^(2*p-2) := by ring

lemma sharp_const_low {A0 A1 p : ℝ} (hA0 : 0 < A0) (hA1 : 0 < A1) :
    16 * A1^2 * (A0 / A1^2)^(2-p) / (2-p)
      = 16 / (2-p) * A0^(2-p) * A1^(2*p-2) := by
  have hA1sq : (A1^2 : ℝ) = A1^(2:ℝ) := (Real.rpow_natCast A1 2).symm
  rw [hA1sq]
  rw [Real.div_rpow hA0.le (by positivity : (0:ℝ) ≤ A1^(2:ℝ))]
  rw [show (A1^(2:ℝ))^(2-p) = A1^(2*(2-p)) by rw [← Real.rpow_mul hA1.le]]
  have hinv : (A1 ^ (2*(2-p)))⁻¹ = A1 ^ (-(2*(2-p))) := by
    rw [← Real.rpow_neg hA1.le]
  have hone : A1^(2:ℝ) * A1^(-(2*(2-p))) = A1^(2*p-2) := by
    rw [← Real.rpow_add hA1]; congr 1; ring
  rw [div_eq_mul_inv]
  calc 16 * A1^(2:ℝ) * (A0 ^ (2 - p) * (A1 ^ (2*(2-p)))⁻¹) * (2 - p)⁻¹
      = 16 * A0^(2-p) * (A1^(2:ℝ) * A1^(-(2*(2-p)))) * (2-p)⁻¹ := by rw [hinv]; ring
    _ = 16 * A0^(2-p) * A1^(2*p-2) * (2-p)⁻¹ := by rw [hone]
    _ = 16 / (2-p) * A0^(2-p) * A1^(2*p-2) := by ring

lemma sharp_final_const {p A0 A1 Bc : ℝ} (hA0 : 0 < A0) (hA1 : 0 < A1) (hBc : 0 < Bc)
    (hp1 : 1 < p) :
    (Bc * A0^(2-p) * A1^(2*p-2))^(1/p) = Bc^(1/p) * A0^(2/p-1) * A1^(2-2/p) := by
  have hpne : p ≠ 0 := by linarith
  rw [Real.mul_rpow (by positivity : (0:ℝ) ≤ Bc * A0^(2-p)) (Real.rpow_nonneg hA1.le _),
      Real.mul_rpow (le_of_lt hBc) (Real.rpow_nonneg hA0.le _),
      ← Real.rpow_mul hA0.le, ← Real.rpow_mul hA1.le]
  have h1 : (2-p)*(1/p) = 2/p-1 := by field_simp
  have h2 : (2*p-2)*(1/p) = 2-2/p := by field_simp
  rw [h1, h2]

theorem marcinkiewicz_weak_one_strong_two_integrable_sharp {α β E : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSpace E] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : MeasureTheory.Measure α} {ν : MeasureTheory.Measure β} {p : ℝ} (hp1 : 1 < p)
    (hp2 : p < 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : (α → E) → (β → E)),
      (∀ f g : α → E, MeasureTheory.Integrable f μ → MeasureTheory.Integrable g μ →
        T (f + g) = T f + T g) →
      ∀ (A0 A1 : ℝ), 0 < A0 → 0 < A1 →
      (∀ (f : α → E) (lam : ℝ), MeasureTheory.Integrable f μ → 0 < lam →
        ν {x : β | lam < ‖T f x‖} ≤ ENNReal.ofReal (A0 / lam) * MeasureTheory.eLpNorm f 1 μ) →
      (∀ f : α → E, MeasureTheory.Integrable f μ →
        MeasureTheory.eLpNorm (T f) 2 ν ≤ ENNReal.ofReal A1 * MeasureTheory.eLpNorm f 2 μ) →
      ∀ f : α → E, MeasureTheory.Integrable f μ →
        MeasureTheory.eLpNorm (T f) (ENNReal.ofReal p) ν
          ≤ ENNReal.ofReal (C * A0 ^ (2 / p - 1) * A1 ^ (2 - 2 / p))
              * MeasureTheory.eLpNorm f (ENNReal.ofReal p) μ := by
  have hp0 : 0 < p := by linarith
  have hp1pos : 0 < p - 1 := by linarith
  have h2p : 0 < 2 - p := by linarith
  set Bc : ℝ := 12 * 2^(p-1)/(p-1) + 16/(2-p) with hBcdef
  have hBcpos : 0 < Bc := by
    rw [hBcdef]
    have h1 : 0 < 12 * 2^(p-1)/(p-1) := by positivity
    have h2 : 0 < 16/(2-p) := by positivity
    linarith
  set C : ℝ := Bc^(1/p) with hCdef
  have hCpos : 0 < C := by rw [hCdef]; exact Real.rpow_pos_of_pos hBcpos _
  refine ⟨C, hCpos, ?_⟩
  intro T hadd A0 A1 hA0 hA1 hweak hstrong f hint
  set d : ℝ := A0 / A1^2 with hddef
  have hd : 0 < d := by rw [hddef]; positivity
  by_cases hfin : eLpNorm f (ENNReal.ofReal p) μ = ∞
  · have hc : ENNReal.ofReal (C * A0 ^ (2 / p - 1) * A1 ^ (2 - 2 / p)) ≠ 0 :=
      (ENNReal.ofReal_pos.mpr (mul_pos (mul_pos hCpos (Real.rpow_pos_of_pos hA0 _))
        (Real.rpow_pos_of_pos hA1 _))).ne'
    rw [hfin, ENNReal.mul_top hc]
    exact le_top
  have hTm : AEStronglyMeasurable (T f) ν :=
    integrable_aestronglyMeasurable_T T hadd hweak hstrong hp1 hp2 hint hfin
  have htoReal : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp0.le
  have hpne : (ENNReal.ofReal p) ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hp0
  have hTf : eLpNorm (T f) (ENNReal.ofReal p) ν = (∫⁻ x, ‖T f x‖ₑ ^ p ∂ν) ^ (1/p) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (p := ENNReal.ofReal p) hpne ENNReal.ofReal_ne_top
      hTm, htoReal]
  have hf : eLpNorm f (ENNReal.ofReal p) μ = (∫⁻ x, ‖f x‖ₑ ^ p ∂μ) ^ (1/p) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (p := ENNReal.ofReal p) hpne ENNReal.ofReal_ne_top
      hint.aestronglyMeasurable, htoReal]
  rw [hTf, hf]
  have hmain : ∫⁻ x, ‖T f x‖ₑ ^ p ∂ν
      ≤ ENNReal.ofReal (Bc * A0^(2-p) * A1^(2*p-2)) * ∫⁻ x, ‖f x‖ₑ ^ p ∂μ := by
    have hconst : 12*A0*(2/d)^(p-1)/(p-1) + 16*A1^2*d^(2-p)/(2-p) = Bc*A0^(2-p)*A1^(2*p-2) := by
      rw [hBcdef, hddef, sharp_const_high hA0 hA1, sharp_const_low hA0 hA1]; ring
    have hmaj : ∀ t : ℝ, 0 < t →
        innerTail ν (fun x => ‖T f x‖ₑ) t * ENNReal.ofReal (t^(p-1))
          ≤ ENNReal.ofReal (6 * A0 * t^(p-2)) * (∫⁻ s in Set.Ioi (d*t/2), innerTail μ (fun x => ‖f x‖ₑ) s)
          + ENNReal.ofReal (4 * A1^2 * t^(p-3)) * (∫⁻ s in Set.Ioc (0:ℝ) ((d*t)^2), innerTail μ (fun x => ‖f x‖ₑ) (Real.sqrt s)) := by
      intro t ht
      have h3 := sharp_high_pointwise (A0 := A0) (p := p) (d := d) (T := T) (f := f) hA0 hp1 hd hint hweak ht
      have h4 := sharp_low_pointwise (A1 := A1) (p := p) (d := d) (T := T) (f := f) hA1 hp1 hd hint hstrong ht
      have hWVM : ∀ x, ‖T f x‖ₑ ≤
          ‖T (Set.indicator {y : α | ENNReal.ofReal (d*t) < ‖f y‖ₑ}ᶜ f) x‖ₑ
            + ENNReal.ofReal (‖T (Set.indicator {y : α | ENNReal.ofReal (d*t) < ‖f y‖ₑ} f) x‖) := by
        intro x
        have hsum : Set.indicator {y : α | ENNReal.ofReal (d*t) < ‖f y‖ₑ} f
            + Set.indicator {y : α | ENNReal.ofReal (d*t) < ‖f y‖ₑ}ᶜ f = f := banach_indicator_add_compl f
        have hkey : ‖T f x‖ₑ ≤ ‖T (Set.indicator {y : α | ENNReal.ofReal (d*t) < ‖f y‖ₑ} f) x‖ₑ
            + ‖T (Set.indicator {y : α | ENNReal.ofReal (d*t) < ‖f y‖ₑ}ᶜ f) x‖ₑ := by
          conv_lhs => rw [← hsum, hadd (Set.indicator {y : α | ENNReal.ofReal (d*t) < ‖f y‖ₑ} f)
            (Set.indicator {y : α | ENNReal.ofReal (d*t) < ‖f y‖ₑ}ᶜ f)
            (integrable_indicator_ofReal_lt_enorm hint (d*t))
            (integrable_indicator_ofReal_lt_enorm_compl hint (d*t))]
          exact enorm_add_le _ _
        calc ‖T f x‖ₑ ≤ ‖T (Set.indicator {y : α | ENNReal.ofReal (d*t) < ‖f y‖ₑ} f) x‖ₑ
              + ‖T (Set.indicator {y : α | ENNReal.ofReal (d*t) < ‖f y‖ₑ}ᶜ f) x‖ₑ := hkey
          _ = ‖T (Set.indicator {y : α | ENNReal.ofReal (d*t) < ‖f y‖ₑ}ᶜ f) x‖ₑ
              + ENNReal.ofReal (‖T (Set.indicator {y : α | ENNReal.ofReal (d*t) < ‖f y‖ₑ} f) x‖) := by
              rw [ofReal_norm]; ring
      have hdec := banach_innerTail_le (ν := ν) (W := fun x => ‖T f x‖ₑ)
          (V := fun x => ‖T (Set.indicator {y : α | ENNReal.ofReal (d*t) < ‖f y‖ₑ}ᶜ f) x‖ₑ)
          (w := fun x => ‖T (Set.indicator {y : α | ENNReal.ofReal (d*t) < ‖f y‖ₑ} f) x‖) hWVM ht
      calc innerTail ν (fun x => ‖T f x‖ₑ) t * ENNReal.ofReal (t^(p-1))
          ≤ (ν {a : β | t/2 < ‖T (Set.indicator {y : α | ENNReal.ofReal (d*t) < ‖f y‖ₑ} f) a‖}
              + innerTail ν (fun a => ‖T (Set.indicator {y : α | ENNReal.ofReal (d*t) < ‖f y‖ₑ}ᶜ f) a‖ₑ) (t/2))
              * ENNReal.ofReal (t^(p-1)) := mul_le_mul_left hdec _
        _ = ENNReal.ofReal (t^(p-1)) * ν {a : β | t/2 < ‖T (Set.indicator {y : α | ENNReal.ofReal (d*t) < ‖f y‖ₑ} f) a‖}
              + ENNReal.ofReal (t^(p-1)) * innerTail ν (fun a => ‖T (Set.indicator {y : α | ENNReal.ofReal (d*t) < ‖f y‖ₑ}ᶜ f) a‖ₑ) (t/2) := by ring
        _ ≤ _ := add_le_add h3 h4
    have hInt : ∫⁻ t in Set.Ioi (0:ℝ), innerTail ν (fun x => ‖T f x‖ₑ) t * ENNReal.ofReal (t^(p-1))
        ≤ ∫⁻ t in Set.Ioi (0:ℝ),
            (ENNReal.ofReal (6 * A0 * t^(p-2)) * (∫⁻ s in Set.Ioi (d*t/2), innerTail μ (fun x => ‖f x‖ₑ) s)
            + ENNReal.ofReal (4 * A1^2 * t^(p-3)) * (∫⁻ s in Set.Ioc (0:ℝ) ((d*t)^2), innerTail μ (fun x => ‖f x‖ₑ) (Real.sqrt s))) := by
      refine lintegral_mono_ae ?_
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
      exact hmaj t ht
    have hMA : Measurable (fun t : ℝ => ENNReal.ofReal (6 * A0 * t^(p-2)) *
        (∫⁻ s in Set.Ioi (d*t/2), innerTail μ (fun x => ‖f x‖ₑ) s)) :=
      (measurable_ofReal_mul_rpow (c := 6 * A0) (q := p-2)).mul
        ((measurable_lintegral_Ioi_half (innerTail_measurable μ _)).comp (measurable_const.mul measurable_id))
    have hML : Measurable (fun t : ℝ => ENNReal.ofReal (4 * A1^2 * t^(p-3)) *
        (∫⁻ s in Set.Ioc (0:ℝ) ((d*t)^2), innerTail μ (fun x => ‖f x‖ₑ) (Real.sqrt s))) :=
      (measurable_ofReal_mul_rpow (c := 4 * A1^2) (q := p-3)).mul
        ((measurable_lintegral_Ioc_sq (innerTail_measurable μ _)).comp (measurable_const.mul measurable_id))
    have hsplit := lintegral_add_left' (μ := volume.restrict (Set.Ioi (0:ℝ))) hMA.aemeasurable
        (fun t : ℝ => ENNReal.ofReal (4 * A1^2 * t^(p-3)) *
          (∫⁻ s in Set.Ioc (0:ℝ) ((d*t)^2), innerTail μ (fun x => ‖f x‖ₑ) (Real.sqrt s)))
    have hHigh : ∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (6 * A0 * t^(p-2)) *
          (∫⁻ s in Set.Ioi (d*t/2), innerTail μ (fun x => ‖f x‖ₑ) s)
        ≤ ENNReal.ofReal (6 * A0) * ENNReal.ofReal ((2/d)^(p-1)/(p-1)) *
            (∫⁻ s in Set.Ioi (0:ℝ), innerTail μ (fun x => ‖f x‖ₑ) s * ENNReal.ofReal (s^(p-1))) := by
      have hTi : Measurable (innerTail μ (fun x => ‖f x‖ₑ)) := innerTail_measurable μ _
      have hc : Measurable (fun t : ℝ => ENNReal.ofReal (6 * A0 * t^(p-2))) :=
        measurable_ofReal_mul_rpow (c := 6 * A0) (q := p-2)
      calc ∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (6 * A0 * t^(p-2)) *
            (∫⁻ s in Set.Ioi (d*t/2), innerTail μ (fun x => ‖f x‖ₑ) s)
          = ∫⁻ s in Set.Ioi (0:ℝ), innerTail μ (fun x => ‖f x‖ₑ) s *
              (∫⁻ t in Set.Ioo (0:ℝ) (2*s/d), ENNReal.ofReal (6 * A0 * t^(p-2))) :=
            lintegral_Ioi_mul_Ioi_half hc hTi hd
        _ = ∫⁻ s in Set.Ioi (0:ℝ), innerTail μ (fun x => ‖f x‖ₑ) s *
              (ENNReal.ofReal (6 * A0) * ∫⁻ t in Set.Ioo (0:ℝ) (2*s/d), ENNReal.ofReal (t^(p-2))) := by
            refine lintegral_congr fun s => ?_
            congr 1
            rw [show (∫⁻ t in Set.Ioo (0:ℝ) (2*s/d), ENNReal.ofReal (6 * A0 * t^(p-2)))
                = ∫⁻ t in Set.Ioo (0:ℝ) (2*s/d), ENNReal.ofReal (6 * A0) * ENNReal.ofReal (t^(p-2)) from
                lintegral_congr fun t => ENNReal.ofReal_mul (by positivity),
              lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        _ = ∫⁻ s in Set.Ioi (0:ℝ), innerTail μ (fun x => ‖f x‖ₑ) s *
              (ENNReal.ofReal (6 * A0) * ENNReal.ofReal ((2*s/d)^(p-1)/(p-1))) := by
            refine lintegral_congr_ae ?_
            filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
            congr 1; congr 1
            rw [lintegral_Ioo_ofReal_rpow (X := 2*s/d) (q := p-2) (by linarith)
                (le_of_lt (div_pos (mul_pos (by norm_num) hs) hd)), show p - 2 + 1 = p - 1 by ring]
        _ = ∫⁻ s in Set.Ioi (0:ℝ), innerTail μ (fun x => ‖f x‖ₑ) s *
              (ENNReal.ofReal (6 * A0) * (ENNReal.ofReal ((2/d)^(p-1)/(p-1)) * ENNReal.ofReal (s^(p-1)))) := by
            refine lintegral_congr_ae ?_
            filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
            congr 1; congr 1
            rw [← rpow_scale_high (le_of_lt hs) hd,
                ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ (2/d)^(p-1)/(p-1))]
        _ = ENNReal.ofReal (6 * A0) * ENNReal.ofReal ((2/d)^(p-1)/(p-1)) *
              (∫⁻ s in Set.Ioi (0:ℝ), innerTail μ (fun x => ‖f x‖ₑ) s * ENNReal.ofReal (s^(p-1))) := by
            refine Eq.trans (lintegral_congr fun s => ?_)
              (lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top))
            ring
        _ ≤ ENNReal.ofReal (6 * A0) * ENNReal.ofReal ((2/d)^(p-1)/(p-1)) *
              (∫⁻ s in Set.Ioi (0:ℝ), innerTail μ (fun x => ‖f x‖ₑ) s * ENNReal.ofReal (s^(p-1))) := le_rfl
    have hLow : ∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (4 * A1^2 * t^(p-3)) *
          (∫⁻ s in Set.Ioc (0:ℝ) ((d*t)^2), innerTail μ (fun x => ‖f x‖ₑ) (Real.sqrt s))
        ≤ ENNReal.ofReal (4 * A1^2) * ENNReal.ofReal (d^(2-p)) * ENNReal.ofReal (1/(2-p)) *
            (∫⁻ s in Set.Ioi (0:ℝ), innerTail μ (fun x => ‖f x‖ₑ) (Real.sqrt s) * ENNReal.ofReal (s^((p-2)/2))) := by
      have hTi : Measurable (innerTail μ (fun x => ‖f x‖ₑ)) := innerTail_measurable μ _
      have hTs : Measurable (fun s : ℝ => innerTail μ (fun x => ‖f x‖ₑ) (Real.sqrt s)) :=
        hTi.comp Real.continuous_sqrt.measurable
      have hc : Measurable (fun t : ℝ => ENNReal.ofReal (4 * A1^2 * t^(p-3))) :=
        measurable_ofReal_mul_rpow (c := 4 * A1^2) (q := p-3)
      calc ∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (4 * A1^2 * t^(p-3)) *
            (∫⁻ s in Set.Ioc (0:ℝ) ((d*t)^2), innerTail μ (fun x => ‖f x‖ₑ) (Real.sqrt s))
          = ∫⁻ s in Set.Ioi (0:ℝ), innerTail μ (fun x => ‖f x‖ₑ) (Real.sqrt s) *
              (∫⁻ t in Set.Ioi (Real.sqrt s / d), ENNReal.ofReal (4 * A1^2 * t^(p-3))) :=
            lintegral_Ioi_mul_Ioc_sq hc hTs hd
        _ = ∫⁻ s in Set.Ioi (0:ℝ), innerTail μ (fun x => ‖f x‖ₑ) (Real.sqrt s) *
              (ENNReal.ofReal (4 * A1^2) * ∫⁻ t in Set.Ioi (Real.sqrt s / d), ENNReal.ofReal (t^(p-3))) := by
            refine lintegral_congr fun s => ?_
            congr 1
            rw [show (∫⁻ t in Set.Ioi (Real.sqrt s / d), ENNReal.ofReal (4 * A1^2 * t^(p-3)))
                = ∫⁻ t in Set.Ioi (Real.sqrt s / d), ENNReal.ofReal (4 * A1^2) * ENNReal.ofReal (t^(p-3)) from
                lintegral_congr fun t => ENNReal.ofReal_mul (by positivity),
              lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        _ = ∫⁻ s in Set.Ioi (0:ℝ), innerTail μ (fun x => ‖f x‖ₑ) (Real.sqrt s) *
              (ENNReal.ofReal (4 * A1^2) * ENNReal.ofReal ((Real.sqrt s / d)^(p-2)/(2-p))) := by
            refine lintegral_congr_ae ?_
            filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
            congr 1; congr 1
            rw [lintegral_Ioi_ofReal_rpow (X := Real.sqrt s / d) (q := p-3) (by linarith) (div_pos (Real.sqrt_pos.2 hs) hd)]
            rw [show p - 3 + 1 = p - 2 by ring, ← div_neg, show (-(p-2)) = 2-p by ring]
        _ = ∫⁻ s in Set.Ioi (0:ℝ), innerTail μ (fun x => ‖f x‖ₑ) (Real.sqrt s) *
              (ENNReal.ofReal (4 * A1^2) * (ENNReal.ofReal (d^(2-p)) * (ENNReal.ofReal (1/(2-p)) * ENNReal.ofReal (s^((p-2)/2))))) := by
            refine lintegral_congr_ae ?_
            filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
            congr 1; congr 1
            rw [rpow_scale_low (le_of_lt hs) hd,
                ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ d^(2-p)),
                ofReal_sqrt_rpow (le_of_lt hs) hp2]
        _ = ENNReal.ofReal (4 * A1^2) * ENNReal.ofReal (d^(2-p)) * ENNReal.ofReal (1/(2-p)) *
              (∫⁻ s in Set.Ioi (0:ℝ), innerTail μ (fun x => ‖f x‖ₑ) (Real.sqrt s) * ENNReal.ofReal (s^((p-2)/2))) := by
            refine Eq.trans (lintegral_congr fun s => ?_) (lintegral_const_mul' _ _ ?_)
            · ring
            · exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top
        _ ≤ ENNReal.ofReal (4 * A1^2) * ENNReal.ofReal (d^(2-p)) * ENNReal.ofReal (1/(2-p)) *
              (∫⁻ s in Set.Ioi (0:ℝ), innerTail μ (fun x => ‖f x‖ₑ) (Real.sqrt s) * ENNReal.ofReal (s^((p-2)/2))) := le_rfl
        _ ≤ ENNReal.ofReal (4 * A1^2) * ENNReal.ofReal (d^(2-p)) * ENNReal.ofReal (1/(2-p)) *
              (∫⁻ s in Set.Ioi (0:ℝ), innerTail μ (fun x => ‖f x‖ₑ) (Real.sqrt s) * ENNReal.ofReal (s^((p-2)/2))) := le_rfl
    have hWT : ENNReal.ofReal p * (∫⁻ s in Set.Ioi (0:ℝ), innerTail μ (fun x => ‖f x‖ₑ) s * ENNReal.ofReal (s^(p-1)))
        ≤ 2 * ∫⁻ x, ‖f x‖ₑ ^ p ∂μ := by
      rw [show (∫⁻ s in Set.Ioi (0:ℝ), innerTail μ (fun x => ‖f x‖ₑ) s * ENNReal.ofReal (s^(p-1)))
          = ∫⁻ s in Set.Ioi (0:ℝ), ENNReal.ofReal (s^(p-1)) * innerTail μ (fun x => ‖f x‖ₑ) s from
          lintegral_congr fun s => mul_comm _ _]
      exact rpow_mul_innerTail_integral_le (μ := μ) (W := fun x => ‖f x‖ₑ) hp1
    have hST : ENNReal.ofReal p * (∫⁻ s in Set.Ioi (0:ℝ), innerTail μ (fun x => ‖f x‖ₑ) (Real.sqrt s) * ENNReal.ofReal (s^((p-2)/2)))
        ≤ 4 * ∫⁻ x, ‖f x‖ₑ ^ p ∂μ := by
      rw [show (∫⁻ s in Set.Ioi (0:ℝ), innerTail μ (fun x => ‖f x‖ₑ) (Real.sqrt s) * ENNReal.ofReal (s^((p-2)/2)))
          = ∫⁻ s in Set.Ioi (0:ℝ), ENNReal.ofReal (s^((p-2)/2)) * innerTail μ (fun x => ‖f x‖ₑ) (Real.sqrt s) from
          lintegral_congr fun s => mul_comm _ _]
      exact sqrt_innerTail_integral_le (μ := μ) (W := fun x => ‖f x‖ₑ) hp1
    have hCH : ENNReal.ofReal (6 * A0) * ENNReal.ofReal ((2/d)^(p-1)/(p-1)) * 2
        = ENNReal.ofReal (12 * A0 * (2/d)^(p-1) / (p-1)) := by
      rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num,
        ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 6 * A0),
        ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 6 * A0 * ((2/d)^(p-1)/(p-1)))]
      congr 1; ring
    have hCL : ENNReal.ofReal (4 * A1^2) * ENNReal.ofReal (d^(2-p)) * ENNReal.ofReal (1/(2-p)) * 4
        = ENNReal.ofReal (16 * A1^2 * d^(2-p) / (2-p)) := by
      rw [show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by norm_num,
        ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 4 * A1^2),
        ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 4 * A1^2 * d^(2-p)),
        ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 4 * A1^2 * d^(2-p) * (1/(2-p)))]
      congr 1; ring
    have hHighB : ENNReal.ofReal p *
          (ENNReal.ofReal (6 * A0) * ENNReal.ofReal ((2/d)^(p-1)/(p-1)) *
            (∫⁻ s in Set.Ioi (0:ℝ), innerTail μ (fun x => ‖f x‖ₑ) s * ENNReal.ofReal (s^(p-1))))
        ≤ ENNReal.ofReal (12 * A0 * (2/d)^(p-1) / (p-1)) * ∫⁻ x, ‖f x‖ₑ ^ p ∂μ := by
      calc ENNReal.ofReal p *
            (ENNReal.ofReal (6 * A0) * ENNReal.ofReal ((2/d)^(p-1)/(p-1)) *
              (∫⁻ s in Set.Ioi (0:ℝ), innerTail μ (fun x => ‖f x‖ₑ) s * ENNReal.ofReal (s^(p-1))))
          = ENNReal.ofReal (6 * A0) * ENNReal.ofReal ((2/d)^(p-1)/(p-1)) *
              (ENNReal.ofReal p *
                (∫⁻ s in Set.Ioi (0:ℝ), innerTail μ (fun x => ‖f x‖ₑ) s * ENNReal.ofReal (s^(p-1)))) := by ring
        _ ≤ ENNReal.ofReal (6 * A0) * ENNReal.ofReal ((2/d)^(p-1)/(p-1)) * (2 * ∫⁻ x, ‖f x‖ₑ ^ p ∂μ) :=
            mul_le_mul_right hWT _
        _ = ENNReal.ofReal (12 * A0 * (2/d)^(p-1) / (p-1)) * ∫⁻ x, ‖f x‖ₑ ^ p ∂μ := by
            rw [← hCH]; ring
    have hLowB : ENNReal.ofReal p *
          (ENNReal.ofReal (4 * A1^2) * ENNReal.ofReal (d^(2-p)) * ENNReal.ofReal (1/(2-p)) *
            (∫⁻ s in Set.Ioi (0:ℝ), innerTail μ (fun x => ‖f x‖ₑ) (Real.sqrt s) * ENNReal.ofReal (s^((p-2)/2))))
        ≤ ENNReal.ofReal (16 * A1^2 * d^(2-p) / (2-p)) * ∫⁻ x, ‖f x‖ₑ ^ p ∂μ := by
      calc ENNReal.ofReal p *
            (ENNReal.ofReal (4 * A1^2) * ENNReal.ofReal (d^(2-p)) * ENNReal.ofReal (1/(2-p)) *
              (∫⁻ s in Set.Ioi (0:ℝ), innerTail μ (fun x => ‖f x‖ₑ) (Real.sqrt s) * ENNReal.ofReal (s^((p-2)/2))))
          = ENNReal.ofReal (4 * A1^2) * ENNReal.ofReal (d^(2-p)) * ENNReal.ofReal (1/(2-p)) *
              (ENNReal.ofReal p *
                (∫⁻ s in Set.Ioi (0:ℝ), innerTail μ (fun x => ‖f x‖ₑ) (Real.sqrt s) * ENNReal.ofReal (s^((p-2)/2)))) := by ring
        _ ≤ ENNReal.ofReal (4 * A1^2) * ENNReal.ofReal (d^(2-p)) * ENNReal.ofReal (1/(2-p)) * (4 * ∫⁻ x, ‖f x‖ₑ ^ p ∂μ) :=
            mul_le_mul_right hST _
        _ = ENNReal.ofReal (16 * A1^2 * d^(2-p) / (2-p)) * ∫⁻ x, ‖f x‖ₑ ^ p ∂μ := by
            rw [← hCL]; ring
    have hlayer := banach_lintegral_rpow_le_innerTail (ν := ν) (W := fun x => ‖T f x‖ₑ) (fun x => enorm_ne_top) hp0
    refine hlayer.trans ?_
    calc ENNReal.ofReal p * (∫⁻ t in Set.Ioi (0:ℝ), innerTail ν (fun x => ‖T f x‖ₑ) t * ENNReal.ofReal (t^(p-1)))
        ≤ ENNReal.ofReal p * (∫⁻ t in Set.Ioi (0:ℝ),
            (ENNReal.ofReal (6 * A0 * t^(p-2)) * (∫⁻ s in Set.Ioi (d*t/2), innerTail μ (fun x => ‖f x‖ₑ) s)
            + ENNReal.ofReal (4 * A1^2 * t^(p-3)) * (∫⁻ s in Set.Ioc (0:ℝ) ((d*t)^2), innerTail μ (fun x => ‖f x‖ₑ) (Real.sqrt s)))) :=
          mul_le_mul_right hInt _
      _ = ENNReal.ofReal p * (∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (6 * A0 * t^(p-2)) * (∫⁻ s in Set.Ioi (d*t/2), innerTail μ (fun x => ‖f x‖ₑ) s))
            + ENNReal.ofReal p * (∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (4 * A1^2 * t^(p-3)) * (∫⁻ s in Set.Ioc (0:ℝ) ((d*t)^2), innerTail μ (fun x => ‖f x‖ₑ) (Real.sqrt s))) := by
          rw [hsplit, mul_add]
      _ ≤ ENNReal.ofReal (12 * A0 * (2/d)^(p-1) / (p-1)) * ∫⁻ x, ‖f x‖ₑ ^ p ∂μ
            + ENNReal.ofReal (16 * A1^2 * d^(2-p) / (2-p)) * ∫⁻ x, ‖f x‖ₑ ^ p ∂μ :=
          add_le_add ((mul_le_mul_right hHigh _).trans hHighB) ((mul_le_mul_right hLow _).trans hLowB)
      _ = ENNReal.ofReal (12 * A0 * (2/d)^(p-1) / (p-1) + 16 * A1^2 * d^(2-p) / (2-p)) * ∫⁻ x, ‖f x‖ₑ ^ p ∂μ := by
          rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)]
      _ = ENNReal.ofReal (Bc * A0^(2-p) * A1^(2*p-2)) * ∫⁻ x, ‖f x‖ₑ ^ p ∂μ := by rw [hconst]
  calc (∫⁻ x, ‖T f x‖ₑ ^ p ∂ν) ^ (1/p)
      ≤ (ENNReal.ofReal (Bc * A0^(2-p) * A1^(2*p-2)) * ∫⁻ x, ‖f x‖ₑ ^ p ∂μ) ^ (1/p) :=
        ENNReal.rpow_le_rpow hmain (by positivity)
    _ = (ENNReal.ofReal (Bc * A0^(2-p) * A1^(2*p-2)))^(1/p) * (∫⁻ x, ‖f x‖ₑ ^ p ∂μ)^(1/p) :=
        ENNReal.mul_rpow_of_nonneg _ _ (by positivity)
    _ = ENNReal.ofReal ((Bc * A0^(2-p) * A1^(2*p-2))^(1/p)) * (∫⁻ x, ‖f x‖ₑ ^ p ∂μ)^(1/p) := by
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]
    _ = ENNReal.ofReal (C * A0^(2/p-1) * A1^(2-2/p)) * (∫⁻ x, ‖f x‖ₑ ^ p ∂μ)^(1/p) := by
        rw [hCdef, sharp_final_const hA0 hA1 hBcpos hp1]

end Commons.Analysis.MeasureTheory
