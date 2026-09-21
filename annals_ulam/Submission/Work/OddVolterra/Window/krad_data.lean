import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.Kernel.Diag

/-!
# Uniform data for the Abel radicand `krad` on the transition window

This file supplies the quantitative bounds on the radicand

`krad h σ t a = (t + hquot h a σ) (line h σ t + line h a t)`

of the Abel denominator `Kden h a σ t = √(krad h σ t a)` that the odd-case
transition-slope argument needs on the "window" region

`σ ∈ [7/10, 1]`, `|t| ∈ [1/5, 2]`, `a ∈ [9/20, σ]`.

There the perturbation is small in `C²` norm (`|h^{(k)}| ≤ δ ≤ 1/100`, `k ≤ 2`), so

* each of the two factors of `krad` has the sign of `t` and modulus bounded below
  (`≥ 19/100` for the first, `≥ 21/100` for the second), whence `1/100 ≤ krad`;
* `krad ≤ 10`, and its deviation from the unperturbed radicand
  `krad 0 σ t a = t²(σ + a)` is at most `10 δ`;
* `a ↦ krad h σ t a` is `5`-Lipschitz on the enclosing box `[3/8, 3/2]`, and the
  deviation `a ↦ krad h σ t a - krad 0 σ t a` is `10 δ`-Lipschitz there.

The Lipschitz constants are transferred to the two `deriv` bounds of `krad_data`
through the mean value inequality (`norm_deriv_le_of_lip'`).
-/

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

namespace Work.OddVolterra.Window

noncomputable section

set_option maxHeartbeats 1600000

/-! ## Elementary one-dimensional Lipschitz lemmas -/

/-- The mean value inequality in dimension one: a differentiable function whose
derivative is bounded by `C` is `C`-Lipschitz. -/
lemma abs_sub_le_mul_of_deriv_bound {f : ℝ → ℝ} {C : ℝ}
    (hdiff : ∀ x : ℝ, DifferentiableAt ℝ f x) (hbound : ∀ x : ℝ, |deriv f x| ≤ C)
    (x y : ℝ) : |f x - f y| ≤ C * |x - y| := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (s := Set.univ) (f := f) (C := C)
    (fun x _ => hdiff x) (fun x _ => by rw [Real.norm_eq_abs]; exact hbound x) convex_univ
    (Set.mem_univ y) (Set.mem_univ x)
  simpa [Real.norm_eq_abs, abs_sub_comm] using h

/-- The divided difference is bounded by any global bound of `|h'|`. -/
lemma abs_hquot_le {h : ℝ → ℝ} {ε a σ : ℝ} (hε : ∀ t : ℝ, |deriv h t| ≤ ε) :
    |hquot h a σ| ≤ ε := by
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
    (f := fun τ : ℝ => deriv h (a + τ * (σ - a))) (C := ε) (by
      intro τ _
      simpa [Real.norm_eq_abs] using hε (a + τ * (σ - a)))
  have hint' : ‖∫ τ in (0 : ℝ)..1, deriv h (a + τ * (σ - a))‖ ≤ ε := by
    simpa using hint
  simpa [hquot, Real.norm_eq_abs] using hint'

lemma hquot_zero (a σ : ℝ) : hquot (0 : ℝ → ℝ) a σ = 0 := by simp [hquot]

/-- `a ↦ hquot h a σ` is `δ`-Lipschitz as soon as `deriv h` is. -/
lemma abs_hquot_sub_le {h : ℝ → ℝ} {δ σ : ℝ} (hδ : 0 ≤ δ) (hcont : Continuous (deriv h))
    (hlip : ∀ x y : ℝ, |deriv h x - deriv h y| ≤ δ * |x - y|) (a b : ℝ) :
    |hquot h a σ - hquot h b σ| ≤ δ * |a - b| := by
  rw [hquot, hquot]
  have hi1 : IntervalIntegrable (fun τ : ℝ => deriv h (a + τ * (σ - a))) volume 0 1 :=
    (hcont.comp (by fun_prop : Continuous fun τ : ℝ => a + τ * (σ - a))).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun τ : ℝ => deriv h (b + τ * (σ - b))) volume 0 1 :=
    (hcont.comp (by fun_prop : Continuous fun τ : ℝ => b + τ * (σ - b))).intervalIntegrable _ _
  rw [← intervalIntegral.integral_sub hi1 hi2]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
    (f := fun τ : ℝ => deriv h (a + τ * (σ - a)) - deriv h (b + τ * (σ - b)))
    (C := δ * |a - b|) (by
      intro τ hτ
      rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hτ
      have hτ0 : 0 ≤ τ := le_of_lt hτ.1
      have hτ1 : τ ≤ 1 := hτ.2
      rw [Real.norm_eq_abs]
      have h1 := hlip (a + τ * (σ - a)) (b + τ * (σ - b))
      have hdiff : a + τ * (σ - a) - (b + τ * (σ - b)) = (a - b) * (1 - τ) := by ring
      rw [hdiff] at h1
      have h2 : |1 - τ| ≤ 1 := by rw [abs_le]; constructor <;> linarith
      calc |deriv h (a + τ * (σ - a)) - deriv h (b + τ * (σ - b))|
          ≤ δ * |(a - b) * (1 - τ)| := h1
        _ = δ * (|a - b| * |1 - τ|) := by rw [abs_mul]
        _ ≤ δ * (|a - b| * 1) := by
            apply mul_le_mul_of_nonneg_left _ hδ
            exact mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
        _ = δ * |a - b| := by ring)
  simpa using hb

/-! ## Lipschitz bounds for `krad` in its first slot -/

/-- On the box `a ∈ [3/8, 3/2]` (which contains the window `[9/20, σ]`), `krad h σ t ·`
is `5`-Lipschitz and its deviation from `krad 0 σ t ·` is `10δ`-Lipschitz. -/
lemma krad_lipschitz_window {h : ℝ → ℝ} {δ σ t : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 100)
    (h0 : ∀ x : ℝ, |h x| ≤ δ) (h1 : ∀ x : ℝ, |deriv h x| ≤ δ)
    (hliph : ∀ x y : ℝ, |h x - h y| ≤ δ * |x - y|)
    (hlip : ∀ x y : ℝ, |hquot h x σ - hquot h y σ| ≤ δ * |x - y|)
    (hσ1 : 7 / 10 ≤ σ) (hσ2 : σ ≤ 1) (ht2 : |t| ≤ 2) :
    (∀ a ∈ Set.Icc (3 / 8 : ℝ) (3 / 2), ∀ a' ∈ Set.Icc (3 / 8 : ℝ) (3 / 2),
      |krad h σ t a - krad h σ t a'| ≤ 5 * |a - a'|) ∧
    (∀ a ∈ Set.Icc (3 / 8 : ℝ) (3 / 2), ∀ a' ∈ Set.Icc (3 / 8 : ℝ) (3 / 2),
      |(krad h σ t a - krad 0 σ t a) - (krad h σ t a' - krad 0 σ t a')| ≤
        (10 * δ) * |a - a'|) := by
  have hK : ∀ a : ℝ, krad h σ t a
      = (t + hquot h a σ) * ((σ + a) * t + (h σ + h a)) := by
    intro a; rw [krad_apply]; unfold line; ring
  have hK0 : ∀ a : ℝ, krad 0 σ t a = t * ((σ + a) * t) := by
    intro a
    rw [krad_apply, hquot_zero]
    simp only [line, Pi.zero_apply, add_zero]
    ring
  have hD : ∀ a : ℝ, krad h σ t a - krad 0 σ t a
      = t * (h σ + h a) + hquot h a σ * ((σ + a) * t + (h σ + h a)) := by
    intro a; rw [hK a, hK0 a]; ring
  have hHbd : ∀ a : ℝ, |hquot h a σ| ≤ δ := fun a => abs_hquot_le h1
  have hsum : ∀ a : ℝ, |h σ + h a| ≤ 2 * δ := by
    intro a
    have h1' := abs_le.mp (h0 σ)
    have h2' := abs_le.mp (h0 a)
    rw [abs_le]; constructor <;> linarith [h1'.1, h1'.2, h2'.1, h2'.2]
  have hA : ∀ a : ℝ, |t + hquot h a σ| ≤ 201 / 100 := by
    intro a
    calc |t + hquot h a σ| ≤ |t| + |hquot h a σ| := abs_add_le _ _
      _ ≤ 2 + δ := by linarith [ht2, hHbd a]
      _ ≤ 201 / 100 := by linarith [hδ1]
  have hB : ∀ a ∈ Set.Icc (3 / 8 : ℝ) (3 / 2),
      |(σ + a) * t + (h σ + h a)| ≤ 251 / 50 := by
    intro a ha
    have ha0 : 0 ≤ σ + a := by linarith [hσ1, ha.1]
    have ha2 : σ + a ≤ 5 / 2 := by linarith [hσ2, ha.2]
    have habs : |σ + a| ≤ 5 / 2 := by rw [abs_of_nonneg ha0]; exact ha2
    calc |(σ + a) * t + (h σ + h a)| ≤ |(σ + a) * t| + |h σ + h a| := abs_add_le _ _
      _ = |σ + a| * |t| + |h σ + h a| := by rw [abs_mul]
      _ ≤ 5 / 2 * 2 + 2 * δ :=
          add_le_add (mul_le_mul habs ht2 (abs_nonneg _) (by norm_num)) (hsum a)
      _ ≤ 251 / 50 := by linarith [hδ1]
  have hBdiff : ∀ a ∈ Set.Icc (3 / 8 : ℝ) (3 / 2), ∀ a' ∈ Set.Icc (3 / 8 : ℝ) (3 / 2),
      |((σ + a) * t + (h σ + h a)) - ((σ + a') * t + (h σ + h a'))|
        ≤ 201 / 100 * |a - a'| := by
    intro a _ a' _
    have heq : ((σ + a) * t + (h σ + h a)) - ((σ + a') * t + (h σ + h a'))
        = (a - a') * t + (h a - h a') := by ring
    rw [heq]
    calc |(a - a') * t + (h a - h a')| ≤ |(a - a') * t| + |h a - h a'| := abs_add_le _ _
      _ = |a - a'| * |t| + |h a - h a'| := by rw [abs_mul]
      _ ≤ |a - a'| * 2 + δ * |a - a'| :=
          add_le_add (mul_le_mul_of_nonneg_left ht2 (abs_nonneg _)) (hliph a a')
      _ = (2 + δ) * |a - a'| := by ring
      _ ≤ 201 / 100 * |a - a'| := by
          apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
          linarith [hδ1]
  refine ⟨?_, ?_⟩
  · intro a ha a' ha'
    have h1 := hA a
    have h2 := hB a' ha'
    have h3 : |(t + hquot h a σ) - (t + hquot h a' σ)| ≤ δ * |a - a'| := by
      simpa using hlip a a'
    have h4 := hBdiff a ha a' ha'
    have h5 : |t + hquot h a σ|
        * |((σ + a) * t + (h σ + h a)) - ((σ + a') * t + (h σ + h a'))|
        ≤ (201 / 100) * (201 / 100 * |a - a'|) :=
      mul_le_mul h1 h4 (abs_nonneg _) (by norm_num)
    have h6 : |(t + hquot h a σ) - (t + hquot h a' σ)| * |(σ + a') * t + (h σ + h a')|
        ≤ (δ * |a - a'|) * (251 / 50) :=
      mul_le_mul h3 h2 (abs_nonneg _) (mul_nonneg hδ0 (abs_nonneg _))
    have hδb : δ * |a - a'| ≤ (1 / 100) * |a - a'| :=
      mul_le_mul_of_nonneg_right hδ1 (abs_nonneg _)
    have heq : krad h σ t a - krad h σ t a'
        = (t + hquot h a σ) * (((σ + a) * t + (h σ + h a)) - ((σ + a') * t + (h σ + h a')))
          + ((t + hquot h a σ) - (t + hquot h a' σ)) * ((σ + a') * t + (h σ + h a')) := by
      rw [hK a, hK a']; ring
    rw [heq]
    calc |(t + hquot h a σ) * (((σ + a) * t + (h σ + h a)) - ((σ + a') * t + (h σ + h a')))
            + ((t + hquot h a σ) - (t + hquot h a' σ)) * ((σ + a') * t + (h σ + h a'))|
        ≤ |(t + hquot h a σ) * (((σ + a) * t + (h σ + h a)) - ((σ + a') * t + (h σ + h a')))|
          + |((t + hquot h a σ) - (t + hquot h a' σ)) * ((σ + a') * t + (h σ + h a'))| :=
          abs_add_le _ _
      _ = |t + hquot h a σ|
            * |((σ + a) * t + (h σ + h a)) - ((σ + a') * t + (h σ + h a'))|
          + |(t + hquot h a σ) - (t + hquot h a' σ)| * |(σ + a') * t + (h σ + h a')| := by
          rw [abs_mul, abs_mul]
      _ ≤ (201 / 100) * (201 / 100 * |a - a'|) + (δ * |a - a'|) * (251 / 50) :=
          add_le_add h5 h6
      _ ≤ 5 * |a - a'| := by
          nlinarith [hδb, abs_nonneg (a - a'), hδ0, hδ1, mul_nonneg hδ0 (abs_nonneg (a - a'))]
  · intro a ha a' ha'
    have h2 := hB a' ha'
    have h3 : |hquot h a σ - hquot h a' σ| ≤ δ * |a - a'| := hlip a a'
    have h4 := hBdiff a ha a' ha'
    have h5 : |hquot h a σ|
        * |((σ + a) * t + (h σ + h a)) - ((σ + a') * t + (h σ + h a'))|
        ≤ δ * (201 / 100 * |a - a'|) :=
      mul_le_mul (hHbd a) h4 (abs_nonneg _) hδ0
    have h6 : |hquot h a σ - hquot h a' σ| * |(σ + a') * t + (h σ + h a')|
        ≤ (δ * |a - a'|) * (251 / 50) :=
      mul_le_mul h3 h2 (abs_nonneg _) (mul_nonneg hδ0 (abs_nonneg _))
    have h7 : |t * (h a - h a')| ≤ 2 * (δ * |a - a'|) := by
      rw [abs_mul]
      exact mul_le_mul ht2 (hliph a a') (abs_nonneg _) (by norm_num)
    have heq : (krad h σ t a - krad 0 σ t a) - (krad h σ t a' - krad 0 σ t a')
        = t * (h a - h a') + (hquot h a σ * ((σ + a) * t + (h σ + h a))
            - hquot h a' σ * ((σ + a') * t + (h σ + h a'))) := by
      rw [hD a, hD a']; ring
    rw [heq]
    calc |t * (h a - h a') + (hquot h a σ * ((σ + a) * t + (h σ + h a))
            - hquot h a' σ * ((σ + a') * t + (h σ + h a')))|
        ≤ |t * (h a - h a')|
          + |hquot h a σ * ((σ + a) * t + (h σ + h a))
              - hquot h a' σ * ((σ + a') * t + (h σ + h a'))| := abs_add_le _ _
      _ ≤ 2 * (δ * |a - a'|)
          + (δ * (201 / 100 * |a - a'|) + (δ * |a - a'|) * (251 / 50)) := by
          apply add_le_add h7
          calc |hquot h a σ * ((σ + a) * t + (h σ + h a))
                - hquot h a' σ * ((σ + a') * t + (h σ + h a'))|
              = |hquot h a σ * (((σ + a) * t + (h σ + h a)) - ((σ + a') * t + (h σ + h a')))
                  + ((hquot h a σ - hquot h a' σ) * ((σ + a') * t + (h σ + h a')))| := by
                congr 1; ring
            _ ≤ |hquot h a σ * (((σ + a) * t + (h σ + h a)) - ((σ + a') * t + (h σ + h a')))|
                  + |((hquot h a σ - hquot h a' σ) * ((σ + a') * t + (h σ + h a')))| :=
                abs_add_le _ _
            _ = |hquot h a σ| * |((σ + a) * t + (h σ + h a)) - ((σ + a') * t + (h σ + h a'))|
                  + |hquot h a σ - hquot h a' σ| * |(σ + a') * t + (h σ + h a')| := by
                rw [abs_mul, abs_mul]
            _ ≤ δ * (201 / 100 * |a - a'|) + (δ * |a - a'|) * (251 / 50) :=
                add_le_add h5 h6
      _ ≤ (10 * δ) * |a - a'| := by
          nlinarith [abs_nonneg (a - a'), hδ0, hδ1, mul_nonneg hδ0 (abs_nonneg (a - a'))]

/-! ## Pointwise data at a fixed `a` -/

/-- On the window, `krad` is bounded below by `1/100`, above by `10`, and differs
from the unperturbed radicand by at most `10 δ`. -/
lemma krad_pointwise_data {h : ℝ → ℝ} {δ σ t a : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 100)
    (h0 : ∀ x : ℝ, |h x| ≤ δ) (h1 : ∀ x : ℝ, |deriv h x| ≤ δ)
    (hσ1 : 7 / 10 ≤ σ) (hσ2 : σ ≤ 1) (ht1 : 1 / 5 ≤ |t|) (ht2 : |t| ≤ 2)
    (ha1 : 9 / 20 ≤ a) (ha2 : a ≤ σ) :
    1 / 100 ≤ krad h σ t a ∧ krad h σ t a ≤ 10 ∧
      |krad h σ t a - krad 0 σ t a| ≤ 10 * δ := by
  have hK : krad h σ t a = (t + hquot h a σ) * ((σ + a) * t + (h σ + h a)) := by
    rw [krad_apply]; unfold line; ring
  have hK0 : krad 0 σ t a = t * ((σ + a) * t) := by
    rw [krad_apply, hquot_zero]
    simp only [line, Pi.zero_apply, add_zero]
    ring
  have hH : |hquot h a σ| ≤ δ := abs_hquot_le h1
  have hHle : |hquot h a σ| ≤ 1 / 100 := le_trans hH hδ1
  have hsum : |h σ + h a| ≤ 2 * δ := by
    have h1' := abs_le.mp (h0 σ)
    have h2' := abs_le.mp (h0 a)
    rw [abs_le]; constructor <;> linarith [h1'.1, h1'.2, h2'.1, h2'.2]
  have hsumle : |h σ + h a| ≤ 1 / 50 := by linarith [hδ1]
  have hσa : (23 : ℝ) / 20 ≤ σ + a := by linarith
  have hσa0 : 0 ≤ σ + a := by linarith
  have hσa2 : σ + a ≤ 2 := by linarith
  have hf2 : |(σ + a) * t + (h σ + h a)| ≤ 201 / 50 := by
    have habs : |σ + a| ≤ 2 := by rw [abs_of_nonneg hσa0]; exact hσa2
    calc |(σ + a) * t + (h σ + h a)| ≤ |(σ + a) * t| + |h σ + h a| := abs_add_le _ _
      _ = |σ + a| * |t| + |h σ + h a| := by rw [abs_mul]
      _ ≤ 2 * 2 + 1 / 50 :=
          add_le_add (mul_le_mul habs ht2 (abs_nonneg _) (by norm_num)) hsumle
      _ = 201 / 50 := by norm_num
  refine ⟨?_, ?_, ?_⟩
  · rw [hK]
    rcases lt_trichotomy t 0 with htn | htz | htp
    · have htle : t ≤ -(1 / 5) := by
        have hh := ht1; rw [abs_of_neg htn] at hh; linarith
      have hf1 : t + hquot h a σ ≤ -(19 / 100) := by
        have := (abs_le.mp hHle).2
        linarith
      have hf2' : (σ + a) * t + (h σ + h a) ≤ -(21 / 100) := by
        have hstep1 : ((σ + a) - 23 / 20) * t ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (by linarith : (0 : ℝ) ≤ σ + a - 23 / 20)
            (le_of_lt htn)
        have hstep2 : (23 / 20) * t ≤ (23 / 20) * (-(1 / 5)) :=
          mul_le_mul_of_nonneg_left htle (by norm_num)
        have h1 : (σ + a) * t ≤ -((23 : ℝ) / 20 * (1 / 5)) := by nlinarith [hstep1, hstep2]
        have h2 := (abs_le.mp hsumle).2
        linarith
      have hprod : (19 / 100) * (21 / 100)
          ≤ (-(t + hquot h a σ)) * (-((σ + a) * t + (h σ + h a))) :=
        mul_le_mul (by linarith) (by linarith) (by norm_num) (by linarith)
      have heq2 : (t + hquot h a σ) * ((σ + a) * t + (h σ + h a))
          = (-(t + hquot h a σ)) * (-((σ + a) * t + (h σ + h a))) := by ring
      rw [heq2]
      linarith
    · exfalso; rw [htz, abs_zero] at ht1; norm_num at ht1
    · have htge : (1 : ℝ) / 5 ≤ t := by
        have hh := ht1; rw [abs_of_pos htp] at hh; exact hh
      have hf1 : (19 : ℝ) / 100 ≤ t + hquot h a σ := by
        have := (abs_le.mp hHle).1
        linarith
      have hf2' : (21 : ℝ) / 100 ≤ (σ + a) * t + (h σ + h a) := by
        have h2 : (23 / 20) * (1 / 5) ≤ (23 / 20) * t :=
          mul_le_mul_of_nonneg_left htge (by norm_num)
        have h3 : (23 / 20) * t ≤ (σ + a) * t :=
          mul_le_mul_of_nonneg_right hσa (le_of_lt htp)
        have h4 := (abs_le.mp hsumle).1
        linarith
      have hprod := mul_le_mul hf1 hf2' (by norm_num) (by linarith)
      linarith
  · rw [hK]
    have hf1 : |t + hquot h a σ| ≤ 201 / 100 := by
      calc |t + hquot h a σ| ≤ |t| + |hquot h a σ| := abs_add_le _ _
        _ ≤ 2 + 1 / 100 := by linarith [ht2, hHle]
        _ = 201 / 100 := by norm_num
    calc (t + hquot h a σ) * ((σ + a) * t + (h σ + h a))
        ≤ |(t + hquot h a σ) * ((σ + a) * t + (h σ + h a))| := le_abs_self _
      _ = |t + hquot h a σ| * |(σ + a) * t + (h σ + h a)| := abs_mul _ _
      _ ≤ (201 / 100) * (201 / 50) := mul_le_mul hf1 hf2 (abs_nonneg _) (by norm_num)
      _ ≤ 10 := by norm_num
  · have hkey : krad h σ t a - krad 0 σ t a
        = t * (h σ + h a) + hquot h a σ * ((σ + a) * t + (h σ + h a)) := by
      rw [hK, hK0]; ring
    rw [hkey]
    calc |t * (h σ + h a) + hquot h a σ * ((σ + a) * t + (h σ + h a))|
        ≤ |t * (h σ + h a)| + |hquot h a σ * ((σ + a) * t + (h σ + h a))| := abs_add_le _ _
      _ = |t| * |h σ + h a| + |hquot h a σ| * |(σ + a) * t + (h σ + h a)| := by
          rw [abs_mul, abs_mul]
      _ ≤ 2 * (2 * δ) + δ * (201 / 50) := by
          apply add_le_add
          · exact mul_le_mul ht2 hsum (abs_nonneg _) (by norm_num)
          · exact mul_le_mul hH hf2 (abs_nonneg _) hδ0
      _ ≤ 10 * δ := by nlinarith [hδ0]

/-! ## The main data lemma -/

theorem krad_data (n : ℕ) (hn : 1 ≤ n) :
    ∃ κ C : ℝ, 0 < κ ∧ 0 ≤ C ∧ ∀ (h : ℝ → ℝ) (δ : ℝ),
      ContDiff ℝ (⊤ : ℕ∞) h → 0 ≤ δ → δ ≤ 1 / 100 →
      Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau) →
      (∀ k : ℕ, k ≤ 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ δ) →
      ∀ σ ∈ Set.Icc (7 / 10 : ℝ) 1, ∀ t : ℝ, 1 / 5 ≤ |t| → |t| ≤ 2 →
      ∀ a ∈ Set.Icc (9 / 20 : ℝ) σ,
        κ ≤ Work.OddVolterra.krad h σ t a ∧ Work.OddVolterra.krad h σ t a ≤ C ∧
        |Work.OddVolterra.krad h σ t a - Work.OddVolterra.krad 0 σ t a| ≤ C * δ ∧
        |deriv (fun a' : ℝ => Work.OddVolterra.krad h σ t a') a| ≤ C ∧
        |deriv (fun a' : ℝ => Work.OddVolterra.krad h σ t a') a -
         deriv (fun a' : ℝ => Work.OddVolterra.krad 0 σ t a') a| ≤ C * δ := by
  refine ⟨1 / 100, 10, by norm_num, by norm_num, ?_⟩
  intro h δ hh hδ0 hδ1 hsupp hbnd σ hσ t ht1 ht2 a ha
  have _ : 1 ≤ n := hn
  have hσ1 : 7 / 10 ≤ σ := hσ.1
  have hσ2 : σ ≤ 1 := hσ.2
  have ha1 : 9 / 20 ≤ a := ha.1
  have ha2 : a ≤ σ := ha.2
  have h0 : ∀ x : ℝ, |h x| ≤ δ := fun x => by
    have hx := hbnd 0 (by norm_num) x
    rwa [iteratedDeriv_zero] at hx
  have h1 : ∀ x : ℝ, |deriv h x| ≤ δ := fun x => by
    have hx := hbnd 1 (by norm_num) x
    rwa [iteratedDeriv_one] at hx
  have h2 : ∀ x : ℝ, |deriv (deriv h) x| ≤ δ := fun x => by
    have hx := hbnd 2 (by norm_num) x
    rwa [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ', iteratedDeriv_one] at hx
  have hd : ContDiff ℝ (⊤ : ℕ∞) (deriv h) := by
    simpa only [Function.iterate_one] using hh.iterate_deriv 1
  have hliph : ∀ x y : ℝ, |h x - h y| ≤ δ * |x - y| :=
    abs_sub_le_mul_of_deriv_bound (f := h) (C := δ)
      (fun x => hh.differentiable (by simp) x) h1
  have hlipd : ∀ x y : ℝ, |deriv h x - deriv h y| ≤ δ * |x - y| :=
    abs_sub_le_mul_of_deriv_bound (f := deriv h) (C := δ)
      (fun x => hd.differentiable (by simp) x) h2
  have hlipq : ∀ x y : ℝ, |hquot h x σ - hquot h y σ| ≤ δ * |x - y| :=
    abs_hquot_sub_le hδ0 hd.continuous hlipd
  obtain ⟨hpos, hub, hclose⟩ :=
    krad_pointwise_data (h := h) (δ := δ) (σ := σ) (t := t) (a := a)
      hδ0 hδ1 h0 h1 hσ1 hσ2 ht1 ht2 ha1 ha2
  obtain ⟨hlip1, hlip2⟩ :=
    krad_lipschitz_window (h := h) (δ := δ) (σ := σ) (t := t)
      hδ0 hδ1 h0 h1 hliph hlipq hσ1 hσ2 ht2
  have haS : a ∈ Set.Icc (3 / 8 : ℝ) (3 / 2) := ⟨by linarith, by linarith⟩
  have hmem : Set.Icc (3 / 8 : ℝ) (3 / 2) ∈ 𝓝 a := Icc_mem_nhds (by linarith) (by linarith)
  refine ⟨hpos, hub, hclose, ?_, ?_⟩
  · have hlip : ∀ᶠ x in 𝓝 a, ‖krad h σ t x - krad h σ t a‖ ≤ 5 * ‖x - a‖ := by
      filter_upwards [hmem] with x hx
      rw [Real.norm_eq_abs, Real.norm_eq_abs]
      exact hlip1 x hx a haS
    have hd5 := norm_deriv_le_of_lip' (f := fun a' : ℝ => krad h σ t a') (C := 5)
      (by norm_num) hlip
    rw [Real.norm_eq_abs] at hd5
    linarith
  · have hdif1 : DifferentiableAt ℝ (fun a' : ℝ => krad h σ t a') a :=
      (contDiff_krad hh σ t).differentiable (by simp) a
    have hdif0 : DifferentiableAt ℝ (fun a' : ℝ => krad 0 σ t a') a :=
      (contDiff_krad (h := (0 : ℝ → ℝ)) contDiff_const σ t).differentiable (by simp) a
    rw [← deriv_sub hdif1 hdif0]
    have hlip : ∀ᶠ x in 𝓝 a,
        ‖(krad h σ t x - krad 0 σ t x) - (krad h σ t a - krad 0 σ t a)‖ ≤
          (10 * δ) * ‖x - a‖ := by
      filter_upwards [hmem] with x hx
      rw [Real.norm_eq_abs, Real.norm_eq_abs]
      exact hlip2 x hx a haS
    have hd10 := norm_deriv_le_of_lip' (f := fun a' : ℝ => krad h σ t a' - krad 0 σ t a')
      (C := 10 * δ) (by linarith) hlip
    rw [Real.norm_eq_abs] at hd10
    exact hd10

end

end Work.OddVolterra.Window
