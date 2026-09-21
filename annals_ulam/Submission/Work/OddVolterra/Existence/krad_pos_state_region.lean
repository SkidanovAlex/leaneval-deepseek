import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.Kernel.Diag

/-!
# Positivity of the Abel radicand on the transition-slope state region

The Abel denominator of the odd-case Volterra system is

`Kden h a σ t = √(krad h σ t a)`,   `krad h σ t a = (t + H(a,σ)) (L_σ(t) + L_a(t))`,

with `H(a,σ) = hquot h a σ = ∫_0^1 h'(a + τ(σ-a)) dτ` the divided difference and
`L_s(t) = s t + h s` the cutting line.

The perturbation `h` is supported in the transition window
`[1 - 2τ, 1 - τ] = [4/5, 9/10]` (`τ = 1/10`) and is small in `C¹` (`|h^{(k)}| ≤ 1/100`,
`k = 0, 1`).  On the state region `0 < b ≤ a ≤ σ ≤ 1`, and for `|t| ≥ 1/5` — the
"far from the axis" region in which the two section endpoints `y σ`, `-(x σ)` of the
odd curve lie — the two factors of `krad` have the sign of `t`, hence their product is
strictly positive.

The mechanism is the same in both factors.  For the first factor, `|H(a,σ)| ≤ 1/100 < 1/5 ≤ |t|`
because `H` is an average of values of `h'`.  For the second factor, the sum splits as
`(σ + a) t + (h σ + h a)`; either `σ < 4/5`, in which case `h` vanishes at both `σ` and `a`
(so the sign of the sum is that of `(σ+a)t`, and `σ + a > 0`), or `σ ≥ 4/5`, in which case
`(σ+a)|t| ≥ (4/5)(1/5) = 4/25 > 1/50 ≥ |h σ + h a|`, and again the sum has the sign of `t`.
-/

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

namespace Work.OddVolterra.Existence

noncomputable section

/-- The divided difference `H(s,σ) = ∫_0^1 h'(s + τ(σ-s)) dτ` is bounded by any global bound
of `|h'|`.  (This is `Work.OddVolterra.abs_hquot_le`, reproved here so that this file only
depends on the definition module.) -/
lemma abs_hquot_le_state {h : ℝ → ℝ} {ε s σ : ℝ} (hε : ∀ t : ℝ, |deriv h t| ≤ ε) :
    |hquot h s σ| ≤ ε := by
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
    (f := fun τ : ℝ => deriv h (s + τ * (σ - s))) (C := ε) (by
      intro τ _
      simpa [Real.norm_eq_abs] using hε (s + τ * (σ - s)))
  have hint' : ‖∫ τ in (0 : ℝ)..1, deriv h (s + τ * (σ - s))‖ ≤ ε := by
    simpa using hint
  simpa [hquot, Real.norm_eq_abs] using hint'

theorem krad_pos_state_region {h : ℝ → ℝ}
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau))
    (hsmall : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100)
    {b a σ t : ℝ} (hb : 0 < b) (ha : b ≤ a) (haσ : a ≤ σ) (hσ1 : σ ≤ 1)
    (ht : 1 / 5 ≤ |t|) :
    0 < Work.OddVolterra.krad h σ t a := by
  have hh0 : ∀ x : ℝ, |h x| ≤ 1 / 100 := fun x => hsmall 0 (by norm_num) x
  have hh1 : ∀ x : ℝ, |deriv h x| ≤ 1 / 100 := by
    intro x
    simpa using hsmall 1 (by norm_num) x
  have htau1 : (1 : ℝ) - 2 * Work.OddVolterra.tau = 4 / 5 := by
    rw [Work.OddVolterra.tau]; norm_num
  have htau2 : (1 : ℝ) - Work.OddVolterra.tau = 9 / 10 := by
    rw [Work.OddVolterra.tau]; norm_num
  -- `h` vanishes on the left of the transition window
  have hzero : ∀ x : ℝ, x < 4 / 5 → h x = 0 := by
    intro x hx
    by_contra hne
    have hmem := hsupp (Function.mem_support.mpr hne)
    rw [htau1, htau2] at hmem
    linarith [hmem.1]
  have hapos : 0 < a := lt_of_lt_of_le hb ha
  have hσpos : 0 < σ := lt_of_lt_of_le hapos haσ
  have hS : 0 < σ + a := by linarith
  -- the divided difference is small: the first factor has the sign of `t`
  have hquotbd : |hquot h a σ| ≤ 1 / 100 :=
    abs_hquot_le_state hh1
  have hbnd := abs_le.mp hquotbd
  -- the two values of `h` together are far smaller than `(σ + a)/5`
  have hhl : |h σ + h a| ≤ 1 / 50 := by
    have h1 := abs_le.mp (hh0 σ)
    have h2 := abs_le.mp (hh0 a)
    rw [abs_le]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have hsumlt : |h σ + h a| < (σ + a) * (1 / 5) := by
    rcases lt_or_ge σ (4 / 5 : ℝ) with hlt | hge
    · rw [hzero σ hlt, hzero a (lt_of_le_of_lt haσ hlt), add_zero, abs_zero]
      exact mul_pos hS (by norm_num)
    · have h1 : (4 : ℝ) / 5 * (1 / 5) ≤ (σ + a) * (1 / 5) :=
        mul_le_mul_of_nonneg_right (by linarith) (by norm_num)
      have h25 : (4 : ℝ) / 5 * (1 / 5) = 4 / 25 := by norm_num
      have h50 : (1 : ℝ) / 50 < 4 / 25 := by norm_num
      linarith
  have hhline : Work.OddVolterra.line h σ t + Work.OddVolterra.line h a t
      = (σ + a) * t + (h σ + h a) := by
    unfold Work.OddVolterra.line; ring
  rw [Work.OddVolterra.krad_apply, hhline]
  rcases lt_trichotomy t 0 with htn | htz | htp
  · -- `t < 0`: both factors are negative
    have htle : t ≤ -(1 / 5) := by
      have h := ht
      rw [abs_of_neg htn] at h
      linarith
    have h1 : t + hquot h a σ < 0 := by linarith [hbnd.2]
    have hlt' : h σ + h a < (σ + a) * (1 / 5) := lt_of_le_of_lt (le_abs_self _) hsumlt
    have hmul : (σ + a) * t ≤ -((σ + a) * (1 / 5)) := by
      have h := mul_le_mul_of_nonneg_left htle (le_of_lt hS)
      rwa [show (σ + a) * (-(1 / 5)) = -((σ + a) * (1 / 5)) by ring] at h
    have h2 : (σ + a) * t + (h σ + h a) < 0 := by linarith
    exact mul_pos_of_neg_of_neg h1 h2
  · -- `t = 0` is excluded by `1/5 ≤ |t|`
    rw [htz] at ht
    norm_num at ht
  · -- `t > 0`: both factors are positive
    have htge : 1 / 5 ≤ t := by
      have h := ht
      rwa [abs_of_pos htp] at h
    have h1 : 0 < t + hquot h a σ := by linarith [hbnd.1]
    have hnegabs : -((σ + a) * (1 / 5)) < -|h σ + h a| := by linarith
    have hgt' : -((σ + a) * (1 / 5)) < h σ + h a :=
      lt_of_lt_of_le hnegabs (neg_abs_le _)
    have hmul : (σ + a) * (1 / 5) ≤ (σ + a) * t :=
      mul_le_mul_of_nonneg_left htge (le_of_lt hS)
    have h2 : 0 < (σ + a) * t + (h σ + h a) := by linarith
    exact mul_pos h1 h2

end

end Work.OddVolterra.Existence
