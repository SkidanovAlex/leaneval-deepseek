import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.liouville

open Polynomial Finset Real
open MeasureTheory

/-- For `c > 0` and `s > 0`, `exp (-c s^{1/10}) ≤ 20! / (c^20 s^2)`.
This is the `k = 20` case of `exp y ≥ y^k / k!`, giving a decay of order `s^-2`. -/
private lemma exp_bound_pointwise (c s : ℝ) (hc : 0 < c) (hs : 0 < s) :
    Real.exp (-c * s ^ (1/10 : ℝ)) ≤ (Nat.factorial 20 : ℝ) / (c ^ 20 * s ^ 2) := by
  rw [neg_mul]
  have hsnn : 0 ≤ s := le_of_lt hs
  have hu : 0 ≤ c * s ^ (1/10 : ℝ) := by
    have : 0 < s ^ (1/10 : ℝ) := Real.rpow_pos_of_pos hs _
    positivity
  have hkey := Real.pow_div_factorial_le_exp (c * s ^ (1/10 : ℝ)) hu 20
  have hpos : 0 < (c * s ^ (1/10 : ℝ)) ^ 20 / (Nat.factorial 20 : ℝ) := by positivity
  have h1 : Real.exp (-(c * s ^ (1/10 : ℝ))) ≤
      ((c * s ^ (1/10 : ℝ)) ^ 20 / (Nat.factorial 20 : ℝ))⁻¹ := by
    rw [Real.exp_neg]
    exact (inv_le_inv₀ (Real.exp_pos _) hpos).mpr hkey
  have hpow : (c * s ^ (1/10 : ℝ)) ^ 20 = c ^ 20 * s ^ 2 := by
    rw [mul_pow]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul hsnn]
    norm_num
  calc Real.exp (-(c * s ^ (1/10 : ℝ)))
      ≤ ((c * s ^ (1/10 : ℝ)) ^ 20 / (Nat.factorial 20 : ℝ))⁻¹ := h1
    _ = (Nat.factorial 20 : ℝ) / (c * s ^ (1/10 : ℝ)) ^ 20 := inv_div _ _
    _ = (Nat.factorial 20 : ℝ) / (c ^ 20 * s ^ 2) := by rw [hpow]

/-- The antiderivative `t ↦ -(Z/2) (log t)^{-2}` has derivative `Z / (t (log t)^3)`. -/
private lemma hasDerivAt_anti (Z t : ℝ) (ht : 1 < t) :
    HasDerivAt (fun t => -(Z/2) * ((Real.log t) ^ 2)⁻¹) (Z * (t * (Real.log t) ^ 3)⁻¹) t := by
  have htne : t ≠ 0 := by linarith
  have hlt : Real.log t ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one (by linarith) (by linarith)
  have hlog : HasDerivAt Real.log t⁻¹ t := Real.hasDerivAt_log htne
  have hsq : HasDerivAt (fun t => (Real.log t) ^ 2) (2 * Real.log t * t⁻¹) t := by
    have h := hlog.pow 2
    convert h using 1
    norm_num [pow_one]
  have hinv : HasDerivAt (fun t => ((Real.log t) ^ 2)⁻¹)
      (-(2 * Real.log t * t⁻¹) / ((Real.log t) ^ 2) ^ 2) t :=
    hsq.inv (by positivity)
  have hG := hinv.const_mul (-(Z/2))
  convert hG using 1
  field_simp

/-- Continuity of the integrand on `[N,M]` when `3 ≤ N`. -/
private lemma continuousOn_integrand (c N M : ℝ) (hN : 3 ≤ N) :
    ContinuousOn (fun t => Real.exp (-c * (Real.log t) ^ (1/10 : ℝ)) / (t * Real.log t))
      (Set.Icc N M) := by
  have hlog_c : ContinuousOn (fun t => Real.log t) (Set.Icc N M) :=
    ContinuousOn.log continuousOn_id (fun t ht => by
      have h3 : (3 : ℝ) ≤ t := le_trans hN ht.1
      show t ≠ 0
      linarith)
  have hpow : ContinuousOn (fun t => (Real.log t) ^ (1/10 : ℝ)) (Set.Icc N M) :=
    ContinuousOn.rpow_const hlog_c (fun _ _ => Or.inr (by norm_num))
  have harg : ContinuousOn (fun t => -c * (Real.log t) ^ (1/10 : ℝ)) (Set.Icc N M) :=
    hpow.const_mul (-c)
  have hnum : ContinuousOn (fun t => Real.exp (-c * (Real.log t) ^ (1/10 : ℝ))) (Set.Icc N M) :=
    Real.continuous_exp.comp_continuousOn harg
  have hden : ContinuousOn (fun t => t * Real.log t) (Set.Icc N M) := continuousOn_id.mul hlog_c
  refine ContinuousOn.div hnum hden (fun t ht => ?_)
  have h3 : (3 : ℝ) ≤ t := le_trans hN ht.1
  have : 0 < Real.log t := Real.log_pos (by linarith)
  positivity

/-- Continuity of the comparison function `t ↦ Z / (t (log t)^3)` on `[N,M]` when `3 ≤ N`. -/
private lemma continuousOn_compare (Z N M : ℝ) (hN : 3 ≤ N) :
    ContinuousOn (fun t => Z * (t * (Real.log t) ^ 3)⁻¹) (Set.Icc N M) := by
  have hlog_c : ContinuousOn (fun t => Real.log t) (Set.Icc N M) :=
    ContinuousOn.log continuousOn_id (fun t ht => by
      have h3 : (3 : ℝ) ≤ t := le_trans hN ht.1
      show t ≠ 0
      linarith)
  have hden : ContinuousOn (fun t => t * (Real.log t) ^ 3) (Set.Icc N M) := by
    have hp := hlog_c.pow 3
    convert continuousOn_id.mul hp using 1
    ext t; rfl
  exact (hden.inv₀ (fun t ht => by
    have h3 : (3 : ℝ) ≤ t := le_trans hN ht.1
    have : 0 < Real.log t := Real.log_pos (by linarith)
    positivity)).const_mul Z

/-- Continuity of the antiderivative `t ↦ -(Z/2)(log t)^{-2}` on `[N,M]` when `3 ≤ N`. -/
private lemma continuousOn_anti (Z N M : ℝ) (hN : 3 ≤ N) :
    ContinuousOn (fun t => -(Z/2) * ((Real.log t) ^ 2)⁻¹) (Set.Icc N M) := by
  have hlog_c : ContinuousOn (fun t => Real.log t) (Set.Icc N M) :=
    ContinuousOn.log continuousOn_id (fun t ht => by
      have h3 : (3 : ℝ) ≤ t := le_trans hN ht.1
      show t ≠ 0
      linarith)
  have hden : ContinuousOn (fun t => (Real.log t) ^ 2) (Set.Icc N M) := hlog_c.pow 2
  exact (hden.inv₀ (fun t ht => by
    have h3 : (3 : ℝ) ≤ t := le_trans hN ht.1
    have : 0 < Real.log t := Real.log_pos (by linarith)
    positivity)).const_mul (-(Z/2))

/-- Interval integrability on `[N,M]` from continuity on the closed interval, for `N ≤ M`. -/
private lemma intervalIntegrable_of_continuousOn_Icc {f : ℝ → ℝ} {N M : ℝ} (hNM : N ≤ M)
    (h : ContinuousOn f (Set.Icc N M)) : IntervalIntegrable f volume N M := by
  have h' : ContinuousOn f (Set.uIcc N M) := by rwa [Set.uIcc_of_le hNM]
  exact h'.intervalIntegrable

/-- For every `c > 0` the integral `∫_N^M exp(-c (log t)^{1/10}) / (t log t) dt` is bounded by a
constant depending only on `c`, uniformly over `3 ≤ N ≤ M`.
Route: substitute `s = log t` (change of variables for interval integrals), reducing to
`∫_{log N}^{log M} exp(-c s^{1/10})/s ds ≤ ∫_{log 3}^{∞} exp(-c s^{1/10})/s ds < ∞`; convergence via
`exp(c s^{1/10}) ≥ (c s^{1/10})^k/k!` with `k = 11`, giving the crude bound
`exp(-c s^{1/10})/s ≤ 1/s` on the compact range and `≤ s^{-11/10}` for `s ≥ 11!/c^{11}`. -/
theorem exp_decay_log_integral :
    ∀ c : ℝ, 0 < c → ∃ K : ℝ, 0 < K ∧ ∀ N M : ℝ, 3 ≤ N → N ≤ M →
      ∫ t in N..M, Real.exp (-c * (Real.log t) ^ (1 / 10 : ℝ)) / (t * Real.log t) ≤ K := by
  intro c hc
  set Z : ℝ := (Nat.factorial 20 : ℝ) / c ^ 20 with hZdef
  have hZpos : 0 < Z := by rw [hZdef]; positivity
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  refine ⟨Z / 2 * ((Real.log 3) ^ 2)⁻¹, ?_, ?_⟩
  · have : 0 < (Real.log 3) ^ 2 := by positivity
    positivity
  intro N M hN hNM
  have hNpos : 0 < N := by linarith
  have hlogN3 : Real.log 3 ≤ Real.log N := Real.log_le_log (by norm_num) hN
  have hlogNM : Real.log N ≤ Real.log M := Real.log_le_log hNpos hNM
  -- Pointwise domination of the integrand by `Z / (t (log t)^3)`.
  have hpoint : ∀ t ∈ Set.Icc N M,
      Real.exp (-c * (Real.log t) ^ (1/10 : ℝ)) / (t * Real.log t)
        ≤ Z * (t * (Real.log t) ^ 3)⁻¹ := by
    intro t ht
    have ht3 : (3 : ℝ) ≤ t := le_trans hN ht.1
    have ht1 : (1 : ℝ) < t := by linarith
    have hlogpos : 0 < Real.log t := Real.log_pos ht1
    have hden : 0 < t * Real.log t := by positivity
    rw [div_le_iff₀ hden]
    have hEq : Z * (t * (Real.log t) ^ 3)⁻¹ * (t * Real.log t)
        = (Nat.factorial 20 : ℝ) / (c ^ 20 * (Real.log t) ^ 2) := by
      rw [hZdef]
      field_simp
    rw [hEq]
    exact exp_bound_pointwise c (Real.log t) hc hlogpos
  have hf_int : IntervalIntegrable
      (fun t => Real.exp (-c * (Real.log t) ^ (1/10 : ℝ)) / (t * Real.log t)) volume N M :=
    intervalIntegrable_of_continuousOn_Icc hNM (continuousOn_integrand c N M hN)
  have hg_int : IntervalIntegrable (fun t => Z * (t * (Real.log t) ^ 3)⁻¹) volume N M :=
    intervalIntegrable_of_continuousOn_Icc hNM (continuousOn_compare Z N M hN)
  have hmono := intervalIntegral.integral_mono_on hNM hf_int hg_int hpoint
  have hFTC : ∫ t in N..M, Z * (t * (Real.log t) ^ 3)⁻¹
      = (fun t => -(Z/2) * ((Real.log t) ^ 2)⁻¹) M
        - (fun t => -(Z/2) * ((Real.log t) ^ 2)⁻¹) N := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hNM
    · exact continuousOn_anti Z N M hN
    · intro x hx
      exact hasDerivAt_anti Z x (by have := hx.1; linarith)
    · exact hg_int
  have hlogNpos : 0 < Real.log N := Real.log_pos (by linarith)
  have hlogMpos : 0 < Real.log M := Real.log_pos (by linarith)
  have hsq_le : (Real.log 3) ^ 2 ≤ (Real.log N) ^ 2 :=
    pow_le_pow_left₀ (le_of_lt hlog3) hlogN3 2
  have hinv_le : ((Real.log N) ^ 2)⁻¹ ≤ ((Real.log 3) ^ 2)⁻¹ :=
    (inv_le_inv₀ (by positivity) (by positivity)).mpr hsq_le
  have htail : 0 ≤ ((Real.log M) ^ 2)⁻¹ := by positivity
  calc ∫ t in N..M, Real.exp (-c * (Real.log t) ^ (1 / 10 : ℝ)) / (t * Real.log t)
      ≤ ∫ t in N..M, Z * (t * (Real.log t) ^ 3)⁻¹ := hmono
    _ = (fun t => -(Z/2) * ((Real.log t) ^ 2)⁻¹) M
          - (fun t => -(Z/2) * ((Real.log t) ^ 2)⁻¹) N := hFTC
    _ = Z / 2 * (((Real.log N) ^ 2)⁻¹ - ((Real.log M) ^ 2)⁻¹) := by
        simp only []
        ring
    _ ≤ Z / 2 * ((Real.log 3) ^ 2)⁻¹ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith

end Work.BMF.liouville
