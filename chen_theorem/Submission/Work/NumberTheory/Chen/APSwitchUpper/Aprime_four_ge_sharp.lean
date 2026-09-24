/-
# A sharp lower bound for `Aprime 4 = ∫_2^4 log (3/(u-1))/u du`

`Aprime x = ∫_2^x log (3/(u-1))/u du` is the primitive of the `C`-part of the `riPsi` delay
profile (see `riPhiEnvDefs`).  The envelope `envNum` of the switched window needs the value at
`x = 4` with a *two-sided* accuracy of order `10⁻³`, so the crude Padé bounds of
`logPad2_L1_lower` (`Aprime 4 ≥ -5/4 + (64/3)log2 - 12log3 ≈ 0.35379`) and `Aprime_four_le`
(`Aprime 4 ≤ 0.3576`) are not enough.  Here we prove the sharp lower bound

  `3552/10000 ≤ Aprime 4`,

the true value being `Aprime 4 = -33989/2240 + (2536/21)log2 - (2172/35)log3 ≈ 0.3554084`.

The proof:  with `s = (4-u)/(u+2)` we have `(1+s)/(1-s) = 3/(u-1)`, so the four-term truncation
of `log ((1+s)/(1-s)) = 2 ∑_{k≥0} s^{2k+1}/(2k+1)` (all terms positive) gives

  `log (3/(u-1)) ≥ 2(s + s³/3 + s⁵/5 + s⁷/7)`  on `[2,4]`.

Integrating the right-hand side against `1/u` is an exact elementary computation:  the
integrand has the partial-fraction expansion

  `2(s+s³/3+s⁵/5+s⁷/7)/u
     = 6164/(105u) - 2172/(35(u+2)) - 2664/(35(u+2)²) - 20448/(35(u+2)³)
       + 69984/(35(u+2)⁴) - 404352/(35(u+2)⁵) + 186624/(7(u+2)⁶) - 279936/(7(u+2)⁷)`,

whose primitive is elementary, giving the exact value above.
-/
import Mathlib
import Submission.Work.NumberTheory.Chen.APSwitchUpper.riPhiEnvDefs
import Submission.Work.NumberTheory.Chen.APSwitchUpper.riPhiEnvBasic
import Submission.Work.NumberTheory.Chen.APSwitchUpper.riPhiEnv_integral

open MeasureTheory

namespace Work.NumberTheory.Chen.APSwitchUpper

noncomputable section

/-! ## §1  The four-term truncation of the logarithm -/

/-- **Four-term Padé/odd-series lower bound.**  For `2 ≤ u ≤ 4`, writing `s = (4-u)/(u+2)`
(so that `(1+s)/(1-s) = 3/(u-1)` and `0 ≤ s ≤ 1/2`),

  `2(s + s³/3 + s⁵/5 + s⁷/7) ≤ log (3/(u-1))`. -/
lemma logPad4_L1_lower (u : ℝ) (h2 : 2 ≤ u) (h4 : u ≤ 4) :
    2 * ((4 - u) / (u + 2) + ((4 - u) / (u + 2)) ^ 3 / 3 + ((4 - u) / (u + 2)) ^ 5 / 5
        + ((4 - u) / (u + 2)) ^ 7 / 7) ≤ Real.log (3 / (u - 1)) := by
  set s : ℝ := (4 - u) / (u + 2) with hs
  have hu2 : (0 : ℝ) < u + 2 := by linarith
  have hs0 : 0 ≤ s := by rw [hs]; exact div_nonneg (by linarith) (by linarith)
  have hs1 : s < 1 := by rw [hs, div_lt_one hu2]; linarith
  have hkey := Real.sum_range_le_log_div hs0 hs1 4
  have hsum : (∑ i ∈ Finset.range 4, s ^ (2 * i + 1) / (2 * i + 1))
      = s + s ^ 3 / 3 + s ^ 5 / 5 + s ^ 7 / 7 := by
    simp [Finset.sum_range_succ]
    ring
  rw [hsum] at hkey
  have harg : (1 + s) / (1 - s) = 3 / (u - 1) := by
    rw [hs]
    have hd1 : (1 : ℝ) - (4 - u) / (u + 2) ≠ 0 := by
      have h : (1 : ℝ) - (4 - u) / (u + 2) = 2 * (u - 1) / (u + 2) := by
        field_simp; ring
      rw [h]; apply div_ne_zero (by linarith) (by linarith)
    have hd2 : (u : ℝ) - 1 ≠ 0 := by linarith
    rw [div_eq_div_iff hd1 hd2]
    field_simp
    ring
  rw [harg] at hkey
  linarith [hkey]

/-! ## §2  The primitive of the truncated integrand -/

/-- Derivative of `c/(v+2)^k` at `u`. -/
private lemma hasDerivAt_div_add_pow (c : ℝ) (k : ℕ) (u : ℝ) (h : u + 2 ≠ 0) :
    HasDerivAt (fun v : ℝ => c / (v + 2) ^ k) (-((k : ℝ) * c) / (u + 2) ^ (k + 1)) u := by
  rcases Nat.eq_zero_or_pos k with hk0 | hk
  · subst hk0; simpa using hasDerivAt_const u c
  have hb : HasDerivAt (fun v : ℝ => v + 2) (1 : ℝ) u := (hasDerivAt_id u).add_const 2
  have hk' : HasDerivAt (fun v : ℝ => (v + 2) ^ k) ((k : ℝ) * (u + 2) ^ (k - 1) * 1) u :=
    hb.pow k
  have h := (hasDerivAt_const u c).div hk' (pow_ne_zero k h)
  have hk2 : ((u + 2) ^ k) ^ 2 = (u + 2) ^ (k - 1) * (u + 2) ^ (k + 1) := by
    rw [pow_two, ← pow_add]
    rw [show k + k = (k - 1) + (k + 1) by omega, pow_add]
  have hd : (0 * (u + 2) ^ k - c * ((k : ℝ) * (u + 2) ^ (k - 1) * 1)) / ((u + 2) ^ k) ^ 2
      = -((k : ℝ) * c) / (u + 2) ^ (k + 1) := by
    have hnum : 0 * (u + 2) ^ k - c * ((k : ℝ) * (u + 2) ^ (k - 1) * 1)
        = -((k : ℝ) * c) * (u + 2) ^ (k - 1) := by ring
    rw [hnum, hk2]
    field_simp
  have hres : HasDerivAt ((fun _ : ℝ => c) / (fun v : ℝ => (v + 2) ^ k))
      (-((k : ℝ) * c) / (u + 2) ^ (k + 1)) u := by
    rw [hd] at h; exact h
  convert hres using 1
  all_goals (funext v; rw [Pi.div_apply])

/-- The explicit primitive

`H v = (6164/105)log v - (2172/35)log(v+2) + (2664/35)/(v+2) + (10224/35)/(v+2)²
        - (23328/35)/(v+2)³ + (101088/35)/(v+2)⁴ - (186624/35)/(v+2)⁵ + (233280/35)/(v+2)⁶`

satisfies `H' u = 2(s+s³/3+s⁵/5+s⁷/7)/u` with `s = (4-u)/(u+2)`. -/
private lemma hasDerivAt_anti (u : ℝ) (hu : 0 < u) :
    HasDerivAt (fun v : ℝ => (6164 / 105) * Real.log v - (2172 / 35) * Real.log (v + 2)
        + (2664 / 35) / (v + 2) + (10224 / 35) / (v + 2) ^ 2 - (23328 / 35) / (v + 2) ^ 3
        + (101088 / 35) / (v + 2) ^ 4 - (186624 / 35) / (v + 2) ^ 5
        + (233280 / 35) / (v + 2) ^ 6)
      (2 * ((4 - u) / (u + 2) + ((4 - u) / (u + 2)) ^ 3 / 3 + ((4 - u) / (u + 2)) ^ 5 / 5
        + ((4 - u) / (u + 2)) ^ 7 / 7) / u) u := by
  have hne : u + 2 ≠ 0 := by linarith
  have h1 := (Real.hasDerivAt_log hu.ne').const_mul (6164 / 105 : ℝ)
  have hlog2 : HasDerivAt (fun v : ℝ => Real.log (v + 2)) ((u + 2)⁻¹) u := by
    have h := ((hasDerivAt_id u).add_const 2).log hne
    simpa [one_div] using h
  have h2 := hlog2.const_mul (2172 / 35 : ℝ)
  have h3 := hasDerivAt_div_add_pow (2664 / 35) 1 u hne
  have h4 := hasDerivAt_div_add_pow (10224 / 35) 2 u hne
  have h5 := (hasDerivAt_div_add_pow (23328 / 35) 3 u hne).neg
  have h6 := hasDerivAt_div_add_pow (101088 / 35) 4 u hne
  have h7 := (hasDerivAt_div_add_pow (186624 / 35) 5 u hne).neg
  have h8 := hasDerivAt_div_add_pow (233280 / 35) 6 u hne
  have hcomb := (((((((h1.sub h2).add h3).add h4).add h5).add h6).add h7).add h8)
  convert hcomb using 1
  all_goals first
    | rfl
    | (funext v; simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply]; ring_nf)
    | (field_simp; ring_nf)

/-- The definition of the primitive, as a `let`-free term (used for the endpoint evaluation). -/
private def antiFun (v : ℝ) : ℝ :=
  (6164 / 105) * Real.log v - (2172 / 35) * Real.log (v + 2)
    + (2664 / 35) / (v + 2) + (10224 / 35) / (v + 2) ^ 2 - (23328 / 35) / (v + 2) ^ 3
    + (101088 / 35) / (v + 2) ^ 4 - (186624 / 35) / (v + 2) ^ 5
    + (233280 / 35) / (v + 2) ^ 6

/-! ## §3  The exact value of the truncated integral -/

/-- **Exact evaluation of the truncated integral.**

  `∫_2^4 2(s+s³/3+s⁵/5+s⁷/7)/u du = -33989/2240 + (2536/21)log2 - (2172/35)log3`,  `s=(4-u)/(u+2)`.

Numerically `= 0.3553733479…`. -/
private lemma integral_R4 :
    (∫ u in (2 : ℝ)..4, 2 * ((4 - u) / (u + 2) + ((4 - u) / (u + 2)) ^ 3 / 3
        + ((4 - u) / (u + 2)) ^ 5 / 5 + ((4 - u) / (u + 2)) ^ 7 / 7) / u)
      = -33989 / 2240 + (2536 / 21) * Real.log 2 - (2172 / 35) * Real.log 3 := by
  have hcont : ContinuousOn (fun u : ℝ => 2 * ((4 - u) / (u + 2) + ((4 - u) / (u + 2)) ^ 3 / 3
        + ((4 - u) / (u + 2)) ^ 5 / 5 + ((4 - u) / (u + 2)) ^ 7 / 7) / u)
      (Set.uIcc (2 : ℝ) 4) := by
    have hne : ∀ x ∈ Set.uIcc (2 : ℝ) 4, x + 2 ≠ 0 := by
      intro x hx; rw [Set.uIcc_of_le (by norm_num : (2 : ℝ) ≤ 4)] at hx
      have := (Set.mem_Icc.mp hx).1; linarith
    have hne0 : ∀ x ∈ Set.uIcc (2 : ℝ) 4, x ≠ 0 := by
      intro x hx; rw [Set.uIcc_of_le (by norm_num : (2 : ℝ) ≤ 4)] at hx
      have := (Set.mem_Icc.mp hx).1; linarith
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := antiFun)
      (f' := fun u : ℝ => 2 * ((4 - u) / (u + 2) + ((4 - u) / (u + 2)) ^ 3 / 3
        + ((4 - u) / (u + 2)) ^ 5 / 5 + ((4 - u) / (u + 2)) ^ 7 / 7) / u)
      (fun u hu => by
        rw [Set.uIcc_of_le (by norm_num : (2 : ℝ) ≤ 4)] at hu
        have hu0 : (0 : ℝ) < u := by linarith [(Set.mem_Icc.mp hu).1]
        exact hasDerivAt_anti u hu0)
      hcont.intervalIntegrable]
  have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; ring
  have h6 : Real.log (6 : ℝ) = Real.log 2 + Real.log 3 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  unfold antiFun
  norm_num
  rw [h4, h6]
  ring

/-! ## §4  The sharp lower bound for `Aprime 4` -/

theorem Aprime_four_ge_sharp :
    (3552 / 10000 : ℝ) ≤ Work.NumberTheory.Chen.APSwitchUpper.Aprime 4 := by
  rw [Aprime]
  have hcont_R : ContinuousOn (fun u : ℝ => 2 * ((4 - u) / (u + 2) + ((4 - u) / (u + 2)) ^ 3 / 3
        + ((4 - u) / (u + 2)) ^ 5 / 5 + ((4 - u) / (u + 2)) ^ 7 / 7) / u)
      (Set.uIcc (2 : ℝ) 4) := by
    have hne : ∀ x ∈ Set.uIcc (2 : ℝ) 4, x + 2 ≠ 0 := by
      intro x hx; rw [Set.uIcc_of_le (by norm_num : (2 : ℝ) ≤ 4)] at hx
      have := (Set.mem_Icc.mp hx).1; linarith
    have hne0 : ∀ x ∈ Set.uIcc (2 : ℝ) 4, x ≠ 0 := by
      intro x hx; rw [Set.uIcc_of_le (by norm_num : (2 : ℝ) ≤ 4)] at hx
      have := (Set.mem_Icc.mp hx).1; linarith
    fun_prop
  have hcont_log : ContinuousOn (fun u : ℝ => Real.log (3 / (u - 1)) / u)
      (Set.uIcc (2 : ℝ) 4) := by
    have hne : ∀ x ∈ Set.uIcc (2 : ℝ) 4, x - 1 ≠ 0 := by
      intro x hx; rw [Set.uIcc_of_le (by norm_num : (2 : ℝ) ≤ 4)] at hx
      have := (Set.mem_Icc.mp hx).1; linarith
    have hne3 : ∀ x ∈ Set.uIcc (2 : ℝ) 4, 3 / (x - 1) ≠ 0 := by
      intro x hx; exact div_ne_zero (by norm_num) (hne x hx)
    have hne0 : ∀ x ∈ Set.uIcc (2 : ℝ) 4, x ≠ 0 := by
      intro x hx; rw [Set.uIcc_of_le (by norm_num : (2 : ℝ) ≤ 4)] at hx
      have := (Set.mem_Icc.mp hx).1; linarith
    fun_prop
  have hmono : (∫ u in (2 : ℝ)..4, 2 * ((4 - u) / (u + 2) + ((4 - u) / (u + 2)) ^ 3 / 3
        + ((4 - u) / (u + 2)) ^ 5 / 5 + ((4 - u) / (u + 2)) ^ 7 / 7) / u)
      ≤ ∫ u in (2 : ℝ)..4, Real.log (3 / (u - 1)) / u := by
    refine intervalIntegral.integral_mono_on (by norm_num : (2 : ℝ) ≤ 4)
      hcont_R.intervalIntegrable hcont_log.intervalIntegrable ?_
    intro x hx
    rw [Set.mem_Icc] at hx
    have hx0 : (0 : ℝ) < x := by linarith [hx.1]
    exact div_le_div_of_nonneg_right (logPad4_L1_lower x hx.1 hx.2) hx0.le
  calc (3552 / 10000 : ℝ)
      ≤ -33989 / 2240 + (2536 / 21) * Real.log 2 - (2172 / 35) * Real.log 3 := by
        linarith [Real.log_two_gt_d9, Real.log_three_lt_d9]
    _ = (∫ u in (2 : ℝ)..4, 2 * ((4 - u) / (u + 2) + ((4 - u) / (u + 2)) ^ 3 / 3
        + ((4 - u) / (u + 2)) ^ 5 / 5 + ((4 - u) / (u + 2)) ^ 7 / 7) / u) :=
        integral_R4.symm
    _ ≤ ∫ u in (2 : ℝ)..4, Real.log (3 / (u - 1)) / u := hmono

end

end Work.NumberTheory.Chen.APSwitchUpper
