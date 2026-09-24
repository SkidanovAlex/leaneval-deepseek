/-
# `APSwitchUpper.riPhiEnv_integral` — lower bounds for `Aprime` on the midpoint grid

`Aprime x = ∫_2^x log (3/(u-1))/u du` is elementary but not explicit.  The switched window
bound needs *lower* bounds for `Aprime` at the grid points `2 + k/16`, and the convexity of
the integrand (`convexOn_aprimeIntegrand`) turns the midpoint rule into such a bound.

The midpoint rule is applied piecewise: on `[2+j/16, 2+(j+1)/16]` the integral dominates
`(1/16) · f (midpoint)`, and `f (midpoint) ≥ fLow (midpoint)` with the rational lower bound
`fLow v = logLowRat (3/(v-1))/v`.
-/
import Mathlib
import Submission.Work.NumberTheory.Chen.APSwitchUpper.riPhiEnvDefs
import Submission.Work.NumberTheory.Chen.APSwitchUpper.riPhiEnvBasic
import Submission.Work.NumberTheory.Chen.APSwitchUpper.convexOn_aprimeIntegrand

set_option maxHeartbeats 4000000

open Finset
open scoped BigOperators

namespace Work.NumberTheory.Chen.APSwitchUpper

noncomputable section

open MeasureTheory Real

/-- The rational lower bound for the integrand of `Aprime`. -/
def fLow (v : ℝ) : ℝ := logLowRat (3/(v - 1))/v

/-- The composite-midpoint lower bound for `Aprime (2 + k/16)`. -/
def ALow (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range k, (1/16) * fLow (2 + ((j:ℝ) + 1/2)/16)

/-- The midpoint Jensen inequality for a convex function. -/
lemma midpoint_jensen_of_convexOn {f : ℝ → ℝ} {a b : ℝ}
    (hf : ConvexOn ℝ (Set.Icc a b) f) :
    ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, f ((x+y)/2) ≤ (f x + f y)/2 := by
  intro x hx y hy
  rcases lt_trichotomy x y with hxy | hxy | hxy
  · have h := hf.secant_mono_aux1 (x := x) (y := (x+y)/2) (z := y) hx hy
      (by linarith : x < (x + y)/2) (by linarith : (x + y)/2 < y)
    have e1 : y - (x+y)/2 = (y-x)/2 := by ring
    have e2 : (x+y)/2 - x = (y-x)/2 := by ring
    rw [e1, e2] at h
    have hd : (0:ℝ) < y - x := by linarith
    refine le_of_mul_le_mul_left ?_ hd
    nlinarith [h]
  · rw [← hxy, add_self_div_two, add_self_div_two]
  · have h := hf.secant_mono_aux1 (x := y) (y := (x+y)/2) (z := x) hy hx
      (by linarith : y < (x + y)/2) (by linarith : (x + y)/2 < x)
    have e1 : x - (x+y)/2 = (x-y)/2 := by ring
    have e2 : (x+y)/2 - y = (x-y)/2 := by ring
    rw [e1, e2] at h
    have hd : (0:ℝ) < x - y := by linarith
    refine le_of_mul_le_mul_left ?_ hd
    nlinarith [h]

private lemma continuousOn_fLow_fun {c d : ℝ} (hc : 2 ≤ c) (hd : d ≤ 4) :
    ContinuousOn (fun x : ℝ => Real.log (3/(x-1))/x) (Set.Icc c d) := by
  have hpos : ∀ x ∈ Set.Icc c d, (1:ℝ) < x := by
    intro x hx; rw [Set.mem_Icc] at hx; linarith [hx.1, hc]
  refine ContinuousOn.div ?_ continuousOn_id (fun x hx => ne_of_gt (by linarith [hpos x hx]))
  refine ContinuousOn.log ?_ (fun x hx => ne_of_gt (div_pos (by norm_num)
    (by linarith [hpos x hx])))
  exact ContinuousOn.div continuousOn_const (continuousOn_id.sub continuousOn_const)
    (fun x hx => by linarith [hpos x hx])

private lemma fLow_le_f (v : ℝ) (hv : 2 ≤ v) (hv4 : v ≤ 4) :
    fLow v ≤ Real.log (3/(v-1))/v := by
  have hv0 : (0:ℝ) < v := by linarith
  have h3 : 3/(v - 1) ∈ Set.Icc 1 3 := by
    rw [Set.mem_Icc]
    exact ⟨by rw [le_div_iff₀ (by linarith : (0:ℝ) < v - 1)]; linarith,
      by rw [div_le_iff₀ (by linarith : (0:ℝ) < v - 1)]; linarith⟩
  rw [show fLow v = logLowRat (3/(v-1))/v from rfl]
  exact div_le_div_of_nonneg_right (logLowRat_le h3.1) hv0.le

/-- Midpoint rule on one grid interval, with the rational lower bound of the integrand. -/
lemma midpoint_step_le (j : ℕ) (hj : j < 32) :
    (1/16) * fLow (2 + ((j:ℝ) + 1/2)/16)
      ≤ ∫ x in (2 + (j:ℝ)/16)..(2 + ((j:ℝ)+1)/16), Real.log (3/(x-1))/x := by
  have hj32 : (j:ℝ) ≤ 31 := by exact_mod_cast (by omega : j ≤ 31)
  have hle : (2:ℝ) + (j:ℝ)/16 ≤ 2 + ((j:ℝ)+1)/16 := by linarith
  have hle4 : (2:ℝ) + ((j:ℝ)+1)/16 ≤ 4 := by linarith
  have hconv : ConvexOn ℝ (Set.Icc (2 + (j:ℝ)/16) (2 + ((j:ℝ)+1)/16))
      (fun x : ℝ => Real.log (3/(x-1))/x) :=
    convexOn_aprimeIntegrand.subset (fun x hx => by
      rw [Set.mem_Icc] at hx ⊢
      exact ⟨by linarith [hx.1], by linarith [hx.2, hle4]⟩) (convex_Icc _ _)
  have hm : (2 + (j:ℝ)/16 + (2 + ((j:ℝ)+1)/16))/2 = 2 + ((j:ℝ) + 1/2)/16 := by ring
  have hmem : (2 + ((j:ℝ) + 1/2)/16) ∈ Set.Icc (2 + (j:ℝ)/16) (2 + ((j:ℝ)+1)/16) :=
    ⟨by linarith, by linarith⟩
  have hjen := midpoint_jensen_of_convexOn hconv (2 + (j:ℝ)/16) ⟨le_rfl, hle⟩
    (2 + ((j:ℝ)+1)/16) ⟨hle, le_rfl⟩
  have hjen' : Real.log (3/((2 + ((j:ℝ) + 1/2)/16)-1))/(2 + ((j:ℝ) + 1/2)/16)
      ≤ (Real.log (3/((2 + (j:ℝ)/16)-1))/(2 + (j:ℝ)/16)
        + Real.log (3/((2 + ((j:ℝ)+1)/16)-1))/(2 + ((j:ℝ)+1)/16))/2 := by
    have := hjen
    rw [hm] at this
    exact this
  have hint : IntervalIntegrable (fun x : ℝ => Real.log (3/(x-1))/x) volume
      (2 + (j:ℝ)/16) (2 + ((j:ℝ)+1)/16) :=
    ContinuousOn.intervalIntegrable (by
      rw [Set.uIcc_of_le hle]
      exact continuousOn_fLow_fun (by linarith) hle4)
  have hmid := midpoint_integral_le hle (midpoint_jensen_of_convexOn hconv) hint
  rw [hm] at hmid
  refine le_trans ?_ hmid
  have hf := fLow_le_f (2 + ((j:ℝ) + 1/2)/16) (by linarith) (by linarith)
  have hw : (2:ℝ) + ((j:ℝ)+1)/16 - (2 + (j:ℝ)/16) = 1/16 := by ring
  rw [hw]
  exact mul_le_mul_of_nonneg_left hf (by norm_num)

/-- The midpoint sums bound `Aprime` from below. -/
lemma ALow_le_Aprime (k : ℕ) (hk : k ≤ 32) :
    ALow k ≤ Aprime (2 + (k:ℝ)/16) := by
  induction k with
  | zero =>
      have h : ALow 0 = 0 := by simp [ALow]
      rw [h]
      have h2 : (2:ℝ) + ((0:ℕ):ℝ)/16 = 2 := by norm_num
      rw [h2, Aprime_two]
  | succ m ih =>
      have hm : m < 32 := by omega
      have hmm : m ≤ 32 := by omega
      have hstep := midpoint_step_le m hm
      have hm1 : (2:ℝ) ≤ 2 + (m:ℝ)/16 := by
        have h : (0:ℝ) ≤ (m:ℝ)/16 := by positivity
        linarith
      have hm2 : (2:ℝ) + (m:ℝ)/16 ≤ 2 + ((m:ℝ)+1)/16 := by linarith
      have hsub : Aprime (2 + ((m:ℝ)+1)/16) - Aprime (2 + (m:ℝ)/16)
          = ∫ x in (2 + (m:ℝ)/16)..(2 + ((m:ℝ)+1)/16), Real.log (3/(x-1))/x :=
        Aprime_sub_eq hm1 hm2
      have hsum : ALow (m+1) = ALow m + (1/16) * fLow (2 + ((m:ℝ) + 1/2)/16) := by
        simp only [ALow, Finset.sum_range_succ]
      have hthis : (2:ℝ) + ((m:ℝ)+1)/16 = 2 + ((m+1:ℕ):ℝ)/16 := by push_cast; ring
      rw [hsum, ← hthis]
      linarith [ih hmm, hsub, hstep]

/-! ## §3  The rational upper envelope `envUp` on the grid `3 + k/8`

`envNum` is not explicit (it contains `Aprime` and `log`), but on the grid `3 + k/8`
(`k ≤ 16`) it is dominated by the fully explicit rational number `envUp k`:  replace
`Aprime` by its midpoint lower bound `ALow (2*k)` and the logarithm by `logUpRat`. -/

/-- Explicit rational majorant of `envNum` at the grid points `3 + k/8`, `k ≤ 16`. -/
def envUp (k : ℕ) : ℝ :=
  envC - (3 + envC) * ALow (2 * k) + (4 - envT) * logUpRat ((3 + (k : ℝ) / 8 - 1) / 2)
    - (3 + (k : ℝ) / 8 - 3)

theorem envNum_le_envUp (k : ℕ) (hk : k ≤ 16) : envNum (3 + (k : ℝ) / 8) ≤ envUp k := by
  have hkR : (k : ℝ) ≤ 16 := by exact_mod_cast hk
  have hmin : min (3 + (k : ℝ) / 8 - 1) 4 = 3 + (k : ℝ) / 8 - 1 := by
    rw [min_eq_left_iff]; linarith
  have hA : ALow (2 * k) ≤ Aprime (3 + (k : ℝ) / 8 - 1) := by
    have h := ALow_le_Aprime (2 * k) (by omega)
    have hcast : 2 + ((2 * k : ℕ) : ℝ) / 16 = 3 + (k : ℝ) / 8 - 1 := by push_cast; ring
    rwa [hcast] at h
  have hlog : Real.log ((3 + (k : ℝ) / 8 - 1) / 2) ≤ logUpRat ((3 + (k : ℝ) / 8 - 1) / 2) :=
    le_logUpRat (by linarith)
  have h1 : (0 : ℝ) ≤ 3 + envC := by norm_num [envC]
  have h2 : (0 : ℝ) ≤ 4 - envT := by norm_num [envT]
  have hm1 := mul_le_mul_of_nonneg_left hA h1
  have hm2 := mul_le_mul_of_nonneg_left hlog h2
  have e1 : (envT - 4 : ℝ) = -7843 / 2000 := by norm_num [envT]
  have e2 : (4 - envT : ℝ) = 7843 / 2000 := by norm_num [envT]
  have e3 : (3 + envC : ℝ) = 8923 / 2500 := by norm_num [envC]
  rw [envNum, hmin, envUp, e1, e2, e3] at *
  linarith

theorem envUp_pos (k : ℕ) (hk : k ≤ 16) : 0 < envUp k := by
  have h1 := envNum_le_envUp k hk
  have h2 : (0 : ℝ) < envNum (3 + (k : ℝ) / 8) :=
    envNum_pos (by have : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k; linarith)
  linarith

/-- The envelope is decreasing on the grid (checked numerically). -/
theorem envUp_anti (k : ℕ) (hk : k < 16) : envUp (k + 1) ≤ envUp k := by
  interval_cases k <;> norm_num [envUp, ALow, fLow, logLowRat, logUpRat, envC, envT]

end

end Work.NumberTheory.Chen.APSwitchUpper
