/-
# ZeroFreeTables/XY/SupEs

The fifth-order bound `Eₛ(λ) ≤ 3/500` for `0 ≤ λ ≤ 628/1000`, where

  `Eₛ(λ) = ∫₀^{3/2} (sinh(λx) - λx) f(x) dx`

and `f = xyFf = tf72f (4/3)` is HB Lemma 7.2's test function with `λ = 4/3`.

## Argument

On `[0, 3/2]` the test function is the quintic `xyP`
(`tf72f43_eq`), and its moments `∫₀^{3/2} x^j xyP = xyM j` are known
(`xyP_moment`).  The pointwise Taylor bound

  `sinh u - u ≤ u³/6 + u⁵/100   (0 ≤ u ≤ 1)`

(proved here from `Real.exp_bound`) turns `Eₛ(λ)` into
`λ³/6 · xyM 3 + (6/5)·λ⁵/120 · xyM 5 = λ³/42 + 3λ⁵/3520`, and monotonicity in `λ`
together with `λ ≤ 628/1000` gives the claimed constant
(`(628/1000)³/42 + (6/5)(628/1000)⁵(9/88)/120 = 0.0059968… ≤ 3/500 = 0.006`).
-/
import Mathlib
import Submission.Work.ZeroFreeTables.XY.LamPrimeData
import Submission.Work.ZeroFreeTables.XY.xyMainLt

open MeasureTheory intervalIntegral Finset
open scoped BigOperators
noncomputable section

namespace Work.ZeroFreeTables.XY

/-! ### A pointwise Taylor bound for `sinh` -/

/-- For `0 ≤ u ≤ 1`, `sinh u - u ≤ u³/6 + u⁵/100`.

Obtained from the two-sided Taylor bound `Real.exp_bound` for `exp u` and `exp (-u)`
(each with `n = 6`, error `u⁶·7/4320`). -/
private lemma sinh_sub_self_le (u : ℝ) (h0 : 0 ≤ u) (hu : u ≤ 1) :
    Real.sinh u - u ≤ u^3/6 + u^5/100 := by
  have h6 : (0:ℕ) < 6 := by norm_num
  have hS1 : (∑ m ∈ Finset.range 6, u ^ m / (↑(m.factorial) : ℝ))
      = 1 + u + u^2/2 + u^3/6 + u^4/24 + u^5/120 := by
    rw [Finset.sum_range_succ (fun m => u ^ m / (↑(m.factorial) : ℝ)) 5,
        Finset.sum_range_succ (fun m => u ^ m / (↑(m.factorial) : ℝ)) 4,
        Finset.sum_range_succ (fun m => u ^ m / (↑(m.factorial) : ℝ)) 3,
        Finset.sum_range_succ (fun m => u ^ m / (↑(m.factorial) : ℝ)) 2,
        Finset.sum_range_succ (fun m => u ^ m / (↑(m.factorial) : ℝ)) 1,
        Finset.sum_range_one]
    norm_num [Nat.factorial]
    try ring
  have hS2 : (∑ m ∈ Finset.range 6, (-u) ^ m / (↑(m.factorial) : ℝ))
      = 1 - u + u^2/2 - u^3/6 + u^4/24 - u^5/120 := by
    rw [Finset.sum_range_succ (fun m => (-u) ^ m / (↑(m.factorial) : ℝ)) 5,
        Finset.sum_range_succ (fun m => (-u) ^ m / (↑(m.factorial) : ℝ)) 4,
        Finset.sum_range_succ (fun m => (-u) ^ m / (↑(m.factorial) : ℝ)) 3,
        Finset.sum_range_succ (fun m => (-u) ^ m / (↑(m.factorial) : ℝ)) 2,
        Finset.sum_range_succ (fun m => (-u) ^ m / (↑(m.factorial) : ℝ)) 1,
        Finset.sum_range_one]
    norm_num [Nat.factorial]
    try ring
  have hb1 := Real.exp_bound (x := u) (by simpa [abs_of_nonneg h0] using hu) h6
  have hb2 := Real.exp_bound (x := -u) (by simpa [abs_of_nonneg h0] using hu) h6
  have h1 : Real.exp u - (1 + u + u^2/2 + u^3/6 + u^4/24 + u^5/120)
      ≤ u^6 * (((Nat.succ 6 : ℕ) : ℝ)
          / (((Nat.factorial 6 : ℕ) : ℝ) * ((6:ℕ) : ℝ))) := by
    have h := (abs_le.1 hb1).2
    rw [hS1, abs_of_nonneg h0] at h
    exact h
  have h2 : (1 - u + u^2/2 - u^3/6 + u^4/24 - u^5/120)
      - u^6 * (((Nat.succ 6 : ℕ) : ℝ)
          / (((Nat.factorial 6 : ℕ) : ℝ) * ((6:ℕ) : ℝ)))
      ≤ Real.exp (-u) := by
    have h := (abs_le.1 hb2).1
    rw [hS2, abs_neg, abs_of_nonneg h0] at h
    linarith [h]
  have herr : (((Nat.succ 6 : ℕ) : ℝ)
      / (((Nat.factorial 6 : ℕ) : ℝ) * ((6:ℕ) : ℝ))) = 7/4320 := by
    norm_num [Nat.factorial]
  rw [herr] at h1 h2
  have h65 : u^6 ≤ u^5 := by
    nlinarith [mul_nonneg (pow_nonneg h0 5) (by linarith : (0:ℝ) ≤ 1 - u)]
  have hCsmall : u^6 * (7/4320) ≤ u^5/600 := by
    have hc : (7/4320:ℝ) ≤ 1/600 := by norm_num
    calc u^6 * (7/4320) ≤ u^5 * (7/4320) := mul_le_mul_of_nonneg_right h65 (by norm_num)
      _ ≤ u^5 * (1/600) := mul_le_mul_of_nonneg_left hc (pow_nonneg h0 5)
      _ = u^5/600 := by ring
  have hsum2 : Real.exp u - Real.exp (-u)
      ≤ 2*u + 2*u^3/6 + 2*u^5/120 + 2*(u^6 * (7/4320)) := by
    linarith [h1, h2]
  rw [Real.sinh_eq]
  linarith [hsum2, hCsmall]

/-! ### Continuity of `xyP`, and `xyFf` vs `xyP` -/

private lemma continuous_xyP : Continuous xyP := by
  unfold xyP
  fun_prop

private lemma xyFf_eq_xyP (x : ℝ) (hx : x ∈ Set.Icc (0:ℝ) (3/2)) : xyFf x = xyP x := by
  unfold xyFf
  exact tf72f43_eq x hx

private lemma xyM_three : xyM 3 = 1/7 := by
  unfold xyM; norm_num

private lemma xyM_five : xyM 5 = 9/88 := by
  unfold xyM; norm_num

/-! ### The main bound -/

theorem SupEs {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 628/1000) :
    Work.ZeroFreeTables.XY.Esc lam ≤ 3/500 := by
  have hI1 : IntervalIntegrable
      (fun x : ℝ => (Real.sinh (lam*x) - lam*x) * xyP x) volume (0:ℝ) (3/2) :=
    Continuous.intervalIntegrable
      ((by fun_prop : Continuous fun x : ℝ => Real.sinh (lam*x) - lam*x).mul continuous_xyP)
      0 (3/2)
  have hI2 : IntervalIntegrable
      (fun x : ℝ => (lam^3/6 * x^3 + (6/5)*(lam^5*x^5/120)) * xyP x) volume (0:ℝ) (3/2) :=
    Continuous.intervalIntegrable
      ((by fun_prop : Continuous fun x : ℝ => lam^3/6 * x^3 + (6/5)*(lam^5*x^5/120)).mul
        continuous_xyP)
      0 (3/2)
  have hpt : ∀ x ∈ Set.Icc (0:ℝ) (3/2),
      (Real.sinh (lam*x) - lam*x) * xyP x
        ≤ (lam^3/6 * x^3 + (6/5)*(lam^5*x^5/120)) * xyP x := by
    intro x hx
    have hx0 : 0 ≤ x := hx.1
    have hlx0 : 0 ≤ lam * x := mul_nonneg h0 hx0
    have hlx1 : lam * x ≤ 1 := by
      have h2 : lam * x ≤ (628/1000) * (3/2) :=
        mul_le_mul h1 hx.2 hx0 (by norm_num)
      linarith [h2]
    have hb := sinh_sub_self_le (lam*x) hlx0 hlx1
    have hf : 0 ≤ xyP x := xyP_nonneg x hx0 hx.2
    have hb' : Real.sinh (lam*x) - lam*x ≤ lam^3/6 * x^3 + (6/5)*(lam^5*x^5/120) := by
      have hA : (lam*x)^3/6 = lam^3/6 * x^3 := by ring
      have hB : (lam*x)^5/100 = (6/5)*(lam^5*x^5/120) := by ring
      rw [hA, hB] at hb
      exact hb
    exact mul_le_mul_of_nonneg_right hb' hf
  have hI3 : IntervalIntegrable (fun x : ℝ => x^3 * xyP x) volume (0:ℝ) (3/2) :=
    Continuous.intervalIntegrable ((continuous_id.pow 3).mul continuous_xyP) 0 (3/2)
  have hI5 : IntervalIntegrable (fun x : ℝ => x^5 * xyP x) volume (0:ℝ) (3/2) :=
    Continuous.intervalIntegrable ((continuous_id.pow 5).mul continuous_xyP) 0 (3/2)
  have hEval : (∫ x in (0:ℝ)..(3/2), (lam^3/6 * x^3 + (6/5)*(lam^5*x^5/120)) * xyP x)
      = lam^3/6 * (1/7) + (6/5)*lam^5/120*(9/88) := by
    have hcongr : (∫ x in (0:ℝ)..(3/2), (lam^3/6 * x^3 + (6/5)*(lam^5*x^5/120)) * xyP x)
        = ∫ x in (0:ℝ)..(3/2),
            ((lam^3/6) * (x^3 * xyP x) + ((6/5)*lam^5/120) * (x^5 * xyP x)) := by
      apply intervalIntegral.integral_congr
      intro x hx
      show (lam^3/6 * x^3 + (6/5)*(lam^5*x^5/120)) * xyP x
        = ((lam^3/6) * (x^3 * xyP x) + ((6/5)*lam^5/120) * (x^5 * xyP x))
      ring
    rw [hcongr,
        intervalIntegral.integral_add (hI3.const_mul (lam^3/6))
          (hI5.const_mul ((6/5)*lam^5/120)),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
        xyP_moment 3, xyP_moment 5, xyM_three, xyM_five]
    try ring
  have hFF : (∫ x in (0:ℝ)..(3/2), (Real.sinh (lam*x) - lam*x) * xyFf x)
      = ∫ x in (0:ℝ)..(3/2), (Real.sinh (lam*x) - lam*x) * xyP x := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 3/2)] at hx
    show (Real.sinh (lam*x) - lam*x) * xyFf x = (Real.sinh (lam*x) - lam*x) * xyP x
    rw [xyFf_eq_xyP x hx]
  have hmain : (∫ x in (0:ℝ)..(3/2), (Real.sinh (lam*x) - lam*x) * xyFf x)
      ≤ lam^3/6 * (1/7) + (6/5)*lam^5/120*(9/88) := by
    rw [hFF, ← hEval]
    exact intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 3/2) hI1 hI2 hpt
  unfold Esc
  refine le_trans hmain ?_
  have hL3 : lam^3 ≤ (628/1000:ℝ)^3 := by gcongr
  have hL5 : lam^5 ≤ (628/1000:ℝ)^5 := by gcongr
  have e1 : lam^3/6*(1/7) ≤ (628/1000:ℝ)^3/6*(1/7) := by nlinarith [hL3]
  have e2 : (6/5)*lam^5/120*(9/88) ≤ (6/5)*(628/1000:ℝ)^5/120*(9/88) := by nlinarith [hL5]
  have hnum : (628/1000:ℝ)^3/6*(1/7) + (6/5)*(628/1000:ℝ)^5/120*(9/88) ≤ 3/500 := by
    norm_num
  linarith [e1, e2, hnum]

end Work.ZeroFreeTables.XY
