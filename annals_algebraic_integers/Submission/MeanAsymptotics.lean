import Submission.Asymptotics
import Mathlib
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-!
# Asymptotics for the root-mean convergence (Gap B keystone)

The keystone's replacement for the RSphere/Saff–Totik input is the per-`n`
root-mean clause of `Contracts.EarlyPolynomialData`:

    |rootMeanReal (R n) − ∫x∂μ| ≤ Cm·(mFloor B n + 1)/n   for n ≥ N0,

with `mFloor B n = ⌊B√n·log n⌋`.  This module supplies the generic
asymptotics that turn that bound into a `Tendsto`:

1. `log n / √n → 0` along the naturals;
2. `Cm·(⌊B√n log n⌋ + 1)/n → 0` for `0 < B`, `0 ≤ Cm` (the floor is
   `O(√n·log n)` and `√n·log n/n → 0`);
3. a squeeze: pointwise `|a n − L| ≤ b n` with `b n → 0` forces `a n → L`.

Namespace `Submission.MeanAsymptotics`.  Only Mathlib + `Submission.Asymptotics`
(which supplies `Contracts.mFloor` / `mFloor_le`).
-/

noncomputable section

open Filter
open scoped Real Topology

namespace Submission.MeanAsymptotics

open Submission.Contracts

/-- `Real.log (n:ℝ) / Real.sqrt (n:ℝ) → 0` along the naturals. -/
lemma tendsto_log_div_sqrt :
    Tendsto (fun n : ℕ => Real.log (n : ℝ) / Real.sqrt (n : ℝ)) atTop (𝓝 0) := by
  have hlo : Real.log =o[atTop] (fun x : ℝ => x ^ (1 / 2 : ℝ)) :=
    isLittleO_log_rpow_atTop (r := (1 / 2 : ℝ)) (by norm_num)
  have hdiv : Tendsto (fun x : ℝ => Real.log x / x ^ (1 / 2 : ℝ)) atTop (𝓝 0) :=
    hlo.tendsto_div_nhds_zero
  have hnat : Tendsto (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ) ^ (1 / 2 : ℝ)) atTop (𝓝 0) :=
    hdiv.comp tendsto_natCast_atTop_atTop
  simpa [Real.sqrt_eq_rpow] using hnat

/-- `1/(n:ℝ) → 0` along the naturals. -/
lemma tendsto_inv_nat : Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
  have h := (tendsto_inv_atTop_zero (𝕜 := ℝ)).comp tendsto_natCast_atTop_atTop
  simpa [Function.comp_def, one_div] using h

/-- Squeeze: `0 ≤ a n`, `a n ≤ b n` pointwise eventually and `b n → 0`
forces `a n → 0`. -/
lemma tendsto_of_nonneg_le {a b : ℕ → ℝ}
    (hb : Tendsto b atTop (𝓝 0))
    (h0 : ∀ᶠ n in atTop, 0 ≤ a n)
    (hab : ∀ᶠ n in atTop, a n ≤ b n) : Tendsto a atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' ?_ hb h0 hab
  exact (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 (0 : ℝ)))

/-- Squeeze for convergence to a limit: pointwise `|a n − L| ≤ b n`
eventually and `b n → 0` force `a n → L`. -/
lemma tendsto_of_abs_sub_le {a : ℕ → ℝ} {L : ℝ} {b : ℕ → ℝ}
    (hb : Tendsto b atTop (𝓝 0))
    (h : ∀ᶠ n in atTop, |a n - L| ≤ b n) : Tendsto a atTop (𝓝 L) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply tendsto_of_nonneg_le (a := fun n => ‖a n - L‖) (b := b)
  · exact hb
  · filter_upwards with n
    exact norm_nonneg (a n - L)
  · filter_upwards [h] with n hn
    simpa [Real.norm_eq_abs] using hn

/-- `Cm·(mFloor B n + 1)/n → 0` along the naturals (`0 < B`, `0 ≤ Cm`). -/
lemma tendsto_mFloor_mean_zero (B Cm : ℝ) (hB : 0 < B) (hCm : 0 ≤ Cm) :
    Tendsto (fun n : ℕ => Cm * ((mFloor B n : ℝ) + 1) / (n : ℝ)) atTop (𝓝 0) := by
  have hB1 := tendsto_log_div_sqrt
  have hB1' : Tendsto (fun n : ℕ => Cm * B * (Real.log (n : ℝ) / Real.sqrt (n : ℝ)))
      atTop (𝓝 0) := by
    simpa using (hB1.const_mul (Cm * B))
  have hInv' : Tendsto (fun n : ℕ => Cm * ((1 : ℝ) / (n : ℝ))) atTop (𝓝 0) := by
    simpa using (tendsto_inv_nat.const_mul Cm)
  have hsum : Tendsto (fun n : ℕ =>
      Cm * B * (Real.log (n : ℝ) / Real.sqrt (n : ℝ)) + Cm * ((1 : ℝ) / (n : ℝ)))
      atTop (𝓝 0) := by
    simpa using (hB1'.add hInv')
  -- algebraic identity: (B·s·l + 1)/n = B·(l/s) + 1/n when s·s = n
  have hdecomp : ∀ {s n l B : ℝ}, s * s = n → s ≠ 0 → n ≠ 0 →
      (B * s * l + 1) / n = B * (l / s) + 1 / n := by
    intro s n l B hsn hs hn
    have hpow : s ^ 2 = n := by
      rw [pow_two]
      exact hsn
    field_simp [hpow, hs, hn]
    ring_nf
    rw [hpow]
    ring
  -- upper function: Cm·(B·√n·log n + 1)/n is eventually equal to the sum
  have hUeq : ∀ᶠ n : ℕ in atTop,
      Cm * B * (Real.log (n : ℝ) / Real.sqrt (n : ℝ)) + Cm * ((1 : ℝ) / (n : ℝ))
        = Cm * (B * Real.sqrt (n : ℝ) * Real.log (n : ℝ) + 1) / (n : ℝ) := by
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn2
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : (0 : ℕ) < n)
    have hs0 : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnpos
    have hsq : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt (le_of_lt hnpos)
    have hss : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) := by
      rw [pow_two] at hsq
      exact hsq
    have hEq := hdecomp (s := Real.sqrt (n : ℝ)) (n := (n : ℝ))
      (l := Real.log (n : ℝ)) (B := B) hss hs0.ne' (ne_of_gt hnpos)
    calc
      Cm * B * (Real.log (n : ℝ) / Real.sqrt (n : ℝ)) + Cm * ((1 : ℝ) / (n : ℝ))
          = Cm * (B * (Real.log (n : ℝ) / Real.sqrt (n : ℝ)) + 1 / (n : ℝ)) := by ring
      _ = Cm * ((B * Real.sqrt (n : ℝ) * Real.log (n : ℝ) + 1) / (n : ℝ)) := by rw [← hEq]
      _ = Cm * (B * Real.sqrt (n : ℝ) * Real.log (n : ℝ) + 1) / (n : ℝ) := by ring
  have hU : Tendsto (fun n : ℕ =>
      Cm * (B * Real.sqrt (n : ℝ) * Real.log (n : ℝ) + 1) / (n : ℝ)) atTop (𝓝 0) :=
    hsum.congr' hUeq
  -- squeeze: 0 ≤ target ≤ U
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (f := fun n : ℕ => Cm * ((mFloor B n : ℝ) + 1) / (n : ℝ))
    (g := fun _ : ℕ => (0 : ℝ))
    (h := fun n : ℕ => Cm * (B * Real.sqrt (n : ℝ) * Real.log (n : ℝ) + 1) / (n : ℝ))
    ?_ hU ?_ ?_
  · exact (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 (0 : ℝ)))
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn1
    have hmn : 0 ≤ (mFloor B n : ℝ) + 1 := by positivity
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : (0 : ℕ) < n)
    exact div_nonneg (mul_nonneg hCm hmn) (le_of_lt hnpos)
  · filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn2
    have hn0 : 0 < (n : ℝ) := by exact_mod_cast (by omega : (0 : ℕ) < n)
    have hml := mFloor_le hB.le hn2
    have hm1 : (mFloor B n : ℝ) + 1 ≤ B * Real.sqrt (n : ℝ) * Real.log (n : ℝ) + 1 := by
      nlinarith
    have hmul : Cm * ((mFloor B n : ℝ) + 1) ≤ Cm * (B * Real.sqrt (n : ℝ) * Real.log (n : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left hm1 hCm
    exact div_le_div_of_nonneg_right hmul (le_of_lt hn0)

end Submission.MeanAsymptotics
