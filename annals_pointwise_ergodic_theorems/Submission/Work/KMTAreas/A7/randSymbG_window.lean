import Mathlib
import Submission.Work.KMTAreas.A7.randSymbG_prep

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySimpa false

namespace Work.KMTAreas.A7

open Finset
open scoped BigOperators

noncomputable section

/-! ## The per-frequency window estimate for the randomised `g`-side symbol

This module isolates the pointwise/window analysis of a single frequency `ξ`:  given scales
`sig`, phases `lam` and coefficients `c` with bounded partial sums, the symbol
`∑_{m ≤ K} c m * g (sig m ·) e (lam m ·)` obeys the three Mikhlin-type bounds at the frequency
`ξ`, with all the input supplied as explicit hypotheses.
-/

/-- **The window estimate.**  For a profile `g` with the sup bounds `M0, M1, M2` (and vanishing
beyond `|u| = 1`), lacunary scales `sig`, phases `lam` with `|ξ| |lam m| ≤ K2 (sig m |ξ|)` and
`|ξ| |lam (m+1) - lam m| ≤ K2 (sig m |ξ| + sig (m+1) |ξ|)`, and coefficients `c` with bounded
partial sums, the three Mikhlin-type bounds hold at the frequency `ξ` with constant
`16 * L * (Csum + 1)`. -/
theorem rSG_window
    {g : ℝ → ℂ} {M0 M1 M2 : ℝ} (hM0 : 0 ≤ M0) (hM1 : 0 ≤ M1) (hM2 : 0 ≤ M2)
    (hg0 : ∀ u : ℝ, ‖g u‖ ≤ M0) (hg1 : ∀ u : ℝ, ‖deriv g u‖ ≤ M1)
    (hg2 : ∀ u : ℝ, ‖iteratedDeriv 2 g u‖ ≤ M2)
    (hv0 : ∀ u : ℝ, 1 ≤ |u| → g u = 0) (hv1 : ∀ u : ℝ, 1 ≤ |u| → deriv g u = 0)
    (hv2 : ∀ u : ℝ, 1 ≤ |u| → iteratedDeriv 2 g u = 0)
    (hdg : ∀ u : ℝ, HasDerivAt g (deriv g u) u)
    (hdg2 : ∀ u : ℝ, HasDerivAt (deriv g) (iteratedDeriv 2 g u) u)
    (hgL : ∀ a b : ℝ, ‖g a - g b‖ ≤ M1 * |a - b|)
    {sig lam : ℕ → ℝ} (hσpos : ∀ m : ℕ, 0 < sig m) (hσmono : ∀ m : ℕ, sig m ≤ sig (m + 1))
    {K2 : ℝ} (hK2 : 0 ≤ K2)
    {K : ℕ} {c : ℕ → ℂ} (hc : ∀ v : ℕ, ‖∑ m ∈ Finset.range (v + 1), c m‖ ≤ 4)
    (hlam2 : ∀ (m : ℕ) (x : ℝ), |x| * |lam m| ≤ K2 * (sig m * |x|))
    (hlam3 : ∀ (m : ℕ) (x : ℝ),
      |x| * |lam (m + 1) - lam m| ≤ K2 * (sig m * |x| + sig (m + 1) * |x|))
    {Csum : ℝ} (hCsum : 0 ≤ Csum)
    (hsumw : ∀ x : ℝ, ∑ i ∈ Finset.range K,
      (sig i * |x| + sig (i + 1) * |x|) * (if sig (i + 1) * |x| ≤ 1 then (1 : ℝ) else 0)
        ≤ 2 * Csum)
    {L : ℝ} (hLnn : 0 ≤ L)
    (hc1L : M0 + M1 + 2 * Real.pi * K2 * M0 ≤ L)
    (hc2L : M2 + 4 * Real.pi * (K2 * M1) + 4 * Real.pi ^ 2 * (K2 ^ 2 * M0) ≤ L)
    (hpi0 : (0 : ℝ) ≤ Real.pi) :
    ∀ ξ : ℝ,
      ‖∑ m ∈ Finset.range (K + 1), c m * (g (sig m * ξ) * ee (lam m * ξ))‖
        ≤ 16 * L * (Csum + 1) ∧
      |ξ| * ‖deriv (fun x : ℝ => ∑ m ∈ Finset.range (K + 1),
          c m * (g (sig m * x) * ee (lam m * x))) ξ‖ ≤ 16 * L * (Csum + 1) ∧
      |ξ| ^ 2 * ‖iteratedDeriv 2 (fun x : ℝ => ∑ m ∈ Finset.range (K + 1),
          c m * (g (sig m * x) * ee (lam m * x))) ξ‖ ≤ 16 * L * (Csum + 1) := by
  intro ξ
  set Ψ : ℕ → ℝ → ℂ := fun m => fun x => g (sig m * x) * ee (lam m * x) with hΨ
  have hΨeq : ∀ m : ℕ, Ψ m = fun x : ℝ => g (sig m * x) * ee (lam m * x) := fun m => rfl
  have hd1val : ∀ (m : ℕ) (x : ℝ), deriv (Ψ m) x
      = (sig m * deriv g (sig m * x) + (2 * Real.pi * Complex.I * (lam m : ℂ)) * g (sig m * x))
          * ee (lam m * x) := by
    intro m x
    have h := (rSG_deriv_modulatedBump_p (g := g) hdg hdg2 (sig m) (lam m)).2.2.1 x
    rw [hΨeq m]
    exact h
  have hd2val : ∀ (m : ℕ) (x : ℝ), iteratedDeriv 2 (Ψ m) x
      = ((sig m) ^ 2 * iteratedDeriv 2 g (sig m * x)
          + 2 * (2 * Real.pi * Complex.I * (lam m : ℂ)) * (sig m * deriv g (sig m * x))
          + (2 * Real.pi * Complex.I * (lam m : ℂ)) ^ 2 * g (sig m * x)) * ee (lam m * x) := by
    intro m x
    have h := (rSG_deriv_modulatedBump_p (g := g) hdg hdg2 (sig m) (lam m)).2.2.2 x
    rw [hΨeq m]
    exact h
  have hd1 : ∀ (m : ℕ) (x : ℝ), HasDerivAt (Ψ m) (deriv (Ψ m) x) x := by
    intro m x
    have h := (rSG_deriv_modulatedBump_p (g := g) hdg hdg2 (sig m) (lam m)).1 x
    rw [hΨeq m, hd1val m x]
    exact h
  have hd2 : ∀ (m : ℕ) (x : ℝ), HasDerivAt (deriv (Ψ m)) (iteratedDeriv 2 (Ψ m) x) x := by
    intro m x
    have h := (rSG_deriv_modulatedBump_p (g := g) hdg hdg2 (sig m) (lam m)).2.1 x
    have hfun : deriv (Ψ m) = fun y : ℝ => (sig m * deriv g (sig m * y)
        + (2 * Real.pi * Complex.I * (lam m : ℂ)) * g (sig m * y)) * ee (lam m * y) :=
      funext fun y => hd1val m y
    rw [hfun, hd2val m x]
    exact h
  change (‖∑ m ∈ Finset.range (K + 1), c m * Ψ m ξ‖ ≤ 16 * L * (Csum + 1) ∧
      |ξ| * ‖deriv (fun x : ℝ => ∑ m ∈ Finset.range (K + 1), c m * Ψ m x) ξ‖
        ≤ 16 * L * (Csum + 1) ∧
      |ξ| ^ 2 * ‖iteratedDeriv 2 (fun x : ℝ => ∑ m ∈ Finset.range (K + 1), c m * Ψ m x) ξ‖
        ≤ 16 * L * (Csum + 1))
  set w : ℕ → ℝ := fun m => sig m * |ξ| with hw
  have hw_def : ∀ m : ℕ, w m = sig m * |ξ| := fun m => by rw [hw]
  set χ : ℕ → ℝ := fun m => if w m ≤ 1 then 1 else 0 with hχ
  have hχ_def : ∀ m : ℕ, χ m = if w m ≤ 1 then 1 else 0 := fun m => by rw [hχ]
  set β : ℕ → ℝ := fun i => (w i + w (i + 1)) * χ (i + 1) + χ i * (1 - χ (i + 1)) with hβ
  have hβ_def : ∀ i : ℕ, β i
      = (w i + w (i + 1)) * χ (i + 1) + χ i * (1 - χ (i + 1)) := fun i => by rw [hβ]
  set CS : ℝ := Csum + 1 with hCS
  have hCS_1 : (1 : ℝ) ≤ CS := by rw [hCS]; linarith
  have hM0c1 : M0 ≤ M0 + M1 + 2 * Real.pi * K2 * M0 := by
    have h2 : (0 : ℝ) ≤ 2 * Real.pi * K2 * M0 := by positivity
    linarith
  have hc1nn : 0 ≤ M0 + M1 + 2 * Real.pi * K2 * M0 := by
    have h2 : (0 : ℝ) ≤ 2 * Real.pi * K2 * M0 := by positivity
    linarith
  have hc2nn : 0 ≤ M2 + 4 * Real.pi * (K2 * M1) + 4 * Real.pi ^ 2 * (K2 ^ 2 * M0) :=
    add_nonneg (add_nonneg hM2 (by positivity)) (by positivity)
  have hwnn : ∀ m : ℕ, 0 ≤ w m := by
    intro m; rw [hw_def m]; exact mul_nonneg (le_of_lt (hσpos m)) (abs_nonneg ξ)
  have hwmono : ∀ m : ℕ, w m ≤ w (m + 1) := by
    intro m; rw [hw_def m, hw_def (m + 1)]
    exact mul_le_mul_of_nonneg_right (hσmono m) (abs_nonneg ξ)
  have hχ01 : ∀ m : ℕ, χ m = 0 ∨ χ m = 1 := by
    intro m
    by_cases h : w m ≤ 1
    · right; rw [hχ_def m]; exact if_pos h
    · left; rw [hχ_def m]; exact if_neg h
  have hχnn : ∀ m : ℕ, 0 ≤ χ m := by
    intro m; rw [hχ_def m]; split <;> norm_num
  have hχle : ∀ m : ℕ, χ m ≤ 1 := by
    intro m; rw [hχ_def m]; split <;> norm_num
  have hχ1w : ∀ m : ℕ, χ m = 1 → w m ≤ 1 := by
    intro m h
    by_contra hc
    rw [hχ_def m, if_neg hc] at h
    exact zero_ne_one h
  have hχ0w : ∀ m : ℕ, χ m = 0 → 1 < w m := by
    intro m h
    by_contra hc
    push_neg at hc
    rw [hχ_def m, if_pos hc] at h
    exact one_ne_zero h
  have hβnn : ∀ i : ℕ, 0 ≤ β i := by
    intro i
    rw [hβ_def i]
    have h1 : 0 ≤ (w i + w (i + 1)) * χ (i + 1) :=
      mul_nonneg (by linarith [hwnn i, hwnn (i + 1)]) (hχnn (i + 1))
    have h2 : 0 ≤ χ i * (1 - χ (i + 1)) :=
      mul_nonneg (hχnn i) (by linarith [hχle (i + 1)])
    linarith
  have hχmono : ∀ m : ℕ, χ (m + 1) ≤ χ m := by
    intro m
    by_cases h : w (m + 1) ≤ 1
    · have h2 : χ (m + 1) = 1 := by rw [hχ_def (m + 1)]; exact if_pos h
      rw [h2]
      have h3 : χ m = 1 := by
        rw [hχ_def m]; exact if_pos (le_trans (hwmono m) h)
      rw [h3]
    · have h2 : χ (m + 1) = 0 := by rw [hχ_def (m + 1)]; exact if_neg h
      rw [h2]; exact hχnn m
  have hlamξ : ∀ m : ℕ, |ξ| * |lam m| ≤ K2 * w m := by
    intro m; rw [hw_def m]; exact hlam2 m ξ
  have hlamξ' : ∀ m : ℕ, |ξ| * |lam (m + 1) - lam m| ≤ K2 * (w m + w (m + 1)) := by
    intro m; rw [hw_def m, hw_def (m + 1)]; exact hlam3 m ξ
  have hvan : ∀ m : ℕ, χ m = 0 →
      Ψ m ξ = 0 ∧ deriv (Ψ m) ξ = 0 ∧ iteratedDeriv 2 (Ψ m) ξ = 0 := by
    intro m h0
    have hw1 : 1 < w m := hχ0w m h0
    have harg : 1 ≤ |sig m * ξ| := by
      rw [hw_def m] at hw1
      rw [abs_mul, abs_of_nonneg (le_of_lt (hσpos m))]
      exact le_of_lt hw1
    refine ⟨?_, ?_, ?_⟩
    · simp only [hΨeq m]
      rw [hv0 _ harg, zero_mul]
    · rw [hd1val m ξ, hv1 _ harg, hv0 _ harg]; ring
    · rw [hd2val m ξ, hv2 _ harg, hv1 _ harg, hv0 _ harg]; ring
  have hsingle0 : ∀ m : ℕ, ‖Ψ m ξ‖ ≤ M0 := by
    intro m
    simp only [hΨeq m]
    rw [norm_mul, rSG_norm_ee, mul_one]
    exact hg0 _
  have hc1nn : 0 ≤ M0 + M1 + 2 * Real.pi * K2 * M0 := by
    have h2 : (0 : ℝ) ≤ 2 * Real.pi * K2 * M0 := by positivity
    linarith
  have hc2nn : 0 ≤ M2 + 4 * Real.pi * (K2 * M1) + 4 * Real.pi ^ 2 * (K2 ^ 2 * M0) :=
    add_nonneg (add_nonneg hM2 (by positivity)) (by positivity)
  have hM0c1 : M0 ≤ M0 + M1 + 2 * Real.pi * K2 * M0 := by
    have h2 : (0 : ℝ) ≤ 2 * Real.pi * K2 * M0 := by positivity
    linarith
  have hsingle1 : ∀ m : ℕ, |ξ| * ‖deriv (Ψ m) ξ‖ ≤ (M0 + M1 + 2 * Real.pi * K2 * M0) * w m := by
    intro m
    rcases hχ01 m with h0 | h1
    · rw [(hvan m h0).2.1, norm_zero, mul_zero]
      exact mul_nonneg hc1nn (hwnn m)
    · have hb := rSG_bump_bounds M0 M1 M2 (sig m) (lam m) ξ K2 hM0 hM1 hM2
        (le_of_lt (hσpos m)) hK2 (fun u => hg0 u) (fun u => hg1 u)
        (fun u => hg2 u) (hlamξ m) (hχ1w m h1)
      rw [hd1val m ξ, hw_def m]
      have hb' : (M1 + 2 * Real.pi * K2 * M0) * (sig m * |ξ|)
          ≤ (M0 + M1 + 2 * Real.pi * K2 * M0) * (sig m * |ξ|) :=
        mul_le_mul_of_nonneg_right (by linarith [hM0])
          (mul_nonneg (le_of_lt (hσpos m)) (abs_nonneg ξ))
      exact hb.2.1.trans hb'
  have hsingle2 : ∀ m : ℕ, |ξ| ^ 2 * ‖iteratedDeriv 2 (Ψ m) ξ‖
      ≤ (M2 + 4 * Real.pi * (K2 * M1) + 4 * Real.pi ^ 2 * (K2 ^ 2 * M0)) * w m := by
    intro m
    rcases hχ01 m with h0 | h1
    · rw [(hvan m h0).2.2, norm_zero, mul_zero]
      exact mul_nonneg hc2nn (hwnn m)
    · have hb := rSG_bump_bounds M0 M1 M2 (sig m) (lam m) ξ K2 hM0 hM1 hM2
        (le_of_lt (hσpos m)) hK2 (fun u => hg0 u) (fun u => hg1 u)
        (fun u => hg2 u) (hlamξ m) (hχ1w m h1)
      rw [hd2val m ξ, hw_def m]
      exact hb.2.2
  have hdiff0 : ∀ i : ℕ, ‖Ψ (i + 1) ξ - Ψ i ξ‖ ≤ (M0 + M1 + 2 * Real.pi * K2 * M0) * β i := by
    intro i
    rcases hχ01 (i + 1) with h0 | h1
    · rcases hχ01 i with h0' | h1'
      · have hβi : β i = 0 := by rw [hβ_def i, h0, h0']; ring
        rw [hβi, mul_zero, (hvan (i + 1) h0).1, (hvan i h0').1, sub_zero, norm_zero]
      · have hβi : β i = 1 := by rw [hβ_def i, h1', h0]; ring
        rw [hβi, mul_one, (hvan (i + 1) h0).1, zero_sub, norm_neg]
        linarith [hsingle0 i, hM0c1]
    · have hw1 : w (i + 1) ≤ 1 := hχ1w (i + 1) h1
      have hβi : β i = w i + w (i + 1) := by rw [hβ_def i, h1]; ring
      rw [hβi]
      simp only [hΨeq (i + 1), hΨeq i]
      rw [show g (sig (i + 1) * ξ) * ee (lam (i + 1) * ξ)
            - g (sig i * ξ) * ee (lam i * ξ)
          = (g (sig (i + 1) * ξ) - g (sig i * ξ)) * ee (lam (i + 1) * ξ)
            + g (sig i * ξ) * (ee (lam (i + 1) * ξ) - ee (lam i * ξ)) by ring]
      refine (norm_add_le _ _).trans ?_
      have hb1 : ‖(g (sig (i + 1) * ξ) - g (sig i * ξ))
          * ee (lam (i + 1) * ξ)‖ ≤ M1 * (w (i + 1) - w i) := by
        have heq : |sig (i + 1) * ξ - sig i * ξ| = w (i + 1) - w i := by
          rw [show sig (i + 1) * ξ - sig i * ξ = (sig (i + 1) - sig i) * ξ by ring, abs_mul,
            abs_of_nonneg (sub_nonneg.mpr (hσmono i)), hw_def]
          ring
        rw [norm_mul, rSG_norm_ee, mul_one]
        calc ‖g (sig (i + 1) * ξ) - g (sig i * ξ)‖
            ≤ M1 * |sig (i + 1) * ξ - sig i * ξ| := hgL _ _
          _ = M1 * (w (i + 1) - w i) := by rw [heq]
      have hb2 : ‖g (sig i * ξ) * (ee (lam (i + 1) * ξ) - ee (lam i * ξ))‖
          ≤ 2 * Real.pi * K2 * M0 * (w i + w (i + 1)) := by
        rw [norm_mul]
        have h2 : ‖ee (lam (i + 1) * ξ) - ee (lam i * ξ)‖
            ≤ 2 * Real.pi * (|ξ| * |lam (i + 1) - lam i|) := by
          refine (rSG_norm_ee_sub_le _ _).trans (le_of_eq ?_)
          rw [show lam (i + 1) * ξ - lam i * ξ = (lam (i + 1) - lam i) * ξ by ring, abs_mul]
          ring
        have h4 := hlamξ' i
        calc ‖g (sig i * ξ)‖ * ‖ee (lam (i + 1) * ξ) - ee (lam i * ξ)‖
            ≤ M0 * (2 * Real.pi * (|ξ| * |lam (i + 1) - lam i|)) :=
              mul_le_mul (hg0 _) h2 (norm_nonneg _) hM0
          _ ≤ M0 * (2 * Real.pi * (K2 * (w i + w (i + 1)))) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h4 (by positivity)) hM0
          _ = 2 * Real.pi * K2 * M0 * (w i + w (i + 1)) := by ring
      calc ‖(g (sig (i + 1) * ξ) - g (sig i * ξ))
            * ee (lam (i + 1) * ξ)‖
            + ‖g (sig i * ξ) * (ee (lam (i + 1) * ξ) - ee (lam i * ξ))‖
          ≤ M1 * (w (i + 1) - w i) + 2 * Real.pi * K2 * M0 * (w i + w (i + 1)) :=
            add_le_add hb1 hb2
        _ ≤ (M0 + M1 + 2 * Real.pi * K2 * M0) * (w i + w (i + 1)) := by
            have hW : (0 : ℝ) ≤ w i + w (i + 1) := by linarith [hwnn i, hwnn (i + 1)]
            have h1 : M1 * (w (i + 1) - w i) ≤ M1 * (w i + w (i + 1)) :=
              mul_le_mul_of_nonneg_left (by linarith [hwnn i]) hM1
            have h2 : (0 : ℝ) ≤ M0 * (w i + w (i + 1)) := mul_nonneg hM0 hW
            linarith
  have hdiff1 : ∀ i : ℕ, |ξ| * ‖deriv (Ψ (i + 1)) ξ - deriv (Ψ i) ξ‖
      ≤ (M0 + M1 + 2 * Real.pi * K2 * M0) * β i := by
    intro i
    rcases hχ01 (i + 1) with h0 | h1
    · rcases hχ01 i with h0' | h1'
      · have hβi : β i = 0 := by rw [hβ_def i, h0, h0']; ring
        rw [hβi, mul_zero, (hvan (i + 1) h0).2.1, (hvan i h0').2.1, sub_zero, norm_zero,
          mul_zero]
      · have hβi : β i = 1 := by rw [hβ_def i, h1', h0]; ring
        rw [hβi, mul_one, (hvan (i + 1) h0).2.1, zero_sub, norm_neg]
        calc |ξ| * ‖deriv (Ψ i) ξ‖ ≤ (M0 + M1 + 2 * Real.pi * K2 * M0) * w i := hsingle1 i
          _ ≤ (M0 + M1 + 2 * Real.pi * K2 * M0) * 1 :=
              mul_le_mul_of_nonneg_left (hχ1w i h1') hc1nn
          _ = M0 + M1 + 2 * Real.pi * K2 * M0 := mul_one _
    · have hβi : β i = w i + w (i + 1) := by rw [hβ_def i, h1]; ring
      rw [hβi]
      calc |ξ| * ‖deriv (Ψ (i + 1)) ξ - deriv (Ψ i) ξ‖
          ≤ |ξ| * (‖deriv (Ψ (i + 1)) ξ‖ + ‖deriv (Ψ i) ξ‖) :=
            mul_le_mul_of_nonneg_left (norm_sub_le _ _) (abs_nonneg ξ)
        _ = |ξ| * ‖deriv (Ψ (i + 1)) ξ‖ + |ξ| * ‖deriv (Ψ i) ξ‖ := by ring
        _ ≤ (M0 + M1 + 2 * Real.pi * K2 * M0) * w (i + 1)
              + (M0 + M1 + 2 * Real.pi * K2 * M0) * w i :=
            add_le_add (hsingle1 (i + 1)) (hsingle1 i)
        _ = (M0 + M1 + 2 * Real.pi * K2 * M0) * (w i + w (i + 1)) := by ring
  have hdiff2 : ∀ i : ℕ, |ξ| ^ 2 * ‖iteratedDeriv 2 (Ψ (i + 1)) ξ - iteratedDeriv 2 (Ψ i) ξ‖
      ≤ (M2 + 4 * Real.pi * (K2 * M1) + 4 * Real.pi ^ 2 * (K2 ^ 2 * M0)) * β i := by
    intro i
    rcases hχ01 (i + 1) with h0 | h1
    · rcases hχ01 i with h0' | h1'
      · have hβi : β i = 0 := by rw [hβ_def i, h0, h0']; ring
        rw [hβi, mul_zero, (hvan (i + 1) h0).2.2, (hvan i h0').2.2, sub_zero, norm_zero,
          mul_zero]
      · have hβi : β i = 1 := by rw [hβ_def i, h1', h0]; ring
        rw [hβi, mul_one, (hvan (i + 1) h0).2.2, zero_sub, norm_neg]
        calc |ξ| ^ 2 * ‖iteratedDeriv 2 (Ψ i) ξ‖
              ≤ (M2 + 4 * Real.pi * (K2 * M1) + 4 * Real.pi ^ 2 * (K2 ^ 2 * M0)) * w i :=
              hsingle2 i
          _ ≤ (M2 + 4 * Real.pi * (K2 * M1) + 4 * Real.pi ^ 2 * (K2 ^ 2 * M0)) * 1 :=
              mul_le_mul_of_nonneg_left (hχ1w i h1') hc2nn
          _ = M2 + 4 * Real.pi * (K2 * M1) + 4 * Real.pi ^ 2 * (K2 ^ 2 * M0) := mul_one _
    · have hβi : β i = w i + w (i + 1) := by rw [hβ_def i, h1]; ring
      rw [hβi]
      calc |ξ| ^ 2 * ‖iteratedDeriv 2 (Ψ (i + 1)) ξ - iteratedDeriv 2 (Ψ i) ξ‖
          ≤ |ξ| ^ 2 * (‖iteratedDeriv 2 (Ψ (i + 1)) ξ‖ + ‖iteratedDeriv 2 (Ψ i) ξ‖) :=
            mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by positivity)
        _ = |ξ| ^ 2 * ‖iteratedDeriv 2 (Ψ (i + 1)) ξ‖ + |ξ| ^ 2 * ‖iteratedDeriv 2 (Ψ i) ξ‖ := by
            ring
        _ ≤ (M2 + 4 * Real.pi * (K2 * M1) + 4 * Real.pi ^ 2 * (K2 ^ 2 * M0)) * w (i + 1)
              + (M2 + 4 * Real.pi * (K2 * M1) + 4 * Real.pi ^ 2 * (K2 ^ 2 * M0)) * w i :=
            add_le_add (hsingle2 (i + 1)) (hsingle2 i)
        _ = (M2 + 4 * Real.pi * (K2 * M1) + 4 * Real.pi ^ 2 * (K2 ^ 2 * M0))
              * (w i + w (i + 1)) := by ring
  have hsumχ : ∑ i ∈ Finset.range K, χ i * (1 - χ (i + 1)) ≤ 1 := by
    have h1 : ∀ i : ℕ, χ i * (1 - χ (i + 1)) = χ i - χ (i + 1) := by
      intro i
      rcases hχ01 i with h0 | h1
      · have hz : χ (i + 1) = 0 := le_antisymm (by rw [← h0]; exact hχmono i) (hχnn (i + 1))
        rw [h0, hz, zero_mul, sub_zero]
      · rw [h1]
        rcases hχ01 (i + 1) with h4 | h4
        · rw [h4]; ring
        · rw [h4]; ring
    rw [Finset.sum_congr rfl (fun i _ => h1 i)]
    have h2 : ∑ i ∈ Finset.range K, (χ i - χ (i + 1)) = χ 0 - χ K := by
      have h := Finset.sum_range_sub (fun i : ℕ => χ i) K
      have hneg : ∑ i ∈ Finset.range K, (χ i - χ (i + 1))
          = - ∑ i ∈ Finset.range K, (χ (i + 1) - χ i) := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl (fun i _ => by ring)
      rw [hneg, h]
      ring
    rw [h2]
    have h3 : 0 ≤ χ K := hχnn K
    have h4 : χ 0 ≤ 1 := hχle 0
    linarith
  have hsumβ : ∑ i ∈ Finset.range K, β i ≤ 2 * Csum + 1 := by
    have hsumw' : ∑ i ∈ Finset.range K, (w i + w (i + 1)) * χ (i + 1) ≤ 2 * Csum := by
      simpa only [hw_def, hχ_def] using hsumw ξ
    have h1 : ∑ i ∈ Finset.range K, β i
        = ∑ i ∈ Finset.range K, (w i + w (i + 1)) * χ (i + 1)
          + ∑ i ∈ Finset.range K, χ i * (1 - χ (i + 1)) := by
      rw [← Finset.sum_add_distrib]
    rw [h1]
    linarith [hsumw', hsumχ]
  have hderivF : ∀ x : ℝ, deriv (fun x : ℝ => ∑ m ∈ Finset.range (K + 1), c m * Ψ m x) x
      = ∑ m ∈ Finset.range (K + 1), c m * deriv (Ψ m) x := by
    intro x
    have hsum : HasDerivAt (∑ i ∈ Finset.range (K + 1), fun y : ℝ => c i * Ψ i y)
        (∑ m ∈ Finset.range (K + 1), c m * deriv (Ψ m) x) x :=
      HasDerivAt.sum (u := Finset.range (K + 1)) (A := fun m y => c m * Ψ m y)
        (A' := fun m => c m * deriv (Ψ m) x) (fun m _ => (hd1 m x).const_mul (c m))
    have hfun : (∑ i ∈ Finset.range (K + 1), fun y : ℝ => c i * Ψ i y)
        = (fun y : ℝ => ∑ i ∈ Finset.range (K + 1), c i * Ψ i y) := by
      funext y
      exact Finset.sum_apply _ _ _
    rw [hfun] at hsum
    exact hsum.deriv
  have hiterF : ∀ x : ℝ,
      iteratedDeriv 2 (fun x : ℝ => ∑ m ∈ Finset.range (K + 1), c m * Ψ m x) x
      = ∑ m ∈ Finset.range (K + 1), c m * iteratedDeriv 2 (Ψ m) x := by
    intro x
    have hsum : HasDerivAt (∑ i ∈ Finset.range (K + 1), fun y : ℝ => c i * deriv (Ψ i) y)
        (∑ m ∈ Finset.range (K + 1), c m * iteratedDeriv 2 (Ψ m) x) x :=
      HasDerivAt.sum (u := Finset.range (K + 1)) (A := fun m y => c m * deriv (Ψ m) y)
        (A' := fun m => c m * iteratedDeriv 2 (Ψ m) x) (fun m _ => (hd2 m x).const_mul (c m))
    have hfun : (∑ i ∈ Finset.range (K + 1), fun y : ℝ => c i * deriv (Ψ i) y)
        = (fun y : ℝ => ∑ i ∈ Finset.range (K + 1), c i * deriv (Ψ i) y) := by
      funext y
      exact Finset.sum_apply _ _ _
    rw [hfun] at hsum
    have h2 : deriv (fun x : ℝ => ∑ m ∈ Finset.range (K + 1), c m * Ψ m x)
        = fun y : ℝ => ∑ m ∈ Finset.range (K + 1), c m * deriv (Ψ m) y :=
      funext fun y => hderivF y
    rw [show iteratedDeriv 2 (fun x : ℝ => ∑ m ∈ Finset.range (K + 1), c m * Ψ m x) x
        = deriv (deriv (fun x : ℝ => ∑ m ∈ Finset.range (K + 1), c m * Ψ m x)) x from by
      rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]]
    rw [h2]
    exact hsum.deriv
  have hfin0 : ‖∑ m ∈ Finset.range (K + 1), c m * Ψ m ξ‖ ≤ 16 * L * CS := by
    have h := rSG_abel_sum_bound K c (fun i => Ψ i ξ) hc
    have h2 : ∑ i ∈ Finset.range K, ‖Ψ (i + 1) ξ - Ψ i ξ‖
        ≤ (M0 + M1 + 2 * Real.pi * K2 * M0) * ∑ i ∈ Finset.range K, β i := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun i _ => hdiff0 i)
    have h3 : (M0 + M1 + 2 * Real.pi * K2 * M0) * ∑ i ∈ Finset.range K, β i
        ≤ L * (2 * Csum + 1) := mul_le_mul hc1L hsumβ (Finset.sum_nonneg (fun i _ => hβnn i)) hLnn
    have h4 : 4 * ‖Ψ K ξ‖ ≤ 4 * L := by
      have h5 : ‖Ψ K ξ‖ ≤ M0 := hsingle0 K
      have h6 : M0 ≤ L := le_trans hM0c1 hc1L
      linarith
    have h6 : 4 * ∑ i ∈ Finset.range K, ‖Ψ (i + 1) ξ - Ψ i ξ‖ ≤ 4 * (L * (2 * Csum + 1)) :=
      mul_le_mul_of_nonneg_left (h2.trans h3) (by norm_num)
    calc ‖∑ m ∈ Finset.range (K + 1), c m * Ψ m ξ‖
        ≤ 4 * ‖Ψ K ξ‖ + 4 * ∑ i ∈ Finset.range K, ‖Ψ (i + 1) ξ - Ψ i ξ‖ := h
      _ ≤ 4 * L + 4 * (L * (2 * Csum + 1)) := add_le_add h4 h6
      _ ≤ 16 * L * CS := by
          have h7 : (1 : ℝ) ≤ CS := hCS_1
          have h8 : 2 * Csum + 1 ≤ 2 * CS := by rw [hCS]; linarith
          have h10 : L * (2 * Csum + 1) ≤ L * (2 * CS) :=
            mul_le_mul_of_nonneg_left h8 hLnn
          have h9 : 4 * (L * (2 * Csum + 1)) ≤ 8 * L * CS := by
            calc 4 * (L * (2 * Csum + 1)) ≤ 4 * (L * (2 * CS)) :=
                  mul_le_mul_of_nonneg_left h10 (by norm_num)
              _ = 8 * L * CS := by ring
          have h12 : (1 : ℝ) ≤ 2 * CS := by linarith [hCS_1]
          have h11 : 4 * L ≤ 8 * L * CS := by
            calc 4 * L = 4 * L * 1 := (mul_one _).symm
              _ ≤ 4 * L * (2 * CS) := mul_le_mul_of_nonneg_left h12 (by positivity)
              _ = 8 * L * CS := by ring
          linarith
  have hfin1 : |ξ| * ‖deriv (fun x : ℝ => ∑ m ∈ Finset.range (K + 1), c m * Ψ m x) ξ‖
      ≤ 16 * L * CS := by
    rw [hderivF ξ]
    have h := rSG_abel_sum_bound K c (fun i => deriv (Ψ i) ξ) hc
    have h2 : |ξ| * ∑ i ∈ Finset.range K, ‖deriv (Ψ (i + 1)) ξ - deriv (Ψ i) ξ‖
        ≤ (M0 + M1 + 2 * Real.pi * K2 * M0) * ∑ i ∈ Finset.range K, β i := by
      rw [Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_le_sum (fun i _ => hdiff1 i)
    have h3 : (M0 + M1 + 2 * Real.pi * K2 * M0) * ∑ i ∈ Finset.range K, β i
        ≤ L * (2 * Csum + 1) := mul_le_mul hc1L hsumβ (Finset.sum_nonneg (fun i _ => hβnn i)) hLnn
    have h4 : |ξ| * ‖deriv (Ψ K) ξ‖ ≤ L := by
      rcases hχ01 K with h0 | h1
      · rw [(hvan K h0).2.1, norm_zero, mul_zero]; exact hLnn
      · calc |ξ| * ‖deriv (Ψ K) ξ‖ ≤ (M0 + M1 + 2 * Real.pi * K2 * M0) * w K := hsingle1 K
          _ ≤ (M0 + M1 + 2 * Real.pi * K2 * M0) * 1 :=
              mul_le_mul_of_nonneg_left (hχ1w K h1) (by linarith [hc1L])
          _ = M0 + M1 + 2 * Real.pi * K2 * M0 := mul_one _
          _ ≤ L := hc1L
    have h6 : 4 * (|ξ| * ∑ i ∈ Finset.range K, ‖deriv (Ψ (i + 1)) ξ - deriv (Ψ i) ξ‖)
        ≤ 4 * (L * (2 * Csum + 1)) :=
      mul_le_mul_of_nonneg_left (h2.trans h3) (by norm_num)
    calc |ξ| * ‖∑ m ∈ Finset.range (K + 1), c m * deriv (Ψ m) ξ‖
        ≤ |ξ| * (4 * ‖deriv (Ψ K) ξ‖
            + 4 * ∑ i ∈ Finset.range K, ‖deriv (Ψ (i + 1)) ξ - deriv (Ψ i) ξ‖) :=
          mul_le_mul_of_nonneg_left h (abs_nonneg ξ)
      _ = 4 * (|ξ| * ‖deriv (Ψ K) ξ‖)
            + 4 * (|ξ| * ∑ i ∈ Finset.range K, ‖deriv (Ψ (i + 1)) ξ - deriv (Ψ i) ξ‖) := by
          ring
      _ ≤ 4 * L + 4 * (L * (2 * Csum + 1)) := by
          exact add_le_add (by linarith [h4]) h6
      _ ≤ 16 * L * CS := by
          have h7 : (1 : ℝ) ≤ CS := hCS_1
          have h8 : 2 * Csum + 1 ≤ 2 * CS := by rw [hCS]; linarith
          have h10 : L * (2 * Csum + 1) ≤ L * (2 * CS) :=
            mul_le_mul_of_nonneg_left h8 hLnn
          have h9 : 4 * (L * (2 * Csum + 1)) ≤ 8 * L * CS := by
            calc 4 * (L * (2 * Csum + 1)) ≤ 4 * (L * (2 * CS)) :=
                  mul_le_mul_of_nonneg_left h10 (by norm_num)
              _ = 8 * L * CS := by ring
          have h12 : (1 : ℝ) ≤ 2 * CS := by linarith [hCS_1]
          have h11 : 4 * L ≤ 8 * L * CS := by
            calc 4 * L = 4 * L * 1 := (mul_one _).symm
              _ ≤ 4 * L * (2 * CS) := mul_le_mul_of_nonneg_left h12 (by positivity)
              _ = 8 * L * CS := by ring
          linarith
  have hfin2 : |ξ| ^ 2
      * ‖iteratedDeriv 2 (fun x : ℝ => ∑ m ∈ Finset.range (K + 1), c m * Ψ m x) ξ‖
      ≤ 16 * L * CS := by
    rw [hiterF ξ]
    have h := rSG_abel_sum_bound K c (fun i => iteratedDeriv 2 (Ψ i) ξ) hc
    have h2 : |ξ| ^ 2
          * ∑ i ∈ Finset.range K, ‖iteratedDeriv 2 (Ψ (i + 1)) ξ - iteratedDeriv 2 (Ψ i) ξ‖
        ≤ (M2 + 4 * Real.pi * (K2 * M1) + 4 * Real.pi ^ 2 * (K2 ^ 2 * M0))
            * ∑ i ∈ Finset.range K, β i := by
      rw [Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_le_sum (fun i _ => hdiff2 i)
    have h3 : (M2 + 4 * Real.pi * (K2 * M1) + 4 * Real.pi ^ 2 * (K2 ^ 2 * M0))
          * ∑ i ∈ Finset.range K, β i ≤ L * (2 * Csum + 1) :=
      mul_le_mul hc2L hsumβ (Finset.sum_nonneg (fun i _ => hβnn i)) hLnn
    have h4 : |ξ| ^ 2 * ‖iteratedDeriv 2 (Ψ K) ξ‖ ≤ L := by
      rcases hχ01 K with h0 | h1
      · rw [(hvan K h0).2.2, norm_zero, mul_zero]; exact hLnn
      · calc |ξ| ^ 2 * ‖iteratedDeriv 2 (Ψ K) ξ‖
            ≤ (M2 + 4 * Real.pi * (K2 * M1) + 4 * Real.pi ^ 2 * (K2 ^ 2 * M0)) * w K :=
            hsingle2 K
          _ ≤ (M2 + 4 * Real.pi * (K2 * M1) + 4 * Real.pi ^ 2 * (K2 ^ 2 * M0)) * 1 :=
              mul_le_mul_of_nonneg_left (hχ1w K h1) (by linarith [hc2L])
          _ = M2 + 4 * Real.pi * (K2 * M1) + 4 * Real.pi ^ 2 * (K2 ^ 2 * M0) := mul_one _
          _ ≤ L := hc2L
    have h6 : 4 * (|ξ| ^ 2
          * ∑ i ∈ Finset.range K, ‖iteratedDeriv 2 (Ψ (i + 1)) ξ - iteratedDeriv 2 (Ψ i) ξ‖)
        ≤ 4 * (L * (2 * Csum + 1)) :=
      mul_le_mul_of_nonneg_left (h2.trans h3) (by norm_num)
    calc |ξ| ^ 2 * ‖∑ m ∈ Finset.range (K + 1), c m * iteratedDeriv 2 (Ψ m) ξ‖
        ≤ |ξ| ^ 2 * (4 * ‖iteratedDeriv 2 (Ψ K) ξ‖
            + 4 * ∑ i ∈ Finset.range K,
                ‖iteratedDeriv 2 (Ψ (i + 1)) ξ - iteratedDeriv 2 (Ψ i) ξ‖) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = 4 * (|ξ| ^ 2 * ‖iteratedDeriv 2 (Ψ K) ξ‖)
            + 4 * (|ξ| ^ 2 * ∑ i ∈ Finset.range K,
                ‖iteratedDeriv 2 (Ψ (i + 1)) ξ - iteratedDeriv 2 (Ψ i) ξ‖) := by
          ring
      _ ≤ 4 * L + 4 * (L * (2 * Csum + 1)) := by
          exact add_le_add (by linarith [h4]) h6
      _ ≤ 16 * L * CS := by
          have h7 : (1 : ℝ) ≤ CS := hCS_1
          have h8 : 2 * Csum + 1 ≤ 2 * CS := by rw [hCS]; linarith
          have h10 : L * (2 * Csum + 1) ≤ L * (2 * CS) :=
            mul_le_mul_of_nonneg_left h8 hLnn
          have h9 : 4 * (L * (2 * Csum + 1)) ≤ 8 * L * CS := by
            calc 4 * (L * (2 * Csum + 1)) ≤ 4 * (L * (2 * CS)) :=
                  mul_le_mul_of_nonneg_left h10 (by norm_num)
              _ = 8 * L * CS := by ring
          have h12 : (1 : ℝ) ≤ 2 * CS := by linarith [hCS_1]
          have h11 : 4 * L ≤ 8 * L * CS := by
            calc 4 * L = 4 * L * 1 := (mul_one _).symm
              _ ≤ 4 * L * (2 * CS) := mul_le_mul_of_nonneg_left h12 (by positivity)
              _ = 8 * L * CS := by ring
          linarith
  exact ⟨hfin0, hfin1, hfin2⟩

end

end Work.KMTAreas.A7
