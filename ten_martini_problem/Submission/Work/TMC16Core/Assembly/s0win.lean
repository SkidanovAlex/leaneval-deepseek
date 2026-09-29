import Mathlib
import Submission.Work.TMC16Core.Defs
import Submission.Work.TMC16Core.Assembly.S0

/-!
# Windows and endgame of the `s = 0` branch (pure arithmetic assembly)

This file discharges the arithmetic content of the `s = 0` branch of AJ's Lemma 9.4(2), in the
`IsRegularBig`  ("big window") formulation used by `Assembly.S0`.

Concretely, with `K ≥ 40`, `c = ⌈K/40⌉ = (K+39)/40`, `U = c + 1`, `a = k₀ - K - c` and `M ≥ 0`,
the two windows
`W₁ = W1s0 a U = [a, a+2U-1]`  and  `W₂ = W2s0 a U (K+1) M = [M+a+2U, M+a+K]`
satisfy:

* `2U ≤ K+1` and `W₁ ⊔ W₂` has exactly `K+1` sites (they are disjoint);
* every site of `W₁` lies in the singular strip `[-(1-δ)K, -δK]`, `δ = 1/40 + 1/K`;
* every site of `W₂` is `K/40`-interior to the `K`-window ending at `M + k₀`.

The geometry hypotheses `K/20 + 3 ≤ k₀ ≤ 19K/20 - 3` are exactly what makes these hold: the
window `[a, a+2U-1]` sits strictly inside the `(1/40)`-neighbourhood of the singular point `0`,
and `M + k₀` sits `⌈K/40⌉` away from both ends of `W₂`.
-/

namespace Work.TMC16Core.Assembly

open Work.TMC16Core
open Work.TMC16Core.Core

theorem s0win {K : ℕ} {k₀ M : ℤ} {c : ℕ} {a : ℤ} {U : ℕ}
    (hK : 40 ≤ K) (hc : c = (K + 39) / 40) (ha : a = k₀ - (K : ℤ) - (c : ℤ)) (hU : U = c + 1)
    (hM : 0 ≤ M)
    (hlo : (K : ℝ) / 20 + 3 ≤ (k₀ : ℝ)) (hhi : (k₀ : ℝ) ≤ 95 * (K : ℝ) / 100 - 3) :
    2 * U ≤ K + 1 ∧
      (Work.TMC16Core.Assembly.W1s0 a U ∪ Work.TMC16Core.Assembly.W2s0 a U (K + 1) M).card = K + 1 ∧
      (∀ x ∈ Work.TMC16Core.Assembly.W1s0 a U,
        -((1 - (1 / 40 + 1 / (K : ℝ))) * (K : ℝ)) ≤ (x : ℝ) ∧
          (x : ℝ) ≤ -((1 / 40 + 1 / (K : ℝ)) * (K : ℝ))) ∧
      (∀ x ∈ Work.TMC16Core.Assembly.W2s0 a U (K + 1) M,
        x ≤ M + k₀ ∧ M + k₀ ≤ x + (K : ℤ) - 1 ∧
          (K : ℤ) ≤ 40 * ((M + k₀) - x) ∧ (K : ℤ) ≤ 40 * ((x + (K : ℤ) - 1) - (M + k₀))) ∧
      (K : ℝ) ≤ 40 * ((K : ℝ) / 40) := by
  have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (by omega : 0 < K)
  have hKne : (K : ℝ) ≠ 0 := ne_of_gt hKpos
  have hkey : 1 / (K : ℝ) * (K : ℝ) = 1 := by
    rw [one_div, inv_mul_cancel₀ hKne]
  -- `c = ⌈K/40⌉` is at most `K/40 + 39/40`
  have hcub : (c : ℝ) ≤ (K : ℝ) / 40 + 39 / 40 := by
    have h1 : 40 * c ≤ K + 39 := by
      rw [hc, mul_comm]
      exact Nat.div_mul_le_self (K + 39) 40
    have h1R : (40 : ℝ) * (c : ℝ) ≤ (K : ℝ) + 39 := by exact_mod_cast h1
    linarith
  have haR : (a : ℝ) = (k₀ : ℝ) - (K : ℝ) - (c : ℝ) := by
    rw [ha]; push_cast; ring
  have hUeq : (U : ℝ) = (c : ℝ) + 1 := by
    rw [hU]; push_cast; ring
  -- ## 1. `2U ≤ K+1`
  have h2U : 2 * U ≤ K + 1 := by omega
  -- ## 2. `W₁` lies in the singular strip `[-(1-δ)K, -δK]`, `δ = 1/40 + 1/K`
  have ha_lo : -((1 - (1 / 40 + 1 / (K : ℝ))) * (K : ℝ)) ≤ (a : ℝ) := by
    rw [haR]
    nlinarith [hkey, hcub, hlo]
  have ha_hi : (a : ℝ) + 2 * (U : ℝ) - 1 ≤ -((1 / 40 + 1 / (K : ℝ)) * (K : ℝ)) := by
    rw [haR, hUeq]
    nlinarith [hkey, hcub, hhi]
  refine ⟨h2U, ?_, ?_, ?_, ?_⟩
  · -- ## 3. The union has `K+1` sites
    exact s0_card (H := K + 1) h2U hM
  · -- ## 4. The `W₁`-containment
    intro x hx
    exact s0_sub (δ := 1 / 40 + 1 / (K : ℝ)) (K := (K : ℝ)) ha_lo ha_hi x hx
  · -- ## 5. The `W₂`-geometry around `M + k₀`
    intro x hx
    have h1 : M + a + (((K + 1 : ℕ)) : ℤ) - 1 + ((((K + 39) / 40 : ℕ)) : ℤ) ≤ M + k₀ := by
      rw [ha, hc]
      omega
    have h2 : M + k₀ ≤ M + a + 2 * (U : ℤ) + (K : ℤ) - 1 - ((((K + 39) / 40 : ℕ)) : ℤ) := by
      rw [ha, hc, hU]
      omega
    have hg := s0_geo (a := a) (M := M) (U := U) (H := K + 1) (K := K) (y := M + k₀)
      (by omega) (by omega) h1 h2
    exact hg x hx
  · -- ## 6. The trivial last conjunct
    have h40 : 40 * ((K : ℝ) / 40) = (K : ℝ) := by ring
    rw [h40]

end Work.TMC16Core.Assembly
