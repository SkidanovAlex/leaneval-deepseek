/-
# The `ρ^{3β}`-difference estimate behind the `A0` Hölder bound

For `0 < β ≤ 1`, `0 ≤ s₁, s₂`, `s₁, s₂ ≤ S` and `|s₁ - s₂| ≤ d`:

  `|s₁ ^ (3β) - s₂ ^ (3β)| ≤ 3^β * S ^ (2β) * d ^ β`.

The right-hand side carries the *Hölder exponent* `β` of the increment `d`, with `S ^ (2β)`
accounting for the homogeneity: the map `s ↦ s ^ (3β)` has degree `3β`, and the estimate is
invariant under `s ↦ S s`, `d ↦ S d` (both sides scale by `S ^ (3β)`).

The proof orders the two points (`x = max`, `y = min`) and factors out the increment:

  `x ^ (3β) - y ^ (3β) = x ^ (3β) * (1 - (1 - u) ^ (3β))`,   `u = (x - y)/x ∈ [0,1]`,

so everything reduces to the one-variable inequality `1 - (1 - u) ^ (3β) ≤ (3u) ^ β` on `[0,1]`
(`one_sub_one_sub_rpow_le`), combined with `x ^ (3β) = x ^ (2β) * x ^ β`,
`u = (x - y)/x` (`mul_sub_mul_div_rpow`) and `x ^ β * u ^ β = (x u) ^ β = (x - y) ^ β`
(`rpow_mul_div_rpow_eq`), plus the monotonicity of `t ↦ t ^ (2β)` and `t ↦ t ^ β` on `[0,∞)`.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.ConstructionInstance.one_sub_one_sub_rpow_le
import Submission.Work.ConstructionInstance.mul_sub_mul_div_rpow
import Submission.Work.ConstructionInstance.rpow_mul_div_rpow_eq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ConstructionInstance

/-- **The core case**: for `0 ≤ y ≤ x ≤ S` and `x - y ≤ d`, the difference of the `3β`-powers is
controlled by `3^β S^{2β} d^β`.  Ordering `s₁`, `s₂` reduces the general statement to this. -/
private lemma rho_core {β S x y d : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) (hy : 0 ≤ y) (hyx : y ≤ x)
    (hxS : x ≤ S) (hxy : x - y ≤ d) (hd : 0 ≤ d) :
    x ^ (3 * β) - y ^ (3 * β) ≤ 3 ^ β * S ^ (2 * β) * d ^ β := by
  have hx : 0 ≤ x := le_trans hy hyx
  rcases eq_or_lt_of_le hx with hx0 | hxpos
  · -- `x = 0`, hence also `y = 0`
    have hy0 : y = 0 := le_antisymm (by linarith) hy
    have hS0 : 0 ≤ S := by linarith
    rw [← hx0, hy0]
    simp only [Real.zero_rpow (by positivity : (3:ℝ) * β ≠ 0), sub_self]
    exact mul_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num) β) (Real.rpow_nonneg hS0 (2*β)))
      (Real.rpow_nonneg hd β)
  · -- `x > 0`: factor out the increment and use the one-variable inequality
    set u : ℝ := (x - y) / x with hu_def
    have hu0 : 0 ≤ u := by rw [hu_def]; exact div_nonneg (by linarith) hxpos.le
    have hu1 : u ≤ 1 := by rw [hu_def]; exact (div_le_one hxpos).mpr (by linarith)
    have hcrux := one_sub_one_sub_rpow_le hβ hβ1 hu0 hu1
    have hfac : x ^ (3*β) * (1 - (1 - u) ^ (3*β)) = x ^ (3*β) - y ^ (3*β) := by
      rw [hu_def]; exact mul_sub_mul_div_rpow hxpos hy
    have hmul := mul_le_mul_of_nonneg_left hcrux (Real.rpow_nonneg hxpos.le (3*β))
    have hdiv : x ^ (3*β) * (3*u)^β = 3^β * x^(2*β) * (x-y)^β := by
      rw [hu_def, Real.mul_rpow (by norm_num : (0:ℝ) ≤ 3) (div_nonneg (by linarith) hxpos.le)]
      rw [show x ^ (3*β) * (3^β * ((x-y)/x)^β) = 3^β * (x ^ (3*β) * ((x-y)/x)^β) by ring]
      rw [rpow_mul_div_rpow_eq hxpos hyx]
      ring
    have hfin : 3^β * x^(2*β) * (x-y)^β ≤ 3^β * S^(2*β) * d^β := by
      have hA : x ^ (2*β) ≤ S ^ (2*β) := Real.rpow_le_rpow hxpos.le hxS (by linarith)
      have hB : (x-y)^β ≤ d^β := Real.rpow_le_rpow (by linarith) hxy hβ.le
      have hAB : x^(2*β) * (x-y)^β ≤ S^(2*β) * d^β :=
        mul_le_mul hA hB (Real.rpow_nonneg (by linarith) β) (Real.rpow_nonneg (by linarith) (2*β))
      calc 3^β * x^(2*β) * (x-y)^β = 3^β * (x^(2*β) * (x-y)^β) := by ring
        _ ≤ 3^β * (S^(2*β) * d^β) := mul_le_mul_of_nonneg_left hAB (Real.rpow_nonneg (by norm_num) β)
        _ = 3^β * S^(2*β) * d^β := by ring
    calc x ^ (3*β) - y ^ (3*β) = x ^ (3*β) * (1 - (1 - u) ^ (3*β)) := hfac.symm
      _ ≤ x ^ (3*β) * (3*u)^β := hmul
      _ = 3^β * x^(2*β) * (x-y)^β := hdiv
      _ ≤ 3^β * S^(2*β) * d^β := hfin

lemma A0_rho_pow_diff {β s₁ s₂ S d : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1)
    (h1 : 0 ≤ s₁) (h2 : 0 ≤ s₂) (hS1 : s₁ ≤ S) (hS2 : s₂ ≤ S) (hd : |s₁ - s₂| ≤ d) :
    |s₁ ^ (3 * β) - s₂ ^ (3 * β)| ≤ 3 ^ β * S ^ (2 * β) * d ^ β := by
  have hd0 : 0 ≤ d := (abs_nonneg _).trans hd
  rcases le_total s₂ s₁ with h | h
  · have hsub : s₁ - s₂ ≤ d := by
      rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ s₁ - s₂)] at hd
      exact hd
    have hcore : s₁ ^ (3*β) - s₂ ^ (3*β) ≤ 3^β * S^(2*β) * d^β :=
      rho_core hβ hβ1 h2 h hS1 hsub hd0
    have hle : s₂ ^ (3*β) ≤ s₁ ^ (3*β) := Real.rpow_le_rpow h2 h (by linarith)
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ s₁ ^ (3*β) - s₂ ^ (3*β))]
    exact hcore
  · have hsub : s₂ - s₁ ≤ d := by
      rw [abs_sub_comm, abs_of_nonneg (by linarith : (0:ℝ) ≤ s₂ - s₁)] at hd
      exact hd
    have hcore : s₂ ^ (3*β) - s₁ ^ (3*β) ≤ 3^β * S^(2*β) * d^β :=
      rho_core hβ hβ1 h1 h hS2 hsub hd0
    have hle : s₁ ^ (3*β) ≤ s₂ ^ (3*β) := Real.rpow_le_rpow h1 h (by linarith)
    rw [abs_sub_comm, abs_of_nonneg (by linarith : (0:ℝ) ≤ s₂ ^ (3*β) - s₁ ^ (3*β))]
    exact hcore

end Work.ConstructionInstance
