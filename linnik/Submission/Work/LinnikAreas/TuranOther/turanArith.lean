import Mathlib
import Submission.Work.LinnikAreas.TuranOther.Defs

namespace Work.LinnikAreas.TuranOther

/-!
# `turanArith` — the arithmetic of the Turán repulsion step

This file proves the real-inequality core of the Turán (power-sum) argument in the
Deuring–Heilbronn form used for Linnik's theorem.  Concretely, from

* the "regulator" inequality `(32+4ε)·2·e·J·(1-β₀) ≤ εα`, which says that the
  quantity `X = εα/((32+4ε)·2·J·(1-β₀))` is at least `e`, and
* the power-sum inequality
  `(ε/(32+4ε))·(1+α-β)^{-2j} ≤ α^{-2j} - (1+α-β₀)^{-2j}`,

one deduces the logarithmic lower bound
`1 - β ≥ α·log(X)/(4J)`.

The proof has two ingredients.

* `invPowDiffLe` (via `one_sub_pow_le`): since `t ↦ t^{2j}` is convex on `[0,1]`,
  `1/α^{2j} - 1/(α+y₀)^{2j} = α^{-2j}·(1 - (α/(α+y₀))^{2j}) ≤ 2j·y₀/α^{2j+1}`.
* `turanArithCore`: the power-sum inequality therefore forces
  `(1 + (1-β)/α)^{2j} ≥ X`, and taking logarithms with `log(1+t) ≤ t` gives
  `(1-β)/α ≥ log X/(2j) ≥ log X/(4J)`.
-/

/-- For `0 ≤ x ≤ 1` and any `m`, `1 - x^m ≤ m(1-x)`.

This is the `m`-fold factorisation `1 - x^m = (1-x)·(1 + x + ⋯ + x^{m-1})` together
with `x^i ≤ 1`. -/
lemma one_sub_pow_le {x : ℝ} {m : ℕ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    1 - x ^ m ≤ (m : ℝ) * (1 - x) := by
  rw [← geom_sum_mul_neg x m]
  have h1x : 0 ≤ 1 - x := by linarith
  have hsum : (∑ i ∈ Finset.range m, x ^ i) ≤ (m : ℝ) := by
    calc (∑ i ∈ Finset.range m, x ^ i) ≤ ∑ i ∈ Finset.range m, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro i _; exact pow_le_one₀ hx0 hx1
      _ = (m : ℝ) := by simp
  exact mul_le_mul_of_nonneg_right hsum h1x

/-- The convexity bound behind the power-sum comparison: for `0 < a ≤ b` and `1 ≤ m`,
`1/a^m - 1/b^m ≤ m(b-a)/a^{m+1}`. -/
lemma invPowDiffLe {a b : ℝ} {m : ℕ} (ha : 0 < a) (hab : a ≤ b) (hm : 1 ≤ m) :
    1 / a ^ m - 1 / b ^ m ≤ (m : ℝ) * (b - a) / a ^ (m + 1) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hx0 : 0 ≤ a / b := by positivity
  have hx1 : a / b ≤ 1 := by rw [div_le_one hb]; exact hab
  have hkey : 1 - (a / b) ^ m ≤ (m : ℝ) * (1 - a / b) := one_sub_pow_le hx0 hx1
  have h1ab : 1 - a / b = (b - a) / b := by field_simp
  have hle : (b - a) / b ≤ (b - a) / a :=
    div_le_div_of_nonneg_left (by linarith) ha hab
  have heq : 1 / a ^ m - 1 / b ^ m = (1 / a ^ m) * (1 - (a / b) ^ m) := by
    have h2 : (1 / a ^ m) * (a / b) ^ m = 1 / b ^ m := by
      rw [div_pow]; field_simp
    rw [mul_sub, mul_one, h2]
  rw [heq]
  calc (1 / a ^ m) * (1 - (a / b) ^ m)
      ≤ (1 / a ^ m) * ((m : ℝ) * (1 - a / b)) :=
        mul_le_mul_of_nonneg_left hkey (by positivity)
    _ = (m : ℝ) * ((1 / a ^ m) * ((b - a) / b)) := by rw [h1ab]; ring
    _ ≤ (m : ℝ) * ((1 / a ^ m) * ((b - a) / a)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hle (by positivity)) (by positivity)
    _ = (m : ℝ) * (b - a) / a ^ (m + 1) := by rw [pow_succ]; field_simp

/-- **Arithmetic core of the Turán repulsion.**  If `X = εα/((32+4ε)·2·J·y₀) ≥ e` and
`(ε/(32+4ε))/(α+y)^{2j} ≤ 2j·y₀/α^{2j+1}`, then `y ≥ α·log X/(4J)`. -/
lemma turanArithCore {α ε y y₀ : ℝ} {j J : ℕ}
    (hα : 1 ≤ α) (hε : 0 < ε) (hj : 1 ≤ j) (hJ : 1 ≤ J) (hjJ : (j:ℝ) ≤ (J:ℝ))
    (hy : 0 ≤ y) (hy₀ : 0 < y₀)
    (hXe : Real.exp 1 ≤ ε * α / ((32 + 4*ε) * 2 * (J:ℝ) * y₀))
    (hkey : (ε / (32 + 4*ε)) / (α + y) ^ (2*j) ≤ (2*(j:ℝ)) * y₀ / α ^ (2*j + 1)) :
    y ≥ α * Real.log (ε * α / ((32 + 4*ε) * 2 * (J:ℝ) * y₀)) / (4*(J:ℝ)) := by
  have hαpos : 0 < α := by linarith
  have hcpos : 0 < 32 + 4*ε := by linarith
  have hJpos : (0:ℝ) < (J:ℝ) := by exact_mod_cast (by omega : 0 < J)
  have hjpos : (0:ℝ) < (j:ℝ) := by exact_mod_cast (by omega : 0 < j)
  have hyy : 0 < α + y := by linarith
  set X : ℝ := ε * α / ((32 + 4*ε) * 2 * (J:ℝ) * y₀) with hX
  have hXpos : 0 < X := by rw [hX]; positivity
  have hXge1 : 1 ≤ X := (Real.one_le_exp (by norm_num)).trans hXe
  have hLnn : 0 ≤ Real.log X := Real.log_nonneg hXge1
  -- multiply the hypothesis by `(α+y)^{2j}·α^{2j+1}`
  have hmain1 : (ε / (32 + 4*ε)) * α ^ (2*j+1) ≤ (α+y)^(2*j) * ((2*(j:ℝ)) * y₀) := by
    have h := mul_le_mul_of_nonneg_right hkey
      (by positivity : (0:ℝ) ≤ (α+y)^(2*j) * α^(2*j+1))
    have h1 : (ε/(32+4*ε))/(α+y)^(2*j) * ((α+y)^(2*j)*α^(2*j+1))
        = (ε/(32+4*ε))*α^(2*j+1) := by
      field_simp
    have h2 : ((2*(j:ℝ))*y₀/α^(2*j+1)) * ((α+y)^(2*j)*α^(2*j+1))
        = (α+y)^(2*j) * ((2*(j:ℝ))*y₀) := by
      field_simp
    rw [h1, h2] at h
    exact h
  have hmain2 : (ε / (32 + 4*ε)) * α ^ (2*j+1) / ((2*(j:ℝ)) * y₀) ≤ (α+y)^(2*j) := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < (2*(j:ℝ)) * y₀)]
    exact hmain1
  -- divide by `α^{2j}`
  have hratio : ε * α / ((32 + 4*ε) * (2*(j:ℝ)) * y₀) ≤ ((α+y)/α)^(2*j) := by
    have hdiv : ((ε / (32 + 4*ε)) * α ^ (2*j+1) / ((2*(j:ℝ)) * y₀)) / α^(2*j)
        = ε * α / ((32 + 4*ε) * (2*(j:ℝ)) * y₀) := by
      have h2j : α^(2*j+1) = α^(2*j) * α := pow_succ α (2*j)
      rw [h2j]; field_simp
    have h := div_le_div_of_nonneg_right hmain2 (by positivity : (0:ℝ) ≤ α^(2*j))
    rw [hdiv] at h
    have h2 : (α+y)^(2*j)/α^(2*j) = ((α+y)/α)^(2*j) := by rw [div_pow]
    rwa [h2] at h
  -- `X` is no larger (since `j ≤ J`), so `(1+y/α)^{2j} ≥ X`
  have hXle : X ≤ ε * α / ((32 + 4*ε) * (2*(j:ℝ)) * y₀) := by
    rw [hX]
    have hden : (32 + 4*ε) * (2*(j:ℝ)) * y₀ ≤ (32 + 4*ε) * 2 * (J:ℝ) * y₀ := by
      have key : 0 ≤ (32+4*ε) * (2*(J:ℝ) - 2*(j:ℝ)) * y₀ :=
        mul_nonneg (mul_nonneg (by linarith) (by linarith)) (le_of_lt hy₀)
      nlinarith [key]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) hden
  have hcomb : X ≤ (1 + y/α)^(2*j) := by
    have h1 : (α+y)/α = 1 + y/α := by field_simp
    rw [h1] at hratio
    exact hXle.trans hratio
  -- take logarithms
  have hlog1 : Real.log X ≤ (2*(j:ℝ)) * Real.log (1 + y/α) := by
    have h := Real.log_le_log hXpos hcomb
    rw [Real.log_pow] at h
    push_cast at h
    linarith [h]
  have hu : Real.log (1 + y/α) ≤ y/α := by
    have h := Real.log_le_sub_one_of_pos (by positivity : (0:ℝ) < 1 + y/α)
    linarith
  have hstep : Real.log X ≤ (2*(j:ℝ)) * (y/α) := by
    have hm := mul_le_mul_of_nonneg_left hu (by positivity : (0:ℝ) ≤ 2*(j:ℝ))
    linarith [hlog1, hm]
  have hstep2 : Real.log X / (2*(j:ℝ)) ≤ y/α := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < 2*(j:ℝ))]
    linarith [hstep]
  have hy1 : y ≥ α * (Real.log X / (2*(j:ℝ))) := by
    have hm := mul_le_mul_of_nonneg_left hstep2 (le_of_lt hαpos)
    rwa [mul_div_cancel₀ y (ne_of_gt hαpos)] at hm
  -- `log X ≥ 0` and `j ≤ J` upgrade `2j` to `4J`
  have hfin : α * Real.log X / (4*(J:ℝ)) ≤ α * (Real.log X / (2*(j:ℝ))) := by
    have h2j : (2*(j:ℝ)) ≤ 4*(J:ℝ) := by linarith
    have h := div_le_div_of_nonneg_left (mul_nonneg (le_of_lt hαpos) hLnn)
      (by positivity : (0:ℝ) < 2*(j:ℝ)) h2j
    have e1 : α * Real.log X / (2*(j:ℝ)) = α * (Real.log X / (2*(j:ℝ))) := by ring
    rwa [e1] at h
  have hgoal : y ≥ α * Real.log X / (4*(J:ℝ)) := le_trans hfin hy1
  rw [hX] at hgoal
  exact hgoal

theorem turanArith {α ε β β₀ : ℝ} {j J : ℕ}
    (hα : 1 ≤ α) (hε : 0 < ε) (hJ : 1 ≤ J) (hj : 1 ≤ j)
    (hjJ : (j : ℝ) ≤ (J : ℝ)) (hβ : β ≤ 1) (hβ₀ : β₀ < 1)
    (hreg : (32 + 4 * ε) * 2 * Real.exp 1 * (J : ℝ) * (1 - β₀) ≤ ε * α)
    (hmain : (ε / (32 + 4 * ε)) * (1 / (1 + α - β) ^ (2 * j)) ≤
        1 / α ^ (2 * j) - (1 / (1 + α - β₀)) ^ (2 * j)) :
    1 - β ≥ α * Real.log (ε * α / ((32 + 4 * ε) * 2 * (J : ℝ) * (1 - β₀))) / (4 * J) := by
  have hy : 0 ≤ 1 - β := by linarith
  have hy₀ : 0 < 1 - β₀ := by linarith
  have hαpos : 0 < α := by linarith
  -- the "regulator" inequality is exactly `X ≥ e`
  have hXe : Real.exp 1 ≤ ε * α / ((32 + 4 * ε) * 2 * (J : ℝ) * (1 - β₀)) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [hreg]
  -- the power-sum inequality yields the convexity bound
  have hkey : (ε / (32 + 4 * ε)) / (α + (1 - β)) ^ (2 * j) ≤
      (2 * (j:ℝ)) * (1 - β₀) / α ^ (2 * j + 1) := by
    have hA : 1 + α - β = α + (1 - β) := by ring
    have hB : 1 + α - β₀ = α + (1 - β₀) := by ring
    have h1 : 1 / α ^ (2 * j) - 1 / (α + (1 - β₀)) ^ (2 * j)
        ≤ (2 * (j:ℝ)) * (1 - β₀) / α ^ (2 * j + 1) := by
      have h := invPowDiffLe (a := α) (b := α + (1 - β₀)) (m := 2 * j)
        hαpos (by linarith) (by omega)
      have hb : α + (1 - β₀) - α = 1 - β₀ := by ring
      rw [hb] at h
      push_cast at h
      exact h
    have h2 : (ε / (32 + 4 * ε)) * (1 / (α + (1 - β)) ^ (2 * j))
        ≤ 1 / α ^ (2 * j) - 1 / (α + (1 - β₀)) ^ (2 * j) := by
      rw [hA, hB, one_div_pow] at hmain
      exact hmain
    calc (ε / (32 + 4 * ε)) / (α + (1 - β)) ^ (2 * j)
        = (ε / (32 + 4 * ε)) * (1 / (α + (1 - β)) ^ (2 * j)) := by
          simp only [div_eq_mul_inv, one_mul]
      _ ≤ 1 / α ^ (2 * j) - 1 / (α + (1 - β₀)) ^ (2 * j) := h2
      _ ≤ (2 * (j:ℝ)) * (1 - β₀) / α ^ (2 * j + 1) := h1
  exact turanArithCore hα hε hj hJ hjJ hy hy₀ hXe hkey

end Work.LinnikAreas.TuranOther
