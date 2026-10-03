import Mathlib

namespace Work.Prop36SW

/-- Window algebra for the reach-step bookkeeping.

Writing `x := c₀' * η ^ e₀'`, the hypotheses say `0 ≤ x ≤ γ`, `x * a ≤ M`,
`c₀ ≤ c₁ * c₀' ^ (e₁ + 1)`, `η ^ e₀ ≤ (η ^ e₀') ^ (e₁ + 1)` (monotonicity of `η ↦ η ^ ·`
with `0 < η ≤ 1` and `e₀' * (e₁ + 1) ≤ e₀`) and `c₁ * γ ^ e₁ * M * b ≤ M'`.  Hence

`c₀ η ^ e₀ (a b) ≤ c₁ (c₀' η ^ e₀') ^ (e₁ + 1) a b
                 = c₁ (c₀' η ^ e₀') ^ e₁ (c₀' η ^ e₀' * a) b
                 ≤ c₁ γ ^ e₁ M b ≤ M'`,

using the first `e₁` of the `e₁ + 1` powers of `x` to replace `x` by `γ` and keeping the last
one paired with `a`, which is exactly what `hu` bounds. -/
theorem reachStepAuxWindow {c₀ c₁ c₀' γ η a b M M' : ℝ} {e₀ e₁ e₀' : ℕ}
    (hc₁ : 0 ≤ c₁) (hc₀' : 0 < c₀') (hη0 : 0 < η) (hη1 : η ≤ 1) (hγ0 : 0 ≤ γ)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc₀ : c₀ ≤ c₁ * c₀' ^ (e₁ + 1)) (he₀ : e₀' * (e₁ + 1) ≤ e₀)
    (hmon : c₀' * η ^ e₀' ≤ γ) (hu : c₀' * η ^ e₀' * a ≤ M)
    (hM : c₁ * γ ^ e₁ * M * b ≤ M') :
    c₀ * η ^ e₀ * (a * b) ≤ M' := by
  set x : ℝ := c₀' * η ^ e₀' with hx
  have hx0 : 0 ≤ x := by
    rw [hx]; exact mul_nonneg (le_of_lt hc₀') (pow_nonneg (le_of_lt hη0) e₀')
  have hxγ : x ≤ γ := by rw [hx]; exact hmon
  have hηe : η ^ e₀ ≤ (η ^ e₀') ^ (e₁ + 1) := by
    have h := pow_le_pow_of_le_one (le_of_lt hη0) hη1 he₀
    rwa [pow_mul] at h
  have h1 : c₀ * η ^ e₀ ≤ c₁ * x ^ (e₁ + 1) := by
    have hbase : c₀ * η ^ e₀ ≤ (c₁ * c₀' ^ (e₁ + 1)) * (η ^ e₀') ^ (e₁ + 1) :=
      mul_le_mul hc₀ hηe (pow_nonneg (le_of_lt hη0) e₀)
        (mul_nonneg hc₁ (pow_nonneg (le_of_lt hc₀') (e₁ + 1)))
    calc c₀ * η ^ e₀ ≤ (c₁ * c₀' ^ (e₁ + 1)) * (η ^ e₀') ^ (e₁ + 1) := hbase
      _ = c₁ * x ^ (e₁ + 1) := by rw [hx, mul_pow]; ring
  have hxe : x ^ e₁ ≤ γ ^ e₁ := pow_le_pow_left₀ hx0 hxγ e₁
  have hcγ : 0 ≤ c₁ * γ ^ e₁ := mul_nonneg hc₁ (pow_nonneg hγ0 e₁)
  have hstep : c₀ * η ^ e₀ * (a * b) ≤ c₁ * x ^ (e₁ + 1) * (a * b) :=
    mul_le_mul_of_nonneg_right h1 (mul_nonneg ha hb)
  have hsplit : c₁ * x ^ (e₁ + 1) * (a * b) = c₁ * x ^ e₁ * (x * a) * b := by
    rw [pow_succ]; ring
  have h2 : c₁ * x ^ e₁ * (x * a) * b ≤ c₁ * γ ^ e₁ * M * b := by
    have hA : c₁ * x ^ e₁ ≤ c₁ * γ ^ e₁ := mul_le_mul_of_nonneg_left hxe hc₁
    have hB : x * a ≤ M := by rw [hx]; exact hu
    have hAB : c₁ * x ^ e₁ * (x * a) ≤ c₁ * γ ^ e₁ * M :=
      mul_le_mul hA hB (mul_nonneg hx0 ha) hcγ
    exact mul_le_mul_of_nonneg_right hAB hb
  calc c₀ * η ^ e₀ * (a * b) ≤ c₁ * x ^ (e₁ + 1) * (a * b) := hstep
    _ = c₁ * x ^ e₁ * (x * a) * b := hsplit
    _ ≤ c₁ * γ ^ e₁ * M * b := h2
    _ ≤ M' := hM

end Work.Prop36SW
