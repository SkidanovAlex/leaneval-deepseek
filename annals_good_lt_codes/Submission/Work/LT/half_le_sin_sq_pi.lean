import Mathlib

/-!
# `sin²(π x) ≥ 1/2` on the interval `[1/4, 1/2]`

On `[1/4, 1/2]` the point `π x` lies in `[π/4, π/2] ⊂ [-π/2, π/2]`, where `sin` is
monotone.  Hence `sin (π x) ≥ sin (π/4) = √2/2 ≥ 0`, and squaring the two nonnegative
sides turns this into `sin² (π x) ≥ (√2/2)² = 1/2`.
-/

namespace Work.LT

theorem half_le_sin_sq_pi (x : ℝ) (h1 : 1 / 4 ≤ x) (h2 : x ≤ 1 / 2) :
    1 / 2 ≤ Real.sin (Real.pi * x) ^ 2 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  -- `π/4 ≤ π x`, so that `π x` sits to the right of `π/4` in `[-π/2, π/2]`.
  have hx1 : Real.pi / 4 ≤ Real.pi * x := by nlinarith [h1, hpi]
  have hm1 : Real.pi / 4 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> nlinarith [hpi]
  have hm2 : Real.pi * x ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor
    · nlinarith [hpi, hx1]
    · nlinarith [hpi, h2]
  -- monotonicity of `sin` on `[-π/2, π/2]`
  have hmono : Real.sin (Real.pi / 4) ≤ Real.sin (Real.pi * x) :=
    Real.monotoneOn_sin hm1 hm2 hx1
  rw [Real.sin_pi_div_four] at hmono
  -- `(√2/2)² = 1/2`
  have hsq2 : (√2 / 2 : ℝ) ^ 2 = 1 / 2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hnn : (0 : ℝ) ≤ √2 / 2 := by positivity
  have hpow := pow_le_pow_left₀ hnn hmono 2
  rwa [hsq2] at hpow

end Work.LT
