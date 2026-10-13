import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.IntervalCases
import Submission.Work.R1G.AnG

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.R1G

/-- **Elementary bound on the iterated angular factor.**  For `i < 3` the `i`-fold `D_θ`-iterate
`Tit i` of `θ ↦ sin (2θ)` is bounded by `2^i · sin (2θ)`; equivalently, after squaring,
`(Tit i θ)² ≤ (2^i)² · sin(2θ)²`.  No hypothesis on `θ` is needed: `Tit 0 = sin(2θ)`,
`Tit 1 = 2 sin(2θ) cos(2θ)`, `Tit 2 = 4 sin(2θ) cos(4θ)`, and `|cos| ≤ 1`. -/
theorem Tit_sq_le_pow_mul_sin_sq (i : ℕ) (hi : i < 3) (θ : ℝ) :
    (Tit i θ) ^ 2 ≤ ((2 : ℝ) ^ i) ^ 2 * (Real.sin (2 * θ)) ^ 2 := by
  interval_cases i
  · rw [Tit_zero, Tf]; norm_num
  · rw [Tit_one, Tf1]
    nlinarith [Real.sin_sq_add_cos_sq (2 * θ), sq_nonneg (Real.sin (2 * θ))]
  · rw [Tit_two, Tf2]
    nlinarith [Real.sin_sq_add_cos_sq (4 * θ), sq_nonneg (Real.sin (2 * θ))]

/-- **The pure-`rpow` estimate.**  For `0 ≤ s ≤ 1` and `g ≤ 2`, the product `s² · s^{-g}` is at
most `1`.  Indeed `s² · s^{-g} = s^{2-g}` (for `s > 0`) and `2 - g ≥ 0`, while `s ∈ [0,1]`; and by
convention `s = 0` gives `0`. -/
theorem sin_sq_mul_rpow_neg_le_one {s g : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hg2 : g ≤ 2) :
    s ^ 2 * s ^ (-g) ≤ 1 := by
  rcases eq_or_lt_of_le hs0 with h | h
  · subst h; simp
  · rw [← Real.rpow_two s, ← Real.rpow_add h (2 : ℝ) (-g)]
    apply Real.rpow_le_one hs0 hs1
    linarith

/-- **The angular weighted estimate for the perturbation `gA`.**  For the exponent
`γ = gam p = 1 + p/10` (with `p ≤ 1`, so that `γ ≤ 2`) and every `θ ∈ Iθ`,

`(Tit i θ)² · sin(2θ)^{-γ} ≤ (2^i)²`,   `i = 0, 1, 2`.

The factor `sin(2θ)` produced by the `D_θ` iterations exactly cancels the negative power of
`sin(2θ)` in the weight, leaving an exponent `2 - γ ≥ 0` and a bounded quantity. -/
theorem gA_Tit_sq_mul_rpow_le (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (i : ℕ) (hi : i < 3)
    {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.R1G.Tit i θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam p)) ≤ ((2 : ℝ) ^ i) ^ 2 := by
  have hsin0 : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hp2 : Work.Spaces.gam p ≤ 2 := by unfold Work.Spaces.gam; linarith
  have hTit : (Tit i θ) ^ 2 ≤ ((2 : ℝ) ^ i) ^ 2 * (Real.sin (2 * θ)) ^ 2 :=
    Tit_sq_le_pow_mul_sin_sq i hi θ
  have hpow : (Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam p)) ≤ 1 :=
    sin_sq_mul_rpow_neg_le_one hsin0 (Real.sin_le_one _) hp2
  calc (Work.R1G.Tit i θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam p))
      ≤ (((2 : ℝ) ^ i) ^ 2 * (Real.sin (2 * θ)) ^ 2)
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam p)) :=
        mul_le_mul_of_nonneg_right hTit (Real.rpow_nonneg hsin0 _)
    _ = ((2 : ℝ) ^ i) ^ 2
          * ((Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam p))) := by ring
    _ ≤ ((2 : ℝ) ^ i) ^ 2 * 1 := mul_le_mul_of_nonneg_left hpow (sq_nonneg _)
    _ = ((2 : ℝ) ^ i) ^ 2 := mul_one _

end Work.R1G
