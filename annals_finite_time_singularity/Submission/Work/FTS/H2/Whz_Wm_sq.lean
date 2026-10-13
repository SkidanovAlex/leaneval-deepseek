import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.H2.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Squaring the two weights of the flat `ℋ⁴` pairing

The weights of `HkIntegrand` (`Submission/Work/Spaces/Defs.lean`, `Submission/Work/FTS/H2/Defs.lean`)
are square roots of the weights that actually appear in the energy:

* `Whz z θ = w z / sin(2θ)^{η/2}`, so `Whz z θ ^ 2 = w z ^ 2 · sin(2θ)^{-η}`;
* `Wm α z θ = W α z θ = w z · sin(2θ)^{-γ/2}`, so `Wm α z θ ^ 2 = w z ^ 2 · sin(2θ)^{-γ}`.

Both identities are pure `rpow` algebra on the base `a = sin(2θ) ≥ 0` (the sign is
the only place the hypothesis `θ ∈ Iθ` is used); at `θ = 0` and `θ = π/2` the
identity survives Lean's totalised `rpow` at `a = 0` because `0 ^ x = 0` for
`x ≠ 0`.  Note that squaring is *not* removed at `θ ∈ {0, π/2}`: the two sides are
both `0` there.
-/

namespace Work.FTS.H2

set_option autoImplicit false

/-- `sin (2θ) ≥ 0` on the angular interval `Iθ = [0, π/2]`: this is the only use of
the hypothesis `θ ∈ Iθ` in `Whz_Wm_sq`. -/
theorem sin_two_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) := by
  have h1 : (0 : ℝ) ≤ θ := hθ.1
  have h2 : θ ≤ Real.pi / 2 := hθ.2
  exact Real.sin_nonneg_of_mem_Icc ⟨by linarith, by linarith [Real.pi_pos]⟩

/-- `(a ^ p) ^ 2 = a ^ (p * 2)` for `a ≥ 0`.  The natural-number power on the left is
converted to a real one by `Real.rpow_natCast` before `Real.rpow_mul` is applied. -/
theorem sq_rpow_mul_two {a : ℝ} (ha : 0 ≤ a) (p : ℝ) : (a ^ p) ^ 2 = a ^ (p * 2) := by
  rw [← Real.rpow_natCast (a ^ p) 2]
  exact (Real.rpow_mul ha p 2).symm

theorem Whz_Wm_sq (α : ℝ) (hα : 0 < α) (z θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.FTS.H2.Whz z θ) ^ 2
        = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta) ∧
      (Work.FTS.H2.Wm α z θ) ^ 2
        = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
  have ha : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_mem_Iθ hθ
  refine ⟨?_, ?_⟩
  · -- `Whz`: pull the division out of the square as an inverse `rpow`, then square.
    have h1 : Whz z θ
        = Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2)) := by
      rw [Whz_eq, div_eq_mul_inv, ← Real.rpow_neg ha (Work.Spaces.eta / 2)]
    rw [h1, mul_pow, sq_rpow_mul_two ha (-(Work.Spaces.eta / 2))]
    rw [show (-(Work.Spaces.eta / 2)) * 2 = -Work.Spaces.eta by ring]
  · -- `Wm`: the angular weight already carries the negative half exponent.
    have h1 : Wm α z θ
        = Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)) := by
      rw [Wm_eq, Work.Spaces.Wt, Work.Spaces.wTheta]
    rw [h1, mul_pow, sq_rpow_mul_two ha (-(Work.Spaces.gam α / 2))]
    rw [show (-(Work.Spaces.gam α / 2)) * 2 = -(Work.Spaces.gam α) by ring]

end Work.FTS.H2
