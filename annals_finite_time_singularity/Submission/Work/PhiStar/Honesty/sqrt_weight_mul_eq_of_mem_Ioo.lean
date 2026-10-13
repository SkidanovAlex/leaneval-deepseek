import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.FamNormValue

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.PhiStar.Honesty

open scoped Real

/-- The two `sin(2θ)`-weights in the `η`-weighted pairing multiply to `1` on the open
interval: `sin(2θ)^{-η} · sin(2θ)^{η} = 1` for `θ ∈ (0, π/2)`. -/
theorem sqrt_weight_mul_eq_of_mem_Ioo (F : ℝ → ℝ → ℝ) (m : ℕ) (z : ℝ) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Real.sqrt ((F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        * Real.sqrt ((Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ) ^ 2
            * (Real.sin (2 * θ)) ^ (Work.Spaces.eta))
      = |F z θ| * |Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ| := by
  have hs : 0 < Real.sin (2 * θ) := by
    refine Real.sin_pos_of_pos_of_lt_pi ?_ ?_
    · linarith [hθ.1]
    · linarith [hθ.2, Real.pi_pos]
  have hnegη : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
    Real.rpow_nonneg hs.le _
  have hposη : 0 ≤ (Real.sin (2 * θ)) ^ (Work.Spaces.eta) :=
    Real.rpow_nonneg hs.le _
  have hprod : (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      * (Real.sin (2 * θ)) ^ (Work.Spaces.eta) = 1 := by
    rw [← Real.rpow_add hs]
    simp
  have hsqrt : Real.sqrt ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      * Real.sqrt ((Real.sin (2 * θ)) ^ (Work.Spaces.eta)) = 1 := by
    rw [← Real.sqrt_mul hnegη, hprod]
    simp
  rw [Real.sqrt_mul (sq_nonneg (F z θ)), Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs]
  calc |F z θ| * Real.sqrt ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        * (|Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ|
            * Real.sqrt ((Real.sin (2 * θ)) ^ (Work.Spaces.eta)))
      = (|F z θ| * |Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ|)
        * (Real.sqrt ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
            * Real.sqrt ((Real.sin (2 * θ)) ^ (Work.Spaces.eta))) := by ring
    _ = (|F z θ| * |Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ|) * 1 := by
          rw [hsqrt]
    _ = |F z θ| * |Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ| := by ring

end Work.PhiStar.Honesty
