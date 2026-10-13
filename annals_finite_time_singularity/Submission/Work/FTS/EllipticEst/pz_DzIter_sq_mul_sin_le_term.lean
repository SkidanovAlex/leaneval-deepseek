/-
Copyright: work module for the Elgindi finite-time singularity project.

# The `∂_z D_z^j`-term against the `D_z^{j+1}`-slot of `H^{k+1}`

For `z > 0` and `θ ∈ Iθ` (so `sin (2θ) ≥ 0`),

  `(∂_z D_z^j F)² · sin(2θ)^{-η}  ≤  (D_z^{j+1} F · w z / sin(2θ)^{η/2})²`.

Writing `a = ∂_z D_z^j F (z,θ)` and `s = sin (2θ) ≥ 0`, the right hand side is
`(z·a·(w z / s^{η/2}))²`, because `D_z^{j+1} F = z · ∂_z D_z^j F`.  By the `rpow` algebra of
`Work.FTS.H2.T1HardWeightAlg` (valid on the non-negative base `s`) this equals

  `w(z)² · ((z·a)² · s^{-η}) = (z·w z)² · (a² · s^{-η})`.

Finally `(z·w z)² ≥ 1` for `z > 0`, since `z·w z = (1+z)²/z = z + 2 + 1/z ≥ 1`, while
`a²·s^{-η} ≥ 0`; this gives the claim.

This is the pointwise ingredient which turns the `pz (DzIter j F)`-term into the `D_z^{j+1}`
slot of `HkIntegrand`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.H2.T1HardWeightAlg

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst

/-- The radial weight beats the reciprocal of `z`: `1 ≤ z · w(z)` for `z > 0`, because
`z·w(z) = (1+z)²/z = z + 2 + 1/z ≥ 1`. -/
private lemma one_le_mul_w {z : ℝ} (hz : 0 < z) : 1 ≤ z * Work.Spaces.w z := by
  have hzw : z * Work.Spaces.w z = (1 + z) ^ 2 / z := by
    rw [Work.Spaces.w]
    field_simp
  rw [hzw, le_div_iff₀ hz]
  nlinarith [sq_nonneg z]

theorem pz_DzIter_sq_mul_sin_le_term (j : ℕ) {F : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.pz (Work.Spaces.DzIter j F) z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      ≤ (Work.Spaces.DzIter (j + 1) F z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  -- Unfold the outermost `D_z` and abbreviate `a = ∂_z D_z^j F (z,θ)`.
  rw [Work.Spaces.DzIter_succ]
  simp only [Work.Spaces.Dz]
  set a : ℝ := Work.Spaces.pz (Work.Spaces.DzIter j F) z θ with ha
  -- `sin (2θ) ≥ 0` on the angular interval.
  have hS : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have hnn : 0 ≤ a ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
    mul_nonneg (sq_nonneg a) (Real.rpow_nonneg hS _)
  -- `D_z^{j+1} F = z·a`, so the right hand side is `(z·a·(w z / s^{η/2}))²`; the `rpow` algebra
  -- of `T1HardWeightAlg` rewrites it as `w(z)²·((z·a)²·s^{-η})`.
  have hkey := (Work.FTS.H2.T1HardWeightAlg 0 z θ (z * a) 0 (le_of_lt hz) hθ).1
  rw [← hkey]
  have h2 : (Work.Spaces.w z) ^ 2 * ((z * a) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      = (z * Work.Spaces.w z) ^ 2
        * (a ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
    ring
  rw [h2]
  exact le_mul_of_one_le_left hnn (one_le_pow₀ (one_le_mul_w hz))

end Work.FTS.EllipticEst
