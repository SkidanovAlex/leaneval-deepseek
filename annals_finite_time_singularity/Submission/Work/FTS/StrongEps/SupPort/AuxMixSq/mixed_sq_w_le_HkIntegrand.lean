/-
Copyright: work module for the Elgindi finite-time singularity project.

# The bare `w²`-weighted square of a mixed slot is dominated by the `ℋ⁴`-integrand

The mixed slot `D_z^j D_θ^i f` of a function contains the angular weight
`w_θ(θ) = sin(2θ)^{-γ/2}` in `HkIntegrand` (`γ = 1 + α/10`), while the plain radial
weight of the slot is just `w(z)`.  On the open quadrant `sin(2θ) ∈ (0,1]`, so the
angular factor is `≥ 1` and therefore the *unweighted* square `(D_z^jD_θ^i f)²·w²` is
dominated by the corresponding squared summand of `HkIntegrand`; since `HkIntegrand` is a
sum of squares, the whole integrand dominates it.

The only analytic input is `1 ≤ sin(2θ)^{-γ/2}`, i.e. `sin(2θ)^{γ/2} ≤ 1` for
`0 < sin(2θ) ≤ 1`, `γ/2 > 0`; the rest is the bookkeeping lemma
`Work.Spaces.sq_le_HkIntegrand_mixed`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HkSq_terms

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.SupPort.AuxMixSq

set_option autoImplicit false

/-- The angular weight factor `w_θ = sin(2θ)^{-γ/2}` is `≥ 1` on the open quadrant:
there `0 < sin(2θ) ≤ 1` and the exponent `-γ/2` is nonpositive (indeed `γ > 1 > 0`). -/
theorem one_le_wTheta_sq {α : ℝ} (hα : 0 < α) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    1 ≤ (Work.Spaces.wTheta α θ) ^ 2 := by
  -- `2θ ∈ (0,π)`, so `0 < sin(2θ) ≤ 1`.
  have ht0 : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos])
  have ht1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hc : 0 ≤ Work.Spaces.gam α / 2 := by
    have h := Work.Spaces.gam_pos hα
    linarith
  -- `sin(2θ)^{γ/2} ≤ 1^{γ/2} = 1`.
  have hpow1 : (Real.sin (2 * θ)) ^ (Work.Spaces.gam α / 2) ≤ 1 := by
    have h := Real.rpow_le_rpow (le_of_lt ht0) ht1 hc
    simpa using h
  have hpow0 : 0 < (Real.sin (2 * θ)) ^ (Work.Spaces.gam α / 2) :=
    Real.rpow_pos_of_pos ht0 _
  -- Hence the reciprocal power `sin(2θ)^{-γ/2}` is `≥ 1`, and so is its square.
  have hkey : 1 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)) := by
    have h : (1 : ℝ)⁻¹ ≤ ((Real.sin (2 * θ)) ^ (Work.Spaces.gam α / 2))⁻¹ := by
      rw [inv_le_inv₀ one_pos hpow0]
      exact hpow1
    rw [Real.rpow_neg (le_of_lt ht0)]
    simpa using h
  rw [Work.Spaces.wTheta]
  exact one_le_pow₀ hkey

/-- The unweighted square of a mixed slot is dominated by the `ℋ⁴`-integrand: on the open
quadrant the angular factor of `Wt` is `≥ 1`, so `(D_z^jD_θ^if)²w² ≤ (D_z^jD_θ^if·Wt)²`,
which is one of the summands of `HkIntegrand α 4 f`. -/
theorem mixed_sq_w_le_HkIntegrand {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ} (j i : ℕ)
    (hi : 1 ≤ i) (hij : i + j ≤ 4) {s σ : ℝ} (hσ : σ ∈ Set.Ioo 0 (π / 2)) :
    (Work.Spaces.mixed j i f s σ) ^ 2 * (Work.Spaces.w s) ^ 2
      ≤ Work.Spaces.HkIntegrand α 4 f s σ := by
  have hWt : 1 ≤ (Work.Spaces.wTheta α σ) ^ 2 := one_le_wTheta_sq hα hσ
  -- `(mixed · Wt)² = (mixed)² w² (w_θ)² ≥ (mixed)² w²`, and it is a summand of the integrand.
  refine le_trans ?_ (Work.Spaces.sq_le_HkIntegrand_mixed α 4 f s σ i j hi hij)
  rw [Work.Spaces.Wt, mul_pow, mul_pow]
  exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_right (sq_nonneg _) hWt) (sq_nonneg _)

end Work.FTS.StrongEps.SupPort.AuxMixSq
