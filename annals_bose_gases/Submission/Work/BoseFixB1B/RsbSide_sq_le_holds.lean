import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseFixB1.RegimeAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open scoped Real Topology BigOperators

namespace Work.BoseFixB1B

open Work.BoseBox Work.BoseFixB1

set_option maxHeartbeats 1000000

/-- **FS `eq:appRassumption`**: at FS's parameters, the range-to-small-box ratio `(R/(dℓ))²` is
dominated by the LHY error scale `K_B³(μ(av)³)^{1/2}`, as soon as the diluteness is below the
threshold `(a²/R²)^{646/341}`.

Both sides are closed monomials in `t = μ A³` (`Submission/Work/BoseFixB1/RegimeAux.lean`):
`d·ℓ = A·t^{-157/323}` and `K_B³ t^{1/2} = t^{287/646}`, so the claim reads
`R²A^{-2} t^{314/323} ≤ t^{287/646}`, i.e. `R²A^{-2} ≤ t^{-341/646}`, which is exactly
`t ≤ (A²/R²)^{646/341}`.

This is the same statement as `Work.BoseFixB1.Regime.RsbSide_sq_le` (which is still a dispatched
`sorry`); it is needed by `Work.BoseFixB1B.perBoxIntegrated` to collect the
`μ²(a v)((R/(dℓ))² + K_B³(μa³)^{1/2})·∫_{I₋}χ_{B(u)}²` error of `Work.BoseFixB1.perBoxF_integrated`
into `2·μ²(a v)ℓ³K_B³(μa³)^{1/2}` (using also `∫_{I₋}χ_{B(u)}² ≤ ℓ³`). -/
theorem RsbSide_sq_le_holds {A R μ : ℝ} (hA : 0 < A) (hR : 0 < R) (hμ : 0 < μ)
    (ht : μ * A ^ 3 ≤ (A ^ 2 / R ^ 2) ^ (646 / 341 : ℝ)) :
    (R / ((Work.BoseBox.paramsAt μ A).d * Work.BoseBox.sideAt μ A)) ^ 2
      ≤ (Work.BoseBox.paramsAt μ A).KB ^ 3 * (μ * A ^ 3) ^ (1 / 2 : ℝ) := by
  have ht0 : (0 : ℝ) < μ * A ^ 3 := by positivity
  have hAR : (0 : ℝ) < A ^ 2 / R ^ 2 := by positivity
  -- (1) `t^{341/646} ≤ A²/R²`, by raising the hypothesis to the power `341/646`.
  have h1 : (μ * A ^ 3) ^ (341 / 646 : ℝ) ≤ A ^ 2 / R ^ 2 := by
    calc (μ * A ^ 3) ^ (341 / 646 : ℝ)
        ≤ ((A ^ 2 / R ^ 2) ^ (646 / 341 : ℝ)) ^ (341 / 646 : ℝ) :=
          Real.rpow_le_rpow ht0.le ht (by norm_num)
      _ = (A ^ 2 / R ^ 2) ^ ((646 / 341 : ℝ) * (341 / 646)) :=
          (Real.rpow_mul hAR.le _ _).symm
      _ = A ^ 2 / R ^ 2 := by
          rw [show (646 / 341 : ℝ) * (341 / 646) = 1 by norm_num, Real.rpow_one]
  -- (2) `R²/A² ≤ t^{-341/646}`, by inversion.
  have h2 : R ^ 2 / A ^ 2 ≤ (μ * A ^ 3) ^ (-(341 / 646) : ℝ) := by
    have h3 : (A ^ 2 / R ^ 2)⁻¹ ≤ ((μ * A ^ 3) ^ (341 / 646 : ℝ))⁻¹ :=
      (inv_le_inv₀ hAR (Real.rpow_pos_of_pos ht0 (341 / 646))).mpr h1
    have h4 : (A ^ 2 / R ^ 2)⁻¹ = R ^ 2 / A ^ 2 := by field_simp
    rw [Real.rpow_neg ht0.le, ← h4]
    exact h3
  have h2' : R ^ 2 / A ^ 2 ≤ fsXp (μ * A ^ 3) (-(341 / 2)) := by
    rw [fsXp, show (-(341 / 2) : ℝ) / 323 = -(341 / 646) by norm_num]
    exact h2
  -- closed forms: `d ℓ = A t^{-157/323}`, `K_B³ t^{1/2} = t^{287/646}`
  have hdl : (0 : ℝ) < (paramsAt μ A).d * sideAt μ A := by
    rw [d_mul_sideAt_eq hA hμ]
    exact mul_pos hA (fsXp_pos ht0)
  have hdl2 : ((paramsAt μ A).d * sideAt μ A) ^ 2
      = A ^ 2 * fsXp (μ * A ^ 3) (-314) := by
    rw [d_mul_sideAt_eq hA hμ, mul_pow, fsXp_pow ht0.le]
    have : (-157 : ℝ) * ((2 : ℕ) : ℝ) = -314 := by norm_num
    rw [this]
  rw [div_pow, div_le_iff₀ (pow_pos hdl 2), hdl2]
  rw [KB3_half_eq hA hμ]
  have hmul : fsXp (μ * A ^ 3) (287 / 2) * (A ^ 2 * fsXp (μ * A ^ 3) (-314))
      = A ^ 2 * fsXp (μ * A ^ 3) (-(341 / 2)) := by
    rw [mul_comm (fsXp (μ * A ^ 3) (287 / 2)) (A ^ 2 * fsXp (μ * A ^ 3) (-314)),
      mul_assoc, fsXp_mul ht0]
    have harg : (-314 : ℝ) + 287 / 2 = -(341 / 2) := by norm_num
    rw [harg]
  rw [hmul]
  have h5 : R ^ 2 = A ^ 2 * (R ^ 2 / A ^ 2) := by field_simp
  rw [h5]
  exact mul_le_mul_of_nonneg_left h2' (by positivity)

end Work.BoseFixB1B
