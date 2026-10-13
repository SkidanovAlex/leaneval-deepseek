import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.LevelOneAsm.EigParsevalDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.LevelOneAsm

local notation "Iθ" => Work.Spaces.Iθ

/-- The normalised angular eigenfunctions form an orthonormal family in `L²(Iθ, cos θ dθ)`.
Elaborate this file with `open scoped Real Topology ENNReal; open MeasureTheory Set Filter`.

Here `eigE n = (Real.sqrt (eigDn n))⁻¹ • eigLp (n + 1) : Lp ℝ 2 angMeasure` is the normalised
class of `Θ_{n+1} = eigFun (n+1)` defined in `Submission/Work/FTS/EllipticEst/LevelOneAsm/EigParsevalDefs.lean`,
`eigDn n = ∫ θ in Iθ, (eigFun (n+1) θ)^2 * Real.cos θ`, and `angMeasure` is the measure with
`∫ F ∂angMeasure = ∫ θ in Iθ, cos θ * F θ` (`integral_angMeasure`).

Route: `orthonormal_iff_ite` reduces the goal to `inner ℝ (eigE n) (eigE m) = if n = m then 1 else 0`.
Unfold `eigE`, pull the two real scalars out of the inner product (`real_inner_smul_left` /
`inner_smul_right` / `inner_smul_left`), then use `inner_eigLp`
(`inner ℝ (eigLp a) (eigLp b) = ∫ θ in Iθ, eigFun a θ * eigFun b θ * Real.cos θ`) with
`eigFun_orth` (`n ≠ m` ⟹ `∫ Θ_n Θ_m cos = 0`) and, for `n = m`, `eigDn_pos` together with
`Real.sq_sqrt` to show `(√(eigDn n))⁻¹ * (√(eigDn n))⁻¹ * eigDn n = 1`. -/
theorem eigE_orthonormal : Orthonormal ℝ eigE := by
  rw [orthonormal_iff_ite]
  intro n m
  -- pull the two normalising scalars out of the inner product
  have hinner : inner ℝ (eigE n) (eigE m)
      = (Real.sqrt (eigDn n))⁻¹ * (Real.sqrt (eigDn m))⁻¹ *
        ∫ θ in Iθ, eigFun (n + 1) θ * eigFun (m + 1) θ * Real.cos θ := by
    rw [eigE, eigE, real_inner_smul_left, inner_smul_right, inner_eigLp]
    ring
  rw [hinner]
  rcases eq_or_ne n m with hnm | hnm
  · -- the diagonal: the weighted integral is `eigDn n` and the scalars cancel it
    subst hnm
    rw [ite_eq_left rfl]
    have hd := eigDn_pos n
    have hI : (∫ θ in Iθ, eigFun (n + 1) θ * eigFun (n + 1) θ * Real.cos θ) = eigDn n := by
      rw [eigDn]
      refine setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)
    rw [hI, ← mul_inv, ← sq, Real.sq_sqrt (le_of_lt hd), inv_mul_cancel₀ (ne_of_gt hd)]
  · -- off the diagonal: orthogonality of the angular eigenfunctions
    rw [ite_eq_right hnm]
    have h : n + 1 ≠ m + 1 := by omega
    rw [eigFun_orth (n + 1) (m + 1) h, mul_zero]

end Work.FTS.EllipticEst.LevelOneAsm
