import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row19.helpers.Row19Ident

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Row 19: the `(k = 1, j = 4)`-slot bound for `∂_θ𝒰(Φ̃_*)`

The frozen `StarPkg α Cs Φs` carries the `𝒲^{5,∞}`-field

  `∂_θ𝒰(Φ̃_*) = ∂_θ (Uop α (PhiTs α Φs))`,   `|·|_{𝒲^{5,∞}} ≤ Cs · α`

(`StarPkg.dU`).  Its slot `(j, k) = (4, 1)` — four angular `D_θ`-derivatives followed by one
radial `∂_z` — is therefore controlled by

  `|∂_z D_θ^4 (∂_θ𝒰(Φ̃_*))(z,θ)| ≤ |·|_{𝒲^{5,∞}} / (1+z) · (α + sin 2θ) sin(2θ)^{α/5}`,

which is `Work.Spaces.pz_Dth_sup_bound` instantiated at `l = 5`, `j = 4`, `k = 1` (legitimate
since `1 + 4 ≤ 5`).  The `z`-weight `1/(z+1)^k = 1/(1+z)` is exactly the one in the statement,
and the `α`-factor `max Cs 0` replaces `Cs` through `Cs ≤ max Cs 0` (`α > 0`).  The proof is
purely bookkeeping: `pzIter 1 = ∂_z`, and the endpoint cases `θ = 0, π/2` are already handled
inside `pz_Dth_sup_bound` (there `sin(2θ) = 0`, so every `D_θ`-iterate vanishes).
-/

namespace Work.FTS.Nonlinear.Pieces.RNP.row19.helpers

/-- **The `(k = 1, j = 4)`-slot bound for `∂_θ𝒰(Φ̃_*)`.**  Directly from the frozen
`𝒲^{5,∞}`-bound `StarPkg.dU` via `Work.Spaces.pz_Dth_sup_bound`. -/
theorem pz_dthIter_four_pthU_le {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hs : Work.FTS.Nonlin.StarPkg α Cs Φs) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.pz (Work.Spaces.DthIter 4 (Work.Spaces.pth
          (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs)))) z θ|
        ≤ max Cs 0 * α * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
            / (1 + z) := by
  intro z hz θ hθ
  -- the frozen `𝒲^{5,∞}`-bound of `∂_θ𝒰(Φ̃_*)`, with `Cs` upgraded to `max Cs 0`
  have hle : Work.Spaces.WlInf α 5 (Work.Spaces.pth (Work.Construction.Uop α
        (Work.FTS.Nonlin.PhiTs α Φs))) ≤ max Cs 0 * α :=
    le_trans hs.dU.2 (mul_le_mul_of_nonneg_right (le_max_left _ _) hα.le)
  -- the slot bound `(j, k) = (4, 1)`, `1 + 4 ≤ 5`
  have hkey := Work.Spaces.pz_Dth_sup_bound α hα 5 (Work.Spaces.pth
      (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs))) hs.dU.1 4 1
      (by norm_num) (by norm_num) z θ hz hθ
  -- the two `z`-weights involved are the same
  have hz1 : (0 : ℝ) < z + 1 := by
    have hz0 : (0 : ℝ) ≤ z := hz
    linarith
  have hsin0 : 0 ≤ Real.sin (2 * θ) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · linarith [hθ.1]
    · linarith [hθ.2]
  have hΛ0 : 0 ≤ (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) :=
    mul_nonneg (by linarith) (Real.rpow_nonneg hsin0 _)
  -- divide the `𝒲^{5,∞}`-bound by `(z+1)^1 = 1+z` and compare with `(max Cs 0 * α)/(1+z)`
  have hdiv : Work.Spaces.WlInf α 5 (Work.Spaces.pth (Work.Construction.Uop α
        (Work.FTS.Nonlin.PhiTs α Φs))) / (z + 1) ^ 1 ≤ (max Cs 0 * α) / (1 + z) := by
    rw [pow_one, show (1 + z : ℝ) = z + 1 by ring]
    exact div_le_div_of_nonneg_right hle hz1.le
  have hstep := mul_le_mul_of_nonneg_right hdiv hΛ0
  -- reassociate the right hand side
  have hri : (max Cs 0 * α) / (1 + z)
        * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
      = max Cs 0 * α * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
          / (1 + z) := by
    ring
  -- `∂_z = pzIter 1`
  calc |Work.Spaces.pz (Work.Spaces.DthIter 4 (Work.Spaces.pth (Work.Construction.Uop α
          (Work.FTS.Nonlin.PhiTs α Φs)))) z θ|
      = |Work.Spaces.pzIter 1 (Work.Spaces.DthIter 4 (Work.Spaces.pth (Work.Construction.Uop α
          (Work.FTS.Nonlin.PhiTs α Φs)))) z θ| := rfl
    _ ≤ max Cs 0 * α * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
          / (1 + z) := by
        rw [← hri]
        exact le_trans hkey hstep

end Work.FTS.Nonlinear.Pieces.RNP.row19.helpers
