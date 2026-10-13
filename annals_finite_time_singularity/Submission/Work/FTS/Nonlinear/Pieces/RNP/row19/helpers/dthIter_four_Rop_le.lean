import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row19.helpers.Row19Ident

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Row 19: the order-4 angular bound for `ℛ(Φ̃_*)`

For a frozen `StarPkg α Cs Φs`, the `𝒲^{4,∞}`-field `StarPkg.R` controls the function

  `ℛ := (z+1)/z · Rop α (Φ̃_*)`   (`Φ̃_* = PhiTs α Φs`),

because `(z+1)/z` is a `z`-only factor.  Its `(k = 0, j = 4)`-slot therefore gives

  `|D_θ^4 ℛ z θ| · sin(2θ)^{-α/5}/(α + sin 2θ) ≤ |ℛ|_{𝒲^{4,∞}} ≤ Cs · α`

for `z ∈ Iz`, `θ ∈ Iθ`; multiplying by `(z+1)/z` is an invertible operation and yields the
bound of `dthIter_four_Rop_le` (`z/(1+z)` on the right).  All the work is in
`Work.Spaces.pz_Dth_sup_bound`, which also disposes of the angular endpoints `θ = 0, π/2`
(there `sin(2θ) = 0`, so `D_θ^4` vanishes identically and both sides are `0`).
-/

namespace Work.FTS.Nonlinear.Pieces.RNP.row19.helpers

/-- **The `(k = 0, j = 4)`-slot bound for `ℛ(Φ̃_*)`.**  `D_θ^4 Rop α (PhiTs α Φs)` inherits
its bound from the frozen `𝒲^{4,∞}`-field of `(z+1)/z · Rop α (PhiTs α Φs)`: the factor
`(z+1)/z` is constant in `θ`, hence commutes with `D_θ`, and it cancels against the
`z/(1+z)` on the right hand side. -/
theorem dthIter_four_Rop_le {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hs : Work.FTS.Nonlin.StarPkg α Cs Φs) :
    ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter 4 (Work.Construction.Rop α
          (Work.FTS.Nonlin.PhiTs α Φs)) z θ|
        ≤ max Cs 0 * α * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
            * (z / (1 + z)) := by
  intro z hz θ hθ
  have hz0 : (0 : ℝ) < z := hz
  have hzIz : z ∈ Work.Spaces.Iz := by
    simp only [Work.Spaces.Iz, Set.mem_Ici]; exact hz.le
  have hz1 : (0 : ℝ) < z + 1 := by linarith
  have hcpos : (0 : ℝ) < (z + 1) / z := div_pos hz1 hz0
  have hsin0 : 0 ≤ Real.sin (2 * θ) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · linarith [hθ.1]
    · linarith [hθ.2]
  have hΛ0 : 0 ≤ (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) :=
    mul_nonneg (by linarith) (Real.rpow_nonneg hsin0 _)
  have hmem := hs.R.1
  have hle : Work.Spaces.WlInf α 4
      (fun z θ => (z + 1) / z * Work.Construction.Rop α
        (Work.FTS.Nonlin.PhiTs α Φs) z θ) ≤ max Cs 0 * α :=
    le_trans hs.R.2 (mul_le_mul_of_nonneg_right (le_max_left _ _) hα.le)
  have hkey := Work.Spaces.pz_Dth_sup_bound α hα 4
    (fun z θ => (z + 1) / z * Work.Construction.Rop α
      (Work.FTS.Nonlin.PhiTs α Φs) z θ) hmem 4 0 (by norm_num) (by norm_num) z θ hzIz hθ
  simp only [Work.Spaces.pzIter_zero, pow_zero, div_one] at hkey
  have hbnd : (z + 1) / z * |Work.Spaces.DthIter 4 (Work.Construction.Rop α
      (Work.FTS.Nonlin.PhiTs α Φs)) z θ|
      ≤ (max Cs 0 * α) * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by
    have h := le_trans hkey (mul_le_mul_of_nonneg_right hle hΛ0)
    have hfac := Work.FTS.Nonlinear.Pieces.RNP.row19.DthIter_mul_zfactor 4
      (fun z => (z + 1) / z) (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs)) z θ
    rw [hfac, abs_mul, abs_of_pos hcpos] at h
    exact h
  have hprod : ((z + 1) / z) * (z / (1 + z)) = 1 := by
    field_simp
    ring
  have hd : 0 ≤ z / (1 + z) := div_nonneg hz0.le (by linarith : (0 : ℝ) ≤ 1 + z)
  have hstep := mul_le_mul_of_nonneg_right hbnd hd
  have hL : ((z + 1) / z * |Work.Spaces.DthIter 4 (Work.Construction.Rop α
        (Work.FTS.Nonlin.PhiTs α Φs)) z θ|) * (z / (1 + z))
      = |Work.Spaces.DthIter 4 (Work.Construction.Rop α
        (Work.FTS.Nonlin.PhiTs α Φs)) z θ| := by
    rw [mul_assoc, mul_left_comm, hprod, mul_one]
  rw [hL] at hstep
  exact hstep

end Work.FTS.Nonlinear.Pieces.RNP.row19.helpers
