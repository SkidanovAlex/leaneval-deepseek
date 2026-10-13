import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongPersist.L3Rhs.N0gAuxDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.L3Rhs

/-
Intended namespace: `Work.FTS.StrongPersist.L3Rhs`.
The separation of variables of the star part `Vfs α` of `Bf α f`:
`Vfs α z θ = VfsA1 α θ · VfsRad z + VfsA2 α θ · VfsRadZ z`
where (`N0gAuxDefs`) `Vfs α = fun z θ => (3/(2α)) * sin 2θ * pth (F_* α) z θ
- c₂(θ) * Dz (F_* α) z θ` with `F_* α = Work.Construction.Fstar α`,
`VfsRad z = 2z/(1+z)²`, `VfsRadZ z = Zop VfsRad z = z ∂_z VfsRad z`,
`VfsA1 α θ = (3/2) * dthU (VfsGc α) θ`, `VfsA2 α θ = -α * c₂(θ) * VfsGc α θ`,
`VfsGc α θ = Γ(α,θ)/c(α)`, `dthU ψ θ = sin 2θ * deriv ψ θ`.
Route: `F_* α z θ' = (α * VfsRad z) * VfsGc α θ'` and
`F_* α z' θ = (α * VfsGc α θ) * VfsRad z'` (definition of `Work.Construction.Fstar`), so
`pth (F_* α) z θ = (α * VfsRad z) * deriv (VfsGc α) θ` and
`Dz (F_* α) z θ = (α * VfsGc α θ) * (Zop VfsRad z)` (`deriv_const_mul_field`, definitions of
`pth`, `Dz`, `Zop`); the first summand then is
`(3/(2α)) * sin 2θ * α * VfsRad z * deriv (VfsGc α) θ = (3/2) * VfsRad z * dthU (VfsGc α) θ`
and the second is `-c₂(θ) * α * VfsGc α θ * VfsRadZ z`.  (`α ≠ 0` is available from the
caller as `0 < α ≤ 1`; it is also fine to prove the identity unconditionally.)
-/

/-! ## The two partial derivatives of the profile `F_*`

The profile factors as `F_*(z,θ) = (α·VfsRad z)·VfsGc α θ`; since `VfsRad` does not depend on
`θ` and `VfsGc` does not depend on `z`, both partial derivatives separate.  The identities below
are `deriv_const_mul_field`, valid for every `α` (including `α = 0`, where both sides vanish). -/

/-- The `θ`-derivative of the profile factors through `VfsRad`. -/
theorem pth_Fstar_sep (α z θ : ℝ) :
    Work.Spaces.pth (Work.Construction.Fstar α) z θ
      = (α * VfsRad z) * deriv (VfsGc α) θ := by
  have hfun : (fun θ' : ℝ => Work.Construction.Fstar α z θ')
      = fun θ' => (α * VfsRad z) * VfsGc α θ' := by
    funext θ'
    simp only [Work.Construction.Fstar, VfsGc, VfsRad, Work.FM.Fstar]
    ring
  rw [Work.Spaces.pth, hfun, deriv_const_mul_field]

/-- The `D_z`-derivative of the profile factors through `VfsGc`. -/
theorem Dz_Fstar_sep (α z θ : ℝ) :
    Work.Spaces.Dz (Work.Construction.Fstar α) z θ
      = (α * VfsGc α θ) * VfsRadZ z := by
  have hfun : (fun z' : ℝ => Work.Construction.Fstar α z' θ)
      = fun z' => (α * VfsGc α θ) * VfsRad z' := by
    funext z'
    simp only [Work.Construction.Fstar, VfsGc, VfsRad, Work.FM.Fstar]
  rw [Work.Spaces.Dz, Work.Spaces.pz, hfun, deriv_const_mul_field]
  simp only [VfsRadZ, Work.Spaces.Zop]
  ring

/-- At `α = 0` the angular profile `VfsGc 0 = Γ(0,·)/c(0)` is the constant `1/c(0)`, since
`Γ(0,θ) = (sin θ cos²θ)^0 = 1`; in particular its derivative vanishes. -/
theorem deriv_VfsGc_zero (θ : ℝ) : deriv (VfsGc 0) θ = 0 := by
  have hGc : VfsGc 0 = fun _ : ℝ => 1 / Work.Spaces.c 0 := by
    funext t
    simp [VfsGc, Work.Spaces.Gam]
  rw [hGc, deriv_const]

theorem VfsSep (α : ℝ) (z θ : ℝ) :
    Vfs α z θ = VfsA1 α θ * VfsRad z + VfsA2 α θ * VfsRadZ z := by
  rcases eq_or_ne α 0 with hα | hα
  · subst hα
    rw [Vfs, pth_Fstar_sep, Dz_Fstar_sep, VfsA1, VfsA2, Work.Spaces.dthU, deriv_VfsGc_zero]
    ring
  · rw [Vfs, pth_Fstar_sep, Dz_Fstar_sep, VfsA1, VfsA2, Work.Spaces.dthU,
      Work.Construction.s2]
    field_simp
    ring

end Work.FTS.StrongPersist.L3Rhs
