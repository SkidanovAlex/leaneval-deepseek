import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Submission.Work.ConstructionInstance.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The parity class of the self-similar vorticity `omegaS`

`Work.LWP.IsOddVorticity ω` is the axial-reflection parity `ω (reflZ x) = - flipZ (ω x)` of the
vorticity of an odd axisymmetric no-swirl velocity field (Elgindi, Annals **194** (2021),
§Setup).  The self-similar vorticity of the construction,

  `omegaS p g x = profile p g (ρ(x)^p) (θ(x)) • e_θ(x)`,

is a field of exactly that shape: an angular profile times `e_θ`.  Under the reflection
`x ↦ (x₀, x₁, -x₃)` we have `ρ ↦ ρ`, `θ ↦ -θ`, `e_θ ↦ e_θ`, and `flipZ` acts on a scalar multiple
of the axis-free vector `e_θ` as the identity; so the parity of `omegaS p g` is the parity of the
profile, which is odd in `θ` (`profile_odd`) precisely because `g` vanishes at `θ = 0`
(`Work.Spaces.VanishTheta`) and `p ≠ 0` (so that `F_*(z,0) = 0`).

This module proves that dictionary:  `isOddVorticity_omegaS`.
-/

namespace Work.ConstructionInstance

/-! ## The `Cyl` coordinate dictionary under the reflection `reflZ` -/

/-- The three dimensional radius is invariant under the reflection in the plane `x₃ = 0`. -/
private lemma rho_reflZ (x : Work.Cyl.R3) : Work.Cyl.rho (Work.Cyl.reflZ x) = Work.Cyl.rho x := by
  simp [Work.Cyl.rho, Work.Cyl.radSq, Work.Cyl.axial, Work.Cyl.reflZ]

/-- The polar angle changes sign under the reflection in the plane `x₃ = 0`. -/
private lemma theta_reflZ (x : Work.Cyl.R3) :
    Work.Cyl.theta (Work.Cyl.reflZ x) = - Work.Cyl.theta x := by
  simp [Work.Cyl.theta, Work.Cyl.radial, Work.Cyl.radSq, Work.Cyl.axial, Work.Cyl.reflZ, neg_div,
    Real.arctan_neg]

/-- The angular frame vector `e_θ` is invariant under the reflection in the plane `x₃ = 0` (it
lies in that plane). -/
private lemma eTheta_reflZ (x : Work.Cyl.R3) :
    Work.Cyl.eTheta (Work.Cyl.reflZ x) = Work.Cyl.eTheta x := by
  simp [Work.Cyl.eTheta, Work.Cyl.radial, Work.Cyl.radSq, Work.Cyl.angularVec, Work.Cyl.reflZ]

/-- The flip of the third component commutes with scalar multiplication. -/
private lemma flipZ_smul (c : ℝ) (v : Work.Cyl.R3) :
    Work.Cyl.flipZ (c • v) = c • Work.Cyl.flipZ v := by
  apply Work.Cyl.ext_coord <;> simp [Work.Cyl.flipZ]

/-- The flip of the third component fixes `e_θ`. -/
private lemma flipZ_eTheta (x : Work.Cyl.R3) : Work.Cyl.flipZ (Work.Cyl.eTheta x) = Work.Cyl.eTheta x := by
  apply Work.Cyl.ext_coord <;> simp [Work.Cyl.flipZ, Work.Cyl.eTheta]

/-! ## The parity class of `omegaS` -/

theorem isOddVorticity_omegaS {p : ℝ} (hp : p ≠ 0) {g : ℝ → ℝ → ℝ}
    (hvt : Work.Spaces.VanishTheta g) :
    Work.LWP.IsOddVorticity (Work.ConstructionInstance.omegaS p g) := by
  intro x
  have hg0 : ∀ z : ℝ, g z 0 = 0 := hvt.1
  show Work.ConstructionInstance.profile p g (Work.Cyl.Rc p (Work.Cyl.reflZ x))
        (Work.Cyl.theta (Work.Cyl.reflZ x)) • Work.Cyl.eTheta (Work.Cyl.reflZ x)
      = - Work.Cyl.flipZ (Work.ConstructionInstance.profile p g (Work.Cyl.Rc p x)
        (Work.Cyl.theta x) • Work.Cyl.eTheta x)
  simp only [Work.Cyl.Rc, rho_reflZ, theta_reflZ, eTheta_reflZ]
  rw [Work.ConstructionInstance.profile_odd hp hg0, neg_smul, flipZ_smul, flipZ_eTheta]

end Work.ConstructionInstance
