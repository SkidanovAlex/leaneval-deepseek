/-
Copyright: work module for the Elgindi finite-time singularity project.

# The `sin 2θ`-substitution for the transport coefficients `ℛ, 𝒰, 𝒱`

`StarPkg` (`Work.FTS.Nonlin.StarPkg`) asks for `𝒲^{l,∞}`-bounds on the three transported
quantities

  `((z+1)/z)·ℛ(Φ̃_*)`,  `∂_θ(𝒰(Φ̃_*))`,  `𝒱(Φ̃_*)`,

where `Φ̃_* = PhiTil α (Fstar α) Φs = Φs - (1/(4α)) sin 2θ · L₁₂(F_*)` is the elliptic residual and
`ℛ, 𝒰, 𝒱` are the transport coefficients of the self-similar vorticity equation
(`Work.Construction.Rop`, `Uop`, `Vop`).

All three are controlled through the single function `Φ := Φ̃_*/sin 2θ`.  The point of the
substitution is that the *singular* factors `tan θ` and `1/cos θ` in the definitions of `ℛ` and
`𝒰` cancel against the `sin 2θ`:

* `ℛ(sin 2θ · Φ) = 2Φ + 2α sin²θ · D_zΦ + sin 2θ · ∂_θΦ`  (bounded angular coefficients);
* `𝒰(sin 2θ · Φ) = -sin 2θ · (3Φ + α D_zΦ)`;
* `𝒱(sin 2θ · Φ) = 2(cos²θ - 2 sin²θ)Φ + sin 2θ · ∂_θΦ`;
* `∂_θ(𝒰(sin 2θ · Φ))·sin 2θ = -sin 2θ·[2cos2θ(3Φ + α D_zΦ) + sin 2θ·(3∂_θΦ + α D_z∂_θΦ)]`.

All four are *pointwise* identities, valid wherever the totalised derivatives are the honest
ones (which is the open quadrant for a `SmoothQuad` function).  They are the algebraic layer of
the `N3` node `StarPkg_inhabitant`.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Construction.Defs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.StarPkg

set_option autoImplicit false

/-- **`ℛ(sin 2θ · Φ) = 2Φ + 2α sin²θ · D_zΦ + sin 2θ · ∂_θΦ`.**  The two `tan θ` factors of
`ℛ = 2 tan θ·g + α tan θ·D_zg + ∂_θg` cancel against the `sin 2θ` into the bounded quantities
`2 sin²θ` and `2α sin²θ`. -/
theorem Rop_sin_two_mul (α : ℝ) (Φ : ℝ → ℝ → ℝ) (z θ : ℝ) (hcos : Real.cos θ ≠ 0)
    (hθ : DifferentiableAt ℝ (fun θ' => Φ z θ') θ) :
    Work.Construction.Rop α (fun z θ => Real.sin (2 * θ) * Φ z θ) z θ
      = 2 * Φ z θ + 2 * α * Real.sin θ ^ 2 * Work.Spaces.Dz Φ z θ
        + Real.sin (2 * θ) * Work.Spaces.pth Φ z θ := by
  have hpz : Work.Spaces.pz (fun z θ => Real.sin (2 * θ) * Φ z θ) z θ
      = Real.sin (2 * θ) * Work.Spaces.pz Φ z θ := by
    simp only [Work.Spaces.pz]
    exact deriv_const_mul_field (Real.sin (2 * θ))
  have hsin2' : HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ')) (Real.cos (2 * θ) * 2) θ := by
    have h2' : HasDerivAt (fun θ' : ℝ => 2 * θ') 2 θ := by
      simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
    exact (Real.hasDerivAt_sin (2 * θ)).comp θ h2'
  have hpth : Work.Spaces.pth (fun z θ => Real.sin (2 * θ) * Φ z θ) z θ
      = Real.cos (2 * θ) * 2 * Φ z θ + Real.sin (2 * θ) * Work.Spaces.pth Φ z θ := by
    simp only [Work.Spaces.pth]
    exact (hsin2'.mul hθ.hasDerivAt).deriv
  rw [Work.Construction.Rop, hpz, hpth]
  have hs2 : Real.sin (2 * θ) = 2 * Real.sin θ * Real.cos θ := Real.sin_two_mul θ
  have hc2 : Real.cos (2 * θ) = 2 * Real.cos θ ^ 2 - 1 := Real.cos_two_mul θ
  field_simp
  rw [hs2, hc2, Work.Spaces.Dz, Work.Spaces.pz]
  linear_combination (4 * Real.cos θ * Φ z θ) * Real.sin_sq_add_cos_sq θ

/-- **`𝒰(sin 2θ · Φ) = -sin 2θ · (3Φ + α D_zΦ)`**, where
`𝒰(Ψ) = -3Ψ - α z ∂_zΨ`. -/
theorem Uop_sin_two_mul (α : ℝ) (Φ : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Construction.Uop α (fun z θ => Real.sin (2 * θ) * Φ z θ) z θ
      = -(Real.sin (2 * θ) * (3 * Φ z θ + α * Work.Spaces.Dz Φ z θ)) := by
  have hpz : Work.Spaces.pz (fun z θ => Real.sin (2 * θ) * Φ z θ) z θ
      = Real.sin (2 * θ) * Work.Spaces.pz Φ z θ := by
    simp only [Work.Spaces.pz]
    exact deriv_const_mul_field (Real.sin (2 * θ))
  rw [Work.Construction.Uop, hpz, Work.Spaces.Dz, Work.Spaces.pz]
  ring

/-- **`𝒱(sin 2θ · Φ) = 2(cos²θ - 2 sin²θ)Φ + sin 2θ · ∂_θΦ`**, where
`𝒱(Ψ) = ∂_θΨ - tan θ · Ψ`. -/
theorem Vop_sin_two_mul (Φ : ℝ → ℝ → ℝ) (z θ : ℝ) (hcos : Real.cos θ ≠ 0)
    (hθ : DifferentiableAt ℝ (fun θ' => Φ z θ') θ) :
    Work.Construction.Vop (fun z θ => Real.sin (2 * θ) * Φ z θ) z θ
      = 2 * (Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2) * Φ z θ
        + Real.sin (2 * θ) * Work.Spaces.pth Φ z θ := by
  have hsin2' : HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ')) (Real.cos (2 * θ) * 2) θ := by
    have h2' : HasDerivAt (fun θ' : ℝ => 2 * θ') 2 θ := by
      simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
    exact (Real.hasDerivAt_sin (2 * θ)).comp θ h2'
  have hpth : Work.Spaces.pth (fun z θ => Real.sin (2 * θ) * Φ z θ) z θ
      = Real.cos (2 * θ) * 2 * Φ z θ + Real.sin (2 * θ) * Work.Spaces.pth Φ z θ := by
    simp only [Work.Spaces.pth]
    exact (hsin2'.mul hθ.hasDerivAt).deriv
  rw [Work.Construction.Vop, hpth, Real.tan_eq_sin_div_cos]
  have hs2 : Real.sin (2 * θ) = 2 * Real.sin θ * Real.cos θ := Real.sin_two_mul θ
  have hc2 : Real.cos (2 * θ) = 2 * Real.cos θ ^ 2 - 1 := Real.cos_two_mul θ
  rw [hs2, hc2]
  field_simp
  linear_combination (Φ z θ) * Real.sin_sq_add_cos_sq θ

/-- **`∂_θ(𝒰(sin 2θ · Φ)) = -[2cos2θ·(3Φ + α D_zΦ) + sin 2θ·(3∂_θΦ + α D_z∂_θΦ)]`** — the
`∂_θ`-derivative (the *plain* one, since `Work.Spaces.pth` is `∂_θ`) of the `𝒰`-identity, in the
form in which the `WlInf α 5 (pth (Uop …))` bound of `StarPkg.dU` needs it. -/
theorem pth_Uop_sin_two_mul (α : ℝ) (Φ : ℝ → ℝ → ℝ) (z θ : ℝ)
    (hz : ∀ θ' : ℝ, DifferentiableAt ℝ (fun z' => Φ z' θ') z)
    (hθ : DifferentiableAt ℝ (fun θ' => Φ z θ') θ)
    (hzθ : DifferentiableAt ℝ (fun θ' => Work.Spaces.Dz Φ z θ') θ) :
    Work.Spaces.pth (Work.Construction.Uop α (fun z θ => Real.sin (2 * θ) * Φ z θ)) z θ
      = -(2 * Real.cos (2 * θ) * (3 * Φ z θ + α * Work.Spaces.Dz Φ z θ)
          + Real.sin (2 * θ) * (3 * Work.Spaces.pth Φ z θ
            + α * Work.Spaces.pth (Work.Spaces.Dz Φ) z θ)) := by
  have hU : (fun θ' : ℝ =>
        Work.Construction.Uop α (fun z θ => Real.sin (2 * θ) * Φ z θ) z θ')
      = fun θ' => -(Real.sin (2 * θ') * (3 * Φ z θ' + α * Work.Spaces.Dz Φ z θ')) := by
    funext θ'
    exact Uop_sin_two_mul α Φ z θ'
  have hsin2' : HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ')) (Real.cos (2 * θ) * 2) θ := by
    have h2' : HasDerivAt (fun θ' : ℝ => 2 * θ') 2 θ := by
      simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
    exact (Real.hasDerivAt_sin (2 * θ)).comp θ h2'
  have hinner : HasDerivAt (fun θ' : ℝ => 3 * Φ z θ' + α * Work.Spaces.Dz Φ z θ')
      (3 * Work.Spaces.pth Φ z θ + α * Work.Spaces.pth (Work.Spaces.Dz Φ) z θ) θ := by
    have h1 : HasDerivAt (fun θ' : ℝ => Φ z θ') (Work.Spaces.pth Φ z θ) θ := hθ.hasDerivAt
    have h2 : HasDerivAt (fun θ' : ℝ => Work.Spaces.Dz Φ z θ')
        (Work.Spaces.pth (Work.Spaces.Dz Φ) z θ) θ := hzθ.hasDerivAt
    exact ((h1.const_mul 3).add (h2.const_mul α))
  have hprod : HasDerivAt
      (fun θ' : ℝ => Real.sin (2 * θ') * (3 * Φ z θ' + α * Work.Spaces.Dz Φ z θ'))
      (Real.cos (2 * θ) * 2 * (3 * Φ z θ + α * Work.Spaces.Dz Φ z θ)
        + Real.sin (2 * θ) * (3 * Work.Spaces.pth Φ z θ
          + α * Work.Spaces.pth (Work.Spaces.Dz Φ) z θ)) θ :=
    hsin2'.mul hinner
  rw [Work.Spaces.pth, hU]
  have hneg : (fun θ' : ℝ => -(Real.sin (2 * θ')
        * (3 * Φ z θ' + α * Work.Spaces.Dz Φ z θ'))) = -(fun θ' : ℝ =>
      Real.sin (2 * θ') * (3 * Φ z θ' + α * Work.Spaces.Dz Φ z θ')) := by
    funext θ'; rfl
  rw [hneg, deriv.neg, hprod.deriv]
  simp only [Work.Spaces.Dz]
  ring_nf

end Work.FTS.H2.StarPkg
