import Mathlib
import Submission.NK.Reconstruct.gammaHaus
import Submission.NK.Reconstruct.Gamma
import Submission.NK.Reconstruct.NumFieldIn

/-!
# The invisible subgroup is transported by a continuous isomorphism `Γ_{K₁} ≃* Γ_{K₂}`

Let `K₁`, `K₂` be finite normal number-field levels of a separable closure `Ω` of `ℚ` and let
`ℓ` be a prime.  Write `Γ_K` for Shimizu's ℓ-adic abelianisation (`NK.Reconstruct.Gamma`) and
`Γ_K^{tf}` for its Hausdorff torsion-free quotient (`NK.Reconstruct.GammaHaus`), with projection
`gammaHausMk`.

By definition (`gammaHausMk_eq_one_iff`) an element of `Γ_K` becomes trivial in `Γ_K^{tf}` exactly
when it lies in the kernel of the whole continuous dual `Hom_cts(Γ_K, ℤ_ℓ)`.  Consequently a
*continuous* group isomorphism `σbar : Γ_{K₁} ≃* Γ_{K₂}` transports this "invisible" condition:

  `gammaHausMk (σbar x) = 1 ↔ gammaHausMk x = 1`.

The only point needing care is that the *inverse* of `σbar` is continuous.  This is where the
hypotheses are used: `Γ_K` is compact and Hausdorff (`instCompactSpaceGamma`, and the type is a
subtype of a product of finite discrete groups), so a continuous bijection out of `Γ_{K₁}` is a
homeomorphism, and in particular has continuous inverse.

Once both `σbar` and `σbar.symm` are continuous, the duals correspond under the two precomposition
maps `dualMap ℓ σbar hσbar : Dual Γ_{K₂} → Dual Γ_{K₁}` and
`dualMap ℓ σbar.symm h : Dual Γ_{K₁} → Dual Γ_{K₂}`, which are mutually inverse; the claim follows
componentwise.

This is the compatibility of the level-`∞` invariant `K^{(∞,ℓ)}` of Shimizu's §4 with an
isomorphism of the abelianisations at two levels, needed in the reconstruction; see
`Submission/Work/Reconstruct/lemma4f4_defs.lean` for the surrounding vocabulary.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NK.Reconstruct

attribute [local instance] NumFieldIn.finite NumFieldIn.numberField

open scoped Pointwise

/-- **The invisible subgroup is preserved by a continuous isomorphism of the ℓ-adic
abelianisations.**  For a continuous group isomorphism `σbar : Γ_{K₁} ≃* Γ_{K₂}` between the
abelianisations of two finite normal levels, `σbar x` is invisible to the continuous dual of
`Γ_{K₂}` if and only if `x` is invisible to the continuous dual of `Γ_{K₁}`; equivalently, `σbar`
maps the kernel of `Γ_{K₁} ↠ Γ_{K₁}^{tf}` onto the kernel of `Γ_{K₂} ↠ Γ_{K₂}^{tf}`. -/
theorem gammaHausMk_sbar_eq_one_iff {Ω : Type*} [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]
    (K₁ K₂ : NumFieldIn ℚ Ω) [IsSepClosure ↥(K₁.L) Ω] [IsSepClosure ↥(K₂.L) Ω] (ℓ : ℕ) [Fact ℓ.Prime]
    (σbar : Gamma ↥(K₁.L) Ω ℓ ≃* Gamma ↥(K₂.L) Ω ℓ) (hσbar : Continuous ⇑σbar)
    (x : Gamma ↥(K₁.L) Ω ℓ) :
    gammaHausMk (K := ↥(K₂.L)) (K' := Ω) (ℓ := ℓ) (σbar x) = 1
      ↔ gammaHausMk (K := ↥(K₁.L)) (K' := Ω) (ℓ := ℓ) x = 1 := by
  -- `σbar` is a continuous bijection from the compact space `Γ_{K₁}` to the Hausdorff space
  -- `Γ_{K₂}`, hence a homeomorphism: its inverse is continuous.
  have hσbar_inv : Continuous ⇑(σbar.symm) := by
    let e : (Gamma ↥(K₁.L) Ω ℓ) ≃ₜ (Gamma ↥(K₂.L) Ω ℓ) :=
      Continuous.homeoOfEquivCompactToT2 (f := σbar.toEquiv) hσbar
    exact e.symm.continuous_toFun
  -- View `σbar` and its inverse as monoid homomorphisms, so that the continuity hypotheses match
  -- the arguments of `dualMap` syntactically.
  let φ : Gamma ↥(K₁.L) Ω ℓ →* Gamma ↥(K₂.L) Ω ℓ := σbar
  let ψ : Gamma ↥(K₂.L) Ω ℓ →* Gamma ↥(K₁.L) Ω ℓ := σbar.symm
  have hφ : Continuous ⇑φ := hσbar
  have hψ : Continuous ⇑ψ := hσbar_inv
  -- Both sides are the statement that the element is killed by the whole continuous dual.
  rw [gammaHausMk_eq_one_iff, gammaHausMk_eq_one_iff]
  constructor
  · -- If `σbar x` is invisible, then so is `x`: test `x` against an arbitrary continuous
    -- homomorphism `f : Γ_{K₁} → ℤ_ℓ` by pulling it back along `σbar.symm`.
    intro h f
    have h1 := h (dualMap ℓ ψ hψ f)
    rw [dualMap_apply] at h1
    simpa [ψ] using h1
  · -- If `x` is invisible, then so is `σbar x`: push a continuous homomorphism
    -- `g : Γ_{K₂} → ℤ_ℓ` forward to `g ∘ σbar`.
    intro h g
    have h1 := h (dualMap ℓ φ hφ g)
    rw [dualMap_apply] at h1
    simpa [φ] using h1

end NK.Reconstruct
