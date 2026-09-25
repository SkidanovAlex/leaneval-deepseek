import Mathlib
import Submission.NK.CFTLib.IdeleHasse.Descent.transferCore
import Submission.NK.CFTLib.IdeleHasse.Crux.localNormRep

/-!
# The cyclic class of a global element at a cyclic level

For a finite Galois extension `F/K` (with `Gal(F/K)` cyclic) and `x ∈ Kˣ`, this module defines the
*cyclic class* `cycClassOf g hg x ∈ H²(Gal(F/K), Fˣ)` of `x` (the class of the cyclic algebra
`(F/K, x)`), and records:

* `unitsRep_norm_apply`: the norm endomorphism of the units representation is the field norm;
* `cycClassOf_eq_zero_iff`: the cyclic class of `x` vanishes iff `x` is a norm.
-/

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance 5000] Rep.hV1 Rep.hV2
attribute [local instance 100] AddCommGroup.toIntModule

open CategoryTheory

namespace NK.CFTLib.IdeleHasse.Descent

open NK.CFTLib.Descent (cycFun cycClass)

variable {K F : Type} [Field K] [Field F] [Algebra K F]

/-- The image of `x ∈ Kˣ` in `Fˣ`, as an element of the units representation `Fˣ`. -/
noncomputable def unitsImage (x : Kˣ) : Additive Fˣ :=
  Additive.ofMul (Units.map (algebraMap K F).toMonoidHom x)

/-- The image of a global element is fixed by the Galois action. -/
lemma unitsRep_apply_unitsImage (σ : F ≃ₐ[K] F) (x : Kˣ) :
    (NK.HassePrinciple.unitsRep K F).ρ σ (unitsImage (K := K) (F := F) x)
      = unitsImage (K := K) (F := F) x := by
  apply Additive.ofMul.injective
  apply Units.ext
  exact σ.commutes (x : K)

/-- **The cyclic class of a global element `x ∈ Kˣ` at a cyclic level `F/K`**, i.e. the class of
the cyclic algebra `(F/K, x)` in `H²(Gal(F/K), Fˣ)`. -/
noncomputable def cycClassOf [FiniteDimensional K F] (g : F ≃ₐ[K] F)
    (hg : ∀ σ : F ≃ₐ[K] F, σ ∈ Subgroup.zpowers g)
    (x : Kˣ) : groupCohomology (NK.HassePrinciple.unitsRep K F) 2 :=
  cycClass (NK.HassePrinciple.unitsRep K F) g hg (unitsImage (K := K) (F := F) x)
    (fun σ => unitsRep_apply_unitsImage (K := K) (F := F) σ x)

/-- **The norm endomorphism of the units representation is the field norm.**

Proof: the norm endomorphism is `∑_{σ} ρ(σ)` (`Representation.norm`), the sum of the conjugates is
the product (additively: `NK.CFTLib.IdeleHasse.Crux.sum_ofMul_eq_ofMul_prod`), and the product of
the conjugates of a unit is the field norm (`Algebra.norm_eq_prod_automorphisms`). -/
lemma unitsRep_norm_apply [FiniteDimensional K F] [IsGalois K F] (y : Fˣ) :
    ((Additive.toMul ((NK.HassePrinciple.unitsRep K F).ρ.norm (Additive.ofMul y)) : Fˣ) : F)
      = algebraMap K F (Algebra.norm K (y : F)) := by
  have hsum : (NK.HassePrinciple.unitsRep K F).ρ.norm (Additive.ofMul y)
      = ∑ σ : F ≃ₐ[K] F, ((NK.HassePrinciple.unitsRep K F).ρ σ (Additive.ofMul y)) := by
    rw [Representation.norm, LinearMap.sum_apply]
  rw [hsum, show (∑ σ : F ≃ₐ[K] F, ((NK.HassePrinciple.unitsRep K F).ρ σ (Additive.ofMul y)))
      = Additive.ofMul (∏ σ : F ≃ₐ[K] F, σ • y) from
    NK.CFTLib.IdeleHasse.Crux.sum_ofMul_eq_ofMul_prod _ _]
  rw [show ((Additive.toMul (Additive.ofMul (∏ σ : F ≃ₐ[K] F, σ • y)) : Fˣ) : F)
      = ((∏ σ : F ≃ₐ[K] F, σ • y : Fˣ) : F) from rfl]
  rw [Units.coe_prod, Algebra.norm_eq_prod_automorphisms]
  rfl

end NK.CFTLib.IdeleHasse.Descent
