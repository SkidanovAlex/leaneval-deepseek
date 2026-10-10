import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open CategoryTheory Representation

set_option autoImplicit false

universe u

namespace NK.HassePrinciple

/-- The coefficient ring `ℤ`, lifted into the universe of the fields so that Mathlib's
`groupCohomology` (which requires the coefficient ring and the group to live in the same universe)
applies. -/
abbrev CoeffInt : Type u := ULift.{u} ℤ

/-- The scalar action of `ULift R` commutes with any action commuting with the `R`-action. -/
instance instSMulCommClassULift (M R A : Type*) [SMul R A] [SMul M A] [SMulCommClass M R A] :
    SMulCommClass M (ULift R) A where
  smul_comm m n x := by
    show m • (n.down • x) = n.down • (m • x)
    exact SMulCommClass.smul_comm m n.down x

section RootsOfUnity

variable {K L : Type u} [Field K] [Field L] [Algebra K L]

/-- **The Galois action on the `p`-th roots of unity of `L`**, i.e. on `μ_p(L) ⊆ Lˣ`. -/
noncomputable instance instMulDistribMulActionRootsOfUnity (p : ℕ) :
    MulDistribMulAction (L ≃ₐ[K] L) (rootsOfUnity p L) where
  smul σ x := ⟨σ • (x : Lˣ), (mem_rootsOfUnity p (σ • (x : Lˣ))).mpr (by
    rw [← smul_pow', (mem_rootsOfUnity p (x : Lˣ)).mp x.2, smul_one])⟩
  one_smul x := Subtype.ext (one_smul _ (x : Lˣ))
  mul_smul a b x := Subtype.ext (mul_smul a b (x : Lˣ))
  smul_mul a x y := Subtype.ext (smul_mul' a (x : Lˣ) (y : Lˣ))
  smul_one a := Subtype.ext (smul_one a)

@[simp]
lemma coe_smul_rootsOfUnity (p : ℕ) (σ : L ≃ₐ[K] L) (x : rootsOfUnity p L) :
    ((σ • x : rootsOfUnity p L) : Lˣ) = σ • (x : Lˣ) := rfl

end RootsOfUnity

section Reps

variable {K L : Type u} [Field K] [Field L] [Algebra K L]

/-- The `ℤ`-linear representation structure on the additive group underlying a multiplicative
`G`-module, transported along `Additive`. -/
noncomputable instance instDistribMulActionAdditiveOfMul {G A : Type*} [Monoid G] [CommGroup A]
    [MulDistribMulAction G A] : DistribMulAction G (Additive A) where
  smul g x := Additive.ofMul (g • Additive.toMul x)
  one_smul x := congrArg Additive.ofMul (one_smul G (Additive.toMul x))
  mul_smul g h x := congrArg Additive.ofMul (mul_smul g h (Additive.toMul x))
  smul_zero g := congrArg Additive.ofMul (smul_one g)
  smul_add g x y := congrArg Additive.ofMul (smul_mul' g (Additive.toMul x) (Additive.toMul y))

/-- **The Kummer coefficient module `μ_p(L)`**, as a `CoeffInt`-linear representation of
`Gal(L/K)`. -/
noncomputable def muRep (p : ℕ) (K L : Type u) [Field K] [Field L] [Algebra K L] :
    Rep CoeffInt (L ≃ₐ[K] L) :=
  Rep.ofDistribMulAction CoeffInt (L ≃ₐ[K] L) (Additive (rootsOfUnity p L))

/-- **The units `Lˣ`**, as a `CoeffInt`-linear representation of `Gal(L/K)`. -/
noncomputable def unitsRep (K L : Type u) [Field K] [Field L] [Algebra K L] :
    Rep CoeffInt (L ≃ₐ[K] L) :=
  Rep.ofDistribMulAction CoeffInt (L ≃ₐ[K] L) (Additive Lˣ)

/-- **The Kummer inclusion** `μ_p(L) ↪ Lˣ` as a morphism of `CoeffInt`-linear
`Gal(L/K)`-representations.  Its induced map in second cohomology is injective onto the `p`-torsion
of the relative Brauer group `H²(Gal(L/K), Lˣ) ≅ Br(L/K)`; see the module docstring and
`NK.HassePrinciple.kummerInjective`. -/
noncomputable def kummerIncl (p : ℕ) (K L : Type u) [Field K] [Field L] [Algebra K L] :
    muRep p K L ⟶ unitsRep K L :=
  Rep.ofHom
    { toFun := fun x => Additive.ofMul ((Additive.toMul x : rootsOfUnity p L) : Lˣ)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => Additive.toMul.injective rfl
      isIntertwining' := fun _ => by
        ext x
        rfl }

/-- **The Kummer map** on second cohomology: the map induced by the inclusion `μ_p(L) ↪ Lˣ`,
`H²(Gal(L/K), μ_p(L)) → H²(Gal(L/K), Lˣ) = Br(L/K)`. -/
noncomputable def kummerMap (p : ℕ) (K L : Type u) [Field K] [Field L] [Algebra K L] :
    groupCohomology (muRep p K L) 2 ⟶ groupCohomology (unitsRep K L) 2 :=
  groupCohomology.map (MonoidHom.id (L ≃ₐ[K] L)) (kummerIncl p K L) 2

end Reps

end NK.HassePrinciple
