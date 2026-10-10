import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Rep.Iso
import Submission.Work.SSGRoute.ext2_iso_cohomology_defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Projectivity of the terms of `stdTensorComplex G R`

The `n`-th term of `stdTensorComplex G R` is `(barResolution Coeff G).complex.X n ⊗ R`, and
`(barResolution Coeff G).complex.X n = Rep.free Coeff G (Fin n → G)` is a free — hence projective —
`Coeff[G]`-module.  If the underlying abelian group of `R` is free over `ℤ`, then
`Rep.free Coeff G α ⊗ R` is projective as well: `Rep.free Coeff G α = Coeff[G]^{⊕α}` is a direct
sum of copies of `Coeff[G]`, and `Coeff[G] ⊗_ℤ R.V` is the induction of the `ℤ`-module `R.V` from
the trivial subgroup, i.e. a left adjoint of the exact forgetful functor `Rep Coeff G ⥤ Mod ℤ`,
hence it preserves projective objects.

The formalisation goes through the monoidal closed structure of `Rep Coeff G`:

* the internal hom `Rep.ihom R` is `Hom_Coeff(R.V, -)` (with the conjugation action), and it
  preserves epimorphisms as soon as `R.V` is projective over `Coeff` (`Module.projective_lifting_property`);
* for projective `P` one has `Hom(P ⊗ R, -) ≅ Hom(P, ihom R -)` (the symmetry of the closed
  monoidal structure moves the braiding), so `Hom(P ⊗ R, -)` preserves epimorphisms and `P ⊗ R` is
  projective.

The remaining bridge is that the hypothesis `Module.Free ℤ R.V` is about the *canonical* `ℤ`-module
structure of the additive group `R.V`, whereas the representation carries its own `Coeff`-module
structure.  These agree: for an additive commutative group every `Module (ULift ℤ) M` structure is
the canonical one, so all such structures on `M` are equal (`subsingleton_module_ulift_int`), and
`Module.Free`/`Module.Projective` transport between them.
-/

open CategoryTheory MonoidalCategory

namespace Work.SSGRoute

/-- For an additive commutative group `M`, the scalar multiplication of any `Module (ULift ℤ) M`
structure is the canonical `ℤ`-action (via `ULift.down`).  This is the key input for the fact that
all `Module (ULift ℤ) M` structures coincide. -/
lemma ulift_int_smul_eq_down {M : Type} [AddCommGroup M] (inst : Module (ULift ℤ) M)
    (u : ULift ℤ) (x : M) :
    @SMul.smul (ULift ℤ) M inst.toDistribMulAction.toSMul u x = u.down • x := by
  cases u with
  | up z =>
    have h1 : @SMul.smul (ULift ℤ) M inst.toDistribMulAction.toSMul ((z : ℤ) : ULift ℤ) x = z • x :=
      @Int.cast_smul_eq_zsmul (ULift ℤ) M _ _ inst z x
    exact h1

/-- All `Module (ULift ℤ) M` structures on an additive commutative group `M` are equal. -/
lemma subsingleton_module_ulift_int (M : Type) [AddCommGroup M] :
    Subsingleton (Module (ULift ℤ) M) where
  allEq P Q := Module.ext' P Q fun u x => by
    show @SMul.smul (ULift ℤ) M P.toDistribMulAction.toSMul u x =
      @SMul.smul (ULift ℤ) M Q.toDistribMulAction.toSMul u x
    rw [ulift_int_smul_eq_down P u x, ulift_int_smul_eq_down Q u x]

section General

variable {k : Type} [CommRing k] {G : Type} [Group G]

/-- The internal hom `Rep.ihom R = Hom_k(R.V, -)` preserves epimorphisms whenever `R.V` is a
projective `k`-module: postcomposition with a surjective linear map is surjective, by the lifting
property of projective modules. -/
lemma ihom_preservesEpimorphisms_of_projective (R : Rep.{0} k G) [Module.Projective k R.V] :
    (ihom R).PreservesEpimorphisms where
  preserves {X Y} f hf := by
    rw [Rep.epi_iff_surjective] at hf ⊢
    intro g
    obtain ⟨h, hh⟩ := Module.projective_lifting_property f.hom.toLinearMap g hf
    refine ⟨h, ?_⟩
    exact hh

/-- If `P` is projective and the internal hom `ihom R = Hom_k(R.V, -)` preserves epimorphisms, then
`P ⊗ R` is projective.  The proof curries a morphism `P ⊗ R ⟶ X` (after braiding) into a morphism
`P ⟶ ihom R X`, lifts it along `P ⟶ ihom R E` (which is an epimorphism because `ihom R` preserves
epimorphisms), and uncurries. -/
lemma projective_tensor_of_ihom (P R : Rep.{0} k G) [Projective P]
    (hR : (ihom R).PreservesEpimorphisms) :
    Projective (P ⊗ R) where
  factors {E X} f e he := by
    have he' : Epi ((ihom R).map e) := hR.preserves e
    let φ : P ⟶ (ihom R).obj X := (ihom.adjunction R).homEquiv P X ((β_ P R).inv ≫ f)
    obtain ⟨ψ, hψ⟩ := Projective.factors (P := P) φ ((ihom R).map e)
    refine ⟨(β_ P R).hom ≫ ((ihom.adjunction R).homEquiv P E).symm ψ, ?_⟩
    have hnat : ((ihom.adjunction R).homEquiv P E).symm ψ ≫ e
        = ((ihom.adjunction R).homEquiv P X).symm (ψ ≫ (ihom R).map e) :=
      (Adjunction.homEquiv_naturality_right_symm (ihom.adjunction R) ψ e).symm
    rw [Category.assoc, hnat, hψ]
    show (β_ P R).hom ≫ ((ihom.adjunction R).homEquiv P X).symm
      (((ihom.adjunction R).homEquiv P X) ((β_ P R).inv ≫ f)) = f
    rw [Equiv.symm_apply_apply]
    exact Iso.hom_inv_id_assoc _ _

end General

/-- `R.V` is a projective `Coeff`-module (for the module structure carried by the representation
`R`) as soon as its underlying abelian group is free over `ℤ`. -/
lemma moduleProjective_of_free_int (G : Type) [Group G] (R : Rep.{0} SSGRoute.PTExt.Coeff G)
    [Module.Free ℤ R.V] :
    @Module.Projective SSGRoute.PTExt.Coeff _ R.V _ R.hV2 := by
  have hfree : Module.Free SSGRoute.PTExt.Coeff R.V := by
    obtain ⟨⟨ι, b⟩⟩ := Module.Free.exists_basis (R := ℤ) (M := R.V)
    exact Module.Free.of_basis (b.mapCoeffs (ULift.ringEquiv.symm) (fun c x => rfl))
  have hp : Module.Projective SSGRoute.PTExt.Coeff R.V := Module.Projective.of_free
  have h : R.hV2 = (inferInstance : Module SSGRoute.PTExt.Coeff R.V) :=
    (subsingleton_module_ulift_int R.V).allEq _ _
  exact h.symm ▸ hp

theorem stdTensorComplex_projective (G : Type) [Group G] (R : Rep.{0} SSGRoute.PTExt.Coeff G)
    [Module.Free ℤ R.V] (n : ℕ) :
    CategoryTheory.Projective ((stdTensorComplex G R).X n) := by
  have hR : (ihom R).PreservesEpimorphisms :=
    @ihom_preservesEpimorphisms_of_projective SSGRoute.PTExt.Coeff _ G _ R
      (moduleProjective_of_free_int G R)
  change CategoryTheory.Projective (Rep.free SSGRoute.PTExt.Coeff G (Fin n → G) ⊗ R)
  exact projective_tensor_of_ihom _ R hR

end Work.SSGRoute
