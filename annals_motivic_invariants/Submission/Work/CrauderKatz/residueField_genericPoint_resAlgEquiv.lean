import Mathlib
import Submission.Work.CrauderKatz.Defs
import Submission.Work.CrauderKatz.residueField_genericPoint_eq_functionField
import Submission.Work.Motivic.resEquiv_of_morphism

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CrauderKatz

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

/-- **`residueFieldEquivSelf` inverts the residue map.**  The canonical identification
`IsLocalRing.ResidueField K ≅ K` of the residue field of a field with the field itself sends the
residue of `x` back to `x`; equivalently `residueFieldEquivSelf K` is a section of the (surjective)
residue map `K → IsLocalRing.ResidueField K`. -/
lemma residueFieldEquivSelf_residue (K : Type) [Field K] (x : K) :
    residueFieldEquivSelf K (IsLocalRing.residue K x) = x := by
  change (IsLocalRing.ResidueField.lift (RingHom.id K)) (IsLocalRing.residue K x) = x
  rw [← RingHom.comp_apply, IsLocalRing.ResidueField.lift_comp_residue]
  rfl

/-- **(F1), step 1, `𝕜`-linearly: the residue field of the generic point of an immersed integral
subscheme is its function field, compatibly with the structure maps.**  For an immersion `i : D ⟶ X` of
integral `𝕜`-schemes (i.e. over `Spec 𝕜`), the residue field of `i (genericPoint D)`, with its
`𝕜`-algebra structure, is `κ(D)` with the structure map `Work.CrauderKatz.functionFieldResMap`:

`Work.LLink.ResAlgEquiv 𝕜 (i (genericPoint D)) κ(D) (functionFieldResMap 𝕜 D)`.

This is the `𝕜`-linear refinement of `Work.CrauderKatz.residueField_genericPoint_eq_functionField` (which
only gives a bare ring isomorphism, not its compatibility with the structure maps), and it is the form
in which the (F1) presentation field `resY`/`resX` of `Work.CrauderKatz.CrauderKatzLink` is stated: take
`D` to be the `ℙ¹`-bundle over `C`, or over `C' = Jac²C`, inside the link's threefold `P` resp. `Q`.  The
companion `𝕜`-linear cylinder computation is
`Work.CrauderKatz.cylinderField_resAlgEquiv_prod`, and the two together give the (F1) fields
(`Work.CrauderKatz.resAlgEquiv_cylinderField_of_model`).

Suggested route: the natural equivalence is `i.residueFieldMap (genericPoint D)` followed by
`residueFieldEquivSelf (functionField D)`; the required compatibility with the structure maps reduces to
`i.residueFieldMap η ∘ resMap 𝕜 X (i η) = resMap 𝕜 D η`, which is the naturality of `resMap` for the
morphism `i` over `Spec 𝕜` (`[i.IsOver (Spec 𝕜)]`, cf. `Submission/Work/Motivic/resEquiv_of_morphism`),
plus the fact that `residueFieldEquivSelf` inverts the residue map. -/
theorem residueField_genericPoint_resAlgEquiv {𝕜 : Type} [Field 𝕜]
    {D X : AlgebraicGeometry.Scheme.{0}} [IrreducibleSpace D] [IrreducibleSpace X]
    [AlgebraicGeometry.IsIntegral D] [AlgebraicGeometry.IsIntegral X]
    [D.Over (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))]
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))] (i : D ⟶ X)
    [AlgebraicGeometry.IsImmersion i]
    [i.IsOver (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))] :
    Work.LLink.ResAlgEquiv 𝕜 (i (genericPoint D))
      (AlgebraicGeometry.Scheme.functionField D : Type)
      (Work.CrauderKatz.functionFieldResMap 𝕜 D) := by
  -- An immersion is a preimmersion, hence induces *surjective* maps on stalks, so the residue-field
  -- map `κ(i η_D) → κ(η_D)` is a surjective (hence bijective) map between fields; composing it with
  -- `residueFieldEquivSelf κ(D)` presents `κ(i η_D)` as `κ(D)`.
  have hsurj : Function.Surjective (i.residueFieldMap (genericPoint D)).hom := by
    intro y
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
    obtain ⟨b, hb⟩ := AlgebraicGeometry.Scheme.Hom.stalkMap_surjective i (genericPoint D) a
    exact ⟨IsLocalRing.residue _ b, by
      change IsLocalRing.ResidueField.map
          (AlgebraicGeometry.Scheme.Hom.stalkMap i (genericPoint D)).hom
          (IsLocalRing.residue _ b) = IsLocalRing.residue _ a
      rw [IsLocalRing.ResidueField.map_residue, hb]⟩
  -- The presentation `κ(i η_D) → κ(η_D) → κ(D)` as a single ring homomorphism, of which we take
  -- the underlying bijective map to build the `RingEquiv`.
  let F : X.residueField (i (genericPoint D)) →+* (D.functionField : Type) :=
    (residueFieldEquivSelf (D.functionField : Type)).toRingHom.comp
      (i.residueFieldMap (genericPoint D)).hom
  have hFbij : Function.Bijective F := by
    refine ⟨RingHom.injective F, ?_⟩
    intro y
    obtain ⟨a, ha⟩ := hsurj ((residueFieldEquivSelf (D.functionField : Type)).symm y)
    exact ⟨a, by
      show (residueFieldEquivSelf (D.functionField : Type))
          ((i.residueFieldMap (genericPoint D)) a) = y
      rw [ha, RingEquiv.apply_symm_apply]⟩
  refine ⟨RingEquiv.ofBijective F hFbij, ?_⟩
  change F.comp (resMap 𝕜 X (i (genericPoint D))) = functionFieldResMap 𝕜 D
  -- * Naturality of `resMap` for the morphism `i` over `Spec 𝕜` *
  -- (`i.residueFieldMap η ∘ resMap 𝕜 X (i η) = resMap 𝕜 D η`).
  have key1 : (i.residueFieldMap (genericPoint D)).hom.comp (resMap 𝕜 X (i (genericPoint D)))
      = resMap 𝕜 D (genericPoint D) :=
    Work.Motivic.resMap_naturality i (CategoryTheory.comp_over i (Spec (.of 𝕜))) (genericPoint D)
  -- * `resMap 𝕜 D η` is `residueFieldEquivSelf`-inverted by the germ map `𝕜 → κ(D)` *:
  -- `resMap 𝕜 D η = residue η ∘ functionFieldResMap 𝕜 D`.
  have key2 : resMap 𝕜 D (genericPoint D)
      = (D.residue (genericPoint D)).hom.comp (functionFieldResMap 𝕜 D) := rfl
  -- * `residueFieldEquivSelf` inverts the residue map `D.functionField → κ(η_D)` *.
  have key3 : (residueFieldEquivSelf (D.functionField : Type)).toRingHom.comp
      (D.residue (genericPoint D)).hom = RingHom.id (D.functionField : Type) := by
    ext x
    show residueFieldEquivSelf (D.functionField : Type) ((D.residue (genericPoint D)).hom x) = x
    rw [show (D.residue (genericPoint D)).hom x
        = IsLocalRing.residue (D.functionField : Type) x from rfl]
    exact residueFieldEquivSelf_residue _ x
  calc F.comp (resMap 𝕜 X (i (genericPoint D)))
      = ((residueFieldEquivSelf (D.functionField : Type)).toRingHom.comp
            (i.residueFieldMap (genericPoint D)).hom).comp
          (resMap 𝕜 X (i (genericPoint D))) := rfl
    _ = (residueFieldEquivSelf (D.functionField : Type)).toRingHom.comp
          ((i.residueFieldMap (genericPoint D)).hom.comp (resMap 𝕜 X (i (genericPoint D)))) :=
          RingHom.comp_assoc _ _ _
    _ = (residueFieldEquivSelf (D.functionField : Type)).toRingHom.comp
          (resMap 𝕜 D (genericPoint D)) := by rw [key1]
    _ = (residueFieldEquivSelf (D.functionField : Type)).toRingHom.comp
          ((D.residue (genericPoint D)).hom.comp (functionFieldResMap 𝕜 D)) := by rw [key2]
    _ = ((residueFieldEquivSelf (D.functionField : Type)).toRingHom.comp
            (D.residue (genericPoint D)).hom).comp (functionFieldResMap 𝕜 D) :=
          (RingHom.comp_assoc _ _ _).symm
    _ = (RingHom.id (D.functionField : Type)).comp (functionFieldResMap 𝕜 D) := by rw [key3]
    _ = functionFieldResMap 𝕜 D := RingHom.id_comp _

end Work.CrauderKatz
