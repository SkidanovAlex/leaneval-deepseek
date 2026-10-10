import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.LeadArch2.gammaHom_H1pi_eq_eCoh_or_neg
import Submission.Work.SSGRoute.exists_e_zero_natural
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Degree zero of the `E0b` bridge on invariants, up to a global sign

`Work.SSGRoute.eZeroToInv G A : (unitRep G ⟶ A) ≃+ ↥A.ρ.invariants` evaluates a morphism at `1`,
and `groupCohomology.H0Iso A : H⁰(G, A) ≅ ↥A.ρ.invariants` is Mathlib's degree-zero identification.
Both `eZeroToInv` and `eCoh 0 G A` are additive isomorphisms with `Ext⁰_G(ℤ, A)`, so the composite

`f ↦ eCoh 0 G A ((H0Iso A).inv (eZeroToInv G A f))`

is an automorphism of the abelian group `(unitRep G ⟶ A)` which is *natural in the coefficient*.
Evaluated on the identity of `unitRep G` it is `±𝟙`
(`Work.SSGRoute.LeadArch2.eCoh_zero_unitRep_inv_one_eq_mk0_or_neg`), and naturality transports that
to every coefficient module. Hence the class of `f` is `mk₀ f` or `-mk₀ f`.

The sign itself is fixed by the `Classical.choose`s implicit in `eCoh` and `H0Iso`; only the
disjunction is provable, and that is all the consumers need (the uses are at `p = 2`, where a sign
is irrelevant, or up to a global sign fixed once and for all).
-/

open CategoryTheory CategoryTheory.Limits SSGRoute.PTExt

attribute [local instance 10000] Rep.hV1 Rep.hV2

attribute [-instance] ULift.module

namespace Work.SSGRoute.ArchDictionary

/-! ## Naturality of the two degree-zero identifications -/

/-- `(H0Iso A).toLinearEquiv` is inverse to `(H0Iso A).inv`. -/
lemma H0Iso_inv_natural_aux {G : Type} [Group G] (A : Rep.{0} Coeff G)
    (x : ↥A.ρ.invariants) :
    (groupCohomology.H0Iso A).toLinearEquiv ((groupCohomology.H0Iso A).inv x) = x := by
  rw [Iso.toLinearEquiv_apply]
  exact Iso.inv_hom_id_apply (groupCohomology.H0Iso A) x

/-- Naturality of `H0Iso` in the coefficient module, in the `inv` direction. -/
lemma H0Iso_inv_natural {G : Type} [Group G] {A B : Rep.{0} Coeff G} (φ : A ⟶ B)
    (x : ↥A.ρ.invariants) :
    (groupCohomology.map (MonoidHom.id G) φ 0).hom ((groupCohomology.H0Iso A).inv x)
      = (groupCohomology.H0Iso B).inv ((Rep.invariantsFunctor Coeff G).map φ x) := by
  have h := Work.SSGRoute.H0_map_H0Iso G A B φ ((groupCohomology.H0Iso A).inv x)
  rw [H0Iso_inv_natural_aux A x] at h
  refine (groupCohomology.H0Iso B).toLinearEquiv.injective ?_
  rw [h, H0Iso_inv_natural_aux B ((Rep.invariantsFunctor Coeff G).map φ x)]

/-- Coefficient naturality of the `E0b` bridge in degree `0`: post-composition with `mk₀ φ` of the
class of an element of `H⁰(G, A)` is the class of its image in `H⁰(G, B)`. -/
lemma eCoh_zero_coeff_natural {G : Type} [Group G] {A B : Rep.{0} Coeff G} (φ : A ⟶ B)
    (y : groupCohomology A 0) :
    eCoh 0 G B ((groupCohomology.map (MonoidHom.id G) φ 0).hom y)
      = (eCoh 0 G A y).comp (Abelian.Ext.mk₀ φ) (add_zero 0) := by
  rw [Work.SSGRoute.eCoh_map 0 G G (MonoidHom.id G) A B φ y]
  exact Work.SSGRoute.E7cOmega.extHMap_id_apply_aux φ (eCoh 0 G A y)

/-- Naturality of the composite `f ↦ eCoh 0 G A ((H0Iso A).inv (eZeroToInv G A f))` in the
coefficient module. -/
lemma eCoh_H0Iso_inv_eZeroToInv_natural {G : Type} [Group G] {A B : Rep.{0} Coeff G}
    (φ : A ⟶ B) (f : SSGRoute.PTExt.unitRep G ⟶ A) :
    eCoh 0 G B ((groupCohomology.H0Iso B).inv (Work.SSGRoute.eZeroToInv G B (f ≫ φ)))
      = (eCoh 0 G A ((groupCohomology.H0Iso A).inv (Work.SSGRoute.eZeroToInv G A f))).comp
          (Abelian.Ext.mk₀ φ) (add_zero 0) := by
  rw [Work.SSGRoute.eZeroToInv_naturality, ← H0Iso_inv_natural φ (Work.SSGRoute.eZeroToInv G A f)]
  exact eCoh_zero_coeff_natural φ _

/-! ## The target -/

theorem eCohZeroInvSign {G : Type} [Group G]
    (A : Rep.{0} SSGRoute.PTExt.Coeff G) (f : SSGRoute.PTExt.unitRep G ⟶ A) :
    SSGRoute.PTExt.eCoh 0 G A
        ((groupCohomology.H0Iso A).inv (Work.SSGRoute.eZeroToInv G A f))
        = Abelian.Ext.mk₀ f ∨
      SSGRoute.PTExt.eCoh 0 G A
        ((groupCohomology.H0Iso A).inv (Work.SSGRoute.eZeroToInv G A f))
        = -Abelian.Ext.mk₀ f := by
  -- Naturality at the source coefficient `unitRep G`, applied to the identity of `unitRep G`.
  have h := eCoh_H0Iso_inv_eZeroToInv_natural (G := G) (A := SSGRoute.PTExt.unitRep G) (B := A)
      f (𝟙 (SSGRoute.PTExt.unitRep G))
  rw [Category.id_comp] at h
  -- The class of the identity of `unitRep G` is the canonical generator of `H⁰(G, Coeff)`.
  have hx : (groupCohomology.H0Iso (SSGRoute.PTExt.unitRep G)).inv
        (Work.SSGRoute.eZeroToInv G (SSGRoute.PTExt.unitRep G) (𝟙 (SSGRoute.PTExt.unitRep G)))
      = (groupCohomology.H0IsoOfIsTrivial (SSGRoute.PTExt.unitRep G)).inv (1 : Coeff) := by
    rw [show Work.SSGRoute.eZeroToInv G (SSGRoute.PTExt.unitRep G) (𝟙 (SSGRoute.PTExt.unitRep G))
        = ⟨(1 : Coeff), by rw [Representation.mem_invariants]; intro g; rfl⟩ from Subtype.ext rfl]
    exact (groupCohomology.H0IsoOfIsTrivial_inv_apply
      (A := SSGRoute.PTExt.unitRep G) (x := (1 : Coeff))).symm
  -- Degree-zero computation at the trivial coefficient: the value is `mk₀ 𝟙` or its negative.
  have hbase := Work.SSGRoute.LeadArch2.eCoh_zero_unitRep_inv_one_eq_mk0_or_neg G
  rw [← hx] at hbase
  rcases hbase with hb | hb
  · left
    rw [h, hb, Abelian.Ext.mk₀_id_comp]
  · right
    rw [h, hb, Abelian.Ext.neg_comp, Abelian.Ext.mk₀_id_comp]

end Work.SSGRoute.ArchDictionary
