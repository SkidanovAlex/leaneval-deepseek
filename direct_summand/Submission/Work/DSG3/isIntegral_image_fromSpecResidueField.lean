import Mathlib
import Submission.Work.DSG3.Basic

/-!
# `IsIntegral` of the scheme-theoretic image of `Spec κ(x) ⟶ X`

For a scheme `X` and a point `x : X`, the scheme-theoretic image of the canonical
morphism `Spec κ(x) ⟶ X` is integral.

* It is reduced: the image is covered by the affine charts `Spec (Γ(X,U) ⧸ f.ker.ideal U)`
  for affine opens `U ⊆ X` (`IdealSheafData.subschemeCover`), and each of these rings is a
  quotient by the kernel of the ring map `Γ(X,U) ⟶ Γ(Spec κ(x), f ⁻¹ᵁ U)`, whose target is
  reduced; a kernel of a map into a reduced ring is radical.
* It is irreducible: its underlying space is `closure {x}` (see
  `DSMap.range_imageι_fromSpecResidueField`), the closure of a point.

## Main results

* `Work.DSG3.isReduced_image_fromSpecResidueField`
* `Work.DSG3.irreducibleSpace_image_fromSpecResidueField`
* `Work.DSG3.isIntegral_image_fromSpecResidueField`
-/

open CategoryTheory AlgebraicGeometry

universe u

namespace Work.DSG3

/-- A ring homomorphism into a reduced ring has radical kernel. -/
lemma isRadical_ker_of_isReduced {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    [_root_.IsReduced S] : (RingHom.ker φ).IsRadical := by
  intro x hx
  rw [Ideal.mem_radical_iff] at hx
  obtain ⟨n, hn⟩ := hx
  rw [RingHom.mem_ker] at hn ⊢
  rw [map_pow] at hn
  exact _root_.IsReduced.eq_zero (φ x) ⟨n, hn⟩

/-- The scheme-theoretic image of `Spec κ(x) ⟶ X` is reduced. -/
lemma isReduced_image_fromSpecResidueField {X : Scheme.{u}} (x : X) :
    IsReduced (X.fromSpecResidueField x).image := by
  have h : ∀ U : X.affineOpens,
      _root_.IsReduced (Γ(X, ↑U) ⧸ (X.fromSpecResidueField x).ker.ideal U) := by
    intro U
    rw [Scheme.Hom.ker_apply]
    exact (Ideal.isRadical_iff_quotient_reduced _).mp (isRadical_ker_of_isReduced _)
  refine (IsReduced.iff_of_openCover _ (X.fromSpecResidueField x).ker.subschemeCover.openCover).mpr
    fun U ↦ ?_
  let V : X.affineOpens := U
  change IsReduced (Spec ↧(Γ(X, ↑V) ⧸ (X.fromSpecResidueField x).ker.ideal V))
  exact (affine_isReduced_iff _).mpr (h V)

/-- The scheme-theoretic image of `Spec κ(x) ⟶ X` is irreducible: its underlying space is
the closure of the point `x`. -/
lemma irreducibleSpace_image_fromSpecResidueField {X : Scheme.{u}} (x : X) :
    IrreducibleSpace (X.fromSpecResidueField x).image := by
  have hι : Topology.IsEmbedding (X.fromSpecResidueField x).imageι :=
    (IsClosedImmersion.isClosedEmbedding _).isEmbedding
  rw [(hι.toHomeomorph).irreducibleSpace_iff, DSMap.range_imageι_fromSpecResidueField x]
  exact isIrreducible_iff_irreducibleSpace.mp isIrreducible_singleton.closure

open CategoryTheory AlgebraicGeometry in
lemma isIntegral_image_fromSpecResidueField {X : AlgebraicGeometry.Scheme} (x : X) :
    AlgebraicGeometry.IsIntegral (X.fromSpecResidueField x).image :=
  (isIntegral_iff_irreducibleSpace_and_isReduced _).mpr
    ⟨irreducibleSpace_image_fromSpecResidueField x, isReduced_image_fromSpecResidueField x⟩

end Work.DSG3
