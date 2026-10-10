import Mathlib
import Submission.Work.CY3.Projective

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CY3

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

/-! ## Auxiliary results

Everything below the main theorem is an auxiliary result of the sanity check that
`Work.CY3.IsP1Fibration` is non-vacuous:

* the residue field of a field is the field itself (`Spec 𝕜` is a one-point scheme whose residue
  field is `𝕜`), so that both the fibre computation and `Proj`-functoriality simplify;
* the irrelevant ideal is preserved by a surjective graded ring homomorphism, which is the side
  condition required by `Proj.map`;
* `Proj` is functorial in an isomorphism of the standard graded polynomial ring;
* the fibre of a morphism at a point whose residue-field morphism is an isomorphism is the source.
-/

namespace IsP1FibAux

/-- For a field `k` and a prime ideal `p` of it, the structure map `k ⟶ κ(p)` to the residue
field of `p` is bijective: every prime ideal of a field is `⊥`, and the `k`-algebra equivalence
`Ideal.algEquivResidueFieldOfField p : k ≃ₐ[k] p.ResidueField` has `algebraMap k p.ResidueField`
as its underlying map. -/
lemma bijective_algebraMap_residueField_of_field {k : Type} [Field k] (p : Ideal k)
    [p.IsPrime] : Function.Bijective (algebraMap k p.ResidueField) :=
  (Ideal.algEquivResidueFieldOfField p).bijective

/-- For a field `𝕜`, the canonical morphism `Spec κ(y) ⟶ Spec 𝕜` at the (unique) point `y` of
`Spec 𝕜` is an isomorphism: `Spec 𝕜` is a one-point scheme whose residue field is `𝕜`.  Indeed,
`Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField` writes `fromSpecResidueField y` as
`Spec` of the field map `𝕜 ⟶ y.asIdeal.ResidueField` (composed with the inverse of the residue
field isomorphism `κ(y) ≅ y.asIdeal.ResidueField`), and that field map is bijective. -/
lemma isIso_fromSpecResidueField_spec_field (𝕜 : Type) [Field 𝕜]
    (y : AlgebraicGeometry.Spec (CommRingCat.of 𝕜)) :
    IsIso ((AlgebraicGeometry.Spec (CommRingCat.of 𝕜)).fromSpecResidueField y) := by
  haveI hp : y.asIdeal.IsPrime := y.isPrime
  rw [← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField (CommRingCat.of 𝕜) y]
  haveI : IsIso (Spec.map (CommRingCat.ofHom (algebraMap 𝕜 y.asIdeal.ResidueField))) := by
    rw [isIso_SpecMap_iff]
    exact bijective_algebraMap_residueField_of_field y.asIdeal
  infer_instance

/-- For a field `𝕜` and a point `y` of `Spec 𝕜`, the residue field `κ(y)` is isomorphic to `𝕜`:
`Spec.residueFieldIso` identifies `κ(y)` with `y.asIdeal.ResidueField` and
`Ideal.algEquivResidueFieldOfField` identifies the latter with `𝕜`. -/
lemma nonempty_ringEquiv_residueField_spec_field (𝕜 : Type) [Field 𝕜]
    (y : AlgebraicGeometry.Spec (CommRingCat.of 𝕜)) :
    Nonempty (𝕜 ≃+* (AlgebraicGeometry.Spec (CommRingCat.of 𝕜)).residueField y) := by
  refine ⟨?_⟩
  haveI : y.asIdeal.IsPrime := y.isPrime
  exact (Ideal.algEquivResidueFieldOfField y.asIdeal).toRingEquiv.trans
    (AlgebraicGeometry.Scheme.Spec.residueFieldIso (CommRingCat.of 𝕜) y).symm.commRingCatIsoToRingEquiv

/-- **The irrelevant ideal is preserved by a surjective graded ring homomorphism.**  If
`φ : 𝒜 →+*ᵍ ℬ` is surjective, then every element of the irrelevant ideal `ℬ₊` of `ℬ` is the image
of an element of `𝒜₊`: for `b = φ a ∈ ℬ₊` (say `b ∈ ℬ i`, `i > 0`) subtract the degree-zero part
of `a` from `a`; the degree-zero parts match because `φ` commutes with `GradedRing.proj`
(`GradedRingHom.map_directSumDecompose`).

This is the hypothesis `ℬ₊ ≤ 𝒜₊.map φ` required by `Proj.map`. -/
lemma irrelevant_le_map_of_surjective {A B : Type*} [CommRing A] [CommRing B]
    {σ : Type*} [SetLike σ A] [AddSubgroupClass σ A]
    {τ : Type*} [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
    (φ : 𝒜 →+*ᵍ ℬ) (hφ : Function.Surjective φ) :
    HomogeneousIdeal.irrelevant ℬ ≤ HomogeneousIdeal.map φ (HomogeneousIdeal.irrelevant 𝒜) := by
  rw [HomogeneousIdeal.irrelevant_le]
  intro i hi b hb
  obtain ⟨a, rfl⟩ := hφ b
  have hproj : GradedRing.proj 𝒜 0 (GradedRing.proj 𝒜 0 a) = GradedRing.proj 𝒜 0 a := by
    rw [GradedRing.proj_apply, GradedRing.proj_apply]
    exact DirectSum.decompose_of_mem_same 𝒜 (SetLike.coe_mem (DirectSum.decompose 𝒜 a 0))
  have hmem : a - GradedRing.proj 𝒜 0 a ∈ (HomogeneousIdeal.irrelevant 𝒜) := by
    rw [HomogeneousIdeal.mem_irrelevant_iff, map_sub, hproj, sub_self]
  have h1 : φ (GradedRing.proj 𝒜 0 a) = GradedRing.proj ℬ 0 (φ a) := by
    rw [GradedRing.proj_apply, GradedRing.proj_apply]
    exact GradedRingHom.map_directSumDecompose 𝒜 ℬ φ (x := a) (i := 0)
  have h2 : GradedRing.proj ℬ 0 (φ a) = 0 := by
    rw [← HomogeneousIdeal.mem_irrelevant_iff]
    exact HomogeneousIdeal.mem_irrelevant_of_mem ℬ hi hb
  have h3 : φ (a - GradedRing.proj 𝒜 0 a) = φ a := by
    rw [map_sub, h1, h2, sub_zero]
  have hmap : φ (a - GradedRing.proj 𝒜 0 a) ∈
      Ideal.map φ (HomogeneousIdeal.irrelevant 𝒜).toIdeal :=
    Ideal.mem_map_of_mem φ hmem
  rw [h3, ← HomogeneousIdeal.toIdeal_map] at hmap
  exact hmap

/-- The graded ring homomorphism `𝕜[X₀,…,Xₙ] → 𝕜'[X₀,…,Xₙ]` induced by a ring homomorphism
`e : 𝕜 →+* 𝕜'` (coefficients only): `MvPolynomial.map e`, which is graded by
`MvPolynomial.IsHomogeneous.map`. -/
def gradedHomMap {𝕜 𝕜' : Type} [CommSemiring 𝕜] [CommSemiring 𝕜']
    (e : 𝕜 →+* 𝕜') (σ : Type) :
    (MvPolynomial.homogeneousSubmodule σ 𝕜) →+*ᵍ (MvPolynomial.homogeneousSubmodule σ 𝕜') :=
  { toRingHom := MvPolynomial.map e
    map_mem := fun {i x} hx => by
      rw [MvPolynomial.mem_homogeneousSubmodule] at hx ⊢
      exact hx.map e }

/-- **`ℙⁿ` is functorial in an isomorphism of coefficient fields**: for a ring isomorphism
`e : 𝕜 ≃+* 𝕜'` the projective spaces `ℙⁿ_𝕜` and `ℙⁿ_𝕜'` are isomorphic.  The isomorphism is
`Proj.map` of the graded isomorphism `gradedHomMap e` and its inverse is `Proj.map` of
`gradedHomMap e.symm`; the two composites are the identity by `Proj.map_comp` and `Proj.map_id`,
and the required side condition `ℬ₊ ≤ 𝒜₊.map φ` holds by
`IsP1FibAux.irrelevant_le_map_of_surjective`. -/
theorem projectiveSpace_iso_of_ringEquiv (𝕜 𝕜' : Type) [Field 𝕜] [Field 𝕜'] (n : ℕ)
    (e : 𝕜 ≃+* 𝕜') :
    Nonempty (Work.CY3.ProjectiveSpace 𝕜 n ≅ Work.CY3.ProjectiveSpace 𝕜' n) := by
  change Nonempty (AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin (n+1)) 𝕜) ≅
    AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin (n+1)) 𝕜'))
  let φ : MvPolynomial.homogeneousSubmodule (Fin (n+1)) 𝕜 →+*ᵍ
      MvPolynomial.homogeneousSubmodule (Fin (n+1)) 𝕜' := gradedHomMap (e : 𝕜 →+* 𝕜') _
  let ψ : MvPolynomial.homogeneousSubmodule (Fin (n+1)) 𝕜' →+*ᵍ
      MvPolynomial.homogeneousSubmodule (Fin (n+1)) 𝕜 := gradedHomMap (e.symm : 𝕜' →+* 𝕜) _
  have hφ : Function.Surjective φ := by
    intro y
    refine ⟨MvPolynomial.map (e.symm : 𝕜' →+* 𝕜) y, ?_⟩
    show MvPolynomial.map (e : 𝕜 →+* 𝕜') (MvPolynomial.map (e.symm : 𝕜' →+* 𝕜) y) = y
    rw [MvPolynomial.map_map, RingEquiv.comp_symm, MvPolynomial.map_id]
  have hψ : Function.Surjective ψ := by
    intro y
    refine ⟨MvPolynomial.map (e : 𝕜 →+* 𝕜') y, ?_⟩
    show MvPolynomial.map (e.symm : 𝕜' →+* 𝕜) (MvPolynomial.map (e : 𝕜 →+* 𝕜') y) = y
    rw [MvPolynomial.map_map, RingEquiv.symm_comp, MvPolynomial.map_id]
  have hfφ : HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin (n+1)) 𝕜') ≤
      HomogeneousIdeal.map φ
        (HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin (n+1)) 𝕜)) :=
    irrelevant_le_map_of_surjective φ hφ
  have hfψ : HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin (n+1)) 𝕜) ≤
      HomogeneousIdeal.map ψ
        (HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin (n+1)) 𝕜')) :=
    irrelevant_le_map_of_surjective ψ hψ
  have hcomp1 : ψ.comp φ =
      GradedRingHom.id (MvPolynomial.homogeneousSubmodule (Fin (n+1)) 𝕜) := by
    refine GradedRingHom.ext fun x => ?_
    show MvPolynomial.map (e.symm : 𝕜' →+* 𝕜) (MvPolynomial.map (e : 𝕜 →+* 𝕜') x) = x
    rw [MvPolynomial.map_map, RingEquiv.symm_comp, MvPolynomial.map_id]
  have hcomp2 : φ.comp ψ =
      GradedRingHom.id (MvPolynomial.homogeneousSubmodule (Fin (n+1)) 𝕜') := by
    refine GradedRingHom.ext fun x => ?_
    show MvPolynomial.map (e : 𝕜 →+* 𝕜') (MvPolynomial.map (e.symm : 𝕜' →+* 𝕜) x) = x
    rw [MvPolynomial.map_map, RingEquiv.comp_symm, MvPolynomial.map_id]
  refine ⟨{ hom := AlgebraicGeometry.Proj.map ψ hfψ
            inv := AlgebraicGeometry.Proj.map φ hfφ
            hom_inv_id := ?_
            inv_hom_id := ?_ }⟩
  · rw [← AlgebraicGeometry.Proj.map_comp]
    convert AlgebraicGeometry.Proj.map_id using 2 <;> simp [hcomp1]
  · rw [← AlgebraicGeometry.Proj.map_comp]
    convert AlgebraicGeometry.Proj.map_id using 2 <;> simp [hcomp2]

end IsP1FibAux

/-- **The fibre at a point whose residue-field morphism is an isomorphism is the source.**  If
`Y.fromSpecResidueField y` is an isomorphism then the scheme-theoretic fibre `f.fiber y` of
`f : X ⟶ Y` at `y` is `X`: the fibre is the pullback `pullback f (Y.fromSpecResidueField y)` and
the first projection of a pullback along an isomorphism is an isomorphism. -/
lemma nonempty_fiber_iso_of_isIso_fromSpecResidueField {X Y : Scheme.{0}} (f : X ⟶ Y) (y : Y)
    (h : IsIso (Y.fromSpecResidueField y)) : Nonempty (f.fiber y ≅ X) :=
  ⟨@asIso _ _ (pullback f (Y.fromSpecResidueField y)) X (pullback.fst f (Y.fromSpecResidueField y))
    ((IsPullback.of_hasPullback f (Y.fromSpecResidueField y)).isIso_fst_of_isIso)⟩

/-- **The notion of `ℙ¹`-fibration is inhabited.**  The structure morphism `ℙ¹_𝕜 ⟶ Spec 𝕜` is a
`ℙ¹`-fibration: `Spec 𝕜` has a single point `y`, whose residue field is `𝕜`, and the
scheme-theoretic fibre of `ℙ¹_𝕜 ⟶ Spec 𝕜` at `y` (`Scheme.Hom.fiber`, i.e. the pullback along
`(Spec 𝕜).fromSpecResidueField y`, an isomorphism for a field) is `ℙ¹_𝕜` itself, which is
`Proj κ(y)[X₀,X₁] = Work.CY3.ProjectiveSpace (↥((Spec 𝕜).residueField y)) 1`.  This is a sanity
check that `Work.CY3.IsP1Fibration` (the CY3 form of the paper's `ℙ¹`-fibrations
`G/B → G/P`, `G/B → G/P'`) is non-vacuous.  `Proj.map`/`map_id`/`map_comp`
(`Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor`) transport `Proj` along graded ring
isomorphisms and are the tool for the `ℙ¹_𝕜 ≅ ℙ¹_{κ(y)}` step. -/
theorem isP1Fibration_projectiveSpaceToSpec_one (𝕜 : Type) [Field 𝕜] :
    Work.CY3.IsP1Fibration (Work.CY3.projectiveSpaceToSpec 𝕜 1) := by
  intro y
  -- `𝕜` is a field, so `Spec 𝕜` is a one-point scheme with residue field `𝕜`: the canonical map
  -- `Spec κ(y) ⟶ Spec 𝕜` is an isomorphism, hence the fibre of `ℙ¹_𝕜 ⟶ Spec 𝕜` at `y` is `ℙ¹_𝕜`.
  haveI hg : IsIso ((AlgebraicGeometry.Spec (CommRingCat.of 𝕜)).fromSpecResidueField y) :=
    IsP1FibAux.isIso_fromSpecResidueField_spec_field 𝕜 y
  obtain ⟨iso1⟩ :=
    nonempty_fiber_iso_of_isIso_fromSpecResidueField (Work.CY3.projectiveSpaceToSpec 𝕜 1) y hg
  -- `κ(y) ≅ 𝕜`, so `ℙ¹_𝕜 ≅ ℙ¹_{κ(y)}` by functoriality of `Proj`.
  obtain ⟨e⟩ := IsP1FibAux.nonempty_ringEquiv_residueField_spec_field 𝕜 y
  obtain ⟨iso2⟩ :=
    IsP1FibAux.projectiveSpace_iso_of_ringEquiv 𝕜
      ((AlgebraicGeometry.Spec (CommRingCat.of 𝕜)).residueField y) 1 e
  exact ⟨iso1 ≪≫ iso2⟩

end

end Work.CY3
