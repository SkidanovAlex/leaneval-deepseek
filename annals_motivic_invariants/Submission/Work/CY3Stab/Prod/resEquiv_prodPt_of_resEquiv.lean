import Mathlib
import Submission.Work.CY3Stab.Defs
import Submission.Work.Motivic.resEquiv_of_morphism
import Submission.Work.CY3Stab.Prod.AlgMapResidue
import Submission.Work.CY3Stab.Prod.isIso_algMapResidue_id
import Submission.Work.CY3Stab.Prod.tensor_iso_tensorInl

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.CY3Stab.Prod.resEquiv_prodPt_of_resEquiv`

The residue-field comparison of the stabilisation step of Lin–Shinder's proof of
`thm:bir-generation` (c): if the base points `x : X`, `z : Z` have `𝕜`-isomorphic residue fields,
then so do the *cylinder points* of the stabilising cylinder `𝔸ᵏ × X` — the generic points of the
`Triplet` fibres of `WProd X k = 𝔸ᵏ ×_{Spec 𝕜} X`.

The mathematical content is that the residue field of the cylinder point over `x` is the fraction
field of the tensor product `κ(x) ⊗_𝕜 κ(𝔸ᵏ)`; the proof below establishes, for an arbitrary
`Triplet` (over an arbitrary base) with `IsDomain T.tensor`, that the residue field map at the
generic point `⊥` of `Spec T.tensor` composed with the projection of the pullback is an
*isomorphism*:
`κ(T.SpecTensorTo ⊥) ≅ κ(⊥) = Frac(T.tensor)`.

The route is the following chain of Mathlib facts.

* `Pullback.carrierEquiv` identifies the points of `X ×[S] Y` with pairs `(T, p)` where `T` is a
  `Triplet` and `p` a prime of `T.tensor`; applying its `right_inv` to `(T, ⊥)` shows that
  `SpecOfPoint (T.SpecTensorTo ⊥) = ⊥` (`specOfPoint_specTensorTo_bot`), i.e. the ring
  homomorphism `ofPointTensor` at that point is injective.
* `ofPointTensor_SpecTensorTo` writes `Spec.map (ofPointTensor t) ≫ (ofPoint t).SpecTensorTo` as the
  canonical map `fromSpecResidueField t`, which is a *preimmersion*; hence its residue field map at
  the generic point is bijective (`isIso_residueFieldMap_fromSpecResidueField`), and from the
  factorisation `residueFieldMap_comp` one deduces that both factors are isomorphisms.
* `tensorCongr_SpecTensorTo` transports this along the identification `ofPoint t = T`.

-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Work.CY3Stab.Prod

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

section GenericPoint

variable {X Y S : Scheme.{0}} {f : X ⟶ S} {g : Y ⟶ S}

/-- The generic point `⊥` of `Spec T.tensor` (for a domain `T.tensor`), as a point of the scheme. -/
noncomputable abbrev botPoint (T : Pullback.Triplet f g) [IsDomain T.tensor] : ↥(Spec T.tensor) :=
  (show ↥(Spec T.tensor) from (⊥ : PrimeSpectrum T.tensor))

/-- **The residue field map of `fromSpecResidueField` at the generic point is an isomorphism.**
`X.fromSpecResidueField x` is a preimmersion, hence surjective on stalks; a surjective ring
homomorphism of fields is bijective. -/
theorem isIso_residueFieldMap_fromSpecResidueField (P : Scheme.{0}) (x : P)
    (p : ↥(Spec (P.residueField x))) :
    IsIso ((P.fromSpecResidueField x).residueFieldMap p) := by
  have hsurj : Function.Surjective ((P.fromSpecResidueField x).residueFieldMap p).hom := by
    intro y
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
    obtain ⟨b, hb⟩ := Scheme.Hom.stalkMap_surjective (P.fromSpecResidueField x) p a
    exact ⟨IsLocalRing.residue _ b, by
      change IsLocalRing.ResidueField.map
        (Scheme.Hom.stalkMap (P.fromSpecResidueField x) p).hom (IsLocalRing.residue _ b) =
        IsLocalRing.residue _ a
      rw [IsLocalRing.ResidueField.map_residue, hb]⟩
  exact (RingEquiv.toCommRingCatIso (RingEquiv.ofBijective
    ((P.fromSpecResidueField x).residueFieldMap p).hom
    ⟨RingHom.injective _, hsurj⟩)).isIso_hom

/-- **A criterion for an isomorphism**: if `F ≫ G` is an isomorphism and both `F` and `G` are
injective, then `F` is an isomorphism (both are ring homomorphisms between fields in the
applications). -/
theorem isIso_left_of_comp_isIso {A B C : CommRingCat.{0}}
    (F : A ⟶ B) (G : B ⟶ C) (hF : Function.Injective F.hom)
    (hG : Function.Injective G.hom) (h : IsIso (F ≫ G)) : IsIso F := by
  have hbij : Function.Bijective (G.hom.comp F.hom) :=
    (asIso (F ≫ G)).commRingCatIsoToRingEquiv.bijective
  have hsurj : Function.Surjective F.hom := by
    intro y
    obtain ⟨x, hx⟩ := hbij.2 (G.hom y)
    exact ⟨x, hG (by simpa only [RingHom.comp_apply] using hx)⟩
  exact (RingEquiv.toCommRingCatIso
    (RingEquiv.ofBijective F.hom ⟨hF, hsurj⟩)).isIso_hom

/-- **Transport of `IsIso` of a residue field map along an equality of points.** -/
theorem isIso_residueFieldMap_congr {X Y : Scheme.{0}} (F : X ⟶ Y) {x₁ x₂ : X} (e : x₁ = x₂)
    (h : IsIso (F.residueFieldMap x₁)) : IsIso (F.residueFieldMap x₂) := by
  have hc := Scheme.Hom.residueFieldMap_congr' (f := F) (x₁ := x₁) (x₂ := x₂) e
  have hD : F.residueFieldMap x₂
      = (Scheme.residueFieldCongr (congrArg F e)).inv
        ≫ (F.residueFieldMap x₁ ≫ (Scheme.residueFieldCongr e).hom) := by
    rw [hc]
    simp
  rw [hD]
  infer_instance

/-- The tensor congruence of an equality of triplets fixes the generic point. -/
theorem tensorCongr_SpecTensorTo_bot {T₁ T₂ : Pullback.Triplet f g} (h : T₁ = T₂)
    [IsDomain T₁.tensor] [IsDomain T₂.tensor] :
    Spec.map (Pullback.Triplet.tensorCongr h).hom (botPoint T₂) = botPoint T₁ := by
  cases h
  rfl

/-- **`SpecOfPoint` of the cylinder point is the generic point.** -/
theorem specOfPoint_specTensorTo_bot (T : Pullback.Triplet f g) [IsDomain T.tensor]
    [IsDomain ↥(Pullback.Triplet.ofPoint (T.SpecTensorTo (botPoint T))).tensor] :
    (show ↥(Spec (Pullback.Triplet.ofPoint (T.SpecTensorTo (botPoint T))).tensor)
        from Pullback.SpecOfPoint (T.SpecTensorTo (botPoint T)))
      = botPoint (Pullback.Triplet.ofPoint (T.SpecTensorTo (botPoint T))) := by
  have h : (Pullback.carrierEquiv (f := f) (g := g)) (T.SpecTensorTo (botPoint T))
      = (⟨T, botPoint T⟩ : Σ T' : Pullback.Triplet f g, ↥(Spec T'.tensor)) :=
    (Pullback.carrierEquiv (f := f) (g := g)).right_inv
      (⟨T, botPoint T⟩ : Σ T' : Pullback.Triplet f g, ↥(Spec T'.tensor))
  rw [show (Pullback.carrierEquiv (f := f) (g := g)) (T.SpecTensorTo (botPoint T))
      = ⟨Pullback.Triplet.ofPoint (T.SpecTensorTo (botPoint T)),
          Pullback.SpecOfPoint (T.SpecTensorTo (botPoint T))⟩ from rfl] at h
  rw [Pullback.carrierEquiv_eq_iff] at h
  obtain ⟨e, he⟩ := h
  have h1 : Spec.map (Pullback.Triplet.tensorCongr e).hom
      (Spec.map (Pullback.Triplet.tensorCongr e).inv
        (Pullback.SpecOfPoint (T.SpecTensorTo (botPoint T))))
      = Spec.map (Pullback.Triplet.tensorCongr e).hom (botPoint T) := congrArg _ he
  rw [← Scheme.Hom.comp_apply, ← Spec.map_comp, Iso.hom_inv_id] at h1
  simp only [Spec.map_id] at h1
  rw [tensorCongr_SpecTensorTo_bot e] at h1
  exact h1

/-- **The residue field of the cylinder point of the `ofPoint` triplet is a fraction field.**
The residue field map of `(ofPoint t).SpecTensorTo` at `SpecOfPoint t` is an isomorphism, because
the composite `Spec.map (ofPointTensor t) ≫ (ofPoint t).SpecTensorTo` is
`(pullback f g).fromSpecResidueField t`, whose residue field map at the generic point is an
isomorphism. -/
theorem isIso_specTensorTo_residueFieldMap_specOfPoint (T : Pullback.Triplet f g)
    [IsDomain T.tensor]
    [IsDomain ↥(Pullback.Triplet.ofPoint (T.SpecTensorTo (botPoint T))).tensor] :
    IsIso (((Pullback.Triplet.ofPoint (T.SpecTensorTo (botPoint T))).SpecTensorTo).residueFieldMap
      (Pullback.SpecOfPoint (T.SpecTensorTo (botPoint T)))) := by
  let p : ↥(Spec ((pullback f g).residueField (T.SpecTensorTo (botPoint T)))) :=
    (show ↥(Spec ((pullback f g).residueField (T.SpecTensorTo (botPoint T))))
      from (⊥ : PrimeSpectrum ((pullback f g).residueField (T.SpecTensorTo (botPoint T)))))
  have hcomp : Spec.map (Pullback.ofPointTensor (T.SpecTensorTo (botPoint T))) ≫
      (Pullback.Triplet.ofPoint (T.SpecTensorTo (botPoint T))).SpecTensorTo
      = (pullback f g).fromSpecResidueField (T.SpecTensorTo (botPoint T)) :=
    Pullback.ofPointTensor_SpecTensorTo _
  have hiso : IsIso ((Spec.map (Pullback.ofPointTensor (T.SpecTensorTo (botPoint T))) ≫
      (Pullback.Triplet.ofPoint (T.SpecTensorTo (botPoint T))).SpecTensorTo).residueFieldMap p) := by
    rw [hcomp]
    exact isIso_residueFieldMap_fromSpecResidueField (pullback f g) (T.SpecTensorTo (botPoint T)) p
  simp only [Scheme.residueFieldMap_comp] at hiso
  exact isIso_left_of_comp_isIso _ _ (RingHom.injective _) (RingHom.injective _) hiso

/-- **The residue field of the cylinder point is the fraction field of the tensor.**
For any `Triplet` with `IsDomain T.tensor`, the residue field map of `T.SpecTensorTo` at the generic
point of `Spec T.tensor` is an isomorphism. -/
theorem isIso_specTensorTo_residueFieldMap_bot (T : Pullback.Triplet f g) [IsDomain T.tensor] :
    IsIso (T.SpecTensorTo.residueFieldMap (botPoint T)) := by
  haveI hI : IsDomain ↥(Pullback.Triplet.ofPoint (T.SpecTensorTo (botPoint T))).tensor :=
    MulEquiv.isDomain ↥T.tensor
      ((Pullback.Triplet.tensorCongr (Pullback.Triplet.ofPoint_SpecTensorTo (T := T)
        (botPoint T))).commRingCatIsoToRingEquiv)
  let e := Pullback.Triplet.ofPoint_SpecTensorTo (T := T) (botPoint T)
  let ψ : (Pullback.Triplet.ofPoint (T.SpecTensorTo (botPoint T))).tensor ≅ T.tensor :=
    Pullback.Triplet.tensorCongr e
  have h5 : IsIso (((Pullback.Triplet.ofPoint (T.SpecTensorTo (botPoint T))).SpecTensorTo).residueFieldMap
      (botPoint (Pullback.Triplet.ofPoint (T.SpecTensorTo (botPoint T))))) :=
    isIso_residueFieldMap_congr _ (specOfPoint_specTensorTo_bot T)
      (isIso_specTensorTo_residueFieldMap_specOfPoint T)
  have htw : Spec.map ψ.hom (botPoint T)
      = botPoint (Pullback.Triplet.ofPoint (T.SpecTensorTo (botPoint T))) :=
    tensorCongr_SpecTensorTo_bot e
  have h6 : IsIso (((Pullback.Triplet.ofPoint (T.SpecTensorTo (botPoint T))).SpecTensorTo).residueFieldMap
      (Spec.map ψ.hom (botPoint T))) :=
    isIso_residueFieldMap_congr _ htw.symm h5
  haveI := h6
  have h7 : IsIso ((Spec.map ψ.hom ≫
      (Pullback.Triplet.ofPoint (T.SpecTensorTo (botPoint T))).SpecTensorTo).residueFieldMap
      (botPoint T)) := by
    rw [Scheme.residueFieldMap_comp]
    exact (asIso (((Pullback.Triplet.ofPoint (T.SpecTensorTo (botPoint T))).SpecTensorTo).residueFieldMap
        (Spec.map ψ.hom (botPoint T))) ≪≫ asIso ((Spec.map ψ.hom).residueFieldMap (botPoint T))).isIso_hom
  rw [show Spec.map ψ.hom ≫ (Pullback.Triplet.ofPoint (T.SpecTensorTo (botPoint T))).SpecTensorTo
      = T.SpecTensorTo from Pullback.tensorCongr_SpecTensorTo e] at h7
  exact h7

end GenericPoint

/-! ## 2. The `𝕜`-structure of the tensor

The tensor `T.tensor` of a triplet over `Spec 𝕜` is a `𝕜`-algebra through the second coprojection
`tensorInr`; `T.SpecTensorTo` is a morphism over `Spec 𝕜` for this structure, which is what makes
the residue field comparison of the cylinder points a statement over `𝕜`.
-/

section Structure

variable {𝕜 : Type} [Field 𝕜]

/-- The base case `Q = Spec 𝕜`: `fromSpecResidueField` is `Spec.map` of the structure map. -/
theorem fromSpecResidueField_self (s : Spec (CommRingCat.of 𝕜)) :
    (Spec (CommRingCat.of 𝕜)).fromSpecResidueField s
      = Spec.map (algMapResidue (𝟙 (Spec (CommRingCat.of 𝕜))) s) := by
  haveI : s.asIdeal.IsPrime := s.isPrime
  have key : algMapResidue (𝟙 (Spec (CommRingCat.of 𝕜))) s
      = CommRingCat.ofHom (algebraMap 𝕜 (s.asIdeal.ResidueField)) ≫
        (Scheme.Spec.residueFieldIso (CommRingCat.of 𝕜) s).inv := by
    rw [show algMapResidue (𝟙 (Spec (CommRingCat.of 𝕜))) s =
        (Scheme.ΓSpecIso (CommRingCat.of 𝕜)).inv ≫
          (Spec (CommRingCat.of 𝕜)).presheaf.germ ⊤ s trivial ≫
            (Spec (CommRingCat.of 𝕜)).residue s from by
      simp only [algMapResidue, Scheme.Hom.id_appTop, Category.id_comp]
      rfl]
    exact (Scheme.Spec.algebraMap_residueFieldIso_inv (CommRingCat.of 𝕜) s).symm
  rw [key, Spec.map_comp, Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField]

/-- **`fromSpecResidueField` composed with the structure morphism is `Spec.map` of the structure
map of the residue field.** -/
theorem fromSpecResidueField_comp_structure_aux (Q : Scheme.{0})
    [Q.Over (Spec (CommRingCat.of 𝕜))] (q : Q) :
    Q.fromSpecResidueField q ≫ (Q ↘ Spec (CommRingCat.of 𝕜))
      = Spec.map (algMapResidue (Q ↘ Spec (CommRingCat.of 𝕜)) q) := by
  rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField
    (f := (Q ↘ Spec (CommRingCat.of 𝕜))) q]
  rw [fromSpecResidueField_self ((Q ↘ Spec (CommRingCat.of 𝕜)) q), ← Spec.map_comp]
  congr 1
  exact algMapResidue_id (𝕜 := 𝕜) (Q ↘ Spec (CommRingCat.of 𝕜)) q

/-- **The structure morphism of the cylinder is `Spec.map` of the `𝕜`-structure of the tensor.** -/
theorem specTensorTo_comp_structure (k : ℕ) (X : Scheme.{0})
    [X.Over (Spec (CommRingCat.of 𝕜))] (x : X) :
    (cylTriplet (𝕜 := 𝕜) X x k).SpecTensorTo
        ≫ (WProd (𝕜 := 𝕜) X k ↘ Spec (CommRingCat.of 𝕜))
      = Spec.map (algMapResidue (X ↘ Spec (CommRingCat.of 𝕜)) x
          ≫ (cylTriplet (𝕜 := 𝕜) X x k).tensorInr) := by
  rw [show (WProd (𝕜 := 𝕜) X k ↘ Spec (CommRingCat.of 𝕜))
      = pullback.snd (AffineK (𝕜 := 𝕜) k ↘ Spec (CommRingCat.of 𝕜))
          (X ↘ Spec (CommRingCat.of 𝕜)) ≫ (X ↘ Spec (CommRingCat.of 𝕜)) from rfl]
  rw [← Category.assoc, Pullback.Triplet.specTensorTo_snd]
  rw [Category.assoc, fromSpecResidueField_comp_structure_aux (𝕜 := 𝕜) X
    (cylTriplet (𝕜 := 𝕜) X x k).y]
  rw [← Spec.map_comp]
  rfl

/-- **`Spec.map` of an injective ring hom sends the generic point to the generic point.** -/
theorem Spec_map_bot {A B : CommRingCat.{0}} [IsDomain ↥A] [IsDomain ↥B] (φ : A ⟶ B)
    (hφ : Function.Injective φ.hom) :
    (Spec.map φ) ((⊥ : PrimeSpectrum ↥B) : ↥(Spec B)) = ((⊥ : PrimeSpectrum ↥A) : ↥(Spec A)) := by
  have hkerI : ((PrimeSpectrum.comap φ.hom (⊥ : PrimeSpectrum ↥B)) : Ideal ↥A) = (⊥ : Ideal ↥A) := by
    rw [PrimeSpectrum.comap_asIdeal]
    show Ideal.comap φ.hom ((⊥ : PrimeSpectrum ↥B) : Ideal ↥B) = (⊥ : Ideal ↥A)
    rw [show ((⊥ : PrimeSpectrum ↥B) : Ideal ↥B) = ⊥ from rfl]
    ext a
    simp only [Ideal.mem_comap, Ideal.mem_bot]
    exact ⟨fun h => hφ (by rw [h, map_zero]), fun h => by rw [h, map_zero]⟩
  have hker : PrimeSpectrum.comap φ.hom (⊥ : PrimeSpectrum ↥B) = (⊥ : PrimeSpectrum ↥A) :=
    PrimeSpectrum.ext hkerI
  rw [show (Spec.map φ) ((⊥ : PrimeSpectrum ↥B) : ↥(Spec B))
      = ((PrimeSpectrum.comap φ.hom (⊥ : PrimeSpectrum ↥B)) : ↥(Spec A)) from rfl]
  rw [hker]

end Structure

/-! ## 2b. The same with the `𝔸ᵏ`-leg

For the comparison of the `𝕜`-structures of the two tensors it is more convenient to use the
structure induced by the *first* coprojection `tensorInl` (the leg over `𝔸ᵏ`), because the two
tensors share that leg. -/

section StructureInl

variable {𝕜 : Type} [Field 𝕜]

/-- **The structure morphism of the cylinder is `Spec.map` of the `𝕜`-structure of the tensor,
via the `𝔸ᵏ`-leg.** -/
theorem specTensorTo_comp_structure_inl (k : ℕ) (X : Scheme.{0})
    [X.Over (Spec (CommRingCat.of 𝕜))] (x : X) :
    (cylTriplet (𝕜 := 𝕜) X x k).SpecTensorTo
        ≫ (WProd (𝕜 := 𝕜) X k ↘ Spec (CommRingCat.of 𝕜))
      = Spec.map (algMapResidue (AffineK (𝕜 := 𝕜) k ↘ Spec (CommRingCat.of 𝕜))
            (cylTriplet (𝕜 := 𝕜) X x k).x
          ≫ (cylTriplet (𝕜 := 𝕜) X x k).tensorInl) := by
  rw [show (WProd (𝕜 := 𝕜) X k ↘ Spec (CommRingCat.of 𝕜))
      = pullback.snd (AffineK (𝕜 := 𝕜) k ↘ Spec (CommRingCat.of 𝕜))
          (X ↘ Spec (CommRingCat.of 𝕜)) ≫ (X ↘ Spec (CommRingCat.of 𝕜)) from rfl,
    ← pullback.condition]
  rw [← Category.assoc, Pullback.Triplet.specTensorTo_fst]
  rw [Category.assoc,
    fromSpecResidueField_comp_structure_aux (𝕜 := 𝕜) (AffineK (𝕜 := 𝕜) k)
      (cylTriplet (𝕜 := 𝕜) X x k).x]
  rw [← Spec.map_comp]

end StructureInl

/-! ## 3. The residue field comparison -/

section Statement

variable {𝕜 : Type} [Field 𝕜]

theorem resEquiv_prodPt_of_resEquiv (𝕜 : Type) [Field 𝕜] (k : ℕ) {X Z : AlgebraicGeometry.Scheme.{0}}
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))] [Z.Over (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))]
    (x : X) (z : Z)
    [IsDomain (Work.CY3Stab.cylTriplet (𝕜 := 𝕜) X x k).tensor]
    [IsDomain (Work.CY3Stab.cylTriplet (𝕜 := 𝕜) Z z k).tensor]
    (h : ResEquiv 𝕜 x z) :
    ResEquiv 𝕜 ((Work.CY3Stab.cylTriplet (𝕜 := 𝕜) X x k).SpecTensorTo
        (⊥ : PrimeSpectrum (Work.CY3Stab.cylTriplet (𝕜 := 𝕜) X x k).tensor))
      ((Work.CY3Stab.cylTriplet (𝕜 := 𝕜) Z z k).SpecTensorTo
        (⊥ : PrimeSpectrum (Work.CY3Stab.cylTriplet (𝕜 := 𝕜) Z z k).tensor)) := by
  obtain ⟨Φ, hΦinl⟩ := tensor_iso_tensorInl (𝕜 := 𝕜) k x z h
  -- the `𝕜`-structures, via the leg over `𝔸ᵏ`
  letI : (Spec (cylTriplet (𝕜 := 𝕜) X x k).tensor).Over (Spec (CommRingCat.of 𝕜)) :=
    ⟨Spec.map (algMapResidue (AffineK (𝕜 := 𝕜) k ↘ Spec (CommRingCat.of 𝕜))
        (cylTriplet (𝕜 := 𝕜) X x k).x ≫ (cylTriplet (𝕜 := 𝕜) X x k).tensorInl)⟩
  letI : (Spec (cylTriplet (𝕜 := 𝕜) Z z k).tensor).Over (Spec (CommRingCat.of 𝕜)) :=
    ⟨Spec.map (algMapResidue (AffineK (𝕜 := 𝕜) k ↘ Spec (CommRingCat.of 𝕜))
        (cylTriplet (𝕜 := 𝕜) Z z k).x ≫ (cylTriplet (𝕜 := 𝕜) Z z k).tensorInl)⟩
  -- (b): `SpecTensorTo` is a morphism over `𝕜`
  have hbX : (cylTriplet (𝕜 := 𝕜) X x k).SpecTensorTo
        ≫ (WProd (𝕜 := 𝕜) X k ↘ Spec (CommRingCat.of 𝕜))
      = (Spec (cylTriplet (𝕜 := 𝕜) X x k).tensor ↘ Spec (CommRingCat.of 𝕜)) := by
    rw [show (Spec (cylTriplet (𝕜 := 𝕜) X x k).tensor ↘ Spec (CommRingCat.of 𝕜))
        = Spec.map (algMapResidue (AffineK (𝕜 := 𝕜) k ↘ Spec (CommRingCat.of 𝕜))
            (cylTriplet (𝕜 := 𝕜) X x k).x ≫ (cylTriplet (𝕜 := 𝕜) X x k).tensorInl) from rfl]
    exact specTensorTo_comp_structure_inl (𝕜 := 𝕜) k X x
  have hbZ : (cylTriplet (𝕜 := 𝕜) Z z k).SpecTensorTo
        ≫ (WProd (𝕜 := 𝕜) Z k ↘ Spec (CommRingCat.of 𝕜))
      = (Spec (cylTriplet (𝕜 := 𝕜) Z z k).tensor ↘ Spec (CommRingCat.of 𝕜)) := by
    rw [show (Spec (cylTriplet (𝕜 := 𝕜) Z z k).tensor ↘ Spec (CommRingCat.of 𝕜))
        = Spec.map (algMapResidue (AffineK (𝕜 := 𝕜) k ↘ Spec (CommRingCat.of 𝕜))
            (cylTriplet (𝕜 := 𝕜) Z z k).x ≫ (cylTriplet (𝕜 := 𝕜) Z z k).tensorInl) from rfl]
    exact specTensorTo_comp_structure_inl (𝕜 := 𝕜) k Z z
  -- step 1: the cylinder point of `X` and the generic point of `Spec D_X`
  haveI hIsoX : IsIso ((cylTriplet (𝕜 := 𝕜) X x k).SpecTensorTo.residueFieldMap
      (botPoint (cylTriplet (𝕜 := 𝕜) X x k))) := isIso_specTensorTo_residueFieldMap_bot _
  have hstep1 : ResEquiv 𝕜 ((cylTriplet (𝕜 := 𝕜) X x k).SpecTensorTo
        (⊥ : PrimeSpectrum (cylTriplet (𝕜 := 𝕜) X x k).tensor))
      (botPoint (cylTriplet (𝕜 := 𝕜) X x k)) :=
    Work.Motivic.resEquiv_of_morphism (f := (cylTriplet (𝕜 := 𝕜) X x k).SpecTensorTo) hbX _
  -- step 2: the cylinder point of `Z` and the generic point of `Spec D_Z`
  haveI hIsoZ : IsIso ((cylTriplet (𝕜 := 𝕜) Z z k).SpecTensorTo.residueFieldMap
      (botPoint (cylTriplet (𝕜 := 𝕜) Z z k))) := isIso_specTensorTo_residueFieldMap_bot _
  have hstep2 : ResEquiv 𝕜 ((cylTriplet (𝕜 := 𝕜) Z z k).SpecTensorTo
        (⊥ : PrimeSpectrum (cylTriplet (𝕜 := 𝕜) Z z k).tensor))
      (botPoint (cylTriplet (𝕜 := 𝕜) Z z k)) :=
    Work.Motivic.resEquiv_of_morphism (f := (cylTriplet (𝕜 := 𝕜) Z z k).SpecTensorTo) hbZ _
  -- `Spec.map Φ.hom` is a morphism over `𝕜`
  have hsΦ : algMapResidue (AffineK (𝕜 := 𝕜) k ↘ Spec (CommRingCat.of 𝕜))
          (cylTriplet (𝕜 := 𝕜) X x k).x
        ≫ (cylTriplet (𝕜 := 𝕜) X x k).tensorInl ≫ Φ.hom
      = algMapResidue (AffineK (𝕜 := 𝕜) k ↘ Spec (CommRingCat.of 𝕜))
          (cylTriplet (𝕜 := 𝕜) Z z k).x
        ≫ (cylTriplet (𝕜 := 𝕜) Z z k).tensorInl := by
    rw [hΦinl]
    rfl
  have hfΦ : Spec.map Φ.hom ≫ (Spec (cylTriplet (𝕜 := 𝕜) X x k).tensor ↘ Spec (CommRingCat.of 𝕜))
      = (Spec (cylTriplet (𝕜 := 𝕜) Z z k).tensor ↘ Spec (CommRingCat.of 𝕜)) := by
    rw [show (Spec (cylTriplet (𝕜 := 𝕜) X x k).tensor ↘ Spec (CommRingCat.of 𝕜))
        = Spec.map (algMapResidue (AffineK (𝕜 := 𝕜) k ↘ Spec (CommRingCat.of 𝕜))
            (cylTriplet (𝕜 := 𝕜) X x k).x ≫ (cylTriplet (𝕜 := 𝕜) X x k).tensorInl) from rfl,
      show (Spec (cylTriplet (𝕜 := 𝕜) Z z k).tensor ↘ Spec (CommRingCat.of 𝕜))
        = Spec.map (algMapResidue (AffineK (𝕜 := 𝕜) k ↘ Spec (CommRingCat.of 𝕜))
            (cylTriplet (𝕜 := 𝕜) Z z k).x ≫ (cylTriplet (𝕜 := 𝕜) Z z k).tensorInl) from rfl,
      ← Spec.map_comp, Spec.map_injective.eq_iff]
    rw [Category.assoc]
    exact hsΦ
  -- step 3: the two generic points
  haveI hIsoΦ : IsIso ((Spec.map Φ.hom).residueFieldMap
      (botPoint (cylTriplet (𝕜 := 𝕜) Z z k))) := inferInstance
  have hstep3 : ResEquiv 𝕜 (botPoint (cylTriplet (𝕜 := 𝕜) X x k))
      (botPoint (cylTriplet (𝕜 := 𝕜) Z z k)) := by
    have h3 := Work.Motivic.resEquiv_of_morphism (f := Spec.map Φ.hom) hfΦ
      (botPoint (cylTriplet (𝕜 := 𝕜) Z z k))
    rwa [Spec_map_bot Φ.hom (ConcreteCategory.bijective_of_isIso Φ.hom).1] at h3
  exact Work.Motivic.ResEquiv.trans hstep1
    (Work.Motivic.ResEquiv.trans hstep3 (Work.Motivic.ResEquiv.symm hstep2))

end Statement

end Work.CY3Stab.Prod
