import Submission.NK.Reconstruct.Basic
import Submission.NeukirchUchida.PrimeCorrespondence
import Mathlib.FieldTheory.Galois.Infinite
import Submission.NK.NeukirchUchida.isHomeomorph_conjHomEquiv

/-!
# The correspondence of finite levels induced by an isomorphism of absolute Galois groups

The Neukirch–Uchida reconstruction compares `ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)` with the conjugation by
a field isomorphism `σ` on finite levels.  The *correspondence of levels* used by `ϕ` itself is the
one of the Galois correspondence of `Mathlib.FieldTheory.Galois.Infinite`:

* `levelMap ϕ L` is the image of a level `L ⊆ K₁'` under `ϕ`, i.e. the fixed field of the image of
  `Gal(K₁'/L)` under `ϕ`;
* `levelMapEquiv ϕ L : Gal(↥L/K₁) ≃* Gal(↥(levelMap ϕ L)/K₂)` is the induced isomorphism of Galois
  groups, obtained from the Galois correspondence and the isomorphism `ϕ` of the quotients;
* `levelPrimeMap ϕ a L P` is the prime of `𝓞 (levelMap ϕ L)` corresponding to a prime `P` of
  `𝓞 L` under the place correspondence `a.placeMap`; it is well defined because `ϕ` maps the
  decomposition groups of corresponding places to each other (`a.map_decomp`) and `ϕ` is
  Galois-equivariant on places (`a.map_smul`).

These are the σ-free analogues of `NK.Reconstruct.sigmaLevel`/`sigmaLevelEquiv`/`primeTransport`,
and they are what makes the *Frobenius correspondence* (input (b)) statable without presupposing the
realizing field isomorphism `σ` (`NK.Reconstruct.FrobeniusCorrespondencePlace`).
-/

namespace NK.Reconstruct

open scoped Pointwise

variable {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

/-- **The image of a level under the correspondence induced by `ϕ`**: the fixed field of the image
of `Gal(K₁'/L)` under `ϕ`. -/
noncomputable def levelMap (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (L : IntermediateField K₁ K₁') :
    IntermediateField K₂ K₂' :=
  IntermediateField.fixedField (L.fixingSubgroup.map (ϕ : Gal(K₁'/K₁) →* Gal(K₂'/K₂)))

/-- A point of `K₂'` lies in `levelMap ϕ L` exactly when it is fixed by `ϕ g` for every
`g ∈ Gal(K₁'/L)`. -/
theorem mem_levelMap_iff {ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)} {L : IntermediateField K₁ K₁'}
    {x : K₂'} :
    x ∈ levelMap ϕ L ↔
      ∀ g : Gal(K₁'/K₁), (∀ y : ↥L, g (y : K₁') = (y : K₁')) → ϕ g x = x := by
  rw [levelMap, IntermediateField.mem_fixedField_iff]
  constructor
  · intro h g hg
    exact h (ϕ g) ⟨g, (IntermediateField.mem_fixingSubgroup_iff L g).mpr
      (fun y hy => hg ⟨y, hy⟩), rfl⟩
  · rintro h _ ⟨g, hg, rfl⟩
    exact h g (fun y => (IntermediateField.mem_fixingSubgroup_iff L g).mp hg y.1 y.2)

/-- **The Galois group of the image level is the image of the Galois group of the level**: for
`IsHomeomorph ϕ` (so that images of open subgroups are open, hence closed), the fixing subgroup of
`levelMap ϕ L` is exactly `ϕ(Gal(K₁'/L))`. -/
theorem fixingSubgroup_levelMap {ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)} (hϕ : IsHomeomorph ϕ)
    (L : IntermediateField K₁ K₁') [FiniteDimensional K₁ L] :
    (levelMap ϕ L).fixingSubgroup =
      L.fixingSubgroup.map (ϕ : Gal(K₁'/K₁) →* Gal(K₂'/K₂)) := by
  haveI : IsGalois K₁ K₁' := IsSepClosure.isGalois
  haveI : IsGalois K₂ K₂' := IsSepClosure.isGalois
  rw [levelMap]
  have hopen : IsOpen ((L.fixingSubgroup : Set Gal(K₁'/K₁))) :=
    IntermediateField.fixingSubgroup_isOpen L
  have hmapopen : IsOpen ((L.fixingSubgroup.map (ϕ : Gal(K₁'/K₁) →* Gal(K₂'/K₂)) :
      Subgroup Gal(K₂'/K₂)) : Set Gal(K₂'/K₂)) := by
    rw [Subgroup.coe_map]
    exact hϕ.isOpenMap _ hopen
  exact InfiniteGalois.fixingSubgroup_fixedField
    ⟨_, Subgroup.isClosed_of_isOpen _ hmapopen⟩

/-- **The image level is finite-dimensional** when the level is: the image of an open subgroup under
the homeomorphism `ϕ` is open, and an open fixing subgroup has finite-dimensional fixed field
(`InfiniteGalois.isOpen_iff_finite`). -/
theorem finiteDimensional_levelMap {ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)} (hϕ : IsHomeomorph ϕ)
    (L : IntermediateField K₁ K₁') [FiniteDimensional K₁ L] :
    FiniteDimensional K₂ (levelMap ϕ L) := by
  haveI : IsGalois K₂ K₂' := IsSepClosure.isGalois
  rw [← InfiniteGalois.isOpen_iff_finite (levelMap ϕ L)]
  rw [fixingSubgroup_levelMap hϕ L]
  convert hϕ.isOpenMap _ (IntermediateField.fixingSubgroup_isOpen L) using 1
  exact (Subgroup.coe_map _ _).symm

/-- **The image of a normal level is normal**: `ϕ` carries the fixing subgroup of a normal level to a
normal subgroup, and normality of the fixing subgroup is equivalent to normality/Galoisness of the
level (`InfiniteGalois.normal_iff_isGalois`). -/
theorem isGalois_levelMap {ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)} (hϕ : IsHomeomorph ϕ)
    (L : IntermediateField K₁ K₁') [FiniteDimensional K₁ L] [Normal K₁ L] :
    IsGalois K₂ ↥(levelMap ϕ L) := by
  haveI : IsGalois K₁ K₁' := IsSepClosure.isGalois
  haveI : IsGalois K₂ K₂' := IsSepClosure.isGalois
  haveI : FiniteDimensional K₂ (levelMap ϕ L) := finiteDimensional_levelMap hϕ L
  have hN₁ : L.fixingSubgroup.Normal :=
    (InfiniteGalois.normal_iff_isGalois L).mpr
      (Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero)
  rw [← InfiniteGalois.normal_iff_isGalois (levelMap ϕ L), fixingSubgroup_levelMap hϕ L]
  exact Subgroup.Normal.map hN₁ (ϕ : Gal(K₁'/K₁) →* Gal(K₂'/K₂)) ϕ.surjective

/-- Normality of the transported level. -/
theorem normal_levelMap {ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)} (hϕ : IsHomeomorph ϕ)
    (L : IntermediateField K₁ K₁') [FiniteDimensional K₁ L] [Normal K₁ L] :
    Normal K₂ (levelMap ϕ L) := by
  haveI : FiniteDimensional K₂ (levelMap ϕ L) := finiteDimensional_levelMap hϕ L
  haveI := isGalois_levelMap hϕ L
  infer_instance

/-- The transported level is a number field. -/
theorem numberField_levelMap {ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)} (hϕ : IsHomeomorph ϕ)
    (L : IntermediateField K₁ K₁') [FiniteDimensional K₁ L] :
    NumberField ↥(levelMap ϕ L) := by
  haveI : FiniteDimensional K₂ (levelMap ϕ L) := finiteDimensional_levelMap hϕ L
  exact Commons.NumberTheory.NumberField.numberField_of_intermediateField (levelMap ϕ L)

/-- **The Galois group of a finite Galois level as a quotient**: for `L/K` finite Galois inside
the separable closure `K'`, the restriction `Gal(K'/K) →* Gal(↥L/K)` has kernel `Gal(K'/L)` and is
surjective, so it induces an isomorphism `Gal(K'/K) ⧸ Gal(K'/L) ≃* Gal(↥L/K)`. -/
noncomputable def quotientEquivOfLevel {k K' : Type*} [Field k] [NumberField k] [Field K']
    [Algebra k K'] [IsSepClosure k K'] (L : IntermediateField k K') [FiniteDimensional k L]
    [Normal k L] : Gal(K'/k) ⧸ L.fixingSubgroup ≃* Gal(↥L/k) := by
  haveI : IsGalois k K' := IsSepClosure.isGalois
  haveI : IsGalois k ↥L := Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
  haveI : L.fixingSubgroup.Normal := (InfiniteGalois.normal_iff_isGalois L).mpr ‹IsGalois k ↥L›
  refine QuotientGroup.liftEquiv
    (φ := AlgEquiv.restrictNormalHom (F := k) (K₁ := K') (E := ↥L))
    L.fixingSubgroup ?_ ?_
  · exact AlgEquiv.restrictNormalHom_surjective (F := k) (K₁ := ↥L) (E := K')
  · exact (IntermediateField.restrictNormalHom_ker L).symm

/-- **The induced isomorphism `Gal(↥L/K₁) ≃* Gal(↥(levelMap ϕ L)/K₂)`**: the Galois correspondence
turns the isomorphism `ϕ` of the absolute Galois groups into an isomorphism of the Galois groups of
corresponding levels. -/
noncomputable def levelMapEquiv {ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)} (hϕ : IsHomeomorph ϕ)
    (L : IntermediateField K₁ K₁') [FiniteDimensional K₁ L] [Normal K₁ L] :
    Gal(↥L/K₁) ≃* Gal(↥(levelMap ϕ L)/K₂) := by
  haveI : IsGalois K₁ K₁' := IsSepClosure.isGalois
  haveI : IsGalois K₂ K₂' := IsSepClosure.isGalois
  haveI hfd' : FiniteDimensional K₂ (levelMap ϕ L) := finiteDimensional_levelMap hϕ L
  haveI hnorm' : Normal K₂ (levelMap ϕ L) := normal_levelMap hϕ L
  haveI hgalL : IsGalois K₁ ↥L :=
    Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
  haveI hN₁ : L.fixingSubgroup.Normal := (InfiniteGalois.normal_iff_isGalois L).mpr hgalL
  haveI hgalL' : IsGalois K₂ ↥(levelMap ϕ L) := isGalois_levelMap hϕ L
  haveI hN₂ : (levelMap ϕ L).fixingSubgroup.Normal :=
    (InfiniteGalois.normal_iff_isGalois (levelMap ϕ L)).mpr hgalL'
  exact (quotientEquivOfLevel (K' := K₁') L).symm.trans
    ((QuotientGroup.congr L.fixingSubgroup (levelMap ϕ L).fixingSubgroup
        (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (fixingSubgroup_levelMap hϕ L).symm).trans
      (quotientEquivOfLevel (K' := K₂') (levelMap ϕ L)))

end NK.Reconstruct
