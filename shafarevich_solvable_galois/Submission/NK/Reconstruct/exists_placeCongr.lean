import Mathlib
import Submission.NK.Reconstruct.Basic
import Submission.NK.Reconstruct.GammaObject
import Submission.NK.Reconstruct.comap_placeMap_eq_of_realizesPlaceMap
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The bijection of the place systems induced by an isomorphism of separable closures

Let `K` be a number field and let `K'` and `Ω` be two separable closures of `K`.  A
`K`-algebra isomorphism `e : K' ≃ₐ[K] Ω` induces a bijection

`placeCongr e : FinitePlaceOf K Ω ≃ FinitePlaceOf K K'`

of the place systems over the finite primes of `K`, by transporting a place `A` of `Ω` to the
place `A.comap e` of `K'`.  This file proves the three properties of this bijection that the
reconstruction step of Neukirch–Uchida needs (this is the elementary bookkeeping behind the
"common separable closure" reduction of the two-closure setting):

* **membership**: `x ∈ (placeCongr e A).1 ↔ e x ∈ A.1` for every `x : K'`;
* **Galois equivariance**: `placeCongr e (g • A) = (algEquivConjHom e.symm g) • placeCongr e A`,
  where `algEquivConjHom e.symm : Gal(Ω/K) →* Gal(K'/K)` is the conjugation
  `g ↦ e⁻¹ ∘ g ∘ e` (so the two absolute Galois groups `Gal(K'/K)` and `Gal(Ω/K)` act on
  corresponding places through corresponding elements);
* **compatibility with decomposition groups**:
  `D_{placeCongr e A} = (D_A).map (algEquivConjHom e.symm)`,

the last being an instance of the general transport of decomposition groups along a
base-field-mapping isomorphism (`NK.Reconstruct.map_conjHomEquiv_decompositionGroup`).
-/

namespace NK.Reconstruct

open scoped Pointwise

set_option linter.unusedSectionVars false

variable {K : Type*} [Field K] [NumberField K] {K' : Type*} [Field K']
    {Ω : Type*} [Field Ω] [Algebra K K'] [Algebra K Ω] [IsSepClosure K K'] [IsSepClosure K Ω]

section PlaceCongr

variable (e : K' ≃ₐ[K] Ω)

/-- `e` composed with the structure map of `K'` is the structure map of `Ω`. -/
lemma comp_algebraMap_eq :
    ((e : K' →+* Ω).comp (algebraMap K K')) = algebraMap K Ω :=
  RingHom.ext fun x => e.commutes x

/-- `e.symm` composed with the structure map of `Ω` is the structure map of `K'`. -/
lemma symm_comp_algebraMap_eq :
    ((e.symm : Ω →+* K').comp (algebraMap K Ω)) = algebraMap K K' :=
  RingHom.ext fun x => e.symm.commutes x

/-- **The transport of places along `e`**: the place `A.comap e` of `K'` associated with a place
`A` of `Ω` over a finite prime of `K`.  It lies over a finite prime because `e` is a
`K`-algebra isomorphism, so that `A.comap e` has the same trace on `K` as `A`. -/
noncomputable def placeCongrFun (A : FinitePlaceOf K Ω) : FinitePlaceOf K K' :=
  ⟨A.1.comap (e : K' →+* Ω), fun h => A.2 (by
    rw [ValuationSubring.comap_comap, comp_algebraMap_eq e] at h
    exact h)⟩

/-- The inverse transport of places: the place `B.comap e.symm` of `Ω` associated with a place
`B` of `K'`. -/
noncomputable def placeCongrInvFun (B : FinitePlaceOf K K') : FinitePlaceOf K Ω :=
  ⟨B.1.comap (e.symm : Ω →+* K'), fun h => B.2 (by
    rw [ValuationSubring.comap_comap, symm_comp_algebraMap_eq e] at h
    exact h)⟩

/-- **The bijection of the place systems induced by `e`.** -/
noncomputable def placeCongr : FinitePlaceOf K Ω ≃ FinitePlaceOf K K' where
  toFun := placeCongrFun e
  invFun := placeCongrInvFun e
  left_inv A := Subtype.ext (by
    show (A.1.comap (e : K' →+* Ω)).comap (e.symm : Ω →+* K') = A.1
    rw [ValuationSubring.comap_comap]
    apply ValuationSubring.ext
    intro x
    rw [ValuationSubring.mem_comap]
    simp)
  right_inv B := Subtype.ext (by
    show (B.1.comap (e.symm : Ω →+* K')).comap (e : K' →+* Ω) = B.1
    rw [ValuationSubring.comap_comap]
    apply ValuationSubring.ext
    intro x
    rw [ValuationSubring.mem_comap]
    simp)

@[simp] lemma placeCongr_apply_val (A : FinitePlaceOf K Ω) :
    (placeCongr e A).1 = A.1.comap (e : K' →+* Ω) := rfl

/-- **The defining membership property** of the transported place. -/
lemma placeCongr_mem (A : FinitePlaceOf K Ω) (x : K') :
    x ∈ (placeCongr e A).1 ↔ e x ∈ A.1 :=
  ValuationSubring.mem_comap

/-- The action of the conjugation `g ↦ e⁻¹ g e` on an element of `K'`, written out: the
conjugate of `g : Gal(Ω/K)` acts on `K'` as `e.symm ∘ g ∘ e`. -/
lemma algEquivConjHom_apply (g : Gal(Ω/K)) (x : K') :
    algEquivConjHom e.symm g x = e.symm (g (e x)) := by
  simp [algEquivConjHom, AlgEquiv.trans_apply]

/-- The inverse of the conjugate acts as `e.symm ∘ g.symm ∘ e`. -/
lemma algEquivConjHom_inv_apply (g : Gal(Ω/K)) (x : K') :
    (algEquivConjHom e.symm g)⁻¹ x = e.symm (g.symm (e x)) := by
  have h : (algEquivConjHom e.symm g)⁻¹ = (algEquivConjHom e.symm g).symm := rfl
  rw [h]
  apply (algEquivConjHom e.symm g).injective
  rw [AlgEquiv.apply_symm_apply, algEquivConjHom_apply]
  simp

/-- **Galois equivariance of the place bijection**: the conjugating isomorphism
`algEquivConjHom e.symm : Gal(Ω/K) →* Gal(K'/K)` intertwines the actions on the two place
systems. -/
lemma placeCongr_smul (A : FinitePlaceOf K Ω) (g : Gal(Ω/K)) :
    placeCongr e (placeSmul g A) = placeSmul (algEquivConjHom e.symm g) (placeCongr e A) := by
  apply Subtype.ext
  show ((g • A.1).comap (e : K' →+* Ω)) = ((algEquivConjHom e.symm g) • (placeCongr e A).1)
  rw [show (placeCongr e A).1 = A.1.comap (e : K' →+* Ω) from rfl]
  apply ValuationSubring.ext
  intro x
  simp only [ValuationSubring.mem_comap, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
    AlgEquiv.smul_def]
  rw [algEquivConjHom_inv_apply]
  simp

/-! ## Decomposition groups -/

/-- The `K`-algebra isomorphism `e`, viewed as a ring isomorphism `K' ≃+* Ω`, maps the embedded
copy of `K` onto the embedded copy of `K` (`MapsBase`). -/
lemma mapsBase_algEquiv :
    Submission.NeukirchUchida.MapsBase (algebraMap K Ω) (algebraMap K K') (e : K' ≃+* Ω) := by
  show (algebraMap K K').range.map (e : K' →+* Ω) = (algebraMap K Ω).range
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨a, rfl⟩ := hy
    exact ⟨a, (e.commutes a).symm⟩
  · rintro ⟨a, rfl⟩
    exact ⟨algebraMap K K' a, ⟨a, rfl⟩, e.commutes a⟩

/-- The conjugation isomorphism `conjHomEquiv` of `e` is `algEquivConjHom e.symm`. -/
lemma conjHomEquiv_eq_conjHom :
    (Submission.NeukirchUchida.conjHomEquiv (mapsBase_algEquiv e) : Gal(Ω/K) →* Gal(K'/K))
      = algEquivConjHom e.symm := by
  ext g x
  show Submission.NeukirchUchida.conj (mapsBase_algEquiv e) g x = algEquivConjHom e.symm g x
  rw [Submission.NeukirchUchida.conj_apply, algEquivConjHom_apply]
  rfl

/-- **Compatibility of the place bijection with decomposition groups**: the decomposition group
of the transported place is the image of the decomposition group under the conjugating
isomorphism `algEquivConjHom e.symm`. -/
lemma placeCongr_decomp (A : FinitePlaceOf K Ω) :
    Submission.NeukirchUchida.decompositionGroup (K₁ := K) (K₁' := K') (placeCongr e A).1 =
      (Submission.NeukirchUchida.decompositionGroup (K₁ := K) (K₁' := Ω) A.1).map
        (algEquivConjHom e.symm) := by
  have h := NK.Reconstruct.map_conjHomEquiv_decompositionGroup (K₁ := K) (K₂ := K) (K₁' := Ω)
    (K₂' := K') (mapsBase_algEquiv e) A.1
  rw [show (↑(Submission.NeukirchUchida.conjHomEquiv (mapsBase_algEquiv e)) :
        Gal(Ω/K) →* Gal(K'/K)) = algEquivConjHom e.symm
      from conjHomEquiv_eq_conjHom e] at h
  exact h.symm

end PlaceCongr

theorem exists_placeCongr {K : Type*} [Field K] [NumberField K] {K' : Type*} [Field K']
    {Ω : Type*} [Field Ω] [Algebra K K'] [Algebra K Ω] [IsSepClosure K K'] [IsSepClosure K Ω]
    (e : K' ≃ₐ[K] Ω) :
    ∃ F : FinitePlaceOf K Ω ≃ FinitePlaceOf K K',
      (∀ (A : FinitePlaceOf K Ω) (x : K'), x ∈ (F A).1 ↔ e x ∈ A.1) ∧
      (∀ (A : FinitePlaceOf K Ω) (g : Gal(Ω/K)),
        F (placeSmul g A) = placeSmul (algEquivConjHom e.symm g) (F A)) ∧
      (∀ A : FinitePlaceOf K Ω,
        Submission.NeukirchUchida.decompositionGroup (K₁ := K) (K₁' := K') (F A).1 =
          (Submission.NeukirchUchida.decompositionGroup (K₁ := K) (K₁' := Ω) A.1).map
            (algEquivConjHom e.symm)) :=
  ⟨placeCongr e, fun A x => placeCongr_mem e A x, fun A g => placeCongr_smul e A g,
    fun A => placeCongr_decomp e A⟩

end NK.Reconstruct
