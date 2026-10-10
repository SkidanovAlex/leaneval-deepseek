import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.GroupTheory.Abelianization.Finite
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.Separation.Lemmas
import Submission.NK.Reconstruct.LevelMap
import Submission.NK.Reconstruct.denseRange_galToGamma
import Submission.NK.Reconstruct.galToGamma_continuous
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The isomorphism `Γ_{K₁} ≃* Γ_{K₂}` induced by a homeomorphic isomorphism `ϕ` of absolute Galois
groups, and its compatibility with `galToGamma`

Let `K₁`, `K₂` be number fields with separable closures `K₁'`, `K₂'`, and let
`ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)` be a homeomorphic isomorphism of the absolute Galois groups.
Shimizu's `Γ_K = Gamma K K' ℓ` (`NK.Reconstruct.Gamma`) is the projective limit of the ℓ-primary
parts of the abelianisations of the finite normal levels of `K'/K`, and
`galToGamma ℓ : Gal(K'/K) →* Γ_K` (`NK.Reconstruct.galToGamma`) is the canonical map sending an
automorphism to the coherent family of the ℓ-primary components of its restrictions.

This file constructs the isomorphism `e : Γ_{K₁} ≃* Γ_{K₂}` induced by `ϕ`, characterised by

  `e (galToGamma g) = galToGamma (ϕ g)`

for every `g : Gal(K₁'/K₁)` (and dually for `ϕ.symm`).  It is item (3) of the infrastructure listed
in `Submission/Work/Reconstruct/README.md` §17.1: the isomorphism of the projective systems
`L ↦ ℓ-part(Gal(L/K₁)^{ab})` and `N ↦ ℓ-part(Gal(N/K₂)^{ab})` induced by the Galois
correspondence of `ϕ` (`NK.Reconstruct.levelMap`, `NK.Reconstruct.levelMapEquiv`).

## The route

The map is *not* built level by level — a levelwise construction would force one to transport
elements of ℓ-primary parts along equalities of intermediate fields.  Instead:

* `galToGamma ℓ` is **surjective** (`galToGamma_surjective`): its range is dense
  (`NK.Reconstruct.denseRange_galToGamma`) and compact, hence closed, hence everything.
  Consequently a homomorphism out of `Γ_K` is determined by its values on the image of
  `galToGamma ℓ`, and can be produced by descending through the first isomorphism theorem
  (`MonoidHom.liftOfSurjective`).
* The only input needed is that `ϕ` carries `ker (galToGamma ℓ)` into `ker (galToGamma ℓ)`
  (`ker_galToGamma_le`), i.e. that the vanishing of the ℓ-primary components of the restrictions of
  `g` is equivalent to the same statement for `ϕ g`.  This is `levelComponent_levelImage`: the
  level isomorphism `Gal(L/K₁) → Gal(levelMap ϕ L/K₂)` of the correspondence of `ϕ` sends `g|_L` to
  `(ϕ g)|_{levelMap ϕ L}` (`levelMapEquiv_restrictNormalHom'`), so it identifies the kernels of the
  ℓ-primary projections.

## References

J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, Ch. X §10.3, Ch. XII;
S. Shimizu, *On the Neukirch–Uchida theorem for small sets of primes*, arXiv:2009.10431, §4.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

namespace NK.Reconstruct

/-! ## Surjectivity of `galToGamma` -/

section Surjective

variable {K : Type*} [Field K] [NumberField K] {K' : Type*} [Field K'] [Algebra K K']
  [IsGalois K K']

/-- **The canonical map `G_K → Γ_K` is surjective.**  Its range is dense
(`NK.Reconstruct.denseRange_galToGamma`) and compact — the image of the compact group
`Gal(K'/K)` under the continuous map `galToGamma ℓ` — hence closed; a dense closed subset of a
topological space is everything. -/
theorem galToGamma_surjective (ℓ : ℕ) :
    Function.Surjective ⇑(galToGamma (K := K) (K' := K') ℓ) := by
  have hclosed : IsClosed (Set.range ⇑(galToGamma (K := K) (K' := K') ℓ)) :=
    (isCompact_range (galToGamma_continuous (K := K) (K' := K') ℓ)).isClosed
  have hdense : closure (Set.range ⇑(galToGamma (K := K) (K' := K') ℓ)) = Set.univ :=
    (denseRange_iff_closure_range).mp (denseRange_galToGamma (K := K) (K' := K') ℓ)
  refine Set.range_eq_univ.mp ?_
  rw [← hclosed.closure_eq]
  exact hdense

end Surjective

/-! ## The correspondence of finite levels induced by `ϕ` -/

section Transport

variable {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [NumberField K₁] [Field K₂] [NumberField K₂]
  [Field K₁'] [Field K₂'] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

/-- **The image of a finite normal level under the correspondence of `ϕ`**, with the `FrobLevel`
structure induced by `NK.Reconstruct.finiteDimensional_levelMap`,
`NK.Reconstruct.normal_levelMap` and `NK.Reconstruct.numberField_levelMap`. -/
noncomputable def levelImage (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ)
    (L : FrobLevel K₁ K₁') : FrobLevel K₂ K₂' where
  L := levelMap ϕ L.L
  finite := finiteDimensional_levelMap hϕ L.L
  normal := normal_levelMap hϕ L.L
  numberField := numberField_levelMap hϕ L.L

/-- **The preimage of a finite normal level under the correspondence of `ϕ`** (the image under
`ϕ.symm`). -/
noncomputable def levelPreimage (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ)
    (N : FrobLevel K₂ K₂') : FrobLevel K₁ K₁' where
  L := levelMap ϕ.symm N.L
  finite := finiteDimensional_levelMap (Submission.NeukirchUchida.isHomeomorph_symm ϕ hϕ) N.L
  normal := normal_levelMap (Submission.NeukirchUchida.isHomeomorph_symm ϕ hϕ) N.L
  numberField := numberField_levelMap (Submission.NeukirchUchida.isHomeomorph_symm ϕ hϕ) N.L

/-- **The round trip of the level correspondence**: `levelMap ϕ (levelMap ϕ.symm M) = M` for a
finite level `M ⊆ K₂'`.  Both maps are the fixed-field correspondence, and on finite levels the
`fixingSubgroup`/`fixedField` adjunction is an equivalence
(`InfiniteGalois.fixedField_fixingSubgroup`). -/
theorem levelMap_levelMap_symm' (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ)
    (M : IntermediateField K₂ K₂') [FiniteDimensional K₂ M] :
    levelMap ϕ (levelMap ϕ.symm M) = M := by
  haveI : IsGalois K₂ K₂' := IsSepClosure.isGalois
  have hsymm : IsHomeomorph (ϕ.symm : Gal(K₂'/K₂) → Gal(K₁'/K₁)) :=
    Submission.NeukirchUchida.isHomeomorph_symm ϕ hϕ
  rw [levelMap, fixingSubgroup_levelMap hsymm M, Subgroup.map_map]
  have hcomp : ((ϕ : Gal(K₁'/K₁) →* Gal(K₂'/K₂)).comp (ϕ.symm : Gal(K₂'/K₂) →* Gal(K₁'/K₁)))
      = MonoidHom.id _ := by
    ext g x
    simp
  rw [hcomp, Subgroup.map_id]
  exact InfiniteGalois.fixedField_fixingSubgroup M

/-- **`levelMapEquiv` is the restriction of `ϕ`**: for a finite normal level `L ⊆ K₁'` and
`g : Gal(K₁'/K₁)`, the element of `Gal(↥(levelMap ϕ L)/K₂)` attached by the Galois correspondence
to the restriction of `g` to `L` is the restriction of `ϕ g` to `levelMap ϕ L`. -/
theorem levelMapEquiv_restrictNormalHom' (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ)
    (L : IntermediateField K₁ K₁') [FiniteDimensional K₁ L] [Normal K₁ L] [NumberField ↥L]
    [FiniteDimensional K₂ (levelMap ϕ L)]
    [Normal K₂ (levelMap ϕ L)]
    [NumberField ↥(levelMap ϕ L)]
    (g : Gal(K₁'/K₁)) :
    levelMapEquiv hϕ L (AlgEquiv.restrictNormalHom L g) =
      AlgEquiv.restrictNormalHom (levelMap ϕ L) (ϕ g) := by
  have h1 : (AlgEquiv.restrictNormalHom L) g = (quotientEquivOfLevel L) (QuotientGroup.mk g) := rfl
  rw [levelMapEquiv, MulEquiv.trans_apply, h1, MulEquiv.symm_apply_apply, MulEquiv.trans_apply,
    QuotientGroup.congr_mk]
  rfl

/-- **The ℓ-primary part of a homomorphic image**: a homomorphism of finite abelian groups carries
elements with ℓ-coprime order to elements with ℓ-coprime order, hence trivial ℓ-primary
components to trivial ℓ-primary components. -/
theorem ellComp_map_eq_one {A B : Type*} [CommGroup A] [Finite A] [CommGroup B] [Finite B]
    (ℓ : ℕ) (f : A →* B) {x : A} (hx : ellComp ℓ x = 1) : ellComp ℓ (f x) = 1 := by
  have h1 : EllCoprimeRel ℓ x 1 := by
    have h := ellCoprimeRel_ellComp (A := A) ℓ x
    rw [hx] at h
    simpa using h
  have h2 : EllCoprimeRel ℓ (f x) 1 := by
    have h := ellCoprimeRel_map f h1
    simpa using h
  exact (eq_ellComp_of_ellCoprimeRel (x := f x) (y := 1) h2).symm

/-- **The ℓ-primary component at the image level is the ℓ-primary component at the level.**  If the
ℓ-primary component of `g` at the level `L/K₁` is trivial, then so is the ℓ-primary component of
`ϕ g` at the image level `levelMap ϕ L`. -/
theorem levelComponent_levelImage (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ) (ℓ : ℕ)
    (L : FrobLevel K₁ K₁') (g : Gal(K₁'/K₁)) (hg : levelComponent ℓ L g = 1) :
    levelComponent ℓ (levelImage ϕ hϕ L) (ϕ g) = 1 := by
  haveI : FiniteDimensional K₂ (levelMap ϕ L.L) := finiteDimensional_levelMap hϕ L.L
  haveI : Normal K₂ (levelMap ϕ L.L) := normal_levelMap hϕ L.L
  haveI : NumberField ↥(levelMap ϕ L.L) := numberField_levelMap hϕ L.L
  have hnat : levelMapEquiv hϕ L.L (AlgEquiv.restrictNormalHom L.L g) =
      AlgEquiv.restrictNormalHom (levelMap ϕ L.L) (ϕ g) :=
    levelMapEquiv_restrictNormalHom' ϕ hϕ L.L g
  have key : Abelianization.of (AlgEquiv.restrictNormalHom (levelMap ϕ L.L) (ϕ g)) =
      Abelianization.map (levelMapEquiv hϕ L.L)
        (Abelianization.of (AlgEquiv.restrictNormalHom L.L g)) := by
    rw [Abelianization.map_of]
    exact congrArg Abelianization.of hnat.symm
  show ellComp ℓ (Abelianization.of (AlgEquiv.restrictNormalHom (levelMap ϕ L.L) (ϕ g))) = 1
  rw [key]
  exact ellComp_map_eq_one ℓ (Abelianization.map (levelMapEquiv hϕ L.L).toMonoidHom) hg

end Transport

/-! ## The kernel of `galToGamma` is respected by `ϕ` -/

section Kernel

variable {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [NumberField K₁] [Field K₂] [NumberField K₂]
  [Field K₁'] [Field K₂'] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

/-- **`ϕ` carries the kernel of `galToGamma ℓ` into the kernel of `galToGamma ℓ`.**

Indeed `galToGamma ℓ g = 1` iff the ℓ-primary component `levelComponent ℓ L g` vanishes at every
finite normal level `L`; and at the image level `levelMap ϕ L` the correspondence
`levelMapEquiv hϕ L` identifies `g|_L` with `(ϕ g)|_{levelMap ϕ L}`
(`levelMapEquiv_restrictNormalHom'`), so the ℓ-primary component of `ϕ g` there vanishes too
(`levelComponent_levelImage`).  A general level `N ⊆ K₂'` is contained in the image of
`levelMap ϕ.symm N` (`levelMap_levelMap_symm'`), and the transition maps `ellRestrict` send `1` to
`1`. -/
theorem ker_galToGamma_le (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ) (ℓ : ℕ) :
    (galToGamma (K := K₁) (K' := K₁') ℓ).ker ≤
      (galToGamma (K := K₂) (K' := K₂') ℓ).ker.comap ϕ := by
  haveI : IsGalois K₁ K₁' := IsSepClosure.isGalois
  haveI : IsGalois K₂ K₂' := IsSepClosure.isGalois
  intro g hg
  rw [MonoidHom.mem_ker] at hg
  rw [Subgroup.mem_comap, MonoidHom.mem_ker]
  refine Gamma.ext (fun N => ?_)
  rw [galToGamma_proj, map_one]
  let L : FrobLevel K₁ K₁' := levelPreimage ϕ hϕ N
  have hL1 : levelComponent ℓ L g = 1 := by
    rw [← galToGamma_proj (K := K₁) (K' := K₁') ℓ L g, hg, map_one]
  have himg : levelComponent ℓ (levelImage ϕ hϕ L) (ϕ g) = 1 :=
    levelComponent_levelImage ϕ hϕ ℓ L g hL1
  have hfield : (levelImage ϕ hϕ L).L = N.L := levelMap_levelMap_symm' ϕ hϕ N.L
  have hcompat : ellRestrict ℓ N (levelImage ϕ hϕ L) hfield.symm.le
      (levelComponent ℓ (levelImage ϕ hϕ L) (ϕ g)) = levelComponent ℓ N (ϕ g) :=
    (levelComponent_compatible ℓ (ϕ g)) N (levelImage ϕ hϕ L) hfield.symm.le
  rw [himg, map_one] at hcompat
  exact hcompat.symm

end Kernel

/-! ## The isomorphism `Γ_{K₁} ≃* Γ_{K₂}` -/

section GammaEquiv

variable {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [NumberField K₁] [Field K₂] [NumberField K₂]
  [Field K₁'] [Field K₂'] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

theorem exists_gammaEquivOfPhi {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [NumberField K₁] [Field K₂]
    [NumberField K₂] [Field K₁'] [Field K₂'] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂'] (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂))
    (hϕ : IsHomeomorph ϕ) (ℓ : ℕ) :
    ∃ e : Gamma K₁ K₁' ℓ ≃* Gamma K₂ K₂' ℓ,
      (∀ g : Gal(K₁'/K₁),
        e (galToGamma (K := K₁) (K' := K₁') ℓ g)
          = galToGamma (K := K₂) (K' := K₂') ℓ (ϕ g)) ∧
      (∀ g : Gal(K₂'/K₂),
        e.symm (galToGamma (K := K₂) (K' := K₂') ℓ g)
          = galToGamma (K := K₁) (K' := K₁') ℓ (ϕ.symm g)) := by
  classical
  haveI : IsGalois K₁ K₁' := IsSepClosure.isGalois
  haveI : IsGalois K₂ K₂' := IsSepClosure.isGalois
  have hsurj₁ : Function.Surjective ⇑(galToGamma (K := K₁) (K' := K₁') ℓ) :=
    galToGamma_surjective ℓ
  have hsurj₂ : Function.Surjective ⇑(galToGamma (K := K₂) (K' := K₂') ℓ) :=
    galToGamma_surjective ℓ
  have hker₁ : (galToGamma (K := K₁) (K' := K₁') ℓ).ker ≤
      ((galToGamma (K := K₂) (K' := K₂') ℓ).comp ϕ).ker :=
    ker_galToGamma_le (K₁ := K₁) (K₂ := K₂) (K₁' := K₁') (K₂' := K₂') ϕ hϕ ℓ
  have hker₂ : (galToGamma (K := K₂) (K' := K₂') ℓ).ker ≤
      ((galToGamma (K := K₁) (K' := K₁') ℓ).comp ϕ.symm).ker :=
    ker_galToGamma_le (K₁ := K₂) (K₂ := K₁) (K₁' := K₂') (K₂' := K₁') ϕ.symm
      (Submission.NeukirchUchida.isHomeomorph_symm ϕ hϕ) ℓ
  let Φ : Gamma K₁ K₁' ℓ →* Gamma K₂ K₂' ℓ :=
    MonoidHom.liftOfSurjective (f := galToGamma (K := K₁) (K' := K₁') ℓ) hsurj₁
      ⟨(galToGamma (K := K₂) (K' := K₂') ℓ).comp ϕ, hker₁⟩
  let Ψ : Gamma K₂ K₂' ℓ →* Gamma K₁ K₁' ℓ :=
    MonoidHom.liftOfSurjective (f := galToGamma (K := K₂) (K' := K₂') ℓ) hsurj₂
      ⟨(galToGamma (K := K₁) (K' := K₁') ℓ).comp ϕ.symm, hker₂⟩
  have hΦ : ∀ g : Gal(K₁'/K₁),
      Φ (galToGamma (K := K₁) (K' := K₁') ℓ g) = galToGamma (K := K₂) (K' := K₂') ℓ (ϕ g) := by
    intro g
    exact MonoidHom.liftOfRightInverse_comp_apply
      (f := galToGamma (K := K₁) (K' := K₁') ℓ)
      (f_inv := Function.surjInv hsurj₁)
      (Function.rightInverse_surjInv hsurj₁)
      ⟨(galToGamma (K := K₂) (K' := K₂') ℓ).comp ϕ, hker₁⟩ g
  have hΨ : ∀ g : Gal(K₂'/K₂),
      Ψ (galToGamma (K := K₂) (K' := K₂') ℓ g) = galToGamma (K := K₁) (K' := K₁') ℓ (ϕ.symm g) := by
    intro g
    exact MonoidHom.liftOfRightInverse_comp_apply
      (f := galToGamma (K := K₂) (K' := K₂') ℓ)
      (f_inv := Function.surjInv hsurj₂)
      (Function.rightInverse_surjInv hsurj₂)
      ⟨(galToGamma (K := K₁) (K' := K₁') ℓ).comp ϕ.symm, hker₂⟩ g
  have hcomp₁ : Φ.comp Ψ = MonoidHom.id (Gamma K₂ K₂' ℓ) := by
    refine MonoidHom.ext (fun x => ?_)
    obtain ⟨g, hg⟩ := hsurj₂ x
    rw [← hg, MonoidHom.comp_apply, hΨ g, hΦ (ϕ.symm g), MulEquiv.apply_symm_apply,
      MonoidHom.id_apply]
  have hcomp₂ : Ψ.comp Φ = MonoidHom.id (Gamma K₁ K₁' ℓ) := by
    refine MonoidHom.ext (fun x => ?_)
    obtain ⟨g, hg⟩ := hsurj₁ x
    rw [← hg, MonoidHom.comp_apply, hΦ g, hΨ (ϕ g), MulEquiv.symm_apply_apply,
      MonoidHom.id_apply]
  let e : Gamma K₁ K₁' ℓ ≃* Gamma K₂ K₂' ℓ :=
    { toFun := Φ
      invFun := Ψ
      left_inv := fun x => by
        have h := DFunLike.congr_fun hcomp₂ x
        simpa using h
      right_inv := fun x => by
        have h := DFunLike.congr_fun hcomp₁ x
        simpa using h
      map_mul' := Φ.map_mul }
  refine ⟨e, ?_, ?_⟩
  · intro g
    show Φ (galToGamma (K := K₁) (K' := K₁') ℓ g) = galToGamma (K := K₂) (K' := K₂') ℓ (ϕ g)
    exact hΦ g
  · intro g
    have h : e (galToGamma (K := K₁) (K' := K₁') ℓ (ϕ.symm g))
        = galToGamma (K := K₂) (K' := K₂') ℓ g := by
      have h' := hΦ (ϕ.symm g)
      rw [MulEquiv.apply_symm_apply] at h'
      show Φ (galToGamma (K := K₁) (K' := K₁') ℓ (ϕ.symm g))
        = galToGamma (K := K₂) (K' := K₂') ℓ g
      exact h'
    rw [← h, MulEquiv.symm_apply_apply]

end GammaEquiv

end NK.Reconstruct
