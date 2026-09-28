import Mathlib
import Submission.Work.Cohomology.dualZ
import Submission.Work.Cohomology.dualZSplitExact
import Submission.Work.Cohomology.isIso_homologyMap_tau1
import Submission.Work.Cohomology.smallChainsHomotopyEquivInt
import Submission.Work.Cohomology.isIso_homologyMap_dualZMap
import Submission.Work.Cohomology.coker_smallOfU_iso_relChains
import Submission.Work.Cohomology.excisionAux
import Submission.Work.Cohomology.relCochain_shortExact

/-!
# Excision for the `ℤ`-dual (into `R`) of the relative chain complexes

Let `X` be a topological space, `A, Z ⊆ X` with `closure Z ⊆ interior A`, and let `V = X \ Z`.
The inclusion of pairs `(V, A ∩ V) ↪ (X, A)` is an excision, i.e. it induces an isomorphism
`H_*(X, A) ≅ H_*(V, A ∩ V)` (`Work.Cohomology.excision`).  This file proves the corresponding
statement for the **cohomology of the `ℤ`-dual complexes** `dualZ R C = Hom_ℤ(C_•, R)`
(`Submission/Work/Cohomology/dualZ.lean`):

`H^n(Hom_ℤ(C_*(X,A), R)) ≅ H^n(Hom_ℤ(C_*(V, A ∩ V), R))`.

This is the remaining ingredient (beyond `relComplexIsoDualZ`) for the cohomological excision
theorem `Work.Cohomology.cohomologicalExcision`.

## The argument

The same two short exact sequences of `ℤ`-chain complexes as in
`Submission/Work/Cohomology/excisionAux.lean` are used:

`S₁ : 0 ⟶ C_*(A) --smallOfU A V--> C^{A,V}_*(X) ⟶ coker --> 0`,
`S₂ : 0 → C_*(A) --inclChains X A--> C_*(X) ⟶ C_*(X,A) ⟶ 0`,

together with the morphism `φ : S₁ ⟶ S₂` with components `𝟙`, `smallToSing A V` and the induced
map `τ` on the cokernels.  Both sequences are degreewise split (`IsDegreewiseSplit`), and
`smallToSing A V` is a chain homotopy equivalence because `interior A ∪ interior V = univ`
(`Work.Cohomology.smallChainsHomotopyEquivInt`).

Applying `dualZ` (contravariantly) turns this into a morphism `θ : dualZShort R S₂ ⟶ dualZShort R S₁`
of short exact sequences of cochain complexes of `R`-modules
(`Work.Cohomology.dualZSplitExact` for the exactness) whose middle and third components are
isomorphisms on cohomology (`Work.Cohomology.isIso_homologyMap_dualZMap` and the identity).  The
five lemma in the `τ₁` direction (`Work.Cohomology.isIso_homologyMap_tau1`, a statement missing
from Mathlib) then shows that `θ.τ₁ = dualZ(τ)`, i.e. the map
`H^n(Hom_ℤ(C_*(X,A), R)) ⟶ H^n(Hom_ℤ(coker (smallOfU A V), R))`, is an isomorphism, and the
identification `coker (smallOfU A V) ≅ C_*(V, A ∩ V)` of
`Work.Cohomology.coker_smallOfU_iso_relChains` finishes the proof.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology
noncomputable section

variable (R : Type) [CommRing R]

/-- degreewise splitting of the pair sequence -/
theorem isDegreewiseSplit_pair (X : TopCat) (A : Set X) :
    IsDegreewiseSplit (hPairShort X A) := by
  intro n
  refine ⟨chainRetract ℤ X A n, ?_⟩
  show (inclChains X A).f n ≫ chainRetract ℤ X A n = 𝟙 _
  rw [inclChains, chainMap]
  exact chainRetract_spec ℤ X A n

theorem isDegreewiseSplit_small (X : TopCat) (A V : Set X) :
    IsDegreewiseSplit (ShortComplex.mk (smallOfU A V) (cokernel.π (smallOfU A V))
      (cokernel.condition _)) := by
  intro n
  refine ⟨(smallToSing A V).f n ≫ chainRetract ℤ X A n, ?_⟩
  show (smallOfU A V).f n ≫ ((smallToSing A V).f n ≫ chainRetract ℤ X A n) = 𝟙 _
  rw [← Category.assoc, ← HomologicalComplex.comp_f, smallOfU_comp_smallToSing]
  rw [inclChains, chainMap]
  exact chainRetract_spec ℤ X A n


/-- The `ℤ`-dual of an isomorphism of `ℤ`-chain complexes. -/
def dualZIsoOfIso {C D : ChainComplex (ModuleCat ℤ) ℕ} (e : C ≅ D) : dualZ R C ≅ dualZ R D :=
  ⟨dualZMap R D C e.inv, dualZMap R C D e.hom,
    (by rw [← dualZMap_comp, e.hom_inv_id, dualZMap_id]),
    (by rw [← dualZMap_comp, e.inv_hom_id, dualZMap_id])⟩

set_option maxHeartbeats 3200000 in
theorem dualZ_excision (X : TopCat) (A Z : Set X) (hZ : closure Z ⊆ interior A) (n : ℕ) :
    Nonempty ((dualZ R (relChains X A)).homology n ≅
      (dualZ R (relChains (TopCat.of {y : X | y ∉ Z})
        {y : {y : X | y ∉ Z} | (y : X) ∈ A})).homology n) := by
  set V : Set X := {y : X | y ∉ Z} with hVdef
  have hcov : interior A ∪ interior V = Set.univ := by
    rw [hVdef]; exact univ_eq_interior_union_compl A Z hZ
  -- the two chain-level short exact sequences
  let S₁ : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) :=
    ShortComplex.mk (smallOfU A V) (cokernel.π (smallOfU A V)) (cokernel.condition _)
  have hS₁ : S₁.ShortExact := ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel _)
    (mono_smallOfU A V) inferInstance
  have hs₁ : IsDegreewiseSplit S₁ := isDegreewiseSplit_small X A V
  let S₂ : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) := hPairShort X A
  have hS₂ : S₂.ShortExact := hPairShort_shortExact X A
  have hs₂ : IsDegreewiseSplit S₂ := isDegreewiseSplit_pair X A
  -- the morphism of short exact sequences `S₁ ⟶ S₂`
  have hcomm1 : (𝟙 (singularChains ℤ (TopCat.of A))) ≫ S₂.f = S₁.f ≫ smallToSing A V := by
    show inclChains X A = smallOfU A V ≫ smallToSing A V
    rw [smallOfU_comp_smallToSing]
  have hzero : smallOfU A V ≫ (smallToSing A V ≫ cokernel.π (inclChains X A)) = 0 := by
    rw [← Category.assoc, smallOfU_comp_smallToSing, cokernel.condition]
  let τ : cokernel (smallOfU A V) ⟶ relChains X A :=
    cokernel.desc (smallOfU A V) (smallToSing A V ≫ cokernel.π (inclChains X A)) hzero
  have hcomm2 : smallToSing A V ≫ S₂.g = S₁.g ≫ τ := by
    show smallToSing A V ≫ cokernel.π (inclChains X A) = cokernel.π (smallOfU A V) ≫ τ
    rw [show τ = cokernel.desc (smallOfU A V)
      (smallToSing A V ≫ cokernel.π (inclChains X A)) hzero from rfl]
    rw [cokernel.π_desc]
  let φ : S₁ ⟶ S₂ := ShortComplex.homMk (𝟙 _) (smallToSing A V) τ hcomm1 hcomm2
  -- the dualised short exact sequences and the dualised morphism
  have hT₁ : (dualZShort R S₁).ShortExact := dualZSplitExact R hS₁ hs₁
  have hT₂ : (dualZShort R S₂).ShortExact := dualZSplitExact R hS₂ hs₂
  let θ : dualZShort R S₂ ⟶ dualZShort R S₁ :=
    ShortComplex.homMk (dualZMap R S₁.X₃ S₂.X₃ τ)
      (dualZMap R S₁.X₂ S₂.X₂ (smallToSing A V)) (dualZMap R S₁.X₁ S₂.X₁ (𝟙 _))
      (by
        show dualZMap R S₁.X₃ S₂.X₃ τ ≫ dualZMap R S₁.X₂ S₁.X₃ S₁.g
          = dualZMap R S₂.X₂ S₂.X₃ S₂.g ≫ dualZMap R S₁.X₂ S₂.X₂ (smallToSing A V)
        rw [← dualZMap_comp, ← dualZMap_comp, hcomm2])
      (by
        show dualZMap R S₁.X₂ S₂.X₂ (smallToSing A V) ≫ dualZMap R S₁.X₁ S₁.X₂ S₁.f
          = dualZMap R S₂.X₁ S₂.X₂ S₂.f ≫ dualZMap R S₁.X₁ S₂.X₁ (𝟙 _)
        rw [← dualZMap_comp, ← dualZMap_comp, hcomm1])
  have hθ₂ : ∀ m, IsIso (HomologicalComplex.homologyMap θ.τ₂ m) := by
    intro m
    have h2 : θ.τ₂ = dualZMap R S₁.X₂ S₂.X₂ (smallToSing A V) := rfl
    rw [h2]
    obtain ⟨e, he⟩ := smallChainsHomotopyEquivInt (X := X) A V hcov
    rw [← he]
    exact isIso_homologyMap_dualZMap R e m
  have hθ₃ : ∀ m, IsIso (HomologicalComplex.homologyMap θ.τ₃ m) := by
    intro m
    haveI : IsIso θ.τ₃ := by
      rw [show θ.τ₃ = dualZMap R S₁.X₁ S₁.X₁ (𝟙 S₁.X₁) from rfl, dualZMap_id]
      exact IsIso.id _
    exact Functor.map_isIso (HomologicalComplex.homologyFunctor (ModuleCat R)
      (ComplexShape.up ℕ) m) θ.τ₃
  have hθ₁ : ∀ m, IsIso (HomologicalComplex.homologyMap θ.τ₁ m) :=
    isIso_homologyMap_tau1 R θ hT₂ hT₁ hθ₂ hθ₃
  haveI : IsIso (HomologicalComplex.homologyMap (dualZMap R S₁.X₃ S₂.X₃ τ) n) := by
    rw [← show θ.τ₁ = dualZMap R S₁.X₃ S₂.X₃ τ from rfl]
    exact hθ₁ n
  -- the identification of the cokernel with the relative chains of `(V, A ∩ V)`
  obtain ⟨e₀⟩ := coker_smallOfU_iso_relChains X A V
  exact ⟨(asIso (HomologicalComplex.homologyMap (dualZMap R S₁.X₃ S₂.X₃ τ) n)).trans
    ((HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℕ) n).mapIso
      (dualZIsoOfIso R e₀))⟩



end

end Work.Cohomology
