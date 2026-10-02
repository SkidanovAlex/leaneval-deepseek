import Mathlib
import Submission.Work.Cohomology.pd_plumbing
import Submission.Work.Cohomology.pd_good

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Vocabulary for the gluing of the `Good` framework

The definitions below fix the vocabulary in which the (honest) Mayer–Vietoris interface used by the
gluing `Good U → Good V → Good (U∩V) → Good (U∪V)` is stated.  They are deliberately written in
terms of the *honest* relative cochain complexes `Work.Cohomology.relComplex` (not the small-chains
model), so that they can be compared with `Work.Cohomology.goodD` and
`Work.Cohomology.pd_goodD_incl`.

The inclusions of open sets are the maps `Work.Cohomology.pdIncl` of `pd_good.lean`, so that the
"subtype of a subtype" identifications never appear: every set is a subset of the ambient space.
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology

noncomputable section

/-- Morphisms of `ℤ`-modules, as a named type (so that statements can avoid the arrow notation). -/
abbrev pdMor (A B : ModuleCat ℤ) : Type := A ⟶ B

/-- Composition of `ℤ`-module morphisms. -/
abbrev pdComp {A B C : ModuleCat ℤ} (f : pdMor A B) (g : pdMor B C) : pdMor A C := f ≫ g

/-- Negation of a `ℤ`-module morphism. -/
abbrev pdNeg {A B : ModuleCat ℤ} (f : pdMor A B) : pdMor A B := -f

/-- The zero morphism of `ℤ`-modules. -/
abbrev pdZero (A B : ModuleCat ℤ) : pdMor A B := 0

/-- Exactness of a composable pair of `ℤ`-module morphisms. -/
abbrev pdExact {A B C : ModuleCat ℤ} (f : pdMor A B) (g : pdMor B C)
    (h : pdComp f g = pdZero A C) : Prop :=
  (CategoryTheory.ShortComplex.mk f g h).Exact

/-- The honest relative cohomology `H^k(X,A)`. -/
abbrev pdCoh (X : TopCat) (A : Set X) (k : ℕ) : ModuleCat ℤ := (relComplex ℤ X A).homology k

/-- The honest relative cohomology of the pair `(U, U∩A)`. -/
abbrev pdCohSub (X : TopCat) (A : Set X) (U : Set X) (k : ℕ) : ModuleCat ℤ :=
  (relComplex ℤ (TopCat.of U) {y : U | (y : X) ∈ A}).homology k

/-- The underlying point of `subtypeIncl`. -/
theorem coe_subtypeIncl (X : TopCat) (U : Set X) (y : U) :
    ((subtypeIncl X U) y : X) = (y : X) := rfl

/-- The underlying point of `pdIncl`. -/
theorem coe_pdIncl {M : TopCat} {W V : Set M} (hVW : V ⊆ W) (y : V) :
    ((pdIncl W V hVW) y : M) = (y : M) := rfl

/-- The map induced on relative cohomology by a map of pairs `(W, W∩A) ⟶ (U, U∩A)` (for `W ⊆ U`). -/
noncomputable def pdCohMap (X : TopCat) (A U W : Set X) (hWU : W ⊆ U) (k : ℕ) :
    pdCohSub X A U k ⟶ pdCohSub X A W k :=
  HomologicalComplex.homologyMap (relComplexMap ℤ (X₁ := TopCat.of W) (X₂ := TopCat.of U)
    {y : W | (y : X) ∈ A} {y : U | (y : X) ∈ A}
    (pdIncl U W hWU) (fun y hy => hy)) k

/-- The pullback of relative cohomology along the inclusion of pairs `(U, U∩A) → (X, A)`. -/
noncomputable def pdCohRes (X : TopCat) (A : Set X) (U : Set X) (k : ℕ) :
    pdCoh X A k ⟶ pdCohSub X A U k :=
  HomologicalComplex.homologyMap (relComplexMap ℤ (X₁ := TopCat.of U) (X₂ := X)
    {y : U | (y : X) ∈ A} A (subtypeIncl X U)
    (fun y hy => hy)) k

/-- `Kᶜ ⊆ (K ∩ L)ᶜ`. -/
theorem pdComplInterLeft {X : Type*} (K L : Set X) : Kᶜ ⊆ (K ∩ L)ᶜ := fun _ hx => fun h => hx h.1

/-- `Lᶜ ⊆ (K ∩ L)ᶜ`. -/
theorem pdComplInterRight {X : Type*} (K L : Set X) : Lᶜ ⊆ (K ∩ L)ᶜ := fun _ hx => fun h => hx h.2

/-- `(K ∪ L)ᶜ ⊆ Kᶜ`. -/
theorem pdComplUnionLeft {X : Type*} (K L : Set X) : (K ∪ L)ᶜ ⊆ Kᶜ := fun _ hx => fun h => hx (Or.inl h)

/-- `(K ∪ L)ᶜ ⊆ Lᶜ`. -/
theorem pdComplUnionRight {X : Type*} (K L : Set X) : (K ∪ L)ᶜ ⊆ Lᶜ := fun _ hx => fun h => hx (Or.inr h)

/-- The pullback of relative cohomology along an inclusion of the *excluded* sets `A ⊆ B`
(i.e. `(X,B) → (X,A)` as pairs). -/
noncomputable def pdCohExMap (X : TopCat) (A B : Set X) (hAB : A ⊆ B) (k : ℕ) :
    pdCoh X B k ⟶ pdCoh X A k :=
  HomologicalComplex.homologyMap (relComplexMap ℤ (X₁ := X) (X₂ := X) A B (𝟙 X)
    (fun x hx => hAB hx)) k

/-- The biproduct `H^k(X,A) ⊞ H^k(X,B)` of two relative cohomologies. -/
abbrev pdCohExBiprod (X : TopCat) (A B : Set X) (k : ℕ) : ModuleCat ℤ :=
  pdCoh X A k ⊞ pdCoh X B k

/-- The first projection of `pdCohExBiprod`. -/
noncomputable def pdCohExBiprodFst (X : TopCat) (A B : Set X) (k : ℕ) :
    pdCohExBiprod X A B k ⟶ pdCoh X A k := biprod.fst

/-- The second projection of `pdCohExBiprod`. -/
noncomputable def pdCohExBiprodSnd (X : TopCat) (A B : Set X) (k : ℕ) :
    pdCohExBiprod X A B k ⟶ pdCoh X B k := biprod.snd

/-- The first inclusion into `pdCohExBiprod`. -/
noncomputable def pdCohExBiprodInl (X : TopCat) (A B : Set X) (k : ℕ) :
    pdCoh X A k ⟶ pdCohExBiprod X A B k := biprod.inl

/-- The second inclusion into `pdCohExBiprod`. -/
noncomputable def pdCohExBiprodInr (X : TopCat) (A B : Set X) (k : ℕ) :
    pdCoh X B k ⟶ pdCohExBiprod X A B k := biprod.inr

/-- The biproduct of the relative cohomologies of the two pieces. -/
abbrev pdCohBiprod (X : TopCat) (A : Set X) (U V : Set X) (k : ℕ) : ModuleCat ℤ :=
  pdCohSub X A U k ⊞ pdCohSub X A V k

/-- The first projection of the biproduct of relative cohomologies. -/
noncomputable def pdCohBiprodFst (X : TopCat) (A : Set X) (U V : Set X) (k : ℕ) :
    pdCohBiprod X A U V k ⟶ pdCohSub X A U k := biprod.fst

/-- The second projection of the biproduct of relative cohomologies. -/
noncomputable def pdCohBiprodSnd (X : TopCat) (A : Set X) (U V : Set X) (k : ℕ) :
    pdCohBiprod X A U V k ⟶ pdCohSub X A V k := biprod.snd

/-- The first inclusion into the biproduct of relative cohomologies. -/
noncomputable def pdCohBiprodInl (X : TopCat) (A : Set X) (U V : Set X) (k : ℕ) :
    pdCohSub X A U k ⟶ pdCohBiprod X A U V k := biprod.inl

/-- The second inclusion into the biproduct of relative cohomologies. -/
noncomputable def pdCohBiprodInr (X : TopCat) (A : Set X) (U V : Set X) (k : ℕ) :
    pdCohSub X A V k ⟶ pdCohBiprod X A U V k := biprod.inr

/-- The singular homology of `X` in degree `m`. -/
abbrev pdHom (X : TopCat) (m : ℕ) : ModuleCat ℤ := (singularChains ℤ X).homology m

/-- The singular homology of the subspace `U` in degree `m`. -/
abbrev pdHomSub (X : TopCat) (U : Set X) (m : ℕ) : ModuleCat ℤ :=
  (singularChains ℤ (TopCat.of U)).homology m

/-- The singular homology of the intersection `U ∩ V` in degree `m`. -/
abbrev pdHomInter (X : TopCat) (U V : Set X) (m : ℕ) : ModuleCat ℤ :=
  (singularChains ℤ (TopCat.of ↥(U ∩ V))).homology m

/-- The biproduct of the singular homologies of the two pieces. -/
abbrev pdHomBiprod (X : TopCat) (U V : Set X) (m : ℕ) : ModuleCat ℤ :=
  pdHomSub X U m ⊞ pdHomSub X V m

/-- The first projection of the biproduct of the homologies of the two pieces. -/
noncomputable def pdHomBiprodFst (X : TopCat) (U V : Set X) (m : ℕ) :
    pdHomBiprod X U V m ⟶ pdHomSub X U m := biprod.fst

/-- The second projection of the biproduct of the homologies of the two pieces. -/
noncomputable def pdHomBiprodSnd (X : TopCat) (U V : Set X) (m : ℕ) :
    pdHomBiprod X U V m ⟶ pdHomSub X V m := biprod.snd

/-- The first inclusion into the biproduct of the homologies of the two pieces. -/
noncomputable def pdHomBiprodInl (X : TopCat) (U V : Set X) (m : ℕ) :
    pdHomSub X U m ⟶ pdHomBiprod X U V m := biprod.inl

/-- The second inclusion into the biproduct of the homologies of the two pieces. -/
noncomputable def pdHomBiprodInr (X : TopCat) (U V : Set X) (m : ℕ) :
    pdHomSub X V m ⟶ pdHomBiprod X U V m := biprod.inr

/-- The pushforward of singular homology along an inclusion of open sets. -/
noncomputable def pdHomMap (X : TopCat) (U W : Set X) (hWU : W ⊆ U) (m : ℕ) :
    pdHomSub X W m ⟶ pdHomSub X U m :=
  HomologicalComplex.homologyMap (chainMap ℤ (TopCat.of W) (TopCat.of U) (pdIncl U W hWU)) m

/-- The pushforward of singular homology along the inclusion `U ⊆ X`. -/
noncomputable def pdHomIncl (X : TopCat) (U : Set X) (m : ℕ) :
    pdHomSub X U m ⟶ pdHom X m :=
  HomologicalComplex.homologyMap (chainMap ℤ (TopCat.of U) X (subtypeIncl X U)) m

end

end Work.Cohomology
