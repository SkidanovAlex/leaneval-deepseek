import Mathlib
import Submission.Work.Thom.ATools
import Submission.Work.Thom.Pair
import Submission.Work.Thom.Ladder

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option linter.style.haveILetI false

open CategoryTheory

namespace Work.Thom

noncomputable section

/-- **The map of pairs `(X,A) → (Y,Cset)` on the short exact sequences of the pair.**  A map of
pairs, i.e. a continuous map `f : C(X,Y)` with `f '' A ⊆ Cset`, induces a morphism
`0 ⟶ C^*(Y,Cset) ⟶ C^*(Y) ⟶ C^*(Cset) ⟶ 0`
`↓          ↓          ↓          ↓`
`0 ⟶ C^*(X,A) ⟶ C^*(X) ⟶ C^*(A) ⟶ 0`
of short exact sequences of cochain complexes, whose three components are the pullbacks
`relComplexMap`, `dualChainMap f` and `dualChainMap (f|_A)` on the relative, absolute and subspace
cochains.  This is the ladder to which the naturality of the connecting homomorphism applies. -/
def pairDeltaShortMap {X Y : TopCat} (A : Set X) (Cset : Set Y) (f : X ⟶ Y)
    (hf : ∀ x ∈ A, (ConcreteCategory.hom f) x ∈ Cset) :
    Work.Cohomology.pairShort ℤ Y Cset ⟶ Work.Cohomology.pairShort ℤ X A :=
  { τ₁ := Work.Cohomology.relComplexMap ℤ A Cset f hf
    τ₂ := Work.Cohomology.dualChainMap ℤ X Y f
    τ₃ := Work.Cohomology.dualChainMap ℤ (TopCat.of A) (TopCat.of Cset)
      (Work.Cohomology.relMapSub A Cset f hf)
    comm₁₂ := by
      change Work.Cohomology.relComplexMap ℤ A Cset f hf ≫ Work.Cohomology.relIncl ℤ X A
        = Work.Cohomology.relIncl ℤ Y Cset ≫ Work.Cohomology.dualChainMap ℤ X Y f
      apply HomologicalComplex.hom_ext
      intro k
      rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
        Work.Cohomology.relComplexMap_f, Work.Cohomology.relIncl_f, Work.Cohomology.relIncl_f]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply]
      exact Work.Cohomology.relMapLM_coe ℤ A Cset f hf k x
    comm₂₃ := Work.Cohomology.dualChainMap_restr_comp ℤ A Cset f hf }

/-- Naturality of the connecting homomorphism `pairδC` of a pair under a map of pairs.  For a
continuous map `f : X → Y` carrying `A ⊆ X` into `C ⊆ Y`, and any `y ∈ H^n(C;ℤ)`, the pullback
along `f` of `pairδC C n y` is `pairδC A n` of the pullback of `y` along the restriction
`f|_A : A → C`. -/
theorem pairDeltaNatural {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : ContinuousMap X Y) (A : Set X) (Cset : Set Y) (hf : ∀ x ∈ A, f x ∈ Cset) (n : ℕ)
    (y : Work.Thom.Coh ℤ n Cset) :
    (Work.Thom.relCohMap f A Cset hf ℤ (n + 1)).hom ((Work.Thom.pairδC Cset n).hom y)
      = (Work.Thom.pairδC A n).hom ((Work.Thom.CohMap (⟨fun a : A => ⟨f ↑a, hf ↑a a.2⟩,
          Continuous.subtype_mk (f.continuous.comp continuous_subtype_val) (fun a => hf ↑a a.2)⟩ :
          ContinuousMap A Cset) ℤ n).hom y) := by
  have hS₁ : (Work.Cohomology.pairShort ℤ (TopCat.of Y) Cset).ShortExact :=
    Work.Cohomology.pairShort_shortExact ℤ (TopCat.of Y) Cset
  have hS₂ : (Work.Cohomology.pairShort ℤ (TopCat.of X) A).ShortExact :=
    Work.Cohomology.pairShort_shortExact ℤ (TopCat.of X) A
  have hnat := Work.Thom.delta_naturality_apply
    (S₁ := Work.Cohomology.pairShort ℤ (TopCat.of Y) Cset)
    (S₂ := Work.Cohomology.pairShort ℤ (TopCat.of X) A)
    (pairDeltaShortMap (X := TopCat.of X) (Y := TopCat.of Y) A Cset (TopCat.ofHom f) hf)
    hS₁ hS₂ (n + 1) (by omega) y
  exact hnat.symm

end

end Work.Thom
