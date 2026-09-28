import Mathlib
import Submission.Work.StemsB.ThomRatShim
import Submission.Work.Cohomology.exists_relComplexMap
import Submission.Work.Cohomology.PairSequence

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Naturality of the connecting homomorphism of a pair, over an arbitrary coefficient ring

`Submission/Work/Thom/pairDeltaNatural.lean` proves, over `ℤ`, that the connecting homomorphism
`δ : H^n(C) ⟶ H^{n+1}(Y,C)` of a pair commutes with the pullback along a map of pairs
`f : (X,A) → (Y,C)`.  The proof (`Work.Thom.pairDeltaNatural`) uses only the ladder of short exact
sequences of a map of pairs (`Work.Cohomology.pairShort` / `pairShort_shortExact`, which are
coefficient-generic) and the naturality of the connecting homomorphism of a morphism of short exact
sequences (`HomologicalComplex.HomologySequence.δ_naturality`, a Mathlib statement valid over any
abelian category).  Only the transcription of the ladder (`Work.Thom.pairDeltaShortMap`) and the
one degree of the naturality (`Work.Thom.delta_naturality_apply`) are pinned to `ℤ` as written.

This file contains the `R`-coefficient versions:

* `Work.StemsB.upRel_predR` — the shape relation `k - 1 ~ k` of `ComplexShape.up ℕ`;
* `Work.StemsB.delta_naturality_applyR` — naturality of the connecting homomorphism;
* `Work.StemsB.pairDeltaShortMapR` — the ladder map of the pair `(X,A) → (Y,C)`;
* `Work.StemsB.pairDeltaNaturalR` — **naturality of `pairδ`** over `R`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

namespace Work.StemsB

noncomputable section

/-- The shape relation `k - 1 ~ k` of the complex shape `ComplexShape.up ℕ`, for `k ≥ 1`. -/
theorem upRel_predR (k : ℕ) (hk : k ≠ 0) : (ComplexShape.up ℕ).Rel (k - 1) k :=
  ComplexShape.up_mk (k - 1) k (by omega)

/-- **Naturality of the connecting homomorphism** of a morphism `φ : S₁ ⟶ S₂` of short exact
sequences of cochain complexes, evaluated on an element. -/
theorem delta_naturality_applyR (R : Type) [CommRing R]
    {S₁ S₂ : ShortComplex (CochainComplex (ModuleCat R) ℕ)}
    (φ : S₁ ⟶ S₂) (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact)
    (k : ℕ) (hk : k ≠ 0) (w : (S₁.X₃).homology (k - 1)) :
    ModuleCat.Hom.hom (hS₂.δ (k - 1) k (upRel_predR k hk))
        (ModuleCat.Hom.hom (HomologicalComplex.homologyMap φ.τ₃ (k - 1)) w)
      = ModuleCat.Hom.hom (HomologicalComplex.homologyMap φ.τ₁ k)
        (ModuleCat.Hom.hom (hS₁.δ (k - 1) k (upRel_predR k hk)) w) := by
  have h := HomologicalComplex.HomologySequence.δ_naturality φ hS₁ hS₂ (k - 1) k
    (upRel_predR k hk)
  have h' := congrArg (fun (g : (S₁.X₃).homology (k - 1) ⟶ (S₂.X₁).homology k) =>
    ModuleCat.Hom.hom g w) h
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h'
  exact h'.symm

/-- **The ladder of a map of pairs**, over `R`: a continuous map `f : X ⟶ Y` carrying `A ⊆ X` into
`Cset ⊆ Y` induces a morphism `pairShort Y Cset ⟶ pairShort X A` of short exact sequences, whose
three components are the pullbacks on the relative, absolute and subspace cochains. -/
def pairDeltaShortMapR (R : Type) [CommRing R]
    {X Y : TopCat} (A : Set X) (Cset : Set Y) (f : X ⟶ Y)
    (hf : ∀ x ∈ A, (ConcreteCategory.hom f) x ∈ Cset) :
    Work.Cohomology.pairShort R Y Cset ⟶ Work.Cohomology.pairShort R X A :=
  { τ₁ := Work.Cohomology.relComplexMap R A Cset f hf
    τ₂ := Work.Cohomology.dualChainMap R X Y f
    τ₃ := Work.Cohomology.dualChainMap R (TopCat.of A) (TopCat.of Cset)
      (Work.Cohomology.relMapSub A Cset f hf)
    comm₁₂ := by
      change Work.Cohomology.relComplexMap R A Cset f hf ≫ Work.Cohomology.relIncl R X A
        = Work.Cohomology.relIncl R Y Cset ≫ Work.Cohomology.dualChainMap R X Y f
      apply HomologicalComplex.hom_ext
      intro k
      rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
        Work.Cohomology.relComplexMap_f, Work.Cohomology.relIncl_f, Work.Cohomology.relIncl_f]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact Work.Cohomology.relMapLM_coe R A Cset f hf k x
    comm₂₃ := Work.Cohomology.dualChainMap_restr_comp R A Cset f hf }

/-- **Naturality of the connecting homomorphism of a pair**, over `R`.  For a continuous map
`f : X → Y` carrying `A ⊆ X` into `Cset ⊆ Y` and a class `y ∈ H^n(Cset;R)`, the pullback along `f`
of `pairδ Cset n y` is `pairδ A n` of the pullback of `y` along the restriction `f|_A`. -/
theorem pairDeltaNaturalR (R : Type) [CommRing R] {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y]
    (f : C(X, Y)) (A : Set X) (Cset : Set Y) (hf : ∀ x ∈ A, f x ∈ Cset) (n : ℕ)
    (y : Work.Thom.Coh R n Cset) :
    (Work.Thom.relCohMap f A Cset hf R (n + 1)).hom
        ((Work.Cohomology.pairδ R (TopCat.of Y) Cset n).hom y)
      = (Work.Cohomology.pairδ R (TopCat.of X) A n).hom
          ((Work.Thom.CohMap (⟨fun a : A => ⟨f ↑a, hf ↑a a.2⟩,
            Continuous.subtype_mk (f.continuous.comp continuous_subtype_val)
              (fun a => hf ↑a a.2)⟩ : C(A, Cset)) R n).hom y) := by
  let F := TopCat.ofHom f
  let e := pairDeltaShortMapR R A Cset F hf
  have h := HomologicalComplex.HomologySequence.δ_naturality (φ := e)
    (Work.Cohomology.pairShort_shortExact R (TopCat.of Y) Cset)
    (Work.Cohomology.pairShort_shortExact R (TopCat.of X) A) n (n + 1)
    (upRel_predR (n + 1) (by omega))
  have h2 := congrArg (fun (g : (Work.Cohomology.pairShort R (TopCat.of Y) Cset).X₃.homology n ⟶
      (Work.Cohomology.pairShort R (TopCat.of X) A).X₁.homology (n + 1)) =>
    ModuleCat.Hom.hom g y) h
  simp only [ModuleCat.hom_comp] at h2
  exact h2

end

end Work.StemsB
