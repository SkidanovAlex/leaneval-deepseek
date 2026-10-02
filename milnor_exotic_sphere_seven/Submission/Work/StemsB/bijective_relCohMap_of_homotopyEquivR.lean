import Mathlib
import Submission.Work.Thom.bijective_relCohMap_of_homotopyEquiv
import Submission.Work.Thom.Cohomology
import Submission.Work.StemsB.RelCohMapPairHomotopyR
import Submission.Work.StemsB.AToolsR
import Submission.Work.Cohomology.relComplexMapDualZ
import Submission.Work.Cohomology.isIso_homologyMap_dualZMap
import Submission.Work.Cohomology.relChainsMapOf_isIso
import Submission.Work.Cohomology.relChainsProjective
import Submission.Work.Cohomology.exists_relComplexMap

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# A homotopy equivalence of pairs induces a bijection on relative cohomology, over any ring

`Submission/Work/Thom/bijective_relCohMap_of_homotopyEquiv.lean` proves, over `ℤ`, that if
`f : (X,A) → (Y,B)` is a map of pairs whose underlying map `f : X → Y` is a homotopy equivalence and
whose restriction to the subspaces `A → B` is a homotopy equivalence, then the pullback
`f^* : H^n(Y,B;ℤ) → H^n(X,A;ℤ)` is bijective in every degree.

The proof there dualises the relative chain complexes and uses
`Work.Cohomology.dualComplexMap_quasiIso`, a statement about the `ℤ`-dual, which is specific to
coefficients in `ℤ`.  Here we record the same theorem for an arbitrary commutative coefficient ring
`R`, replacing the `ℤ`-dual by the `R`-dual `Work.Cohomology.dualZMap R`
(`Submission/Work/Cohomology/dualZ.lean`).  The single new ingredient is that the `R`-dual of a
*quasi-isomorphism* between degreewise projective `ℤ`-chain complexes is a quasi-isomorphism: a
quasi-isomorphism of complexes of projective modules is a homotopy equivalence
(`ChainComplex.quasiIso_iff_of_projective`), and `Work.Cohomology.isIso_homologyMap_dualZMap`
dualises homotopy equivalences.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false

open CategoryTheory

namespace Work.StemsB

noncomputable section

variable (R : Type) [CommRing R]

/-! ## Dualising quasi-isomorphisms of projective `ℤ`-chain complexes, with values in `R` -/

/-- **The `R`-dual of a quasi-isomorphism between degreewise projective `ℤ`-chain complexes is a
quasi-isomorphism.**

A quasi-isomorphism between complexes of projective modules concentrated in non-negative degrees is
a homotopy equivalence (`ChainComplex.quasiIso_iff_of_projective`), and the `R`-dual of a homotopy
equivalence is a homotopy equivalence (`Work.Cohomology.isIso_homologyMap_dualZMap`). -/
lemma isIso_homologyMap_dualZMap_of_quasiIso_R
    {C D : ChainComplex (ModuleCat ℤ) ℕ} (φ : C ⟶ D)
    (hC : ∀ n, Module.Projective ℤ ↥(C.X n)) (hD : ∀ n, Module.Projective ℤ ↥(D.X n))
    (h : ∀ n, IsIso (HomologicalComplex.homologyMap φ n)) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (Work.Cohomology.dualZMap R C D φ) n) := by
  haveI hprojC : ∀ n, CategoryTheory.Projective (C.X n) := fun n => by
    haveI := hC n; infer_instance
  haveI hprojD : ∀ n, CategoryTheory.Projective (D.X n) := fun n => by
    haveI := hD n; infer_instance
  have hq : QuasiIso φ := by
    rw [quasiIso_iff]
    intro i
    rw [quasiIsoAt_iff_isIso_homologyMap]
    exact h i
  obtain ⟨e, he⟩ := (ChainComplex.quasiIso_iff_of_projective φ).mp hq
  rw [← he]
  exact Work.Cohomology.isIso_homologyMap_dualZMap R e n

/-! ## The pair map on relative cochains is a quasi-isomorphism -/

/-- **A map of pairs which is a homology isomorphism on both the total space and the subspace
induces an isomorphism on relative cohomology with coefficients in any commutative ring `R`.**

The relative cochain complex over `R` is the `R`-dual of the relative `ℤ`-chain complex
(`Work.Cohomology.relComplexMapDualZ`); the induced map on relative chains is a quasi-isomorphism by
the five lemma (`Work.Cohomology.relChainsMapOf_isIso`) and the relative chains are degreewise
projective (`Work.Cohomology.relChainsProjective`), so its `R`-dual is a quasi-isomorphism
(`isIso_homologyMap_dualZMap_of_quasiIso_R`). -/
lemma relComplexMap_homologyMap_isIso_R
    {X₁ X₂ : TopCat} (A₁ : Set X₁) (A₂ : Set X₂)
    (f : X₁ ⟶ X₂) (h : ∀ x ∈ A₁, (ConcreteCategory.hom f) x ∈ A₂)
    (hf : ∀ k, IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℤ X₁ X₂ f) k))
    (hg : ∀ k, IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℤ (TopCat.of ↑A₁) (TopCat.of ↑A₂)
        (Work.Cohomology.relMapSub A₁ A₂ f h)) k))
    (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (Work.Cohomology.relComplexMap R A₁ A₂ f h) n) := by
  have hrel : ∀ k, IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.relChainsMapOf X₁ X₂ A₁ A₂ f (Work.Cohomology.relMapSub A₁ A₂ f h)
        (Work.Cohomology.relMapSub_spec A₁ A₂ f h)) k) :=
    fun k => Work.Cohomology.relChainsMapOf_isIso A₁ A₂ f (Work.Cohomology.relMapSub A₁ A₂ f h)
      (Work.Cohomology.relMapSub_spec A₁ A₂ f h) k hf hg
  have hdual := isIso_homologyMap_dualZMap_of_quasiIso_R R
    (Work.Cohomology.relChainsMapOf X₁ X₂ A₁ A₂ f (Work.Cohomology.relMapSub A₁ A₂ f h)
      (Work.Cohomology.relMapSub_spec A₁ A₂ f h))
    (fun m => Work.Cohomology.relChainsProjective X₁ A₁ m)
    (fun m => Work.Cohomology.relChainsProjective X₂ A₂ m) hrel n
  have heq := Work.Cohomology.relComplexMapDualZ R A₁ A₂ f h
  rw [heq, HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp]
  haveI := hdual
  infer_instance

/-! ## The target statement -/

/-- **A homotopy equivalence of pairs induces a bijection on relative cohomology**, over `R`.

This is the `R`-coefficient form of `Work.Thom.bijective_relCohMap_of_homotopyEquiv`. -/
theorem bijective_relCohMap_of_homotopyEquivR (R : Type) [CommRing R]
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) (f : C(X, Y)) (hf : ∀ x ∈ A, f x ∈ B)
    (e1 : ContinuousMap.HomotopyEquiv X Y) (he1 : ⇑e1.toFun = ⇑f)
    (e2 : ContinuousMap.HomotopyEquiv ↥A ↥B)
    (he2 : ∀ q : ↥A, ((e2.toFun q : ↥B) : Y) = f (q : X)) :
    ∀ n, Function.Bijective (Work.Thom.relCohMap f A B hf R n).hom := by
  intro n
  -- `f` is the forward map of the homotopy equivalence `e1`
  have hfe : (TopCat.ofHom f : TopCat.of X ⟶ TopCat.of Y) = TopCat.ofHom e1.toFun := by
    ext x
    exact (congrFun he1 x).symm
  -- hence the induced map on singular chains is a quasi-isomorphism
  have hf' : ∀ k, IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℤ (TopCat.of X) (TopCat.of Y) (TopCat.ofHom f)) k) := by
    intro k
    rw [hfe]
    exact Work.Thom.homologyMap_chainMap_isIso_of_homotopyEquiv e1 k
  -- the induced map of pairs on the subspaces is the continuous map underlying `e2`
  have hsub : Work.Cohomology.relMapSub A B (TopCat.ofHom f) hf = TopCat.ofHom e2.toFun := by
    ext q
    simp only [Work.Cohomology.relMapSub]
    exact (he2 q).symm
  -- so the restriction to the subspaces is a quasi-isomorphism on singular chains as well
  have hg' : ∀ k, IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℤ (TopCat.of ↥A) (TopCat.of ↥B)
        (Work.Cohomology.relMapSub A B (TopCat.ofHom f) hf)) k) := by
    intro k
    rw [hsub]
    exact Work.Thom.homologyMap_chainMap_isIso_of_homotopyEquiv e2 k
  -- the map of relative cochain complexes is therefore a quasi-isomorphism
  have hIso : IsIso (HomologicalComplex.homologyMap (Work.Cohomology.relComplexMap
      (X₁ := TopCat.of X) (X₂ := TopCat.of Y) R A B (TopCat.ofHom f) hf) n) :=
    relComplexMap_homologyMap_isIso_R R (X₁ := TopCat.of X) (X₂ := TopCat.of Y)
      A B (TopCat.ofHom f) hf hf' hg' n
  exact (ConcreteCategory.isIso_iff_bijective (Work.Thom.relCohMap f A B hf R n)).mp hIso

end

end Work.StemsB
