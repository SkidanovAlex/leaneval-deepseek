import Mathlib
import Submission.Work.Cohomology.relComplexMapDualZ
import Submission.Work.Cohomology.isIso_homologyMap_dualZMap
import Submission.Work.Cohomology.relChainsMapOf_isIso
import Submission.Work.Cohomology.relChainsProjective
import Submission.Work.Cohomology.dualComplexMap_quasiIso

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option linter.style.haveILetI false

namespace Work.Cohomology.Crux

/-- **A map of pairs which is a homology isomorphism on both the total space and the subspace
induces an isomorphism on relative cohomology (with `ℤ`-coefficients).**

The relative cochain complex is naturally the `ℤ`-dual of the relative chain complex
(`relComplexMapDualZ`), and the pair map is the conjugate of the transposed pair map on chains under
this identification.  The map on relative chains is a quasi-isomorphism by the five lemma
(`relChainsMapOf_isIso`), and since relative chains are degreewise projective
(`relChainsProjective`), dualising a quasi-isomorphism of such complexes preserves quasi-isomorphisms
(`dualComplexMap_quasiIso`).  The two duality isomorphisms are isomorphisms, so the composite — the
pair map on relative cochains — induces an isomorphism on homology. -/
theorem relComplexMap_homologyMap_isIso {X₁ X₂ : TopCat} (A₁ : Set X₁) (A₂ : Set X₂) (f : X₁ ⟶ X₂)
    (h : ∀ x ∈ A₁, f x ∈ A₂) (n : ℕ)
    (hf : ∀ k, CategoryTheory.IsIso
      (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ X₁ X₂ f) k))
    (hg : ∀ k, CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℤ (TopCat.of A₁) (TopCat.of A₂)
        (Work.Cohomology.relMapSub A₁ A₂ f h)) k)) :
    CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.relComplexMap ℤ A₁ A₂ f h) n) := by
  -- the induced map of relative chain complexes is a quasi-isomorphism
  have hφ : ∀ k, CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.relChainsMapOf X₁ X₂ A₁ A₂ f (Work.Cohomology.relMapSub A₁ A₂ f h)
        (Work.Cohomology.relMapSub_spec A₁ A₂ f h)) k) :=
    fun k => Work.Cohomology.relChainsMapOf_isIso _ _ _ _
      (Work.Cohomology.relMapSub_spec A₁ A₂ f h) k hf hg
  -- its `ℤ`-dual is a quasi-isomorphism, as the relative chains are degreewise projective
  have hdual : CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.dualZMap ℤ (Work.Cohomology.relChains X₁ A₁)
        (Work.Cohomology.relChains X₂ A₂)
        (Work.Cohomology.relChainsMapOf X₁ X₂ A₁ A₂ f (Work.Cohomology.relMapSub A₁ A₂ f h)
          (Work.Cohomology.relMapSub_spec A₁ A₂ f h))) n) :=
    Work.Cohomology.dualComplexMap_quasiIso _
      (fun k => Work.Cohomology.relChainsProjective X₁ A₁ k)
      (fun k => Work.Cohomology.relChainsProjective X₂ A₂ k) hφ n
  haveI := hdual
  -- the pair map is the dual pair map conjugated by the duality isomorphisms
  rw [Work.Cohomology.relComplexMapDualZ ℤ A₁ A₂ f h]
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp]
  infer_instance

end Work.Cohomology.Crux
