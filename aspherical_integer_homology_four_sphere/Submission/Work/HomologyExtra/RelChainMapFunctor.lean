import Mathlib
import Submission.Work.HomologyExtra.SimplexFaceSetup
import Submission.Work.Homology.Corollaries
import Submission.Work.Cohomology.localHomology
import Submission.Work.Cohomology.excision

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Functoriality of the map induced by a map of pairs on relative chains

* `Work.HomologyExtra.relChainMap_eq_relChainsMapOf` — the map on relative chains chosen by
  `Work.Homology.relChainMap` (via `Classical.choose`) is the explicit map obtained from the
  universal property of the cokernel, `Work.Cohomology.relChainsMapOf`.
* `Work.HomologyExtra.relChainMap_comp` / `relHomologyMap_comp` — functoriality in the pair.
* `Work.HomologyExtra.isIso_relHomologyMap_of_pairMap` — the five lemma in the form used below:
  a map of pairs whose two components are quasi-isomorphisms (in the range needed by the five
  lemma) induces an isomorphism on relative homology.
-/

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.HomologyExtra

noncomputable section

/-! ## The chosen relative chain map is the explicit cokernel map -/

/-- The map induced by a map of pairs on relative chains, as chosen by
`Work.Homology.relChainMap`, is the explicit map `Work.Cohomology.relChainsMapOf` obtained from
the universal property of the cokernel.  (Both are the unique map compatible with the projections,
and the projection is an epimorphism.) -/
theorem relChainMap_eq_relChainsMapOf {X Y : TopCat} {A : Set X} {B : Set Y}
    (Φ : Work.Homology.PairHom X Y A B) :
    Work.Homology.relChainMap Work.Homology.ZMod Φ =
      Work.Cohomology.relChainsMapOf X Y A B Φ.hom Φ.sub
        (Work.Homology.PairHom.sub_comp_incl Φ).symm := by
  apply (cancel_epi (Work.Homology.relProj Work.Homology.ZMod X A)).1
  rw [← Work.Homology.relChainMap_comp_relProj]
  unfold Work.Cohomology.relChainsMapOf
  exact (Work.Cohomology.cokernel_π_map _ _ _ _ _).symm

/-! ## Functoriality -/

/-- **Functoriality of the relative chain map in the pair.** -/
theorem relChainMap_comp (R : ModuleCat ℤ) {X Y Z : TopCat} {A : Set X} {B : Set Y}
    {C : Set Z} (Φ : Work.Homology.PairHom X Y A B) (Ψ : Work.Homology.PairHom Y Z B C) :
    Work.Homology.relChainMap R (Ψ.comp Φ) =
      Work.Homology.relChainMap R Φ ≫ Work.Homology.relChainMap R Ψ := by
  apply (cancel_epi (Work.Homology.relProj R X A)).1
  rw [← Work.Homology.relChainMap_comp_relProj]
  rw [show (Ψ.comp Φ).hom = Φ.hom ≫ Ψ.hom from rfl, Work.Homology.singChainMap_comp,
    Category.assoc, Work.Homology.relChainMap_comp_relProj R Ψ, ← Category.assoc,
    Work.Homology.relChainMap_comp_relProj R Φ, Category.assoc]

/-- **Functoriality of the relative homology map in the pair.** -/
theorem relHomologyMap_comp (R : ModuleCat ℤ) (k : ℕ) {X Y Z : TopCat} {A : Set X} {B : Set Y}
    {C : Set Z} (Φ : Work.Homology.PairHom X Y A B) (Ψ : Work.Homology.PairHom Y Z B C) :
    Work.Homology.relHomologyMap R k (Ψ.comp Φ) =
      Work.Homology.relHomologyMap R k Φ ≫ Work.Homology.relHomologyMap R k Ψ := by
  rw [Work.Homology.relHomologyMap, Work.Homology.relHomologyMap, Work.Homology.relHomologyMap,
    relChainMap_comp, HomologicalComplex.homologyMap_comp]

/-- A composite of maps of pairs whose relative homology maps are isomorphisms has an isomorphic
relative homology map. -/
theorem isIso_relHomologyMap_comp {R : ModuleCat ℤ} {k : ℕ} {X Y Z : TopCat} {A : Set X}
    {B : Set Y} {C : Set Z} (Φ : Work.Homology.PairHom X Y A B)
    (Ψ : Work.Homology.PairHom Y Z B C)
    (hΦ : IsIso (Work.Homology.relHomologyMap R k Φ))
    (hΨ : IsIso (Work.Homology.relHomologyMap R k Ψ)) :
    IsIso (Work.Homology.relHomologyMap R k (Ψ.comp Φ)) := by
  rw [relHomologyMap_comp]
  haveI : IsIso (Work.Homology.relHomologyMap R k Φ) := hΦ
  haveI : IsIso (Work.Homology.relHomologyMap R k Ψ) := hΨ
  infer_instance

/-! ## Homotopy equivalences induce isomorphisms on homology -/

/-- A homotopy equivalence of topological spaces induces an isomorphism on singular homology in
every degree (for the chain map of the homotopy equivalence itself). -/
theorem isIso_singHomologyMap_of_isHomotopyEquivalence {X Y : TopCat} (f : X ⟶ Y)
    (hf : Work.Homology.IsHomotopyEquivalence f) (k : ℕ) :
    IsIso (Work.Homology.singHomologyMap Work.Homology.ZMod k f) := by
  obtain ⟨g, h1, h2⟩ := hf
  refine ⟨Work.Homology.singHomologyMap Work.Homology.ZMod k g, ?_, ?_⟩
  · rw [← Work.Homology.singHomologyMap_comp,
      Work.Homology.singHomologyMap_congr Work.Homology.ZMod k h1.some,
      Work.Homology.singHomologyMap_id]
  · rw [← Work.Homology.singHomologyMap_comp,
      Work.Homology.singHomologyMap_congr Work.Homology.ZMod k h2.some,
      Work.Homology.singHomologyMap_id]

/-! ## The five lemma for maps of pairs -/

/-- **The five lemma for a map of pairs.**  If the map induced on the subspaces is a quasi-isomorphism
(in the weak form needed by the five lemma: epimorphic in degree `n`, isomorphic in degree `n - 1`)
and the map induced on the ambient spaces is an isomorphism in degree `n` and a monomorphism in
degree `n - 1`, then the induced map on relative homology in degree `n` is an isomorphism. -/
theorem isIso_relHomologyMap_of_pairMap {X Y : TopCat} {A : Set X} {B : Set Y}
    (Φ : Work.Homology.PairHom X Y A B) (n : ℕ)
    (h₁ : Epi (HomologicalComplex.homologyMap
      (Work.Homology.singChainMap Work.Homology.ZMod Φ.sub) n))
    (h₂ : IsIso (HomologicalComplex.homologyMap
      (Work.Homology.singChainMap Work.Homology.ZMod Φ.hom) n))
    (h₃ : IsIso (HomologicalComplex.homologyMap
      (Work.Homology.singChainMap Work.Homology.ZMod Φ.sub) (n - 1)))
    (h₄ : Mono (HomologicalComplex.homologyMap
      (Work.Homology.singChainMap Work.Homology.ZMod Φ.hom) (n - 1))) :
    IsIso (Work.Homology.relHomologyMap Work.Homology.ZMod n Φ) := by
  refine HomologicalComplex.HomologySequence.isIso_homologyMap_τ₃
    (Work.Homology.pairSeqMap Work.Homology.ZMod Φ)
    (Work.Homology.pairSeq_shortExact Work.Homology.ZMod X A)
    (Work.Homology.pairSeq_shortExact Work.Homology.ZMod Y B) n ?_ ?_ ?_ ?_
  · show Epi (HomologicalComplex.homologyMap
      (Work.Homology.singChainMap Work.Homology.ZMod Φ.sub) n)
    exact h₁
  · show IsIso (HomologicalComplex.homologyMap
      (Work.Homology.singChainMap Work.Homology.ZMod Φ.hom) n)
    exact h₂
  · intro j hj
    have hj' : j + 1 = n := hj
    have hjn : j = n - 1 := by omega
    subst hjn
    exact h₃
  · intro j hj
    have hj' : j + 1 = n := hj
    have hjn : j = n - 1 := by omega
    subst hjn
    exact h₄

end

end Work.HomologyExtra
