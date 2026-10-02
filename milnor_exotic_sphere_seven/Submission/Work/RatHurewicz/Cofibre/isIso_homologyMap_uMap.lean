import Mathlib
import Submission.Work.RatHurewicz.Cofibre.AssemblyDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.RatHurewicz.Cofibre

/-- **The comparison map `uMap` is a quasi-isomorphism.**

`uMap F e₀ : C_*(U, U∩V) ⟶ C_*(E, F)` is the map of pairs whose components are the retraction
`cofibreURetract : ↥U → E` (a homotopy equivalence, `cofibreUHomotopyEquiv`) and the "base of a
cone point" `collarBase : ↥(U∩V) → ↥F` (also a homotopy equivalence,
`isIso_intHomologyMap_collarBase`).  A morphism of pairs which is a quasi-isomorphism on both
spaces induces an isomorphism on the relative chain complexes
(`Work.Cohomology.relChainsMapOf_homologyMap_isIso`, a five lemma argument on the long exact
sequences of the two pairs), which is exactly the statement. -/
theorem isIso_homologyMap_uMap (E : Type) [TopologicalSpace E] (F : Set E) [Nonempty E] [Nonempty F]
    (e₀ : E) (n : ℕ) :
    CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.RatHurewicz.Cofibre.uMap F e₀) n) := by
  have hf : ∀ k, CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℤ (TopCat.of ↥(cofibreU (setIncl F))) (TopCat.of E)
        (TopCat.ofHom (cofibreURetract (setIncl F) e₀))) k) :=
    fun k => Work.Serre.isIso_intHomologyMap_of_homotopyEquiv
      (cofibreUHomotopyEquiv (setIncl F) e₀) k
  have hg : ∀ k, CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℤ (TopCat.of (collarSet (setIncl F))) (TopCat.of F)
        (TopCat.ofHom (collarBase (setIncl F)))) k) :=
    fun k => isIso_intHomologyMap_collarBase (setIncl F) k
  exact Work.Cohomology.relChainsMapOf_homologyMap_isIso
    (X := TopCat.of ↥(cofibreU (setIncl F))) (Y := TopCat.of E)
    (A := collarSet (setIncl F)) (B := F)
    (f := TopCat.ofHom (cofibreURetract (setIncl F) e₀))
    (g := TopCat.ofHom (collarBase (setIncl F))) _ n hf hg

end Work.RatHurewicz.Cofibre
