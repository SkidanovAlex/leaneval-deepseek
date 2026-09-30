import Submission.Work.Homology.Basic
import Submission.Work.Homology.Pairs
import Submission.Work.Homology.Point
import Submission.Work.Homology.RelChainMap
import Submission.Work.Homology.SingHomologyHomeomorph
import Submission.Work.Homology.ContractibleHomology
import Submission.Work.Homology.BallHomology
import Submission.Work.Homology.StdSimplexHomology
import Submission.Work.Homology.HomotopyEquivHomology
import Submission.Work.Homology.DeformationRetractHomology

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Corollaries: naturality of the pair sequence and `intHomology` wrappers
-/

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Homology

noncomputable section

/-! ## Naturality of the pair sequence -/

/-- The map induced by a map of pairs on relative chains. -/
def relChainMap (R : ModuleCat ℤ) {X Y : TopCat} {A : Set X} {B : Set Y}
    (Φ : PairHom X Y A B) : relChain R X A ⟶ relChain R Y B :=
  Classical.choose (RelChainMap R Φ)

/-- Characterising property of `relChainMap`. -/
theorem relChainMap_comp_relProj (R : ModuleCat ℤ) {X Y : TopCat} {A : Set X} {B : Set Y}
    (Φ : PairHom X Y A B) :
    singChainMap R Φ.hom ≫ relProj R Y B = relProj R X A ≫ relChainMap R Φ :=
  Classical.choose_spec (RelChainMap R Φ)

/-- The map induced by a map of pairs on relative homology. -/
abbrev relHomologyMap (R : ModuleCat ℤ) (k : ℕ) {X Y : TopCat} {A : Set X} {B : Set Y}
    (Φ : PairHom X Y A B) : relHomology R k X A ⟶ relHomology R k Y B :=
  HomologicalComplex.homologyMap (relChainMap R Φ) k

/-- The morphism of short complexes `0 → C(A) → C(X) → C(X,A) → 0` induced by a
map of pairs. -/
def pairSeqMap (R : ModuleCat ℤ) {X Y : TopCat} {A : Set X} {B : Set Y}
    (Φ : PairHom X Y A B) : pairSeq R X A ⟶ pairSeq R Y B :=
  ShortComplex.homMk (singChainMap R Φ.sub) (singChainMap R Φ.hom) (relChainMap R Φ)
    (inclChain_naturality R Φ).symm (relChainMap_comp_relProj R Φ)

/-- Naturality of the projection `H_k(X) → H_k(X,A)`. -/
theorem relProjHom_naturality (R : ModuleCat ℤ) (k : ℕ) {X Y : TopCat} {A : Set X} {B : Set Y}
    (Φ : PairHom X Y A B) :
    singHomologyMap R k Φ.hom ≫ relProjHom R k Y B =
      relProjHom R k X A ≫ relHomologyMap R k Φ := by
  simp only [relProjHom, relHomologyMap]
  rw [← HomologicalComplex.homologyMap_comp, relChainMap_comp_relProj R Φ,
    HomologicalComplex.homologyMap_comp]

/-- Naturality of the connecting homomorphism of the pair sequence. -/
theorem pairδ_naturality (R : ModuleCat ℤ) (k : ℕ) {X Y : TopCat} {A : Set X} {B : Set Y}
    (Φ : PairHom X Y A B) :
    pairδ R X A k ≫ singHomologyMap R k Φ.sub =
      relHomologyMap R (k + 1) Φ ≫ pairδ R Y B k := by
  have := HomologicalComplex.HomologySequence.δ_naturality
    (hS₁ := pairSeq_shortExact R X A) (hS₂ := pairSeq_shortExact R Y B)
    (φ := pairSeqMap R Φ) (k + 1) k (by simp)
  simpa [pairδ, relHomologyMap, pairSeqMap] using this

/-! ## `intHomology` wrappers -/

/-- Homeomorphism invariance of `intHomology`. -/
theorem intHomology_iso_of_homeomorph (k : ℕ) {X Y : TopCat} (e : X ≃ₜ Y) :
    Nonempty (LeanEval.Topology.intHomology k X ≅ LeanEval.Topology.intHomology k Y) := by
  rw [intHomology_eq, intHomology_eq]
  exact SingHomologyHomeomorph ZMod k e

/-- Vanishing of the positive-degree `intHomology` of a contractible space. -/
theorem intHomology_isZero_of_contractible (k : ℕ) (X : TopCat) [ContractibleSpace X] :
    IsZero (LeanEval.Topology.intHomology (k + 1) X) := by
  rw [intHomology_eq]
  exact ContractibleHomology ZMod X k

/-- Vanishing of the positive-degree `intHomology` of the standard simplex. -/
theorem intHomology_stdSimplex_isZero (n k : ℕ) :
    IsZero (LeanEval.Topology.intHomology (k + 1)
      (TopCat.of (Convexity.StdSimplex ℝ (Fin (n + 1))))) := by
  rw [intHomology_eq]
  exact StdSimplexHomology ZMod n k

end

end Work.Homology

-- appended: homotopy and deformation-retract wrappers for `intHomology`

namespace Work.Homology

noncomputable section

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

/-- Homotopy equivalences induce isomorphisms on `intHomology`. -/
theorem intHomology_iso_of_homotopyEquiv (k : ℕ) {X Y : TopCat} (f : X ⟶ Y)
    (hf : IsHomotopyEquivalence f) :
    Nonempty (LeanEval.Topology.intHomology k X ≅ LeanEval.Topology.intHomology k Y) := by
  rw [intHomology_eq, intHomology_eq]
  exact HomotopyEquivHomology ZMod k f hf

/-- Deformation retracts induce isomorphisms on `intHomology`. -/
theorem intHomology_iso_of_deformationRetract (k : ℕ) {X : TopCat} {A : Set X}
    (h : DeformationRetract X A) :
    Nonempty (LeanEval.Topology.intHomology k X ≅
      LeanEval.Topology.intHomology k (TopCat.of A)) := by
  rw [intHomology_eq, intHomology_eq]
  exact DeformationRetractHomology ZMod k h

end

end Work.Homology
