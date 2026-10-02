import Mathlib
import Submission.Work.Serre.DiscPair.collarDefs
import Submission.Work.Bordism.HomotopyHomology
import Submission.Work.Thom.PairPrism
import Submission.Work.RatHurewicz.relHurewiczClass_eq_of_homotopic
import Submission.Work.Serre.DiscPair.cokernelMapHomologyEq

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval

namespace Work.Serre.DiscPair

/-- **Relative rational homology is invariant under a homotopy of maps of pairs.**  If `f, g : X → Y`
are homotopic through maps carrying `A` into `B` (a homotopy `H` with `H (t,x) ∈ B` for `x ∈ A`),
then the induced maps of relative chain complexes `C_*(X,A;ℚ) → C_*(Y,B;ℚ)` agree on homology. -/
theorem relPairHomotopic {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X}
    {B : Set Y} {f g : C(X, Y)} (hf : Set.MapsTo f A B) (hg : Set.MapsTo g A B)
    (H : ContinuousMap.Homotopy f g)
    (hH : ∀ (t : unitInterval) (x : X), x ∈ A → H (t, x) ∈ B) (n : ℕ) :
    HomologicalComplex.homologyMap (Work.Serre.relChainsRPairMap A B f hf) n
      = HomologicalComplex.homologyMap (Work.Serre.relChainsRPairMap A B g hg) n := by
  -- the homotopy of pairs, as a homotopy of maps of `TopCat`
  let Hf : TopCat.Homotopy (TopCat.ofHom f) (TopCat.ofHom g) := H
  -- the induced chain homotopy between the chain maps of the ambient spaces
  let P : Homotopy (Work.Cohomology.chainMap ℚ (TopCat.of X) (TopCat.of Y) (TopCat.ofHom f))
      (Work.Cohomology.chainMap ℚ (TopCat.of X) (TopCat.of Y) (TopCat.ofHom g)) :=
    Hf.toSSet.chainComplexMap (ModuleCat.of ℚ ℚ)
  -- the pair map is the map induced on the cokernels
  have ha₀ : cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of X) A) ≫
      Work.Serre.relChainsRPairMap A B f hf
      = Work.Cohomology.chainMap ℚ (TopCat.of X) (TopCat.of Y) (TopCat.ofHom f) ≫
        cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of Y) B) := by
    rw [Work.Serre.relChainsRPairMap, Work.Serre.csrRelMapOf]
    exact Work.Cohomology.cokernel_π_cokernelMap _ _ _ _ _
  have ha₁ : cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of X) A) ≫
      Work.Serre.relChainsRPairMap A B g hg
      = Work.Cohomology.chainMap ℚ (TopCat.of X) (TopCat.of Y) (TopCat.ofHom g) ≫
        cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of Y) B) := by
    rw [Work.Serre.relChainsRPairMap, Work.Serre.csrRelMapOf]
    exact Work.Cohomology.cokernel_π_cokernelMap _ _ _ _ _
  -- the prism operator of the homotopy of pairs carries chains of `A` into chains of `B`
  refine cokernelMapHomologyEq (Work.StemsB.relChainsRIncl ℚ (TopCat.of X) A)
    (Work.StemsB.relChainsRIncl ℚ (TopCat.of Y) B) P
    (fun i => ((Work.Thom.restrHomotopyTop Hf hf hg hH).toSSet.chainComplexMap
      (ModuleCat.of ℚ ℚ)).hom i (i+1))
    (fun i => (Work.Thom.prism_preserves Hf hf hg hH ℚ i).symm)
    (a₀ := Work.Serre.relChainsRPairMap A B f hf)
    (a₁ := Work.Serre.relChainsRPairMap A B g hg) ha₀ ha₁ n

end Work.Serre.DiscPair
