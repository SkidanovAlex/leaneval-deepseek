import Mathlib
import Submission.Work.Serre.csrDefs
import Submission.Work.Serre.csrGlue
import Submission.Work.Cohomology.relChainsMapOf_comp

set_option maxHeartbeats 8000000

open CategoryTheory CategoryTheory.Limits

namespace Work.Serre

noncomputable section

/-- **Functoriality of the rational pair map on relative chains.**  The construction `(X,A) ↦ C_*(X,A;ℚ)` of `Work.Serre.relChainsRPairMap` is a functor on continuous maps of pairs: it carries a composite to the composite.  This is the identity by which the comparison squares of the rational cell step commute.  The underlying statement for `Work.Serre.csrRelMapOf` is `Work.Serre.csrRelMapOf_comp` in `Submission/Work/Serre/csrGlue.lean`; the only difficulty is that the direct application of it to the `relChainsRPairMap`-spelling needs the definitional unfolding of `relChainsRPairMap`, which is expensive (a naive `exact` times out at 1.6M heartbeats); spelling the goal explicitly with `show` and then applying `csrRelMapOf_comp`, or proving it by `cancel_epi` with `Work.Serre.cokernel_π_csrRelMapOf`, works. -/
theorem csrPairFunctoriality {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} (g : C(X, Y)) (h : C(Y, Z)) (hg : Set.MapsTo g A B) (hh : Set.MapsTo h B C) : CategoryTheory.CategoryStruct.comp (Work.Serre.relChainsRPairMap A B g hg) (Work.Serre.relChainsRPairMap B C h hh) = Work.Serre.relChainsRPairMap A C (h.comp g) (hh.comp hg) := by
  apply (cancel_epi (cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of X) A))).mp
  show cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of X) A) ≫
      (relChainsRPairMap A B g hg ≫ relChainsRPairMap B C h hh)
    = cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of X) A) ≫
      relChainsRPairMap A C (h.comp g) (hh.comp hg)
  unfold relChainsRPairMap csrRelMapOf
  rw [← Category.assoc, Work.Cohomology.cokernel_π_map, Category.assoc,
    Work.Cohomology.cokernel_π_map, Work.Cohomology.cokernel_π_map, ← Category.assoc,
    ← Work.Cohomology.chainMap_comp_relChains ℚ, ← TopCat.ofHom_comp]

end

end Work.Serre
