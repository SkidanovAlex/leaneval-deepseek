import Mathlib
import Submission.Work.RatHurewicz.SkelGraph.assembly
import Submission.Work.RatHurewicz.SkelGraph.graphElement
import Submission.Work.RatHurewicz.SkelGraph.isOpenMapPhi
import Submission.Work.RatHurewicz.finiteGraphPiFg

/-!
# The fundamental group of the `1`-skeleton of the cycle model is finitely generated

The `1`-skeleton of the cycle model `Work.RatHurewicz.Model D` of
`Submission/Work/RatHurewicz/cycleModelDefs.lean` is the finite graph built from the `1`-faces of
the copies of `Δ^{n+2}` and the arcs.  `Submission/Work/RatHurewicz/SkelGraph/` exhibits that
graph as `Work.RatHurewicz.GraphX (a D) (b D)` and its fundamental group is finitely generated
(`Work.RatHurewicz.finiteGraphPiFg`); `Work.RatHurewicz.SkelGraph.graphElement` shows that the
comparison map `Phi D` is a bijection and `Work.RatHurewicz.SkelGraph.isOpenMapPhi` shows that it
is open, so that `Phi D` is a homeomorphism and finite generation transfers.
-/

namespace Work.RatHurewicz

theorem skeletonPiOneFg {X : Type} [TopologicalSpace X] {x₀ : X} {n : ℕ} (D : Work.RatHurewicz.MData X n x₀) [Nonempty D.Idx] : Group.FG (HomotopyGroup (Fin 1) ↥(Work.RatHurewicz.skeleton D) ⟨Work.RatHurewicz.modelBase D, Work.RatHurewicz.mem_skeleton_modelBase D⟩) :=
  Work.RatHurewicz.SkelGraph.fg_of_fg_graph D
    ⟨Work.RatHurewicz.SkelGraph.Phi_injective D
        (show Work.RatHurewicz.SkelGraph.GraphElementData D from
          Work.RatHurewicz.SkelGraph.graphElement D),
      Work.RatHurewicz.SkelGraph.Phi_surjective D
        (show Work.RatHurewicz.SkelGraph.GraphElementData D from
          Work.RatHurewicz.SkelGraph.graphElement D)⟩
    (Work.RatHurewicz.SkelGraph.isOpenMapPhi D)
    (Work.RatHurewicz.finiteGraphPiFg (Work.RatHurewicz.SkelGraph.E D)
      (Work.RatHurewicz.SkelGraph.V D) (Work.RatHurewicz.SkelGraph.a D)
      (Work.RatHurewicz.SkelGraph.b D) (Work.RatHurewicz.SkelGraph.v₀ D))

end Work.RatHurewicz
