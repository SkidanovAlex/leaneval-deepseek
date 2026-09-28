import Mathlib
import Submission.Work.Serre.E3aDefs
import Submission.Work.Stems.Hurewicz

/-!
# `E3(a)`: the `1`-skeleton of the model of a space

The cellular proof of `Work.Serre.SerreE3a` needs a model of the path-connected space `B` by a
cell complex; the first step creates `π₁`, and for that one has to attach `1`-cells.  The
construction here is the `ℚ`-side counterpart of `Work.Serre.SPC.Skeleton`
(`Submission/Work/Serre/SPC/B1Skeleton.lean`), spelled with the `1`-cell vocabulary of
`Submission/Work/Serre/E3aDefs.lean`.

It contains only definitions, so that lemmas proved against it are `sorry`-free.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval

namespace Work.Serre.E3aSk

noncomputable section

/-- The attaching maps of the `1`-skeleton: all the `1`-cells are glued at the single point of
`PUnit`, and there is one cell per based loop of `B`. -/
def skeletonAttach (B : Type) [TopologicalSpace B] (b₀ : B) :
    ↥(GenLoop (Fin 1) B b₀) → C(Work.Serre.cellSphereZero, PUnit) :=
  fun _ => ContinuousMap.const Work.Serre.cellSphereZero ⟨⟩

/-- **The `1`-skeleton of the model of `B`**: the wedge of one circle per based loop of `B`. -/
abbrev Skeleton (B : Type) [TopologicalSpace B] (b₀ : B) : Type :=
  Work.Serre.attachOneCells PUnit ↥(GenLoop (Fin 1) B b₀) (skeletonAttach B b₀)

/-- The base point of the skeleton. -/
def skeletonBase (B : Type) [TopologicalSpace B] (b₀ : B) : Skeleton B b₀ :=
  Work.Serre.oneIncl PUnit _ (skeletonAttach B b₀) ⟨⟩

end

end Work.Serre.E3aSk
