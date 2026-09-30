import Mathlib
import Submission.Work.Serre.SPC.B1Skeleton

set_option synthInstance.maxHeartbeats 400000


/-!
# The `1`-skeleton is path connected

`Work.Serre.SPC.Skeleton B b₀` is the space obtained from the one-point space `PUnit` by attaching
one `1`-cell per based loop of `B`, all of them glued at the single point `skeletonBase B b₀`
(the wedge of one circle per element of `π₁(B, b₀)`).

Every point of the skeleton is either the base point (the image of the `PUnit` summand) or lies on
one of the attached circles, i.e. is the image of a point of the model `1`-disc `D¹` under a
characteristic map `oneCellMap`.  The disc `D¹` is path connected (it is a convex subset of `ℝ`),
and the `-1` endpoint of every cell is glued to the base point, so each point of the skeleton can
be joined to the base point along the image of a path in `D¹`.  Hence the skeleton is path
connected.
-/

open scoped Topology unitInterval

namespace Work.Serre.SPC

noncomputable section

/-- The model `1`-disc `D¹ = [-1,1]` is path connected: it is a convex subset of `ℝ`. -/
private theorem pathConnectedSpace_cellD1 : PathConnectedSpace cellD1 :=
  isPathConnected_iff_pathConnectedSpace.mp <|
    (convex_closedBall (0 : ℝ) 1).isPathConnected ⟨0, by simp [Metric.mem_closedBall]⟩

/-- Any two points of the model `1`-disc are joined by a path. -/
private theorem joined_cellD1 (x y : cellD1) : Joined x y :=
  @PathConnectedSpace.joined cellD1 _ pathConnectedSpace_cellD1 x y

/-- Every point of the `1`-skeleton is joined to the base point: it is either the base point
itself (the `PUnit` summand) or lies on one of the circles, which passes through the base point. -/
private theorem joined_skeletonBase {B : Type} [TopologicalSpace B] (b₀ : B)
    (z : Skeleton B b₀) : Joined z (skeletonBase B b₀) := by
  refine Quotient.inductionOn z ?_
  intro a
  rcases a with y | p
  · -- the `PUnit` summand: the point is the base point
    rw [Subsingleton.elim y (⟨⟩ : PUnit)]
    exact Joined.refl _
  · -- the cell summand: a point of the `i`-th circle
    obtain ⟨i, t⟩ := p
    change Joined ((oneCellMap PUnit ↥(GenLoop (Fin 1) B b₀) (skeletonAttach B b₀) i) t)
      (skeletonBase B b₀)
    -- the `-1` endpoint of the cell is glued to the base point
    let e : cellS0 := ⟨-1, by simp⟩
    have h2 : (oneCellMap PUnit ↥(GenLoop (Fin 1) B b₀) (skeletonAttach B b₀) i)
        (cellS0ToD1 e) = skeletonBase B b₀ := by
      rw [← oneIncl_oneCellRel PUnit ↥(GenLoop (Fin 1) B b₀) (skeletonAttach B b₀) i e]
      rfl
    have h3 : Joined ((oneCellMap PUnit ↥(GenLoop (Fin 1) B b₀) (skeletonAttach B b₀) i) t)
        ((oneCellMap PUnit ↥(GenLoop (Fin 1) B b₀) (skeletonAttach B b₀) i) (cellS0ToD1 e)) :=
      (joined_cellD1 t (cellS0ToD1 e)).map
        (oneCellMap PUnit ↥(GenLoop (Fin 1) B b₀) (skeletonAttach B b₀) i).continuous
    rwa [h2] at h3

/-- **The `1`-skeleton of the model of `B` is path connected.**  It is the wedge of one circle per
based loop of `B`, all glued at `skeletonBase B b₀`, and each of these circles passes through the
base point. -/
theorem skeleton_pathConnected (B : Type) [TopologicalSpace B] (b₀ : B) :
    PathConnectedSpace (Work.Serre.SPC.Skeleton B b₀) :=
  ⟨⟨skeletonBase B b₀⟩, fun x y =>
    (joined_skeletonBase b₀ x).trans (joined_skeletonBase b₀ y).symm⟩

end

end Work.Serre.SPC
