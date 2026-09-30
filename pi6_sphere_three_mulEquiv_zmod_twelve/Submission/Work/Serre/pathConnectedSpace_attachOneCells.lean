import Mathlib
import Submission.Work.Serre.E3aSkDefs

namespace Work.Serre

/-- **The space obtained by attaching `1`-cells to a path-connected space is path connected.**

Every point of the `i`-th interval `D¹` is joined inside the interval to the endpoint `1`, whose
gluing image is `f i 1 ∈ Y`; and `Y`, being path connected, joins every one of its points to a
fixed base point. -/
theorem pathConnectedSpace_attachOneCells (Y : Type) [TopologicalSpace Y] [PathConnectedSpace Y]
    (ι : Type) (f : ι → ContinuousMap Work.Serre.cellSphereZero Y) :
    PathConnectedSpace (Work.Serre.attachOneCells Y ι f) := by
  classical
  -- the interval `D¹ = [-1,1]` is convex, hence path connected
  have hIP : IsPathConnected (Metric.closedBall (0 : ℝ) 1) :=
    (convex_closedBall (0 : ℝ) 1).isPathConnected ⟨0, by simp [Metric.mem_closedBall]⟩
  -- the endpoint `1` of `D¹`, viewed as a point of the `0`-sphere
  let zOne : cellSphereZero := ⟨1, by rw [Metric.mem_sphere]; norm_num⟩
  -- a base point of `Y`
  let y₀ : Y := Classical.arbitrary Y
  -- every point of `Y` is joined to the base point
  have hmem : ∀ y : Y, Joined (oneIncl Y ι f y) (oneIncl Y ι f y₀) := fun y =>
    Joined.map (PathConnectedSpace.joined y y₀) (oneIncl Y ι f).continuous
  -- every point of a `1`-cell is joined to the glued endpoint of that cell
  have hcell : ∀ (i : ι) (x : cellDiskOne),
      Joined (oneCellMap Y ι f i x) (oneIncl Y ι f (f i zOne)) := by
    intro i x
    have hpath : Joined x (cellSphereZeroToDiskOne zOne) :=
      JoinedIn.joined_subtype (hIP.joinedIn x.1 x.2
        (cellSphereZeroToDiskOne zOne).1 (cellSphereZeroToDiskOne zOne).2)
    have h1 : Joined ((oneCellMap Y ι f i) x)
        ((oneCellMap Y ι f i) (cellSphereZeroToDiskOne zOne)) :=
      Joined.map hpath (oneCellMap Y ι f i).continuous
    have h2 : Joined ((oneCellMap Y ι f i) (cellSphereZeroToDiskOne zOne))
        (oneIncl Y ι f (f i zOne)) := by
      rw [oneIncl_oneCellRel Y ι f i zOne]
    exact Joined.trans h1 h2
  -- it remains to join arbitrary two quotient points through the base point
  refine ⟨⟨oneIncl Y ι f y₀⟩, fun x y => ?_⟩
  have hAll : ∀ z : attachOneCells Y ι f, Joined z (oneIncl Y ι f y₀) := fun z => by
    induction z using Quotient.inductionOn with
    | h a =>
      cases a with
      | inl yy => exact hmem yy
      | inr p =>
        obtain ⟨i, xx⟩ := p
        exact Joined.trans (hcell i xx) (hmem (f i zOne))
  exact Joined.trans (hAll x) (Joined.symm (hAll y))

end Work.Serre
