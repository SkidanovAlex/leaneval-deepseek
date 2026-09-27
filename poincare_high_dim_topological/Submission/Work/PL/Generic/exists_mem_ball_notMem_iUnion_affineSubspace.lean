import Mathlib
import Submission.Work.PL.Defs
import Submission.Work.PL.Generic.Basic

namespace Work.PL.Generic

/-- A proper affine subspace of `ℝᵐ` is nowhere dense: it is closed (finite dimension), and its
interior is empty because a convex set with nonempty interior affinely spans the whole space
(`Convex.interior_nonempty_iff_affineSpan_eq_top`), while `affineSpan ℝ (F : Set _) = F`. -/
theorem isNowhereDense_affineSubspace {m : ℕ} (F : AffineSubspace ℝ (PL.E m)) (hF : F ≠ ⊤) :
    IsNowhereDense (F : Set (PL.E m)) := by
  have hiff : (interior (F : Set (PL.E m))).Nonempty ↔ F = ⊤ := by
    rw [Convex.interior_nonempty_iff_affineSpan_eq_top F.convex, AffineSubspace.affineSpan_coe]
  have hempty : interior (F : Set (PL.E m)) = ∅ :=
    Set.not_nonempty_iff_eq_empty.mp (fun h => hF (hiff.mp h))
  rw [F.closed_of_finiteDimensional.isNowhereDense_iff]
  exact hempty

/-- Finitely many proper affine subspaces of `ℝᵐ` miss a point of every ball.  Proof: a proper
affine subspace is closed with empty interior (its interior would span everything, use
`affineSpan_eq_top_of_nonempty_interior` from `Mathlib/Analysis/Normed/Affine/AddTorsorBases.lean`
via `AffineSubspace.convex`/`convexHull_eq_self`), hence nowhere dense; a finite union of nowhere
dense sets is nowhere dense, so its complement is dense and meets the nonempty open ball. -/
theorem exists_mem_ball_notMem_iUnion_affineSubspace {m : ℕ} {ι : Type*} [Fintype ι]
    (F : ι → AffineSubspace ℝ (PL.E m)) (hF : ∀ i, F i ≠ ⊤) (x : PL.E m) {ε : ℝ} (hε : 0 < ε) :
    ∃ y ∈ Metric.ball x ε, ∀ i, y ∉ (F i : Set (PL.E m)) := by
  classical
  have hN : IsNowhereDense (⋃ i, (F i : Set (PL.E m))) :=
    IsNowhereDense.iUnion fun i => isNowhereDense_affineSubspace (F i) (hF i)
  -- a nowhere dense set has empty interior, in particular the union does
  have hinter : interior (⋃ i, (F i : Set (PL.E m))) = ∅ :=
    Set.eq_empty_of_subset_empty (hN ▸ interior_mono subset_closure)
  by_contra h
  push Not at h
  -- the ball is open and contained in the union, hence in its interior
  have hsub : Metric.ball x ε ⊆ interior (⋃ i, (F i : Set (PL.E m))) :=
    interior_maximal (fun y hy => Set.mem_iUnion.mpr (h y hy)) Metric.isOpen_ball
  rw [hinter] at hsub
  have hne : (Metric.ball x ε).Nonempty := ⟨x, Metric.mem_ball_self hε⟩
  exact hne.ne_empty (Set.eq_empty_of_subset_empty hsub)

end Work.PL.Generic
