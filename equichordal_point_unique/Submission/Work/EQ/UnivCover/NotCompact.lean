import Submission.Work.EQ.UnivCover.Defs
import Submission.Work.EQ.UnivCover.Sheet
import Submission.Work.EQ.UnivCover.Topology

/-!
# The universal cover of a non-compact space is non-compact

The projection of the universal cover is surjective as soon as `X` is path connected, so a compact
total space would force `X` compact.
-/

set_option autoImplicit false
open _root_.Topology
open scoped Topology
open Work.EQ.UnivCover

namespace Work.EQ.UnivCover

variable {X : Type*} [TopologicalSpace X] {x₀ : X}

/-- The universal cover of a non-compact, path connected space is non-compact. -/
theorem UC_not_compactSpace [PathConnectedSpace X] (hB : HasDiscBasis X)
    (hX : ¬ CompactSpace X) : ¬ CompactSpace (UC x₀) := by
  intro h
  refine hX ?_
  rw [← isCompact_univ_iff]
  have hsurj : Function.Surjective (UC.proj (x₀ := x₀)) := by
    intro x
    obtain ⟨γ⟩ := PathConnectedSpace.joined x₀ x
    exact ⟨⟨x, Path.Homotopic.Quotient.mk γ⟩, rfl⟩
  have himg : (UC.proj (x₀ := x₀)) '' (Set.univ : Set (UC x₀)) = Set.univ :=
    Set.image_univ_of_surjective hsurj
  have hcomp : IsCompact (Set.univ : Set (UC x₀)) := isCompact_univ
  rw [← himg]
  exact hcomp.image (UC_continuous_proj hB)

end Work.EQ.UnivCover
