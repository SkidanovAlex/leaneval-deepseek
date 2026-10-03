import Mathlib
import Submission.Work.ORBassSerre.Action.Basic
import Submission.Work.ORBassSerre.Tree.IsTreeAPI

namespace Work.ORBassSerre.Action.Structure

theorem isFinitelyPresented_of_isEmpty_total {G : Type*} {V : Type*} [Group G] [Quiver V]
    [Quiver.HasInvolutiveReverse V] [MulAction G V] [Work.ORBassSerre.GraphAction G V]
    [Nonempty V] (hT : Work.ORBassSerre.IsTree V) (hne : IsEmpty (Quiver.Total V))
    (hstab : ∀ v : V, Group.IsFinitelyPresented (MulAction.stabilizer G v)) :
    Group.IsFinitelyPresented G := by
  -- A tree with no arrows is a single vertex: any path between two vertices must be
  -- a `nil` path, because a `cons` step would require an arrow of `V`, and there is none.
  have hsub : Subsingleton V := by
    rw [subsingleton_iff]
    intro a b
    obtain ⟨p⟩ := hT.1 a b
    induction p with
    | nil => rfl
    | cons p e ih => exact (hne.false ⟨_, _, e⟩).elim
  obtain ⟨v0⟩ := ‹Nonempty V›
  -- Hence the stabiliser of the unique vertex is all of `G`.
  have htop : MulAction.stabilizer G v0 = ⊤ := by
    ext g
    simp only [MulAction.mem_stabilizer_iff, Subgroup.mem_top, iff_true]
    exact Subsingleton.elim _ _
  have hfp : Group.IsFinitelyPresented (⊤ : Subgroup G) := htop ▸ hstab v0
  exact @Group.IsFinitelyPresented.equiv (⊤ : Subgroup G) G _ _ Subgroup.topEquiv hfp

end Work.ORBassSerre.Action.Structure
