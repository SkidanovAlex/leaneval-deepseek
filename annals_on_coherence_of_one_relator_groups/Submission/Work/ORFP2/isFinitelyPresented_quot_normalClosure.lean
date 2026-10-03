import Mathlib

namespace Work.ORFP2

/-- The quotient of the finitely presented free group `FreeGroup (Fin n)` by the normal
closure of a finite set of relations is finitely presented. -/
theorem isFinitelyPresented_quot_normalClosure {n : ℕ} (S : Set (FreeGroup (Fin n)))
    (hS : S.Finite) :
    Group.IsFinitelyPresented (FreeGroup (Fin n) ⧸ Subgroup.normalClosure S) :=
  Group.IsFinitelyPresented.quotient (Subgroup.normalClosure S) ⟨S, hS, rfl⟩

end Work.ORFP2
