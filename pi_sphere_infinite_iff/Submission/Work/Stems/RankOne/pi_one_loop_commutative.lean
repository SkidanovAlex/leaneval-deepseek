import Mathlib
import Submission.Work.Stems.homotopyGroup_loop

namespace Work.Stems.RankOne

/-- `π₁(Ω X, refl) = π₂(X)` is commutative: transport commutativity across the loop-space
isomorphism `curryMulEquiv : π₂(X) ≃* π₁(Ω X)`. -/
theorem pi_one_loop_commutative {X : Type} [TopologicalSpace X] (pt : X) :
    ∀ a b : HomotopyGroup (Fin 1) (Path pt pt) (Path.refl pt), a * b = b * a := by
  obtain ⟨e⟩ := homotopyGroup_loop (X := X) (n := 1) pt
  intro a b
  have h : e (e.symm a * e.symm b) = e (e.symm b * e.symm a) := by rw [mul_comm]
  simpa using h

end Work.Stems.RankOne
