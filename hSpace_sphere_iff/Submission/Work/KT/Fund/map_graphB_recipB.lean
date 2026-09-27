import Mathlib
import Submission.Work.KT.Fund.Clutch

namespace Work.KT.Fund

theorem map_graphB_recipB {n : ℕ} {R S : Type} [Ring R] [Ring S]
    (φ : R →+* S) (F : Matrix (Fin n) (Fin n) R) :
    (Work.KT.Fund.graphB R F).map ⇑φ = Work.KT.Fund.graphB S (F.map ⇑φ) ∧
    (Work.KT.Fund.recipB R F).map ⇑φ = Work.KT.Fund.recipB S (F.map ⇑φ) := by
  constructor
  · ext i j
    cases i with
    | inl a => simp [graphB, Matrix.map_apply]
    | inr a => simp [graphB, Matrix.map_apply]
  · ext i j
    cases i with
    | inl a => simp [recipB, Matrix.map_apply]
    | inr a => simp [recipB, Matrix.map_apply]

end Work.KT.Fund
