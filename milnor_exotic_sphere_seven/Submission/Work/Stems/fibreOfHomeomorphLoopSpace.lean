import Mathlib
import Submission.Work.RatHurewicz.PairFibre

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Stems

/-- **The fibre of the projection of the homotopy fibre is the loop space.**  The fibre
`Work.RatHurewicz.fibreOf i a₀` of the projection `homotopyFibreFst i a₀` of the homotopy fibre of
`i : C(A, X)` over `a₀` is homeomorphic to the loop space `Path (i a₀) (i a₀)`, by the explicit
mutually inverse continuous maps `Work.RatHurewicz.fibrePhi` and `Work.RatHurewicz.fibrePsi`
(the identity on the underlying path in one direction, and the pair `(a₀, γ)` in the other). -/
theorem fibreOfHomeomorphLoopSpace {X : Type} [TopologicalSpace X] {A : Type}
    [TopologicalSpace A] (i : C(A, X)) (a₀ : A) :
    Nonempty (Work.RatHurewicz.fibreOf i a₀ ≃ₜ Path (i a₀) (i a₀)) :=
  ⟨{ toFun := Work.RatHurewicz.fibrePhi i a₀
     invFun := Work.RatHurewicz.fibrePsi i a₀
     left_inv := Work.RatHurewicz.fibrePsi_fibrePhi i a₀
     right_inv := Work.RatHurewicz.fibrePhi_fibrePsi i a₀
     continuous_toFun := (Work.RatHurewicz.fibrePhi i a₀).continuous
     continuous_invFun := (Work.RatHurewicz.fibrePsi i a₀).continuous }⟩

end Work.Stems
