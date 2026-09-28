import Mathlib
import Submission.Work.Stems.Hur2b.GluingCancel

/-!
# Existence of the cancellation family of the gluing of `∂I³`

Specialisation of `Work.Stems.Hur2b.gluingCancelFamily`: the gluing of the six filled faces of a
3-cube is freely homotopic to a constant map, through a family which is *explicit* (the `K₁`-fillings
are cancelled by `psiFunCancel` and the clamp collapse is then contracted radially).  This is the
"cancellation" half of Hutchings' proof of `(2.5)`.
-/

open scoped unitInterval Topology

namespace Work.Stems.Hur2b

open Work.Stems.Cubical Work.Stems.Hur2

noncomputable section

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]

theorem exists_gluingCancel_family (x₀ : X) (τ : ContinuousMap (Work.Stems.Cubical.IC 3) X) :
    ∃ Φ : ContinuousMap (Work.Stems.Hur2b.Bdy3 × unitInterval) X,
      (∀ p, Φ (p, 0) = Work.Stems.Hur2b.gluingMap x₀ τ p) ∧
      (∃ z : X, ∀ p, Φ (p, 1) = z) :=
  ⟨gluingCancelFamily x₀ τ, gluingCancelFamily_zero x₀ τ, τ 0, gluingCancelFamily_one x₀ τ⟩

end

end Work.Stems.Hur2b
