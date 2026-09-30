import Mathlib
import Submission.Work.Stems.Hur2b.GluingModel
import Submission.Work.Stems.Hur2b.exists_gluingCancel_family
import Submission.Work.Stems.Hur2b.exists_collapse_IC2_Bdy3

/-!
# The cube model of the gluing is null

Combining
* the cancellation family `gluingCancelFamily` (`exists_gluingCancel_family`), and
* the collapse `ψ : I² → ∂I³` of `∂I²` to the vertex `(0,0,0)` (`exists_collapse_IC2_Bdy3`),

with the model machinery of `GluingModel.lean` gives the "cancellation half" of Hutchings' proof of
`(2.5)`: **the cube model `G ∘ ψ` of the gluing `G = gluingMap x₀ τ` is null as a based cube**,
i.e. `cl x₀ (G ∘ ψ) = 1`.

The other half — `cl x₀ (G ∘ ψ) = ∏_k cl (layer_k)` for the collapse `ψ` (Hutchings 2.2(b), the
"sum of the faces") — is not proved here; see `PLAN_HAC.md`.
-/

open scoped unitInterval Topology

namespace Work.Stems.Hur2b

open Work.Stems.Cubical Work.Stems.Hur2

noncomputable section

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]

/-- **The cube model of the gluing, along the collapse of `∂I²`, is null.**

This is the "cancellation" half of Hutchings' `(2.5)`. -/
theorem collapseModel_class_eq_one (x₀ : X) (τ : ContinuousMap (Work.Stems.Cubical.IC 3) X) :
    ∃ (ψ : ContinuousMap (Work.Stems.Cubical.IC 2) (Work.Stems.Hur2b.Bdy3))
      (hψ : ∀ y ∈ Cube.boundary (Fin 2), ψ y = Work.Stems.Hur2b.vertexBdy3),
      cl x₀ (model x₀ τ ψ hψ) = 1 := by
  obtain ⟨ψ, hψ, _⟩ := Work.Stems.Hur2b.exists_collapse_IC2_Bdy3
  exact ⟨ψ, hψ, model_class_eq_one' x₀ τ ψ hψ⟩

/-- **The cube model of the gluing along the collapse is null as a based cube.** -/
theorem collapseModel_homotopic_const (x₀ : X) (τ : ContinuousMap (Work.Stems.Cubical.IC 3) X) :
    ∃ (ψ : ContinuousMap (Work.Stems.Cubical.IC 2) (Work.Stems.Hur2b.Bdy3))
      (hψ : ∀ y ∈ Cube.boundary (Fin 2), ψ y = Work.Stems.Hur2b.vertexBdy3),
      GenLoop.Homotopic (model x₀ τ ψ hψ) GenLoop.const := by
  obtain ⟨ψ, hψ, _⟩ := Work.Stems.Hur2b.exists_collapse_IC2_Bdy3
  exact ⟨ψ, hψ, model_homotopic_const' x₀ τ ψ hψ⟩

end

end Work.Stems.Hur2b
