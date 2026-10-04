import Mathlib
import Submission.Work.Diff.EXT.curvDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Two-parameter families of tangent fields

A family `F : ℝ → ℝ → TField I M` of tangent fields is *jointly smooth* (written `JointField2`) if
the section `(σ, (τ, y)) ↦ ⟨y, F σ τ y⟩` of the tangent bundle of `M` is `C^∞` on the open set
`W3 V`, where `V` is the open set on which both the metric time `σ` and the field time `τ` are
allowed to live (with the *same* base point `y`).

This is the two-time version of `Work.Diff.EXT.JointField`, needed for the joint smoothness of the
curvature tower in a metric time `σ` and a field time `τ` that are independent.
-/

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT.evolX

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-- The set of triples `(σ, τ, y)` where both times `σ` (for the metric) and `τ` (for the fields)
are flow times at the base point `y`: this is the two-parameter version of `V`. -/
def W3 (V : Set (ℝ × M)) : Set (ℝ × (ℝ × M)) :=
  {q | (q.1, q.2.2) ∈ V ∧ (q.2.1, q.2.2) ∈ V}

/-- A family of tangent fields, jointly smooth in a metric time `σ` and a field time `τ`. -/
def JointField2 (V : Set (ℝ × M)) (F : ℝ → ℝ → TField (I := I) (M := M)) : Prop :=
  ContMDiffOn ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod I)) I.tangent ∞
    (fun q : ℝ × (ℝ × M) => (⟨q.2.2, F q.1 q.2.1 q.2.2⟩ : TangentBundle I M)) (W3 V)

theorem isOpen_W3 {V : Set (ℝ × M)} (hV : IsOpen V) : IsOpen (W3 V) := by
  have h1 : IsOpen {q : ℝ × (ℝ × M) | (q.1, q.2.2) ∈ V} :=
    hV.preimage (continuous_fst.prodMk (continuous_snd.comp continuous_snd))
  have h2 : IsOpen {q : ℝ × (ℝ × M) | (q.2.1, q.2.2) ∈ V} :=
    hV.preimage ((continuous_fst.comp continuous_snd).prodMk
      (continuous_snd.comp continuous_snd))
  exact h1.inter h2

theorem mem_W3 {V : Set (ℝ × M)} {σ τ : ℝ} {y : M} :
    (σ, (τ, y)) ∈ W3 V ↔ (σ, y) ∈ V ∧ (τ, y) ∈ V := Iff.rfl

/-- A one-time jointly smooth family of fields is jointly smooth as a family independent of the
second time. -/
theorem jointField2_of_jointField {V : Set (ℝ × M)} {F : ℝ → TField (I := I) (M := M)}
    (hF : JointField F V) : JointField2 V (fun _ τ => F τ) := by
  have hproj : ContMDiffOn ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod I))
      ((𝓘(ℝ, ℝ)).prod I) ∞ (Prod.snd : ℝ × (ℝ × M) → ℝ × M) (W3 V) :=
    contMDiffOn_snd (I := 𝓘(ℝ, ℝ)) (J := (𝓘(ℝ, ℝ)).prod I) (M := ℝ) (N := ℝ × M)
  exact hF.comp hproj (fun q hq => hq.2)

end Work.Diff.EXT.evolX
