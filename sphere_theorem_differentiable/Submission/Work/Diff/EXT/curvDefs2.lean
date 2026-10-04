import Mathlib
import Submission.Work.Diff.EXT.curvDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Neighbourhood-smoothness vocabulary for the value dependence of `∇^k Rm`

`ContMDiffAt I I.tangent ∞` does **not** imply smoothness on a neighbourhood of the point
(Mathlib: "this does not hold for `n = ∞`").  The value-dependence (tensoriality) of the tower
`covKRmExt` is naturally proved for fields that are smooth on a *neighbourhood* of the base point:
then one can cut them off to globally smooth fields and expand with the field-level linearity.
This file provides that vocabulary.
-/

namespace Work.Diff.EXT

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-- A tangent field which is `C^∞` on a neighbourhood of `x`. -/
def SmoothNear (X : TField (I := I) (M := M)) (x : M) : Prop :=
  ∃ u ∈ 𝓝 x, ContMDiffOn I I.tangent ∞ (T% X) u

/-- A field smooth on a neighbourhood of `x` is smooth at `x`. -/
theorem SmoothNear.smoothAt {X : TField (I := I) (M := M)} {x : M} (h : SmoothNear (I := I) X x) :
    SmoothTFieldAt (I := I) (M := M) X x := by
  obtain ⟨u, hu, hX⟩ := h
  exact hX.contMDiffAt hu

/-- The slice at a fixed time of a jointly smooth family of fields is smooth on a neighbourhood of
the base point. -/
theorem jointField_sliceNear {X : ℝ → TField (I := I) (M := M)} {V : Set (ℝ × M)}
    (hV : IsOpen V) (hX : JointField X V) {p : ℝ × M} (hp : p ∈ V) :
    SmoothNear (I := I) (M := M) (fun y : M => X p.1 y) p.2 := by
  have hcont : ContinuousAt (fun y : M => (p.1, y)) p.2 :=
    continuousAt_const.prodMk continuousAt_id
  refine ⟨(fun y : M => (p.1, y)) ⁻¹' V, hcont.preimage_mem_nhds (hV.mem_nhds hp), ?_⟩
  show ContMDiffOn I I.tangent ∞ (T% (fun y : M => X p.1 y)) ((fun y : M => (p.1, y)) ⁻¹' V)
  exact ContMDiffOn.comp (t := V) hX
    (contMDiffOn_const.prodMk contMDiffOn_id) (fun y hy => hy)

/-- **Value-dependence of `∇^k Rm` for fields smooth on a neighbourhood of the base point**: the
value of `covKRmExt g k V A B C D` at `x` depends only on the values of the fields at `x`. -/
def KrValueDepN (g : Submission.Diff.SMet I M) (k : ℕ) : Prop :=
  ∀ (V V' : Fin k → TField (I := I) (M := M)) (A A' B B' C C' D D' : TField (I := I) (M := M))
    (x : M),
    (∀ j, SmoothNear (I := I) (V j) x) → (∀ j, SmoothNear (I := I) (V' j) x) →
    SmoothNear (I := I) A x → SmoothNear (I := I) A' x →
    SmoothNear (I := I) B x → SmoothNear (I := I) B' x →
    SmoothNear (I := I) C x → SmoothNear (I := I) C' x →
    SmoothNear (I := I) D x → SmoothNear (I := I) D' x →
    (∀ j, V j x = V' j x) → A x = A' x → B x = B' x → C x = C' x → D x = D' x →
    covKRmExt g k V A B C D x = covKRmExt g k V' A' B' C' D' x

/-- Every globally smooth field is smooth on a neighbourhood of every point. -/
theorem SmoothTField.smoothNear {X : TField (I := I) (M := M)}
    (hX : SmoothTField (I := I) (M := M) X) (x : M) : SmoothNear (I := I) X x :=
  ⟨univ, Filter.univ_mem, hX.contMDiffOn⟩

end Work.Diff.EXT
