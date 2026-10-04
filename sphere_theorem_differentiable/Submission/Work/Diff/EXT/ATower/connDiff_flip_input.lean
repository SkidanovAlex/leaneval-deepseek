import Mathlib
import Submission.Work.Diff.EXT.ATower.Defs
import Submission.Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `Work.Diff.EXT.ATower.connDiff_flip_input`

The **input** of the flip identity `Work.Diff.EXT.ATower.step_flip`: the two connections
`∇^{G t} = lcOf (G t)` and `∇^{G 0} = lcOf (G 0)` on the same manifold, together with the
difference tensor

`δ Y Z = (∇^{G t}_Y Z) − (∇^{G 0}_Y Z)`

which has to be fed to `step_flip` (with `cov = ∇^{G 0}`, `cov' = ∇^{G t}`).

The content is exactly the *smoothness* statement of contract T1 (`Submission.Diff.LCSmooth`,
area T): if `Y` and `Z` are `C^∞` fields, then so is `y ↦ lcOf g Y y (Z y)`, for every smooth
metric `g`; the flip difference is then smooth by `ContMDiff.sub_section`.

The two connections are *not* tensors, but their difference is: the smoothness of both sides is
what makes `step_flip` applicable, and the pointwise identity `∇^{G t} = ∇^{G 0} + δ` is the
hypothesis `hδ` of that lemma.

The proof is `Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply`,
which extracts from the *class* `ContMDiffCovariantDerivative (lcOf g) ∞` (the first component of
`LCSmooth`) the smoothness of the hom-bundle section `y ↦ lcOf g Y y` and evaluates it against
the smooth field `Z`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT.ATower

/-- **Smoothness of `∇_Y Z` for the Levi-Civita connection of a smooth metric.**  If `Y` and `Z`
are `C^∞` tangent fields then so is `y ↦ lcOf g Y y (Z y)`, as soon as the Levi-Civita connection
of `g` is a smooth covariant derivative (contract `LCSmooth`). -/
theorem lcOf_apply_smE
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M)
    (Y Z : Π y : M, TangentSpace I y) (hY : SmE I M Y) (hZ : SmE I M Z) :
    SmE I M (fun y => Submission.Diff.lcOf g Y y (Z y)) := by
  haveI : CovariantDerivative.ContMDiffCovariantDerivative (Submission.Diff.lcOf g) ∞ :=
    (hLC g).1.some
  exact Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply
    (Submission.Diff.lcOf g) inferInstance hY hZ

theorem connDiff_flip_input
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (G : ℝ → Submission.Diff.SMet I M) (t : ℝ) :
    ∃ δ : (Π y : M, TangentSpace I y) → (Π y : M, TangentSpace I y) → (Π y : M, TangentSpace I y),
      (∀ (Y Z : Π y : M, TangentSpace I y), Work.Diff.EXT.ATower.SmE I M Y → Work.Diff.EXT.ATower.SmE I M Z →
        Work.Diff.EXT.ATower.SmE I M (fun y => δ Y Z y)) ∧
      (∀ (Y Z : Π y : M, TangentSpace I y), Work.Diff.EXT.ATower.SmE I M Y → Work.Diff.EXT.ATower.SmE I M Z →
        ∀ y : M, (Submission.Diff.lcOf (G t)) Y y (Z y)
          = (Submission.Diff.lcOf (G 0)) Y y (Z y) + δ Y Z y) ∧
      (∀ (Y Z : Π y : M, TangentSpace I y), Work.Diff.EXT.ATower.SmE I M Y → Work.Diff.EXT.ATower.SmE I M Z →
        Work.Diff.EXT.ATower.SmE I M (fun y => (Submission.Diff.lcOf (G 0)) Y y (Z y))) ∧
      (∀ (Y Z : Π y : M, TangentSpace I y), Work.Diff.EXT.ATower.SmE I M Y → Work.Diff.EXT.ATower.SmE I M Z →
        Work.Diff.EXT.ATower.SmE I M (fun y => (Submission.Diff.lcOf (G t)) Y y (Z y))) := by
  refine ⟨fun Y Z => (fun y => (Submission.Diff.lcOf (G t)) Y y (Z y))
      - (fun y => (Submission.Diff.lcOf (G 0)) Y y (Z y)), ?_, ?_, ?_, ?_⟩
  · intro Y Z hY hZ
    exact (lcOf_apply_smE hLC (G t) Y Z hY hZ).sub_section
      (lcOf_apply_smE hLC (G 0) Y Z hY hZ)
  · intro Y Z hY hZ y
    simp only [Pi.sub_apply]
    abel
  · intro Y Z hY hZ
    exact lcOf_apply_smE hLC (G 0) Y Z hY hZ
  · intro Y Z hY hZ
    exact lcOf_apply_smE hLC (G t) Y Z hY hZ

end Work.Diff.EXT.ATower
