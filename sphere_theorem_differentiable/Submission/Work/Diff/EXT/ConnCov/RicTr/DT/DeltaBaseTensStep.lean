import Mathlib
import Submission.Work.Diff.EXT.ConnCov.RicTr.DT.DeltaTower

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The base of the δ-tower is tensorial

The δ-tower chapter of `Submission/Work/Diff/EXT/ConnCov/` (see `deltaTower.lean`) converts the
`∇^{G t}`-tower of the curvature into the `∇^{G 0}`-tower, and needs the level-`0` object

  `deltaBase G t = δ = covDiff G t`,   `δ X Y x = (∇^{G t} X x)(Y x) − (∇^{G 0} X x)(Y x)`,

to be a *tensor*: its value at the base point `x` may only depend on the values `X x`, `Y x` of the
two fields.

That is a special case of a Mathlib fact which we use rather than reprove: **the difference of two
covariant derivatives is a one-form taking values in the endomorphisms of the bundle**,

  `CovariantDerivative.difference cov cov' : Π x, V x →L[ℝ] TₓM →L[ℝ] V x`,

together with its evaluation lemma `IsCovariantDerivativeOn.difference_apply`

  `difference cov cov' x (σ x) = cov σ x − cov' σ x`   (`σ` differentiable at `x`),

i.e. precisely the tensoriality of the difference: the `(d f) ⊗ σ` terms of the two Leibniz rules
coincide and cancel.  (In this workspace that cancellation is also available in explicit form as the
proved `covDiff_smul_section` + `covDiff_add_section` of `deltaTower.lean`; the two routes say the
same thing, and here the bundled Mathlib one-form is shorter and avoids the value-dependence
machine `Work.Diff.GE.field_value_dep_of_linear` and its frame decomposition.)

The two statements below record this in the field form used by the tower:

* `covDiff_eq_difference` — the value of `covDiff` at `x` is the difference one-form evaluated on
  the values of the fields (no smoothness of the *direction* field `Z` is needed, only of the
  section `X` that is being differentiated);
* `deltaBase_tens_step` — hence `deltaBase G t` is tensorial.
-/

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false

namespace Work.Diff.EXT.ConnCov.DT

/-- **`covDiff` is the difference one-form of the two Levi-Civita connections.**

For a *smooth* section `X` and an arbitrary direction field `Z`,

  `covDiff G t X Z x = (difference (lcOf (G t)) (lcOf (G 0))) x (X x) (Z x)`.

The right-hand side depends only on the values of the fields at `x`, which is what makes
`deltaBase G t` a tensor (cf. `deltaBase_tens_step`).  The proof is the evaluation lemma
`IsCovariantDerivativeOn.difference_apply` of the difference of the two covariant derivatives
(`difference` is *defined* as that difference, so the two are interchangeable definitionally) plus
`sub_apply` for the continuous linear maps. -/
theorem covDiff_eq_difference
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    (G : ℝ → Submission.Diff.SMet I M) (t : ℝ)
    (X Z : Π y : M, TangentSpace I y) (x : M)
    (hX : Work.Diff.EXT.ATower.SmE I M X) :
    Work.Diff.EXT.ConnCov.covDiff G t X Z x
      = (CovariantDerivative.difference (Submission.Diff.lcOf (G t))
          (Submission.Diff.lcOf (G 0))) x (X x) (Z x) := by
  -- `covDiff` is a pointwise difference of the two connections, i.e. `sub_apply` of the two CLMs.
  rw [show Work.Diff.EXT.ConnCov.covDiff G t X Z x
      = ((Submission.Diff.lcOf (G t)) X x) (Z x)
        - ((Submission.Diff.lcOf (G 0)) X x) (Z x) from rfl]
  rw [← sub_apply]
  -- tensoriality of the difference of two covariant derivatives (Mathlib), evaluated at `Z x`.
  exact congrArg (fun L : TangentSpace I x →L[ℝ] TangentSpace I x => L (Z x))
    (IsCovariantDerivativeOn.difference_apply
      (hcov := (Submission.Diff.lcOf (G t)).isCovariantDerivativeOnUniv)
      (hcov' := (Submission.Diff.lcOf (G 0)).isCovariantDerivativeOnUniv)
      (x := x) (hx := trivial) (σ := X) (hX.mdifferentiableAt (by simp))).symm

theorem deltaBase_tens_step
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (G : ℝ → Submission.Diff.SMet I M) (t : ℝ) :
    Work.Diff.EXT.ConnCov.DT.VOpTens (I := I) (M := M) (Work.Diff.EXT.ConnCov.DT.deltaBase G t) := by
  intro v v' X X' Y Y' x hv hv' hvv hX hX' hY hY' hXX hYY
  -- `deltaBase G t` ignores its derivative tuple, so the goal is tensoriality of `covDiff`.
  show Work.Diff.EXT.ConnCov.covDiff G t X Y x = Work.Diff.EXT.ConnCov.covDiff G t X' Y' x
  rw [covDiff_eq_difference G t X Y x hX, covDiff_eq_difference G t X' Y' x hX', hXX, hYY]

end Work.Diff.EXT.ConnCov.DT
