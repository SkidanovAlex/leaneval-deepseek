import Mathlib
import Submission.Work.Diff.L.Defs
import Submission.Work.Diff.GE.Gest.Base
import Submission.Work.Diff.T.lcOf_apply_inner_koszul

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# A torsion-free metric-compatible connection is the Levi-Civita connection

`Work.Diff.L.lc_eq_cov`: on *smooth* vector fields the challenge's connection `cov` (assumed
torsion-free and compatible with the instance metric in the sense of
`LeanEval.Geometry.SphereTheorem.IsMetricCompatible`) agrees with `lcOf (initSMet)`, Mathlib's
Levi-Civita connection of the ambient metric.

The proof is the classical Koszul argument, done by comparing the two Koszul formulae:

* `Work.Diff.T.lcOf_apply_inner_koszul` gives the Koszul formula for `lcOf` (Mathlib's
  `leviCivitaConnection_apply_inner` transported to explicit inner products);
* `cov_koszul` below derives the *same* formula for `cov` from the two hypotheses;
* a tangent vector is determined by its inner products with smooth fields (`smoothExt`),
  which gives the equality.

Note that `hLC : LCSmooth I M` is not needed: uniqueness of the Levi-Civita connection is
independent of the smoothness of `lcOf`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Work.Diff.L

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

section Helpers

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

/-- **Koszul formula for a torsion-free metric-compatible connection.**  For smooth vector fields
`X`, `Y`, `Z` the pairing `⟪∇_X Y, Z⟫` of the challenge's connection `cov` is given by the
expression on the right, which does not involve `cov`.  Only the compatibility hypothesis `hmet`
(which is stated for globally smooth fields) and torsion-freeness are used. -/
theorem cov_koszul
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {X Y Z : Π x : M, TangentSpace I x} (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y))
    (hZ : CMDiff ∞ (T% Z)) (x : M) :
    inner ℝ (cov Y x (X x)) (Z x) =
      (mvfderiv I (fun y : M ↦ inner ℝ (Y y) (Z y)) x (X x)
        + mvfderiv I (fun y : M ↦ inner ℝ (Z y) (X y)) x (Y x)
        - mvfderiv I (fun y : M ↦ inner ℝ (X y) (Y y)) x (Z x)
        - inner ℝ (Y x) (mlieBracket I X Z x)
        - inner ℝ (Z x) (mlieBracket I Y X x)
        + inner ℝ (X x) (mlieBracket I Z Y x)) / 2 := by
  have hX' : MDiffAt (T% X) x := hX.contMDiffAt.mdifferentiableAt (by simp)
  have hY' : MDiffAt (T% Y) x := hY.contMDiffAt.mdifferentiableAt (by simp)
  have hZ' : MDiffAt (T% Z) x := hZ.contMDiffAt.mdifferentiableAt (by simp)
  have htor' : ∀ {X Y : Π x : M, TangentSpace I x} {x : M},
      MDiffAt (T% X) x → MDiffAt (T% Y) x →
        cov Y x (X x) - cov X x (Y x) = mlieBracket I X Y x :=
    fun hX hY => (CovariantDerivative.torsion_eq_zero_iff (cov := cov)).mp htor hX hY
  have eq1a := hmet Y Z hY hZ x (X x)
  have eq2a := hmet Z X hZ hX x (Y x)
  have eq3a := hmet X Y hX hY x (Z x)
  have eq1b : inner ℝ (Y x) (cov Z x (X x)) - inner ℝ (Y x) (cov X x (Z x))
      = inner ℝ (Y x) (mlieBracket I X Z x) := by
    have h := congrArg (fun w => inner ℝ (Y x) w) (htor' (X := X) (Y := Z) hX' hZ')
    rw [inner_sub_right] at h
    exact h
  have eq2b : inner ℝ (Z x) (cov X x (Y x)) - inner ℝ (Z x) (cov Y x (X x))
      = inner ℝ (Z x) (mlieBracket I Y X x) := by
    have h := congrArg (fun w => inner ℝ (Z x) w) (htor' (X := Y) (Y := X) hY' hX')
    rw [inner_sub_right] at h
    exact h
  have eq3b : inner ℝ (X x) (cov Y x (Z x)) - inner ℝ (X x) (cov Z x (Y x))
      = inner ℝ (X x) (mlieBracket I Z Y x) := by
    have h := congrArg (fun w => inner ℝ (X x) w) (htor' (X := Z) (Y := Y) hZ' hY')
    rw [inner_sub_right] at h
    exact h
  have eq2a' : mvfderiv I (fun y : M ↦ inner ℝ (Z y) (X y)) x (Y x)
      = inner ℝ (X x) (cov Z x (Y x)) + inner ℝ (Z x) (cov X x (Y x)) := by
    rw [eq2a, real_inner_comm (X x) (cov Z x (Y x))]
  have eq3a' : mvfderiv I (fun y : M ↦ inner ℝ (X y) (Y y)) x (Z x)
      = inner ℝ (Y x) (cov X x (Z x)) + inner ℝ (X x) (cov Y x (Z x)) := by
    rw [eq3a, real_inner_comm (Y x) (cov X x (Z x))]
  have hsym : inner ℝ (Z x) (cov Y x (X x)) = inner ℝ (cov Y x (X x)) (Z x) :=
    real_inner_comm (cov Y x (X x)) (Z x)
  linear_combination (- eq1a - eq2a' + eq3a' - eq1b - eq2b + eq3b - hsym) / 2

/-- **Koszul formula for `lcOf (initSMet)`**, in the exact shape of `cov_koszul`. -/
theorem lcOf_initSMet_koszul
    {X Y Z : Π x : M, TangentSpace I x} (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y))
    (hZ : CMDiff ∞ (T% Z)) (x : M) :
    inner ℝ (lcOf (initSMet (I := I) (M := M)) Y x (X x)) (Z x) =
      (1 / 2 : ℝ) * (mvfderiv I (fun y : M ↦ inner ℝ (Y y) (Z y)) x (X x)
        + mvfderiv I (fun y : M ↦ inner ℝ (Z y) (X y)) x (Y x)
        - mvfderiv I (fun y : M ↦ inner ℝ (X y) (Y y)) x (Z x)
        - inner ℝ (Y x) (mlieBracket I X Z x)
        - inner ℝ (Z x) (mlieBracket I Y X x)
        + inner ℝ (X x) (mlieBracket I Z Y x)) := by
  have h := Work.Diff.T.lcOf_apply_inner_koszul (I := I) (M := M)
    (G := fun _ : ℝ => initSMet (I := I) (M := M)) (t := 0) X Y Z hX hY hZ x
  simpa only [initSMet_inner] using h

end Helpers

/-- A torsion-free connection compatible with the ambient metric is the Levi-Civita connection of
that metric, on smooth fields. -/
theorem lc_eq_cov
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M]
    [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    [ContMDiffCovariantDerivative cov ∞]
    (htor : cov.torsion = 0) (hmet : IsMetricCompatible cov)
    (hLC : LCSmooth I M) :
    ∀ (Y : Π x : M, TangentSpace I x), CMDiff ∞ (T% Y) →
      ∀ (x : M) (v : TangentSpace I x),
        lcOf (initSMet (I := I) (M := M)) Y x v = cov Y x v := by
  intro Y hY x v
  -- the two Koszul formulae agree
  have key : ∀ (Z : Π y : M, TangentSpace I y), CMDiff ∞ (T% Z) →
      inner ℝ (lcOf (initSMet (I := I) (M := M)) Y x v) (Z x) = inner ℝ (cov Y x v) (Z x) := by
    intro Z hZ
    have hXs : CMDiff ∞ (T% (smoothExt x v)) := Work.Diff.GE.Gest.smoothExt_contMDiff x v
    have hX0 : smoothExt x v x = v := Work.Diff.GE.Gest.smoothExt_apply_self x v
    have hlc := lcOf_initSMet_koszul (I := I) (M := M) hXs hY hZ x
    have hcv := cov_koszul (I := I) (M := M) cov hmet htor hXs hY hZ x
    rw [hX0] at hlc hcv
    rw [hcv, hlc]
    ring
  -- a vector is determined by its pairings with smooth fields
  have hzz : inner ℝ (lcOf (initSMet (I := I) (M := M)) Y x v - cov Y x v)
      (lcOf (initSMet (I := I) (M := M)) Y x v - cov Y x v) = 0 := by
    have hZ : CMDiff ∞ (T% (smoothExt x (lcOf (initSMet (I := I) (M := M)) Y x v
        - cov Y x v))) := Work.Diff.GE.Gest.smoothExt_contMDiff x _
    have h := key (smoothExt x (lcOf (initSMet (I := I) (M := M)) Y x v - cov Y x v)) hZ
    rw [Work.Diff.GE.Gest.smoothExt_apply_self x
      (lcOf (initSMet (I := I) (M := M)) Y x v - cov Y x v)] at h
    rw [inner_sub_left, h, sub_self]
  exact sub_eq_zero.mp (inner_self_eq_zero.mp hzz)

end Work.Diff.L
