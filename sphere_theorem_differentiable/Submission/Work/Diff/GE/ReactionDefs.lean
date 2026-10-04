import Mathlib
import Submission.Work.Diff.GE.NablaRm

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The reaction form of Hamilton's curvature evolution (definitions)

This module collects the *definitions* shared by the lemmas that build the evolution equations of
the curvature and of `∇Rm` in the GE area.

`reactionFormAt F g x a b c d` evaluates, on the four vectors `a b c d`, the `(0,4)`-tensor whose
components in the chosen orthonormal frame `onFrame g x` are `F (rmC g x) i j k l`, where `F` is a
map on curvature arrays.  The special case `F = Q` is exactly the workspace's `qFormAt` (Hamilton's
reaction form `Q(Rm)`); the general form lets one state the *structure* of the true
fixed-vector reaction of the curvature under a Ricci flow (which is `Q(Rm)` plus the Ricci-action
terms coming from the derivative of the metric and of the connection) without committing to the
explicit contraction coefficients.

Nothing in this file is a mathematical statement beyond the trivial `reactionFormAt Q = qFormAt`.
-/

set_option linter.unusedSectionVars false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.GE

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The general reaction form: the `(0,4)`-tensor whose components in the chosen orthonormal frame
are `F (rmC g x)`, evaluated on the four vectors `a b c d`.  The coefficients of the frame vectors
are the metric inner products with the four vectors. -/
noncomputable def reactionFormAt (F : Curv4 (Module.finrank ℝ E) → Curv4 (Module.finrank ℝ E))
    (g : SMet I M) (x : M) (a b c d : TangentSpace I x) : ℝ :=
  let e := onFrame g x
  ∑ i, ∑ j, ∑ k, ∑ l,
    (g.inner x (e i) a * g.inner x (e j) b * g.inner x (e k) c * g.inner x (e l) d)
      * (F (rmC g x)) i j k l

/-- The special case `F = Q` is the workspace's `qFormAt`. -/
lemma reactionFormAt_Q (g : SMet I M) (x : M) (a b c d : TangentSpace I x) :
    reactionFormAt Q g x a b c d = qFormAt g x a b c d := rfl

end Work.Diff.GE

namespace Work.Diff.GE

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The covariant derivative `∇_v (ΔRm)` of the `(0,4)`-tensor field `y ↦ ΔRm(y) = lapRmAt g y`,
evaluated at `x` on the four vectors `a b c d` (the standard `Ext` pattern: the derivative of the
component expression minus the four tensorialising corrections).  The identity relating this to the
rough Laplacian `Δ(∇Rm) = lapCovRmAt` of `∇Rm` is the Weitzenböck/Ricci commutation identity; see
the lemma `Work.Diff.GE.covLapRm_le_lapCovRm`. -/
noncomputable def covLapRmAt (g : SMet I M) (x : M) (v a b c d : TangentSpace I x) : ℝ :=
  mvfderiv I (fun y : M ↦ lapRmAt g y (smoothExt x a y) (smoothExt x b y) (smoothExt x c y)
      (smoothExt x d y)) x v
    - lapRmAt g x (lcOf g (smoothExt x a) x v) b c d
    - lapRmAt g x a (lcOf g (smoothExt x b) x v) c d
    - lapRmAt g x a b (lcOf g (smoothExt x c) x v) d
    - lapRmAt g x a b c (lcOf g (smoothExt x d) x v)

end Work.Diff.GE

namespace Work.Diff.GE

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The covariant derivative `∇_v (F(Rm))` of the `(0,4)`-tensor field `y ↦ F(Rm)(y) = F (rmC g y)`
(hypothetically) evaluated at `x` on the four vectors `a b c d`, in the standard `Ext` pattern: the
derivative of the component expression minus the four tensorialising corrections.  This is the
tensorial object whose bound `≤ C |Rm| |∇Rm| ‖v‖‖a‖‖b‖‖c‖‖d‖` (lemma
`Work.Diff.GE.covReactionFormAt_le`) is the "reaction derivative" input of the `∇Rm` evolution
estimate. -/
noncomputable def covReactionFormAt
    (F : Curv4 (Module.finrank ℝ E) → Curv4 (Module.finrank ℝ E))
    (g : SMet I M) (x : M) (v a b c d : TangentSpace I x) : ℝ :=
  mvfderiv I (fun y : M ↦ reactionFormAt F g y (smoothExt x a y) (smoothExt x b y)
      (smoothExt x c y) (smoothExt x d y)) x v
    - reactionFormAt F g x (lcOf g (smoothExt x a) x v) b c d
    - reactionFormAt F g x a (lcOf g (smoothExt x b) x v) c d
    - reactionFormAt F g x a b (lcOf g (smoothExt x c) x v) d
    - reactionFormAt F g x a b c (lcOf g (smoothExt x d) x v)

end Work.Diff.GE

namespace Work.Diff.GE

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- `IsConnVar G t x X Y w` says that `w` is the time derivative at `t` of the connection applied to
the two smooth fields `X`, `Y` at the point `x`, i.e. of `∇_{X}Y`, as given by the contract
`LCVariation` with `h = dtMet G t`: for every smooth field `Z`,
`⟪w, Z⟫ = ½(covDerivSym2 h X Y Z + covDerivSym2 h Y X Z − covDerivSym2 h Z X Y)`.
This is the (one half of the) Koszul combination that the variation of the Levi-Civita connection
produced; `LCVariation` supplies the *existence* of such a `w` for every `X`, `Y`. -/
def IsConnVar (G : ℝ → SMet I M) (t : ℝ) (x : M)
    (X Y : Π y : M, TangentSpace I y) (w : TangentSpace I x) : Prop :=
  ∀ Z : Π y : M, TangentSpace I y, CMDiff ∞ (T% Z) →
    (G t).inner x w (Z x) =
      (1 / 2 : ℝ) * (covDerivSym2 (lcOf (G t)) (dtMet G t) X Y Z x
        + covDerivSym2 (lcOf (G t)) (dtMet G t) Y X Z x
        - covDerivSym2 (lcOf (G t)) (dtMet G t) Z X Y x)

end Work.Diff.GE
