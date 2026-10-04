import Mathlib
import Submission.Work.Diff.GE.curvbasic
import Submission.Work.Diff.GE.dRmPhi
import Submission.Work.Diff.GE.Kato3.CovRmKit
import Submission.Work.Diff.Evol.Deps
import Submission.Work.EXT.rmP_pair_symm

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.Evol

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

/-- **Pair symmetry of `∇Rm`.**  `(∇_v Rm)(a,b,c,d) = (∇_v Rm)(c,d,a,b)`.

`covRm = dRmPhi` on the chosen extensions (`Submission.Work.Diff.GE.dRmPhi`,
`covRm_eq_dRmPhi`), and `dRmPhi` is `mvfderiv` of the component function of `rmP` plus four
connection corrections, so the pair symmetry follows from the pointwise pair symmetry of `rmP`
(`g (R(a,b)d) c = g (R(c,d)b) a`); the four correction terms map onto each other under the swap.
(`Submission.Work.Diff.L.rmP_pair_exchange` proves it but lives in another import family; if it is not
importable here, re-derive it from `Submission.CurvatureVec`, or from `rmP`'s definition and
`curvVec_eq`.)  Stay in the chain of `curvbasic`: do NOT import
`Submission/Work/Diff/GE/bianchi_kato_defs.lean` or `.../dRSec_bianchi.lean` (name clashes).
State the manifold hypothesis at the SMOOTH level, as written. -/
theorem covRm_pair
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (((⊤ : ℕ∞) : WithTop ℕ∞)) M]
    [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (x : M)
    (v a b c d : TangentSpace I x) :
    Submission.Diff.covRm g x v a b c d = Submission.Diff.covRm g x v c d a b := by
  -- Abbreviation for the component function of `rmP` on the four chosen extensions.
  set F : M → ℝ :=
    fun y : M => Submission.Diff.rmP g y (smoothExt x a y) (smoothExt x b y)
      (smoothExt x c y) (smoothExt x d y) with hF
  set G : M → ℝ :=
    fun y : M => Submission.Diff.rmP g y (smoothExt x c y) (smoothExt x d y)
      (smoothExt x a y) (smoothExt x b y) with hG
  -- Pointwise pair symmetry of `rmP` (`⟪R(a,b)d, c⟫ = ⟪R(c,d)b, a⟫`).
  have hpt : ∀ y : M, F y = G y := by
    intro y
    rw [hF, hG]
    exact Work.EXT.rmP_pair_symm hLC g y _ _ _ _
  -- Hence the two derivative terms agree.
  have hderiv : mvfderiv I F x v = mvfderiv I G x v :=
    congrArg (fun (L : TangentSpace I x →L[ℝ] ℝ) => L v)
      (Work.Diff.GE.mvfderiv_congr_eventuallyEq (Filter.Eventually.of_forall hpt))
  -- Each of the four connection corrections of the left-hand side is the corresponding
  -- correction of the right-hand side, by pair symmetry of `rmP`.
  have e₁ : Submission.Diff.rmP g x (lcOf g (smoothExt x a) x v) b c d
      = Submission.Diff.rmP g x c d (lcOf g (smoothExt x a) x v) b :=
    Work.EXT.rmP_pair_symm hLC g x _ _ _ _
  have e₂ : Submission.Diff.rmP g x a (lcOf g (smoothExt x b) x v) c d
      = Submission.Diff.rmP g x c d a (lcOf g (smoothExt x b) x v) :=
    Work.EXT.rmP_pair_symm hLC g x _ _ _ _
  have e₃ : Submission.Diff.rmP g x a b (lcOf g (smoothExt x c) x v) d
      = Submission.Diff.rmP g x (lcOf g (smoothExt x c) x v) d a b :=
    Work.EXT.rmP_pair_symm hLC g x _ _ _ _
  have e₄ : Submission.Diff.rmP g x a b c (lcOf g (smoothExt x d) x v)
      = Submission.Diff.rmP g x c (lcOf g (smoothExt x d) x v) a b :=
    Work.EXT.rmP_pair_symm hLC g x _ _ _ _
  simp only [Submission.Diff.covRm, hF, hG] at hderiv ⊢
  rw [hderiv, e₁, e₂, e₃, e₄]
  ring

end Work.Diff.Evol
