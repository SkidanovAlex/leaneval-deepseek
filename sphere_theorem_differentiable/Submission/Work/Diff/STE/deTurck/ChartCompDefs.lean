import Mathlib
import Submission.Work.Diff.STE.DeTurckJet
import Submission.Work.Diff.GE.norms_defs
import Submission.Work.Diff.EXT.dOp_koszulPair_eq_sKzD
import Submission.Work.Diff.STE.deTurck.koszulPair_eq_jKz

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The chart-coordinate expression of the DeTurck field `W(g) = tr_g(∇^g - ∇^{g̃})`

This module fixes the *coordinate* (chart-coordinate, i.e. model-space) expression that the
manifold function

`Work.Diff.STE.DeTurck.deTurckChartComp g gbar x₀ · c`

reduces to in the chart at `x₀`, and in terms of which its coordinate derivative is computed in
`Work.Diff.STE.deTurck.deTurckChartComp_mvfderiv`.

Fix the chart centre `x₀`, the chart coordinate `y = (extChartAt I x₀) p`, and let

`A = Work.Diff.EXT.chartMatFun g x₀ : E → MatE`     (the chart matrix of `g`),

`L = fderiv ℝ A : E → LinMat`                        (its first coordinate jet),

`B = fderiv ℝ L : E → BilMat`                        (its second coordinate jet),

with `Ā`, `L̄`, `B̄` the same data for the background metric `gbar`.  Then

* `coGamU A c a b y = ∑ p γ^{cp} Γ_{abp}` is the upper Christoffel symbol `Γ^c_{ab}`, where
  `γ = (A y)⁻¹ = Work.Diff.EXT.jInv (A y)` and `Γ = Work.Diff.EXT.jKz (L y)`;
* `coPhi A Ā c y = ∑_{ab} γ^{ab}(Γ^c_{ab} - Γ̃^c_{ab})` is the `c`-th component of the DeTurck
  field `W = tr_g(∇^g - ∇^{g̃})`.

These are exactly the functions of `y` whose Fréchet derivatives are `jdGamU` and `jdWU`:

`d(coGamU A c a b)(y) = jdGamU (A y) (L y) (B y) · c a b`,
`d(coPhi A Ā c)(y) = jdWU (A y) (L y) (B y) (Ā y) (L̄ y) (B̄ y) · c`.

Nothing here is proved; the file only fixes the vocabulary and a few elementary rewriting lemmas
used both by the derivative computation and by the identification of the manifold function
`deTurckChartComp` with `coPhi` in the chart.
-/

set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Bundle Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]

namespace Work.Diff.STE.deTurck

open Work.Diff.EXT Work.Diff.STE.DeTurck

noncomputable section

/-- The chart-coordinate expression for the upper Christoffel symbol `Γ^c_{ab}` of the metric whose
chart matrix is `A`: `coGamU A c a b y = ∑_p γ^{cp}(y) Γ_{abp}(y)` with `γ = (A y)⁻¹` and
`Γ_{abp} = Work.Diff.EXT.jKz (fderiv ℝ A y) a b p`. -/
def coGamU (A : E → MatE (E := E)) (c a b : Idx E) : E → ℝ :=
  fun y => ∑ p, jInv (A y) c p * jKz (fderiv ℝ A y) a b p

/-- The chart-coordinate expression for the `c`-th component of the DeTurck field
`W = tr_g(∇^g - ∇^{g̃})`: `coPhi A Ā c y = ∑_{ab} γ^{ab}(y)(Γ^c_{ab}(y) - Γ̃^c_{ab}(y))`. -/
def coPhi (A Ā : E → MatE (E := E)) (c : Idx E) : E → ℝ :=
  fun y => ∑ a, ∑ b, jInv (A y) a b * (coGamU A c a b y - coGamU Ā c a b y)

@[simp] lemma coGamU_apply (A : E → MatE (E := E)) (c a b : Idx E) (y : E) :
    coGamU A c a b y = ∑ p, jInv (A y) c p * jKz (fderiv ℝ A y) a b p := rfl

@[simp] lemma coPhi_apply (A Ā : E → MatE (E := E)) (c : Idx E) (y : E) :
    coPhi A Ā c y
      = ∑ a, ∑ b, jInv (A y) a b * (coGamU A c a b y - coGamU Ā c a b y) := rfl

/-- The chart matrix of a Riemannian metric is symmetric. -/
theorem chartMatFun_symm
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    (g : Submission.Diff.SMet I M) (x₀ : M) (y : E) (i j : Idx E) :
    chartMatFun g x₀ y i j = chartMatFun g x₀ y j i :=
  g.symm ((extChartAt I x₀).symm y) _ _

/-- The matrix of the first jet of the chart matrix of a Riemannian metric is symmetric. -/
theorem fderiv_chartMatFun_symm
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (g : Submission.Diff.SMet I M) (x₀ : M) {y : E} (hy : y ∈ (extChartAt I x₀).target)
    (k i j : Idx E) :
    (fderiv ℝ (chartMatFun g x₀) y (bB (E := E) k)) i j
      = (fderiv ℝ (chartMatFun g x₀) y (bB (E := E) k)) j i :=
  kz_chartMatFun_swap g x₀ hy k i j

end

end Work.Diff.STE.deTurck
