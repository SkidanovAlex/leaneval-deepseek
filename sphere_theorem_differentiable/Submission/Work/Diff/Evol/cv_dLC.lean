import Mathlib
import Submission.Work.Diff.Evol.cv_section
import Submission.Work.Diff.GE.curv_var_prelim
import Submission.Work.Diff.T.dtMet_pairing_smooth
import Submission.Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Smoothness of the field `y ↦ dLC G t₀ Y Z y`

`cv_dLC_smooth`: for smooth `Y`, `Z` and a smooth family `G` of metrics, the section
`y ↦ dLC G t₀ Y Z y` (the first variation of the Levi-Civita connection) is smooth at every point.
This is proved by exhibiting its pairings with smooth fields (`Work.Diff.GE.dLC_pairing`) as smooth
functions and appealing to `cv_section_smooth_of_pairings`.

Also `cv_lcOf_arg_smooth`: the field `y ↦ ∇^{t₀}_Y Z y` is smooth (Levi-Civita connection of a
smooth metric applied to smooth fields).
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

namespace Work.Diff.Evol

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [T2Space M]

/-- The Levi-Civita connection of a smooth metric, applied to smooth fields, is smooth. -/
theorem cv_lcOf_arg_smooth (hLC : LCSmooth I M) (g : SMet I M)
    {Y Z : Π y : M, TangentSpace I y} (hY : CMDiff ∞ (T% Y)) (hZ : CMDiff ∞ (T% Z)) :
    CMDiff ∞ (T% (fun y : M ↦ lcOf g Z y (Y y))) := by
  letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun y : M ↦ TangentSpace I y) := inferInstance
  have hcov : ContMDiffCovariantDerivative (lcOf g) ∞ := (hLC g).1.some
  exact Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply
    (lcOf g) hcov hZ hY

/-- **Smoothness of the first variation of the connection as a field.** -/
theorem cv_dLC_smooth (hLC : LCSmooth I M) (hLV : LCVariation I M)
    {G : ℝ → SMet I M} {J : Set ℝ} (hJopen : IsOpen J) (hJs : JointSmooth G J)
    {t₀ : ℝ} (ht₀ : t₀ ∈ J)
    (Y Z : Π y : M, TangentSpace I y) (hY : CMDiff ∞ (T% Y)) (hZ : CMDiff ∞ (T% Z)) (x : M) :
    CMDiffAt ∞ (T% (fun y : M ↦ dLC G t₀ Y Z y)) x := by
  refine cv_section_smooth_of_pairings (I := I) (M := M) (g := G t₀) (x := x) ?_
  intro W hW
  have hform : (fun y : M ↦ (G t₀).inner y (dLC G t₀ Y Z y) (W y))
      = fun y : M ↦ (1 / 2 : ℝ) * Work.Diff.T.dtKoszulForm G t₀ Y Z W y
          - dtMet G t₀ y (lcOf (G t₀) Z y (Y y)) (W y) := by
    funext y
    exact Work.Diff.GE.dLC_pairing (I := I) (M := M) hLV hJopen hJs ht₀ hY hZ hW y
  rw [hform]
  have h1 : ContMDiffAt I 𝓘(ℝ,ℝ) ∞
      (fun y : M ↦ (1 / 2 : ℝ) * Work.Diff.T.dtKoszulForm G t₀ Y Z W y) x :=
    (contMDiffAt_const (c := (1 / 2 : ℝ))).mul
      (cv_dtKoszulForm_at (I := I) (M := M) hJopen hJs ht₀ Y Z W hY hZ hW x)
  exact h1.sub (Work.Diff.T.dtMet_pairing_smooth hJopen hJs ht₀
    (cv_lcOf_arg_smooth (I := I) (M := M) hLC (G t₀) hY hZ) hW x)

end Work.Diff.Evol
