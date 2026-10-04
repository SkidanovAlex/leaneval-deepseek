import Mathlib
import Submission.Diff.Evol
import Submission.Work.Diff.T.lcOf_apply_inner_koszul
import Submission.Work.Diff.T.lc_variation
import Submission.Work.Diff.T.dtMet_pairing_smooth
import Submission.Work.Diff.T.metric_pairing_smooth
import Submission.Work.Diff.T.metric_family_deriv
import Submission.Work.Diff.T.hasDerivAt_metric_inner_moving
import Submission.Work.Diff.T.mvfderiv_frameVector_real
import Submission.Work.Diff.Evol.cv_prelim
import Submission.Work.Diff.Evol.cv_section
import Submission.Work.Diff.Evol.cv_dLC
import Submission.Work.Diff.Evol.cv_product
import Submission.Work.Diff.Evol.cv_compose
import Submission.Work.Diff.GE.curv_var_prelim

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# CONTRACT CV: the first variation of the curvature

`∂ₜ R(X,Y)Z = (∇_X A)(Y,Z) − (∇_Y A)(X,Z)`, `A = ∂ₜ∇`, for fixed smooth fields `X`, `Y`, `Z`.

The proof is assembled from

* `Work.Diff.Evol.cv_compose_lcOf_deriv` (the product rule for the composed connection), applied to
  `(X,Y)` and to `(Y,X)`;
* `Work.Diff.GE.hasDerivAt_lcOf_fixed` for the `∇_{[X,Y]}Z` term;
* torsion-freeness (`Work.Diff.T.lcOf_torsion_free`) and the definition of `covDLC`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

namespace Work.Diff.Evol

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

theorem curv_variation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hLC : LCSmooth I M) (hLV : LCVariation I M) :
    CurvVariation I M := by
  intro G J hJopen hJs t₀ ht₀ X Y Z hX hY hZ x
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(G t₀).toRiemannianMetric⟩
  -- the two product rules
  have h1 := cv_compose_lcOf_deriv (I := I) (M := M) hLC hLV hJopen hJs ht₀ X Y Z hX hY hZ x
  have h2 := cv_compose_lcOf_deriv (I := I) (M := M) hLC hLV hJopen hJs ht₀ Y X Z hY hX hZ x
  -- the bracket term
  have hbr : CMDiff ∞ (T% (mlieBracket I X Y)) := cv_mlieBracket_cmdiff hX hY
  have h3 := Work.Diff.GE.hasDerivAt_lcOf_fixed (I := I) (M := M) hLV hJopen hJs ht₀ hbr hZ x
  -- torsion-freeness of `lcOf (G t₀)`
  have htor : (fun y : M ↦ lcOf (G t₀) Y y (X y) - lcOf (G t₀) X y (Y y)) = mlieBracket I X Y :=
    funext fun y ↦ Work.Diff.T.lcOf_torsion_free (I := I) (M := M) (G t₀) hX hY y
  have hD3 : dLC G t₀ (mlieBracket I X Y) Z x
      = dLC G t₀ (fun y : M ↦ lcOf (G t₀) Y y (X y) - lcOf (G t₀) X y (Y y)) Z x := by
    rw [← htor]
  have hlf : dLC G t₀ (fun y : M ↦ lcOf (G t₀) Y y (X y) - lcOf (G t₀) X y (Y y)) Z x
      = dLC G t₀ (fun y : M ↦ lcOf (G t₀) Y y (X y)) Z x
        - dLC G t₀ (fun y : M ↦ lcOf (G t₀) X y (Y y)) Z x :=
    Work.Diff.GE.dLC_sub_fst (I := I) (M := M) hLV hJopen hJs ht₀
      (cv_lcOf_arg_smooth (I := I) (M := M) hLC (G t₀) hX hY)
      (cv_lcOf_arg_smooth (I := I) (M := M) hLC (G t₀) hY hX) hZ x
  -- the derivative of the curvature
  have htot : HasDerivAt (fun t : ℝ ↦ curv (lcOf (G t)) X Y Z x)
      (lcOf (G t₀) (fun y : M ↦ dLC G t₀ Y Z y) x (X x)
        + dLC G t₀ X (fun y : M ↦ lcOf (G t₀) Z y (Y y)) x
        - (lcOf (G t₀) (fun y : M ↦ dLC G t₀ X Z y) x (Y x)
          + dLC G t₀ Y (fun y : M ↦ lcOf (G t₀) Z y (X y)) x)
        - dLC G t₀ (mlieBracket I X Y) Z x) t₀ :=
    (h1.sub h2).sub h3
  have hfinal : lcOf (G t₀) (fun y : M ↦ dLC G t₀ Y Z y) x (X x)
        + dLC G t₀ X (fun y : M ↦ lcOf (G t₀) Z y (Y y)) x
        - (lcOf (G t₀) (fun y : M ↦ dLC G t₀ X Z y) x (Y x)
          + dLC G t₀ Y (fun y : M ↦ lcOf (G t₀) Z y (X y)) x)
        - dLC G t₀ (mlieBracket I X Y) Z x
      = covDLC G t₀ X Y Z x - covDLC G t₀ Y X Z x := by
    rw [hD3, hlf]
    simp only [covDLC]
    abel
  rw [hfinal] at htot
  exact htot

end Work.Diff.Evol
