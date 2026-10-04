import Mathlib
import Submission.Work.Diff.GE.swap_defs
import Submission.Work.Diff.GE.kato_covRm_field
import Submission.Work.Diff.GE.kato_mvfderiv_inner_lc
import Submission.Work.Diff.GE.contMDiff_rmP_fields

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The covariant derivative of the curvature section `y ↦ R(Y,P)A(y)`

`Work.Diff.GE.covAlong_curv_fields` is the Leibniz rule for the covariant derivative of the section
`y ↦ curv (lcOf g) Ys Ps As y`: it is `(∇_X R)(Y,P)A` (the vector `curvDeriv`) plus the three terms
obtained by differentiating the three arguments `Y`, `P`, `A`.

The proof reduces the vector identity to the identity of all pairings with smooth fields `Z`: the
pairing `g(∇_X(R(Y,P)A), Z)` is `mvfderiv (g(R(Y,P)A, Z)) - g(R(Y,P)A, ∇_X Z)`
(`Work.Diff.GE.kato_mvfderiv_inner_lc`, metric compatibility, for which the section `R(Y,P)A` is
smooth by `Work.Diff.GE.contMDiff_curv_fields`), and `g(R(Y,P)A, Z) = rmP g y (Y y) (P y) (Z y) (A y)`
is a Leibniz expression whose covariant derivative is computed by `Work.Diff.GE.kato_covRm_field`;
the remaining `∇Rm`-term is identified with `⟪curvDeriv g x X Y P A, Z⟫` by
`Work.Diff.GE.curvDeriv_pairing`.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.GE

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

/-- **Leibniz rule for the curvature section.**  With `∇_X Y` the section `fun y => (lcOf g) Y y (X y)`:
`∇_X (R(Y,P)A) = (∇_X R)(Y,P)A + R(∇_X Y, P)A + R(Y, ∇_X P)A + R(Y, P)(∇_X A)`. -/
theorem covAlong_curv_fields (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    {Xs Ys Ps As : Π y : M, TangentSpace I y}
    (hXs : CMDiff ∞ (T% Xs)) (hYs : CMDiff ∞ (T% Ys)) (hPs : CMDiff ∞ (T% Ps))
    (hAs : CMDiff ∞ (T% As)) :
    (lcOf g) (fun y : M => curv (lcOf g) Ys Ps As y) x (Xs x)
      = curvDeriv g x (Xs x) (Ys x) (Ps x) (As x)
        + curv (lcOf g) (fun y : M => (lcOf g) Ys y (Xs y)) Ps As x
        + curv (lcOf g) Ys (fun y : M => (lcOf g) Ps y (Xs y)) As x
        + curv (lcOf g) Ys Ps (fun y : M => (lcOf g) As y (Xs y)) x := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  obtain ⟨hcov, -, -⟩ := hLC g
  obtain ⟨hcov⟩ := hcov
  -- the four sections occurring on the right
  have hdYs : CMDiff ∞ (T% (fun y : M => (lcOf g) Ys y (Xs y))) :=
    Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply
      (lcOf g) hcov hYs hXs
  have hdPs : CMDiff ∞ (T% (fun y : M => (lcOf g) Ps y (Xs y))) :=
    Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply
      (lcOf g) hcov hPs hXs
  have hdAs : CMDiff ∞ (T% (fun y : M => (lcOf g) As y (Xs y))) :=
    Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply
      (lcOf g) hcov hAs hXs
  have hcur : CMDiff ∞ (T% (fun y : M => curv (lcOf g) Ys Ps As y)) :=
    contMDiff_curv_fields (lcOf g) hcov hYs hPs hAs
  -- the pairing identity
  have hconj : ∀ Zs : Π y : M, TangentSpace I y, CMDiff ∞ (T% Zs) →
      g.inner x ((lcOf g) (fun y : M => curv (lcOf g) Ys Ps As y) x (Xs x)) (Zs x)
        = g.inner x (curvDeriv g x (Xs x) (Ys x) (Ps x) (As x)
            + curv (lcOf g) (fun y : M => (lcOf g) Ys y (Xs y)) Ps As x
            + curv (lcOf g) Ys (fun y : M => (lcOf g) Ps y (Xs y)) As x
            + curv (lcOf g) Ys Ps (fun y : M => (lcOf g) As y (Xs y)) x) (Zs x) := by
    intro Zs hZs
    -- metric compatibility for the pairing of the smooth curvature section with `Zs`
    have hmet := kato_mvfderiv_inner_lc (I := I) (M := M) g x (Xs x)
      (Y := fun y : M => curv (lcOf g) Ys Ps As y) (Z := Zs) hcur hZs
    have hpair : (fun y : M => g.inner y (curv (lcOf g) Ys Ps As y) (Zs y))
        = fun y : M => rmP g y (Ys y) (Ps y) (Zs y) (As y) := by
      funext y
      rw [curv_section_apply_eq_rmVec (I := I) (M := M) hLC g hYs hPs hAs y]
      rfl
    have hmet' : mvfderiv I (fun y : M => rmP g y (Ys y) (Ps y) (Zs y) (As y)) x (Xs x)
        = g.inner x ((lcOf g) (fun y : M => curv (lcOf g) Ys Ps As y) x (Xs x)) (Zs x)
          + g.inner x (curv (lcOf g) Ys Ps As x) ((lcOf g) Zs x (Xs x)) := by
      rw [← hpair]
      exact hmet
    -- the Leibniz expansion of the same `mvfderiv`
    have hk := (kato_covRm_field (I := I) (M := M) hLC g x Xs Ys Ps Zs As hXs hYs hPs hZs hAs).1
    have hkmv : mvfderiv I (fun y : M => rmP g y (Ys y) (Ps y) (Zs y) (As y)) x (Xs x)
        = covRm g x (Xs x) (Ys x) (Ps x) (Zs x) (As x)
          + rmP g x ((lcOf g) Ys x (Xs x)) (Ps x) (Zs x) (As x)
          + rmP g x (Ys x) ((lcOf g) Ps x (Xs x)) (Zs x) (As x)
          + rmP g x (Ys x) (Ps x) ((lcOf g) Zs x (Xs x)) (As x)
          + rmP g x (Ys x) (Ps x) (Zs x) ((lcOf g) As x (Xs x)) := by
      rw [hk]
      ring
    have h1 : covRm g x (Xs x) (Ys x) (Ps x) (Zs x) (As x)
        = g.inner x (curvDeriv g x (Xs x) (Ys x) (Ps x) (As x)) (Zs x) :=
      (curvDeriv_pairing (I := I) (M := M) hLC g x (Xs x) (Ys x) (Ps x) (As x) (Zs x)).symm
    have h2 : rmP g x ((lcOf g) Ys x (Xs x)) (Ps x) (Zs x) (As x)
        = g.inner x (curv (lcOf g) (fun y : M => (lcOf g) Ys y (Xs y)) Ps As x) (Zs x) := by
      rw [curv_section_apply_eq_rmVec (I := I) (M := M) hLC g hdYs hPs hAs x]
      rfl
    have h3 : rmP g x (Ys x) ((lcOf g) Ps x (Xs x)) (Zs x) (As x)
        = g.inner x (curv (lcOf g) Ys (fun y : M => (lcOf g) Ps y (Xs y)) As x) (Zs x) := by
      rw [curv_section_apply_eq_rmVec (I := I) (M := M) hLC g hYs hdPs hAs x]
      rfl
    have h4 : rmP g x (Ys x) (Ps x) ((lcOf g) Zs x (Xs x)) (As x)
        = g.inner x (curv (lcOf g) Ys Ps As x) ((lcOf g) Zs x (Xs x)) := by
      rw [curv_section_apply_eq_rmVec (I := I) (M := M) hLC g hYs hPs hAs x]
      rfl
    have h5 : rmP g x (Ys x) (Ps x) (Zs x) ((lcOf g) As x (Xs x))
        = g.inner x (curv (lcOf g) Ys Ps (fun y : M => (lcOf g) As y (Xs y)) x) (Zs x) := by
      rw [curv_section_apply_eq_rmVec (I := I) (M := M) hLC g hYs hPs hdAs x]
      rfl
    rw [h4] at hkmv
    rw [h1, h2, h3, h5] at hkmv
    simp only [map_add, ContinuousLinearMap.add_apply]
    linarith [hmet', hkmv]

  -- conclude the vector identity from the pairings
  have hLL : g.inner x ((lcOf g) (fun y : M => curv (lcOf g) Ys Ps As y) x (Xs x))
      ((lcOf g) (fun y : M => curv (lcOf g) Ys Ps As y) x (Xs x))
      = g.inner x (curvDeriv g x (Xs x) (Ys x) (Ps x) (As x)
            + curv (lcOf g) (fun y : M => (lcOf g) Ys y (Xs y)) Ps As x
            + curv (lcOf g) Ys (fun y : M => (lcOf g) Ps y (Xs y)) As x
            + curv (lcOf g) Ys Ps (fun y : M => (lcOf g) As y (Xs y)) x)
          ((lcOf g) (fun y : M => curv (lcOf g) Ys Ps As y) x (Xs x)) := by
    have h := hconj (smoothExt x ((lcOf g) (fun y : M => curv (lcOf g) Ys Ps As y) x (Xs x)))
      (smoothExt_cmdiff x _)
    simpa only [smoothExt_apply] using h
  have hRL : g.inner x ((lcOf g) (fun y : M => curv (lcOf g) Ys Ps As y) x (Xs x))
      (curvDeriv g x (Xs x) (Ys x) (Ps x) (As x)
            + curv (lcOf g) (fun y : M => (lcOf g) Ys y (Xs y)) Ps As x
            + curv (lcOf g) Ys (fun y : M => (lcOf g) Ps y (Xs y)) As x
            + curv (lcOf g) Ys Ps (fun y : M => (lcOf g) As y (Xs y)) x)
      = g.inner x (curvDeriv g x (Xs x) (Ys x) (Ps x) (As x)
            + curv (lcOf g) (fun y : M => (lcOf g) Ys y (Xs y)) Ps As x
            + curv (lcOf g) Ys (fun y : M => (lcOf g) Ps y (Xs y)) As x
            + curv (lcOf g) Ys Ps (fun y : M => (lcOf g) As y (Xs y)) x)
          (curvDeriv g x (Xs x) (Ys x) (Ps x) (As x)
            + curv (lcOf g) (fun y : M => (lcOf g) Ys y (Xs y)) Ps As x
            + curv (lcOf g) Ys (fun y : M => (lcOf g) Ps y (Xs y)) As x
            + curv (lcOf g) Ys Ps (fun y : M => (lcOf g) As y (Xs y)) x) := by
    have h := hconj (smoothExt x (curvDeriv g x (Xs x) (Ys x) (Ps x) (As x)
            + curv (lcOf g) (fun y : M => (lcOf g) Ys y (Xs y)) Ps As x
            + curv (lcOf g) Ys (fun y : M => (lcOf g) Ps y (Xs y)) As x
            + curv (lcOf g) Ys Ps (fun y : M => (lcOf g) As y (Xs y)) x)) (smoothExt_cmdiff x _)
    simpa only [smoothExt_apply] using h
  have hzero : g.inner x (((lcOf g) (fun y : M => curv (lcOf g) Ys Ps As y) x (Xs x))
        - (curvDeriv g x (Xs x) (Ys x) (Ps x) (As x)
            + curv (lcOf g) (fun y : M => (lcOf g) Ys y (Xs y)) Ps As x
            + curv (lcOf g) Ys (fun y : M => (lcOf g) Ps y (Xs y)) As x
            + curv (lcOf g) Ys Ps (fun y : M => (lcOf g) As y (Xs y)) x))
      (((lcOf g) (fun y : M => curv (lcOf g) Ys Ps As y) x (Xs x))
        - (curvDeriv g x (Xs x) (Ys x) (Ps x) (As x)
            + curv (lcOf g) (fun y : M => (lcOf g) Ys y (Xs y)) Ps As x
            + curv (lcOf g) Ys (fun y : M => (lcOf g) Ps y (Xs y)) As x
            + curv (lcOf g) Ys Ps (fun y : M => (lcOf g) As y (Xs y)) x)) = 0 := by
    simp only [map_sub, ContinuousLinearMap.sub_apply]
    rw [hLL, hRL]
    ring
  have hinner : Inner.inner ℝ (((lcOf g) (fun y : M => curv (lcOf g) Ys Ps As y) x (Xs x))
        - (curvDeriv g x (Xs x) (Ys x) (Ps x) (As x)
            + curv (lcOf g) (fun y : M => (lcOf g) Ys y (Xs y)) Ps As x
            + curv (lcOf g) Ys (fun y : M => (lcOf g) Ps y (Xs y)) As x
            + curv (lcOf g) Ys Ps (fun y : M => (lcOf g) As y (Xs y)) x))
      (((lcOf g) (fun y : M => curv (lcOf g) Ys Ps As y) x (Xs x))
        - (curvDeriv g x (Xs x) (Ys x) (Ps x) (As x)
            + curv (lcOf g) (fun y : M => (lcOf g) Ys y (Xs y)) Ps As x
            + curv (lcOf g) Ys (fun y : M => (lcOf g) Ps y (Xs y)) As x
            + curv (lcOf g) Ys Ps (fun y : M => (lcOf g) As y (Xs y)) x)) = 0 := hzero
  exact sub_eq_zero.mp (inner_self_eq_zero.mp hinner)

end Work.Diff.GE
