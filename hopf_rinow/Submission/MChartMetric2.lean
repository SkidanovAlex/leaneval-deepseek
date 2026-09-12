import Submission.MChartMetric
import Mathlib

/-!
# The coordinate metric is C³ on its chart (stronger smoothness)

Task: prove the final theorem `chart_metric_contDiffOn`.

`Submission.MChartMetric.chart_metric` already gives, on the chart target `U`, a symmetric
positive definite family `g : E → E →L[ℝ] E →L[ℝ] ℝ` agreeing with the fibre inner products
applied to `mfderiv[range I] (extChartAt I p).symm y`, with each *evaluation*
`y ↦ (g y) u v` being `ContDiffAt ℝ 3` at every point of `U`.  This task upgrades that to the
stronger, joint statement needed to run the model ODE theory: on a smaller open set around
`φ p := extChartAt I p p`, the two-argument evaluation is `ContDiffOn ℝ 3`:

    ContDiffOn ℝ 3 (fun q : E × E × E => ((g q.1) q.2.1) q.2.2) (U' ×ˢ univ ×ˢ univ)

Equivalently (and preferred): the map `g : E → E →L[ℝ] E →L[ℝ] ℝ` itself is `ContDiffOn ℝ 3`
on `U'`, where the codomain `E →L[ℝ] E →L[ℝ] ℝ` carries its normed-space structure (it is a
normed space over ℝ since `E` is a finite-dimensional real normed space; if instances are
missing, import/register them as in `Submission/CLMInstances.lean`, or state the theorem with
the uncurried evaluation form above).

## Proof route

Re-run the smoothness part of the proof of `chart_metric`, but establish the joint (or
two-argument) smoothness directly rather than pointwise:
* fix a chart open neighbourhood `U' ∋ φ p` with `closure U' ⊆ (extChartAt I p).target` (or just
  `U' := (extChartAt I p).target ∩ ball (φ p) r` for a small `r`);
* for the section smoothness use the joint version: the map
  `(m, a) ↦ (total-space section with trivialized fibre coordinate a)` is smooth jointly, i.e.
  apply `contMDiffAt_section_iff`-style lemmas in the product or use the smoothness of the
  trivialization `e.symmL ℝ m` in both `m` and the fibre coordinate;
* `ContMDiffAt.inner_bundle` (or its within/prod variants) applied to sections depending
  smoothly on parameters gives joint smoothness of the inner product;
* compose with `(extChartAt I p).symm` and restrict to `U'` to get `ContDiffOn ℝ 3` of the
  evaluations; conclude `ContDiffOn ℝ 3 g U'` (map into the bilinear-form space) via the
  equivalence between smoothness of the curried and uncurried forms (search for lemmas like
  `ContDiffOn.clm_apply`, `contDiffOn_iff_contDiffOn_...` or prove by applying evaluations).

If the exact `ContDiffOn`-of-`g` statement fights you, state and prove the theorem with the
uncurried evaluation formulation:

    ContDiffOn ℝ 3 (fun q : E × E × E => ((g q.1) q.2.1) q.2.2)
      ((U' : Set E) ×ˢ (univ : Set (E × E)))

## Concrete statement to prove (keep the signature)

    theorem chart_metric_contDiffOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E]
        {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
        (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
        [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
        [IsContMDiffRiemannianBundle I ∞ E (fun x : M => TangentSpace I x)]
        [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
        (p : M) :
        ∃ U' : Set E, (extChartAt I p p) ∈ U' ∧ IsOpen U' ∧
          ∃ g : E → E →L[ℝ] E →L[ℝ] ℝ,
            ContDiffOn ℝ 3 g U' ∧
            (∀ y ∈ U', ∀ u v : E, (g y) u v = (g y) v u) ∧
            (∀ y ∈ U', ∀ v : E, v ≠ 0 → 0 < (g y) v v) ∧
            (∀ y ∈ U', ∀ u v : E,
               (g y) u v = (Bundle.RiemannianBundle.g (E := fun x : M => TangentSpace I x)).inner
                             ((extChartAt I p).symm y)
                             ((mfderiv[range I] (extChartAt I p).symm y) u)
                             ((mfderiv[range I] (extChartAt I p).symm y) v))

(If `ContDiffOn ℝ 3 g U'` with codomain the bilinear maps needs instances that are painful,
fall back to the uncurried-evaluation formulation above — that is acceptable, but prefer the
`ContDiffOn ℝ 3 g U'` form.)

Do NOT change the statement of `chart_metric_contDiffOn`.  You may add helper definitions/lemmas.
No placeholders/axioms may remain.
-/

open scoped Manifold ContDiff Bundle
open Set Bundle

namespace Submission

open LeanEval.Geometry

noncomputable section

/-- The coordinate metric tensor is C³ on a neighbourhood of the chart centre (as a map into the
space of continuous bilinear forms). -/
theorem chart_metric_contDiffOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M => TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (p : M) :
    ∃ U' : Set E, (extChartAt I p p) ∈ U' ∧ IsOpen U' ∧
      ∃ g : E → E →L[ℝ] E →L[ℝ] ℝ,
        ContDiffOn ℝ 3 g U' ∧
        (∀ y ∈ U', ∀ u v : E, (g y) u v = (g y) v u) ∧
        (∀ y ∈ U', ∀ v : E, v ≠ 0 → 0 < (g y) v v) ∧
        (∀ y ∈ U', ∀ u v : E,
           (g y) u v = (Bundle.RiemannianBundle.g (E := fun x : M => TangentSpace I x)).inner
                         ((extChartAt I p).symm y)
                         ((mfderiv[range I] (extChartAt I p).symm y) u)
                         ((mfderiv[range I] (extChartAt I p).symm y) v)) := by
  let φ := extChartAt I p
  let e : Trivialization E (Bundle.TotalSpace.proj : Bundle.TotalSpace E (fun x : M => TangentSpace I x) → M)
    := trivializationAt E (TangentSpace I) p
  let gmetric := Bundle.RiemannianBundle.g (E := fun x : M => TangentSpace I x)
  let g : E → E →L[ℝ] E →L[ℝ] ℝ :=
    fun y : E => pull (gmetric.inner (φ.symm y)) (e.symmL ℝ (φ.symm y))
  refine ⟨φ.target, mem_extChartAt_target p, isOpen_extChartAt_target (I := I) p, g, ?_, ?_, ?_, ?_⟩
  · -- ContDiffOn ℝ 3 g φ.target
    have hEvalAt : ∀ (y0 : E), y0 ∈ φ.target → ∀ u v : E,
        ContDiffAt ℝ ∞ (fun y : E => (g y) u v) y0 := by
      intro y0 hy0 u v
      have hA : ContDiffAt ℝ ∞
          (fun y : E => (gmetric.inner (φ.symm y))
             ((trivializationAt E (TangentSpace I) p).symmL ℝ (φ.symm y) u)
             ((trivializationAt E (TangentSpace I) p).symmL ℝ (φ.symm y) v)) y0 := by
        simpa [φ, gmetric] using chartEval_contDiffAt (I := I) (M := M) p hy0 u v
      simpa [g, pull_apply] using hA
    have hEval : ∀ u v : E, ContDiffOn ℝ ∞ (fun y : E => (g y) u v) (φ.target) := by
      intro u v y0 hy0
      exact (hEvalAt y0 hy0 u v).contDiffWithinAt
    have hGinf : ContDiffOn ℝ ∞ g (φ.target) := by
      rw [contDiffOn_clm_apply]
      intro u
      rw [contDiffOn_clm_apply]
      intro v
      exact hEval u v
    exact hGinf.of_le (ENat.LEInfty.out (m := (3 : ℕ∞ω)))
  · intro y hy u v
    simpa [g] using (gmetric.symm (φ.symm y) (e.symmL ℝ (φ.symm y) u) (e.symmL ℝ (φ.symm y) v))
  · intro y hy v hv
    have hm_e : φ.symm y ∈ e.baseSet := by
      have hsrc : φ.symm y ∈ φ.source := φ.map_target hy
      simpa [φ, e, extChartAt_source] using hsrc
    have hTv : e.symmL ℝ (φ.symm y) v ≠ 0 := by
      intro hz
      have h1 := Trivialization.continuousLinearMapAt_symmL (R := ℝ) (e := e) hm_e v
      rw [hz] at h1
      have hz' : (0 : E) = v := by simpa using h1
      exact hv hz'.symm
    simpa [g] using (gmetric.pos (φ.symm y) (e.symmL ℝ (φ.symm y) v) hTv)
  · intro y hy u v
    have hL := chart_lm_eq_mfderiv (I := I) (M := M) p hy
    simp [g]
    rw [hL]
    rfl

end

end Submission
