import Mathlib
import Submission.Work.Projection.TransverseDefs

/-!
# The derivative of the pair parametrisation's "difference" map

`Work.Projection.pairZ e p q` is the chartwise difference `(a, b) ↦ chartRep e q b - chartRep e p a`
of the two embedded points.  This file computes its derivative at a point `(a, b)` of the product
of the two chart targets: it is the difference of the derivatives of the two chart representations,
composed with the two projections of the product.
-/

set_option linter.style.haveILetI false

namespace Work.Projection

open scoped Manifold ContDiff
open Topology

/-- `chartRep f p` is differentiable at every point of the target of the chart at `p`. -/
lemma differentiableAt_chartRep {n k : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (f : M → EuclideanSpace ℝ (Fin (k + 1))) (hf : ContMDiff (𝓡 n) (𝓡 (k + 1)) ∞ f)
    (p : M) {y : EuclideanSpace ℝ (Fin n)}
    (hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).target) :
    DifferentiableAt ℝ (chartRep f p) y := by
  have h : ContDiffOn ℝ ∞ (chartRep f p) (chartAt (EuclideanSpace ℝ (Fin n)) p).target :=
    ((hf.contMDiffOn (s := Set.univ)).comp (contMDiffOn_chart_symm (x := p))
      (by intro x _; trivial)).contDiffOn
  exact (h.contDiffAt ((chartAt (EuclideanSpace ℝ (Fin n)) p).open_target.mem_nhds hy)
    ).differentiableAt (by simp)

section Helpers

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The derivative of `ab ↦ g ab.2` is the derivative of `g` at `b` composed with the second
projection. -/
private lemma fderiv_comp_snd (g : E → F) {b : E} (hg : DifferentiableAt ℝ g b) (a : E) :
    fderiv ℝ (fun ab : E × E => g ab.2) (a, b) =
      (fderiv ℝ g b).comp (ContinuousLinearMap.snd ℝ E E) := by
  have h1 : (fun ab : E × E => g ab.2) = g ∘ Prod.snd := rfl
  rw [h1, fderiv_comp (x := (a, b)) hg (differentiableAt_snd), fderiv_snd]

/-- The derivative of `ab ↦ g ab.1` is the derivative of `g` at `a` composed with the first
projection. -/
private lemma fderiv_comp_fst (g : E → F) {a : E} (hg : DifferentiableAt ℝ g a) (b : E) :
    fderiv ℝ (fun ab : E × E => g ab.1) (a, b) =
      (fderiv ℝ g a).comp (ContinuousLinearMap.fst ℝ E E) := by
  have h1 : (fun ab : E × E => g ab.1) = g ∘ Prod.fst := rfl
  rw [h1, fderiv_comp (x := (a, b)) hg (differentiableAt_fst), fderiv_fst]

/-- `ab ↦ g ab.2` is differentiable wherever `g` is. -/
private lemma differentiableAt_comp_snd (g : E → F) {b : E} (hg : DifferentiableAt ℝ g b) (a : E) :
    DifferentiableAt ℝ (fun ab : E × E => g ab.2) (a, b) := by
  have h1 : (fun ab : E × E => g ab.2) = g ∘ Prod.snd := rfl
  rw [h1]
  exact hg.comp (a, b) differentiableAt_snd

/-- `ab ↦ g ab.1` is differentiable wherever `g` is. -/
private lemma differentiableAt_comp_fst (g : E → F) {a : E} (hg : DifferentiableAt ℝ g a) (b : E) :
    DifferentiableAt ℝ (fun ab : E × E => g ab.1) (a, b) := by
  have h1 : (fun ab : E × E => g ab.1) = g ∘ Prod.fst := rfl
  rw [h1]
  exact hg.comp (a, b) differentiableAt_fst

end Helpers

/-- The derivative of `Work.Projection.pairZ e p q` (defined in
`Submission.Work.Projection.TransverseDefs` as `(a,b) ↦ chartRep e q b - chartRep e p a`,
where `chartRep` is the chart representation, see `Submission.Work.Projection.Defs`) at a point
`(a,b)` of the product of the two chart targets. -/
theorem fderiv_pairZ {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ⊤ M]
    (e : M → EuclideanSpace ℝ (Fin (2 * n + 1)))
    (he : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n + 1)))) ⊤ e) (p q : M)
    (a b : EuclideanSpace ℝ (Fin n))
    (ha : a ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).target)
    (hb : b ∈ (chartAt (EuclideanSpace ℝ (Fin n)) q).target) :
    fderiv ℝ (pairZ e p q) (a, b) =
      (fderiv ℝ (chartRep e q) b).comp
          (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n))) -
        (fderiv ℝ (chartRep e p) a).comp
          (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n))) := by
  -- `⊤` (analytic order) is above `∞` (smooth order), which is what the helpers use.
  haveI : IsManifold (𝓡 n) ∞ M := IsManifold.of_le (m := ∞) (n := ⊤) le_top
  have he' : ContMDiff (𝓡 n) (𝓡 (2 * n + 1)) ∞ e := he.of_le le_top
  have hcq : DifferentiableAt ℝ (chartRep e q) b := differentiableAt_chartRep e he' q hb
  have hcp : DifferentiableAt ℝ (chartRep e p) a := differentiableAt_chartRep e he' p ha
  have hq2 : DifferentiableAt ℝ
      (fun ab : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => chartRep e q ab.2) (a, b) :=
    differentiableAt_comp_snd _ hcq a
  have hp2 : DifferentiableAt ℝ
      (fun ab : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => chartRep e p ab.1) (a, b) :=
    differentiableAt_comp_fst _ hcp b
  have hZ : pairZ e p q =
      (fun ab : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => chartRep e q ab.2) -
      (fun ab : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => chartRep e p ab.1) := rfl
  rw [hZ, fderiv_sub hq2 hp2, fderiv_comp_snd _ hcq a, fderiv_comp_fst _ hcp b]

end Work.Projection
