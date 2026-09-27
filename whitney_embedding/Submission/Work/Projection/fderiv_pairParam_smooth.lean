import Mathlib
import Submission.Work.Projection.TransverseDefs
import Submission.Work.Projection.fderiv_pairZ_smooth
import Submission.Work.Projection.hasFDerivAt_extract
import Submission.Work.Projection.contDiffOn_pairParam_smooth

set_option linter.style.haveILetI false

namespace Work.Projection

open scoped Manifold ContDiff
open Topology

/-- The derivative of the pair parametrisation `Work.Projection.pairParam e p q` (defined in
`Submission.Work.Projection.TransverseDefs` as `pairEquiv n ∘ extract ∘ pairZ e p q`, with the
*smooth* (`C^∞`) manifold structure, i.e. the order `∞ = ((⊤ : ℕ∞) : WithTop ℕ∞)`) at a point
`(a,b)` of its domain.  Here `projVec u : ℝ^{2n+1} →L ℝ^{2n}` is the projection with kernel spanned
by `(u,1)` and `z = pairZ e p q (a,b)`.  This is identical to `Work.Projection.fderiv_pairParam`
in `Submission.Work.Projection.fderiv_pairParam` except that the hypothesis is smoothness rather
than analyticity, so no `of_le` downgrading is needed. -/
theorem fderiv_pairParam_smooth {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (e : M → EuclideanSpace ℝ (Fin (2 * n + 1)))
    (he : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n + 1)))) ((⊤ : ℕ∞) : WithTop ℕ∞) e)
    (p q : M) (a b : EuclideanSpace ℝ (Fin n))
    (ha : a ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).target)
    (hb : b ∈ (chartAt (EuclideanSpace ℝ (Fin n)) q).target)
    (hz : (pairZ e p q (a, b)) (Fin.last (2 * n)) ≠ 0) :
    fderiv ℝ (pairParam e p q) (a, b) =
      (LinearMap.toContinuousLinearMap (pairEquiv n).toLinearMap) ∘L
        (((pairZ e p q (a, b)) (Fin.last (2 * n)))⁻¹ •
          (projVec (pairDir e p q (a, b)) ∘L fderiv ℝ (pairZ e p q) (a, b))) := by
  -- The two chart representations are differentiable at the two parameters.
  have hcq : DifferentiableAt ℝ (chartRep e q) b := differentiableAt_chartRep e he q hb
  have hcp : DifferentiableAt ℝ (chartRep e p) a := differentiableAt_chartRep e he p ha
  have hq2 : DifferentiableAt ℝ
      (fun ab : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => chartRep e q ab.2)
      (a, b) := by
    have h1 : (fun ab : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => chartRep e q ab.2)
        = chartRep e q ∘ Prod.snd := rfl
    rw [h1]
    exact hcq.comp (a, b) differentiableAt_snd
  have hp2 : DifferentiableAt ℝ
      (fun ab : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => chartRep e p ab.1)
      (a, b) := by
    have h1 : (fun ab : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => chartRep e p ab.1)
        = chartRep e p ∘ Prod.fst := rfl
    rw [h1]
    exact hcp.comp (a, b) differentiableAt_fst
  -- `pairZ e p q = (b ↦ chartRep e q b) ∘ snd - (a ↦ chartRep e p a) ∘ fst` is differentiable.
  have hZdiff : DifferentiableAt ℝ (pairZ e p q) (a, b) := by
    rw [show pairZ e p q = (fun ab : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        chartRep e q ab.2 - chartRep e p ab.1) from rfl]
    exact hq2.sub hp2
  have hZ1 : HasFDerivAt (pairZ e p q) (fderiv ℝ (pairZ e p q) (a, b)) (a, b) :=
    hZdiff.hasFDerivAt
  -- Chain rule for `pairDir = extract ∘ pairZ`, using the derivative of `extract`.
  have hdir : HasFDerivAt (pairDir e p q)
      (((pairZ e p q (a, b)) (Fin.last (2 * n)))⁻¹ •
        (projVec (pairDir e p q (a, b)) ∘L fderiv ℝ (pairZ e p q) (a, b))) (a, b) := by
    have h := (hasFDerivAt_extract (k := 2 * n) (pairZ e p q (a, b)) hz).comp (a, b) hZ1
    rw [ContinuousLinearMap.smul_comp] at h
    exact h
  -- Chain rule for `pairParam = pairEquiv n ∘ pairDir`; `pairEquiv n` is linear with itself as
  -- derivative.
  have hL : HasFDerivAt (fun v : EuclideanSpace ℝ (Fin (2 * n)) => pairEquiv n v)
      (LinearMap.toContinuousLinearMap (pairEquiv n).toLinearMap) (pairDir e p q (a, b)) :=
    ContinuousLinearEquiv.hasFDerivAt ((pairEquiv n).toContinuousLinearEquiv)
  exact (hL.comp (a, b) hdir).fderiv

end Work.Projection
