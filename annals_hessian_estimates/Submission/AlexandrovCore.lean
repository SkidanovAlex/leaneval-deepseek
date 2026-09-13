/-
The analytic core of Proposition 3.1 of Shankar--Yuan (arXiv:2305.12587): the paper's Lemma
`lem:o(r^2)` of the appendix, in its abstract form, together with the pointwise Hessian identity
for a mollification of a function with a weak Hessian measure.

Given a continuous function `u` on an open set `s`, a weak gradient `G` and a weak Hessian
`M dx + σ` (see `Submission/WeakDerivative.lean`), at a point `x₀` which is a Lebesgue point of
`G` and of `M` and at which the singular part `σ` has zero density, the second order Taylor
remainder of `u` at `x₀` is `o(r^2)` in `L^1` average on `ball x₀ r`.

The proof follows the appendix of the paper: mollify `u` by a bump function of radius comparable
to `r`, use Taylor's theorem for the smooth mollification, use the measure identity for the second
derivative of the mollification, and let the bump radius go to zero.
-/
import Mathlib
import Submission.WeakDerivative
import Submission.Commons.Analysis.Convolution.fderiv_fderiv_moll
import Submission.Commons.Analysis.Convolution.fderiv_fderiv_moll_apply
import Submission.Commons.Analysis.Calculus.FDeriv.fderiv_fderiv_const_sub
import Submission.Commons.Measure.VectorMeasure.pairing_abs_le

open MeasureTheory Metric Set Filter Function
open Commons.Analysis.Convolution Commons.Analysis.Calculus.FDeriv
open scoped BigOperators ENNReal Topology RealInnerProductSpace InnerProductSpace Convolution

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Submission

local notation "ℝ⁴" => EuclideanSpace ℝ (Fin 4)

/-- **Pointwise Hessian identity for the mollification.**  If `u` has weak Hessian `M dx + σ` on
`s` and `k` is a smooth compactly supported kernel whose reflected support at `z` lies in `s`, then
the second derivative of the convolution `u ⋆ k` at `z` is the pairing of `M dx + σ` with the
kernel `k (z - ·)`. -/
theorem fderiv_fderiv_moll_eq (k u : ℝ⁴ → ℝ) (M : Fin 4 → Fin 4 → ℝ⁴ → ℝ)
    (σ : Fin 4 → Fin 4 → SignedMeasure ℝ⁴) (s : Set ℝ⁴) (z : ℝ⁴) (i j : Fin 4)
    (hk : ContDiff ℝ (⊤ : ℕ∞) k) (hks : HasCompactSupport k)
    (hsupp : ∀ τ ∈ tsupport k, z - τ ∈ s)
    (hu : LocallyIntegrable u volume) (hM : HasWeakHessian u s M σ) :
    (fderiv ℝ (fderiv ℝ (fun y => ∫ t, u t * k (y - t) ∂volume)) z) (stdE i) (stdE j)
      = ∫ t, k (z - t) * M i j t ∂volume + (∫ᵛ t, k (z - t) ∂•(σ i j)) := by
  rw [fderiv_fderiv_moll_apply k u z (stdE i) (stdE j) hks hk hu]
  -- move the second derivative of the kernel onto the reflected test function `τ ↦ k (z - τ)`
  have hsupp' : tsupport (fun τ : ℝ⁴ => k (z - τ)) ⊆ s := by
    intro τ hτ
    have hmem : z - τ ∈ tsupport k := by
      by_contra hc
      rw [notMem_tsupport_iff_eventuallyEq] at hc
      have h2 : (fun τ' : ℝ⁴ => k (z - τ')) =ᶠ[𝓝 τ] 0 :=
        hc.comp_tendsto (tendsto_const_nhds.sub tendsto_id)
      have hnot : τ ∉ tsupport (fun τ' : ℝ⁴ => k (z - τ')) :=
        notMem_tsupport_iff_eventuallyEq.mpr h2
      exact hnot hτ
    simpa using hsupp (z - τ) hmem
  have hcomp : ContDiff ℝ (⊤ : ℕ∞) (fun τ : ℝ⁴ => k (z - τ)) :=
    hk.comp (contDiff_const.sub contDiff_id)
  have hchain : (∫ t, u t * ((fderiv ℝ (fderiv ℝ k) (z - t)) (stdE i) (stdE j)) ∂volume)
      = ∫ t, u t * ((fderiv ℝ (fderiv ℝ (fun τ : ℝ⁴ => k (z - τ))) t) (stdE i)
          (stdE j)) ∂volume := by
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    dsimp only
    rw [fderiv_fderiv_const_sub k z t (hk.of_le (WithTop.coe_le_coe.mpr le_top))]
  rw [hchain]
  exact hM (fun τ => k (z - τ)) hcomp hsupp' i j

end Submission
