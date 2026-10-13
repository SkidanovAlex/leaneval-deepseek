import Mathlib
import Submission.Work.WilE3.Defs
import Submission.Work.Taylor.Grad.exists_order_of_partial
import Submission.Work.WilE3.eaEval_analytic

namespace Work.WilE3.Taylor.Grad

theorem deriv_eaEval_eventually {k r : ℕ} (c : WilkiesDesign.E.EAChain k r)
    (Φ : WilkiesDesign.E.EAPoly k r) (γ : ℝ → Fin k → ℝ) (hγ : AnalyticAt ℝ γ 0) :
    Filter.EventuallyEq (nhds 0) (deriv (fun t : ℝ => WilkiesDesign.E.eaEval c Φ (γ t)))
      (fun t => ∑ j : Fin k,
        WilkiesDesign.E.eaEval c (WilkiesDesign.E.eaD c j Φ) (γ t) *
          deriv (fun s : ℝ => γ s j) t) := by
  -- `γ` is analytic, hence differentiable, on a neighbourhood of `0`; there the one-variable
  -- chain rule identifies `deriv (Φ ∘ γ)` with the contraction of the symbolic gradient with
  -- the tangent vector `deriv γ t`, which is the claimed sum.
  filter_upwards [hγ.eventually_analyticAt] with t ht
  have hγt : HasDerivAt γ (deriv γ t) t := by
    have h := ht.differentiableAt.hasFDerivAt.hasDerivAt
    rwa [show (fderiv ℝ γ t) 1 = deriv γ t from rfl] at h
  rw [_root_.Work.Taylor.Grad.deriv_eaEval_comp c Φ γ hγt]
  simp only [sum_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  -- The `j`-th component of `deriv γ t` is `deriv (fun s => γ s j) t`.
  have hproj : HasDerivAt (fun s : ℝ => γ s j) (deriv γ t j) t :=
    HasFDerivAt.comp_hasDerivAt t (ContinuousLinearMap.hasFDerivAt
      (ContinuousLinearMap.proj j : (Fin k → ℝ) →L[ℝ] ℝ)) hγt
  rw [← hproj.deriv]

end Work.WilE3.Taylor.Grad
