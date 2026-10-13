import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongLWP.Sobolev.HolderHalf.NashData

theorem slice_facts {u : ℝ × ℝ → ℝ} (hu : ContDiff ℝ 1 u) (hc : HasCompactSupport u) :
    (∀ t : ℝ, ContDiff ℝ 1 fun s : ℝ => u (s, t)) ∧
    (∀ s : ℝ, ContDiff ℝ 1 fun t : ℝ => u (s, t)) ∧
    (∀ t : ℝ, HasCompactSupport fun s : ℝ => u (s, t)) ∧
    (∀ s : ℝ, HasCompactSupport fun t : ℝ => u (s, t)) ∧
    (∀ s t : ℝ, deriv (fun r : ℝ => u (r, t)) s = fderiv ℝ u (s, t) (1, 0)) ∧
    (∀ s t : ℝ, (deriv (fun r : ℝ => u (r, t)) s) ^ 2 ≤ ‖fderiv ℝ u (s, t)‖ ^ 2) ∧
    (∀ s t : ℝ, (deriv (fun r : ℝ => u (s, r)) t) ^ 2 ≤ ‖fderiv ℝ u (s, t)‖ ^ 2) := by
  -- `u` is differentiable on all of `ℝ × ℝ` (it is `C¹`), with derivative `fderiv ℝ u p` at `p`.
  have hdiff : ∀ p : ℝ × ℝ, HasFDerivAt (𝕜 := ℝ) u (fderiv ℝ u p) p :=
    fun p => (hu.differentiable (by norm_num) p).hasFDerivAt
  -- the derivative of a slice is the derivative of `u` applied to `(1,0)` resp. `(0,1)`
  have hslice₁ : ∀ s t : ℝ,
      deriv (fun r : ℝ => u (r, t)) s = fderiv ℝ u (s, t) (1, 0) := by
    intro s t
    have h1 : HasFDerivAt (𝕜 := ℝ) (fun r : ℝ => (r, t)) (ContinuousLinearMap.inl ℝ ℝ ℝ) s :=
      hasFDerivAt_prodMk_left s t
    have h2 : HasFDerivAt (𝕜 := ℝ) (fun r : ℝ => u (r, t))
        ((fderiv ℝ u (s, t)) ∘SL (ContinuousLinearMap.inl ℝ ℝ ℝ)) s :=
      (hdiff (s, t)).comp s h1
    rw [← fderiv_apply_one_eq_deriv, h2.fderiv, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inl_apply]
  have hslice₂ : ∀ s t : ℝ,
      deriv (fun r : ℝ => u (s, r)) t = fderiv ℝ u (s, t) (0, 1) := by
    intro s t
    have h1 : HasFDerivAt (𝕜 := ℝ) (fun r : ℝ => (s, r)) (ContinuousLinearMap.inr ℝ ℝ ℝ) t :=
      hasFDerivAt_prodMk_right s t
    have h2 : HasFDerivAt (𝕜 := ℝ) (fun r : ℝ => u (s, r))
        ((fderiv ℝ u (s, t)) ∘SL (ContinuousLinearMap.inr ℝ ℝ ℝ)) t :=
      (hdiff (s, t)).comp t h1
    rw [← fderiv_apply_one_eq_deriv, h2.fderiv, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inr_apply]
  refine ⟨?_, ?_, ?_, ?_, hslice₁, ?_, ?_⟩
  · -- first coordinate slices of a `C¹` function are `C¹`
    intro t
    have h : ContDiff ℝ 1 (fun s : ℝ => (s, t)) :=
      (contDiff_id : ContDiff ℝ 1 (id : ℝ → ℝ)).prodMk (contDiff_const (c := t))
    simpa [Function.comp_def] using hu.comp h
  · -- second coordinate slices of a `C¹` function are `C¹`
    intro s
    have h : ContDiff ℝ 1 (fun t : ℝ => (s, t)) :=
      (contDiff_const (c := s)).prodMk (contDiff_id : ContDiff ℝ 1 (id : ℝ → ℝ))
    simpa [Function.comp_def] using hu.comp h
  · -- first coordinate slices of a compactly supported function are compactly supported
    intro t
    have hsub : Function.support (fun s : ℝ => u (s, t)) ⊆ Prod.fst '' tsupport u := by
      intro s hs
      exact ⟨(s, t), subset_tsupport u (by simpa [Function.mem_support] using hs), rfl⟩
    exact IsCompact.of_isClosed_subset (hc.image continuous_fst) (isClosed_tsupport _)
      (closure_minimal hsub (hc.image continuous_fst).isClosed)
  · -- second coordinate slices of a compactly supported function are compactly supported
    intro s
    have hsub : Function.support (fun t : ℝ => u (s, t)) ⊆ Prod.snd '' tsupport u := by
      intro t ht
      exact ⟨(s, t), subset_tsupport u (by simpa [Function.mem_support] using ht), rfl⟩
    exact IsCompact.of_isClosed_subset (hc.image continuous_snd) (isClosed_tsupport _)
      (closure_minimal hsub (hc.image continuous_snd).isClosed)
  · -- `(∂ₛ u)² ≤ ‖Du‖²` because `‖(1,0)‖ = 1`
    intro s t
    have hle : ‖fderiv ℝ u (s, t) (1, 0)‖ ≤ ‖fderiv ℝ u (s, t)‖ := by
      have h := ContinuousLinearMap.le_opNorm (fderiv ℝ u (s, t)) ((1 : ℝ), (0 : ℝ))
      simpa [Prod.norm_def] using h
    rw [hslice₁ s t]
    calc (fderiv ℝ u (s, t) (1, 0)) ^ 2 = ‖fderiv ℝ u (s, t) (1, 0)‖ ^ 2 := by
          rw [Real.norm_eq_abs, sq_abs]
      _ ≤ ‖fderiv ℝ u (s, t)‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hle 2
  · -- `(∂ₜ u)² ≤ ‖Du‖²` because `‖(0,1)‖ = 1`
    intro s t
    have hle : ‖fderiv ℝ u (s, t) (0, 1)‖ ≤ ‖fderiv ℝ u (s, t)‖ := by
      have h := ContinuousLinearMap.le_opNorm (fderiv ℝ u (s, t)) ((0 : ℝ), (1 : ℝ))
      simpa [Prod.norm_def] using h
    rw [hslice₂ s t]
    calc (fderiv ℝ u (s, t) (0, 1)) ^ 2 = ‖fderiv ℝ u (s, t) (0, 1)‖ ^ 2 := by
          rw [Real.norm_eq_abs, sq_abs]
      _ ≤ ‖fderiv ℝ u (s, t)‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hle 2

end Work.FTS.StrongLWP.Sobolev.HolderHalf.NashData
