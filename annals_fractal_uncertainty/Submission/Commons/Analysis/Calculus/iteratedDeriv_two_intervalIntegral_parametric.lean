import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Order.CompletePartialOrder
import Submission.Commons.Analysis.Calculus.intervalIntegral_hasDerivAt_upper_piece_of_continuous

namespace Commons.Analysis.Calculus

open MeasureTheory intervalIntegral
open scoped Topology ContDiff

/-- If `F` is differentiable at `(u, t)`, then the partial function `v ↦ F v t` has derivative
at `u` given by the first partial derivative of `F`. -/
lemma hasDerivAt_fst_of_differentiableAt {F : ℝ → ℝ → ℝ} {u t : ℝ}
    (h : DifferentiableAt ℝ (Function.uncurry F) (u, t)) :
    HasDerivAt (fun v : ℝ => F v t) (fderiv ℝ (Function.uncurry F) (u, t) (1, 0)) u := by
  have hγ : HasDerivAt (fun v : ℝ => (v, t)) (1, 0) u :=
    (hasDerivAt_id u).prodMk (hasDerivAt_const u t)
  have hcomp := h.hasFDerivAt.comp_hasDerivAt u hγ
  have hfun : (fun v : ℝ => F v t) = Function.uncurry F ∘ (fun v : ℝ => (v, t)) := by
    funext v; rfl
  rw [hfun]
  exact hcomp

theorem iteratedDeriv_two_intervalIntegral_parametric
    {F : ℝ → ℝ → ℝ} {a b s₀ : ℝ} (hF : ContDiff ℝ 2 (Function.uncurry F)) :
    iteratedDeriv 2 (fun s => ∫ t in a..b, F s t) s₀
      = ∫ t in a..b, iteratedDeriv 2 (fun s => F s t) s₀ := by
  -- The first and second partial derivatives of `F` in the first variable.
  let F1 : ℝ → ℝ → ℝ := fun x t => fderiv ℝ (Function.uncurry F) (x, t) (1, 0)
  let F2 : ℝ → ℝ → ℝ := fun x t => fderiv ℝ (Function.uncurry F1) (x, t) (1, 0)
  have hF_cont : Continuous (fun p : ℝ × ℝ => F p.1 p.2) := hF.continuous
  -- `F1` is `C¹` and `F2` is `C⁰`.
  have hF1_cd : ContDiff ℝ 1 (Function.uncurry F1) := by
    have h := hF.contDiff_fderiv_apply (m := (1 : WithTop ℕ∞))
      (by norm_num : ((1 : WithTop ℕ∞) + 1) ≤ 2)
    have hv : ContDiff ℝ 1 (fun p : ℝ × ℝ => (p, ((1 : ℝ), (0 : ℝ)))) :=
      contDiff_id.prodMk contDiff_const
    have hh := h.comp hv
    convert hh using 1
    ext p
    simp only [F1, Function.uncurry, Function.comp_apply, Prod.mk.eta]
  have hF1_cont : Continuous (fun p : ℝ × ℝ => F1 p.1 p.2) := hF1_cd.continuous
  have hF2_cd : ContDiff ℝ 0 (Function.uncurry F2) := by
    have h := hF1_cd.contDiff_fderiv_apply (m := (0 : WithTop ℕ∞))
      (by norm_num : ((0 : WithTop ℕ∞) + 1) ≤ 1)
    have hv : ContDiff ℝ 0 (fun p : ℝ × ℝ => (p, ((1 : ℝ), (0 : ℝ)))) :=
      contDiff_id.prodMk contDiff_const
    have hh := h.comp hv
    convert hh using 1
    ext p
    simp only [F2, Function.uncurry, Function.comp_apply, Prod.mk.eta]
  have hF2_cont : Continuous (fun p : ℝ × ℝ => F2 p.1 p.2) := contDiff_zero.mp hF2_cd
  -- Derivative identities.
  have hderiv1 : ∀ u t : ℝ, HasDerivAt (fun v : ℝ => F v t) (F1 u t) u := by
    intro u t
    have hd : DifferentiableAt ℝ (Function.uncurry F) (u, t) :=
      (hF.differentiable (by norm_num)).differentiableAt
    simpa [F1] using hasDerivAt_fst_of_differentiableAt (F := F) hd
  have hderiv2 : ∀ u t : ℝ, HasDerivAt (fun v : ℝ => F1 v t) (F2 u t) u := by
    intro u t
    have hd : DifferentiableAt ℝ (Function.uncurry F1) (u, t) :=
      (hF1_cd.differentiable (by norm_num)).differentiableAt
    simpa [F2] using hasDerivAt_fst_of_differentiableAt (F := F1) hd
  -- Derivatives of the parametric integrals.
  have h1 : HasDerivAt (fun x : ℝ => ∫ t in a..b, F x t) (∫ t in a..b, F1 s₀ t) s₀ :=
    intervalIntegral_hasDerivAt_fixed_upper_of_continuous (F := F) (F' := F1)
      (a := a) (b := b) (x₀ := s₀) hF_cont hF1_cont hderiv1
  have h2 : HasDerivAt (fun x : ℝ => ∫ t in a..b, F1 x t) (∫ t in a..b, F2 s₀ t) s₀ :=
    intervalIntegral_hasDerivAt_fixed_upper_of_continuous (F := F1) (F' := F2)
      (a := a) (b := b) (x₀ := s₀) hF1_cont hF2_cont hderiv2
  -- `deriv` of the first parametric integral is the second parametric function.
  have hf_deriv : (fun x : ℝ => deriv (fun s => ∫ t in a..b, F s t) x) =ᶠ[𝓝 s₀]
      (fun x => ∫ t in a..b, F1 x t) := by
    filter_upwards with x
    exact (intervalIntegral_hasDerivAt_fixed_upper_of_continuous (F := F) (F' := F1)
      (a := a) (b := b) (x₀ := x) hF_cont hF1_cont hderiv1).deriv
  -- The double derivative of the parametric integral.
  have hmain : iteratedDeriv 2 (fun s => ∫ t in a..b, F s t) s₀ = ∫ t in a..b, F2 s₀ t := by
    have hiter : iteratedDeriv 2 (fun s => ∫ t in a..b, F s t) s₀
        = deriv (fun x => deriv (fun s => ∫ t in a..b, F s t) x) s₀ := by
      simp only [iteratedDeriv_succ, iteratedDeriv_zero]
    rw [hiter, Filter.EventuallyEq.deriv_eq hf_deriv]
    exact h2.deriv
  -- Pointwise identification of `iteratedDeriv 2` of the slice.
  have hpt : ∀ t : ℝ, iteratedDeriv 2 (fun s => F s t) s₀ = F2 s₀ t := by
    intro t
    have hd : deriv (fun v : ℝ => F v t) = fun v => F1 v t := by
      funext v
      exact (hderiv1 v t).deriv
    rw [show (2 : ℕ) = 0 + 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_succ,
      iteratedDeriv_zero, hd]
    exact (hderiv2 s₀ t).deriv
  rw [hmain]
  exact intervalIntegral.integral_congr (fun t _ => (hpt t).symm)

end Commons.Analysis.Calculus