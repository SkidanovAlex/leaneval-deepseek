import Mathlib
import Submission.Work.FunctionalEquations.KernelSchwartz.Defs
import Submission.Work.FunctionalEquations.KernelSchwartz.psi_smooth
import Submission.Work.FunctionalEquations.KernelSchwartz.psi_deriv_bound

/-!
# The coefficients of CKMRV Theorem 3.1 are radial Schwartz functions

The four coefficient families of the CKMRV interpolation basis are given by contour
integrals of a kernel `N` along a horizontal line of the upper half plane,

`m ↦ f m x = c m ∫_0^1 N (u + i y) x · e^{-2π i m (u + i y)} du`   (`y > 0`),

the value being independent of the height `y` (this is the hypothesis `hf`).

This file proves that, whenever the kernel `N` is continuous in `τ` on the upper half
plane, smooth and radial in `x`, and satisfies the radial-derivative growth bound of
CKMRV Theorem 3.1 (iii), and `‖c m‖ ≤ 1`, the coefficients `f m` are the value functions
of *radial Schwartz functions* whose radial seminorms grow at most polynomially in `m`.

The proof evaluates the contour integral at the height `y_m = 1/(m+1)`, at which

* the exponential factor has modulus `e^{2π m/(m+1)} ≤ e^{2π}` (`expM_norm_le`), and
* the weight `(Im τ)^{-1} = m + 1` grows polynomially in `m` (`ym_inv`),

so that the profile `psi N c m` of the `m`-th coefficient is a one-variable Schwartz
function with polynomially growing seminorms.  The remaining analytic content is the
differentiation under the integral sign (`Work.FunctionalEquations.KernelSchwartz.psi_smooth`)
and the resulting estimate (`Work.FunctionalEquations.KernelSchwartz.psi_deriv_bound`).

## Main result

* `Work.FunctionalEquations.KernelSchwartz.kernel_isSchwartz`
-/

namespace Work.FunctionalEquations.KernelSchwartz

open LeanEval.Analysis.CKMRVInterpolation Work.Core Work.FE Filter Topology
open scoped FourierTransform SchwartzMap

noncomputable section

theorem kernel_isSchwartz {n : ℕ} [NeZero n]
    (N : ℂ → E n → ℂ) (c : Set.Ici (1:ℕ) → ℂ) (f : Set.Ici (1:ℕ) → E n → ℂ)
    (hN_cont : ∀ x : E n, ContinuousOn (fun τ : ℂ => N τ x) {τ : ℂ | 0 < τ.im})
    (hN_smooth : ∀ τ : ℂ, ContDiff ℝ ⊤ (fun x : E n => N τ x))
    (hN_radial : ∀ τ : ℂ, Radial (fun x : E n => N τ x))
    (hN_growth : ∀ k ℓ : ℕ, ∃ C : ℝ, ∃ N' : ℝ, 0 ≤ C ∧ 0 ≤ N' ∧
      ∀ (τ : ℂ) (x : E n), 0 < τ.im →
        ‖x‖ ^ k * ‖radialDeriv ℓ (fun y : E n => N τ y) x‖
          ≤ C * (1 + (τ.im)⁻¹ + ‖τ‖) ^ N')
    (hc : ∀ m : Set.Ici (1:ℕ), ‖c m‖ ≤ 1)
    (hf : ∀ (m : Set.Ici (1:ℕ)) (x : E n) (y : ℝ), 0 < y →
      f m x = c m * ∫ u in (0:ℝ)..1, N ((u:ℂ) + (y:ℂ)*Complex.I) x
        * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (m.1 : ℂ) * ((u:ℂ) + (y:ℂ)*Complex.I)))) :
    ∃ (G : Set.Ici (1:ℕ) → RSch n),
        (∀ (m : Set.Ici (1:ℕ)) (x : E n), (G m).1 x = f m x) ∧
        (∀ k ℓ : ℕ, ∃ C : ℝ, ∃ N' : ℕ, 0 ≤ C ∧
          ∀ (m : Set.Ici (1:ℕ)) (x : E n),
            ‖x‖ ^ k * ‖radialDeriv ℓ (⇑(G m).1) x‖ ≤ C * ((m.1 : ℝ) + 1) ^ N') := by
  obtain ⟨hpsi_smooth, hpsi_deriv⟩ :=
    psi_smooth N c hN_cont hN_smooth hN_radial hN_growth
  have hpsi_bound := psi_deriv_bound N c hN_radial hN_growth hc hpsi_deriv
  -- `psi N c m` is a Schwartz function of one variable
  have hSch : ∀ m : Set.Ici (1:ℕ), ∃ g : 𝓢(ℝ, ℂ), ∀ t, g t = psi N c m t := by
    intro m
    refine ⟨⟨psi N c m, hpsi_smooth m, ?_⟩, fun t => rfl⟩
    intro k j
    obtain ⟨C, N', _, hB⟩ := hpsi_bound k j
    refine ⟨C * ((m.1 : ℝ) + 1) ^ N', fun t => ?_⟩
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
    exact hB m t
  choose g hg using hSch
  let G : Set.Ici (1:ℕ) → RSch n := fun m =>
    Work.RadialSpace.rschOfEven n (g m) (fun t => by
      rw [hg m, hg m]
      exact psi_even N c hN_radial m t)
  have hGcoe : ∀ (m : Set.Ici (1:ℕ)) (x : E n), (G m).1 x = psi N c m ‖x‖ := by
    intro m x
    show (Work.RadialSpace.rschOfEven n (g m) _).1 x = psi N c m ‖x‖
    rw [Work.RadialSpace.rschOfEven_coe, hg m]
  refine ⟨G, ?_, ?_⟩
  · intro m x
    rw [hGcoe m x, hf m x (ym m) (ym_pos m), psi_apply]
    congr 1
    refine intervalIntegral.integral_congr (fun u _ => ?_)
    have h : N (tauM m u) (realIncl (n := n) ‖x‖) = N (tauM m u) x :=
      hN_radial (tauM m u) _ _ (by
        rw [Work.Sampling.realIncl_norm, abs_of_nonneg (norm_nonneg x)])
    rw [h]
    simp only [tauM, expM]
  · intro k ℓ
    obtain ⟨C, N', hC, hB⟩ := hpsi_bound k ℓ
    refine ⟨C, N', hC, fun m x => ?_⟩
    have hprof : (fun r : ℝ => (G m).1 (realIncl (n := n) r)) = psi N c m := by
      funext r
      show (Work.RadialSpace.rschOfEven n (g m) _).1 (realIncl r) = psi N c m r
      rw [Work.RadialSpace.rschOfEven_coe, hg m, Work.Sampling.realIncl_norm]
      rcases le_total 0 r with hr | hr
      · rw [abs_of_nonneg hr]
      · rw [abs_of_nonpos hr]
        exact psi_even N c hN_radial m r
    have hrad : radialDeriv ℓ (⇑(G m).1) x = iteratedDeriv ℓ (psi N c m) ‖x‖ := by
      rw [radialDeriv, hprof]
    rw [hrad]
    simpa [abs_of_nonneg (norm_nonneg x)] using hB m ‖x‖

end

end Work.FunctionalEquations.KernelSchwartz
