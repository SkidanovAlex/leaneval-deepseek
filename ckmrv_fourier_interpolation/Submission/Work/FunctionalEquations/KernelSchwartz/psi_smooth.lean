import Mathlib
import Submission.Work.FunctionalEquations.KernelSchwartz.Defs

namespace Work.FunctionalEquations.KernelSchwartz

open LeanEval.Analysis.CKMRVInterpolation

theorem psi_smooth {n : ℕ} [NeZero n]
    (N : ℂ → Work.FE.E n → ℂ) (c : Set.Ici (1:ℕ) → ℂ)
    (hN_cont : ∀ x : Work.FE.E n, ContinuousOn (fun τ : ℂ => N τ x) {τ : ℂ | 0 < τ.im})
    (hN_smooth : ∀ τ : ℂ, ContDiff ℝ ⊤ (fun x : Work.FE.E n => N τ x))
    (hN_radial : ∀ τ : ℂ, LeanEval.Analysis.CKMRVInterpolation.Radial (fun x : Work.FE.E n => N τ x))
    (hN_growth : ∀ k ℓ : ℕ, ∃ C : ℝ, ∃ N' : ℝ, 0 ≤ C ∧ 0 ≤ N' ∧
      ∀ (τ : ℂ) (x : Work.FE.E n), 0 < τ.im →
        ‖x‖ ^ k * ‖Work.FE.radialDeriv ℓ (fun y : Work.FE.E n => N τ y) x‖
          ≤ C * (1 + (τ.im)⁻¹ + ‖τ‖) ^ N') :
    (∀ m : Set.Ici (1:ℕ), ContDiff ℝ Work.RadialSpace.Smooth
        (Work.FunctionalEquations.KernelSchwartz.psi N c m)) ∧
    (∀ (m : Set.Ici (1:ℕ)) (j : ℕ) (t : ℝ),
      iteratedDeriv j (Work.FunctionalEquations.KernelSchwartz.psi N c m) t
        = c m * ∫ u in (0:ℝ)..1,
            iteratedDeriv j (fun r : ℝ => N (Work.FunctionalEquations.KernelSchwartz.tauM m u)
              (LeanEval.Analysis.CKMRVInterpolation.realIncl (n := n) r)) t
              * Work.FunctionalEquations.KernelSchwartz.expM m u) := by
  have hpb := profile_iteratedDeriv_bound N hN_radial hN_growth
  -- The integral `F_m t = ∫_0^1 N (τ_m u) (t e₁) e^{-2π i m τ_m u} du` is smooth and its
  -- iterated derivatives are computed by differentiating under the integral sign.
  have key : ∀ m : Set.Ici (1:ℕ),
      ContDiff ℝ Work.RadialSpace.Smooth
        (fun r : ℝ => ∫ u in (0:ℝ)..1,
          N (tauM m u) (realIncl (n := n) r) * expM m u) ∧
      (∀ j : ℕ, ∀ t : ℝ,
        iteratedDeriv j (fun r : ℝ => ∫ u in (0:ℝ)..1,
            N (tauM m u) (realIncl (n := n) r) * expM m u) t
          = ∫ u in (0:ℝ)..1, iteratedDeriv j
              (fun r : ℝ => N (tauM m u) (realIncl (n := n) r)) t * expM m u) := by
    intro m
    -- A uniform (in `u ∈ [0,1]` and `r ∈ ℝ`) bound for the iterated derivatives of the
    -- integrand, obtained from the radial-derivative growth hypothesis.
    have hbnd : ∀ j : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ u ∈ Set.Icc (0:ℝ) 1, ∀ r : ℝ,
        ‖iteratedDeriv j (fun r' : ℝ =>
          N (tauM m u) (realIncl (n := n) r') * expM m u) r‖ ≤ B := by
      intro j
      obtain ⟨C, N', hC, hN', hb⟩ := hpb 0 j
      have hbase2 : 0 ≤ 1 + (ym m)⁻¹ + 2 := by
        have h : 0 ≤ (ym m)⁻¹ := inv_nonneg.mpr (ym_pos m).le
        linarith
      have hCpow : 0 ≤ C * (1 + (ym m)⁻¹ + 2) ^ N' :=
        mul_nonneg hC (Real.rpow_nonneg hbase2 N')
      refine ⟨Real.exp (2 * Real.pi) * (C * (1 + (ym m)⁻¹ + 2) ^ N'),
        mul_nonneg (Real.exp_pos _).le hCpow, ?_⟩
      intro u hu r
      have hτ : 0 < (tauM m u).im := tauM_im_pos m u
      have h1 := hb (tauM m u) hτ r
      simp only [pow_zero, one_mul] at h1
      have him : (tauM m u).im = ym m := tauM_im m u
      have hnorm : ‖tauM m u‖ ≤ 2 := tauM_norm_le m hu
      have hbase : 0 ≤ 1 + ((tauM m u).im)⁻¹ + ‖tauM m u‖ := by positivity
      have hmono : (1 + ((tauM m u).im)⁻¹ + ‖tauM m u‖) ^ N'
          ≤ (1 + (ym m)⁻¹ + 2) ^ N' := by
        apply Real.rpow_le_rpow hbase _ hN'
        rw [him]; linarith
      rw [iteratedDeriv_mul_const_field, norm_mul]
      calc ‖iteratedDeriv j (fun r' => N (tauM m u) (realIncl (n := n) r')) r‖
              * ‖expM m u‖
          ≤ (C * (1 + (ym m)⁻¹ + 2) ^ N') * Real.exp (2 * Real.pi) := by
            apply mul_le_mul _ (expM_norm_le m u) (norm_nonneg _) hCpow
            calc ‖iteratedDeriv j (fun r' => N (tauM m u) (realIncl (n := n) r')) r‖
                  ≤ C * (1 + ((tauM m u).im)⁻¹ + ‖tauM m u‖) ^ N' := h1
                _ ≤ C * (1 + (ym m)⁻¹ + 2) ^ N' := mul_le_mul_of_nonneg_left hmono hC
        _ = Real.exp (2 * Real.pi) * (C * (1 + (ym m)⁻¹ + 2) ^ N') := by ring
    have h := Work.Analysis.ParamIntegral.iteratedDeriv_intervalIntegral_of_cont
      (fun r u => N (tauM m u) (realIncl (n := n) r) * expM m u)
      (fun r => continuous_integrand N hN_cont m r)
      (fun u => (contDiff_integrand N hN_smooth m u).of_le le_top)
      hbnd
    refine ⟨h.1, fun j t => ?_⟩
    rw [h.2 j t]
    refine intervalIntegral.integral_congr (fun u _ => ?_)
    rw [iteratedDeriv_mul_const_field]
  have hpsi : ∀ m : Set.Ici (1:ℕ),
      psi N c m = fun t : ℝ => c m * ∫ u in (0:ℝ)..1,
        N (tauM m u) (realIncl (n := n) t) * expM m u := by
    intro m
    funext t
    rw [psi_apply]
  constructor
  · intro m
    rw [hpsi m]
    simpa using contDiff_const.mul (key m).1
  · intro m j t
    rw [hpsi m, iteratedDeriv_const_mul_field, (key m).2 j t]

end Work.FunctionalEquations.KernelSchwartz
