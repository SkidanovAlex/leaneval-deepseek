import Submission.Work.FunctionalEquations.KernelSchwartz.psi_deriv_bound
import Submission.Work.CKFinal.Shadow.Util
import Submission.Work.CKFinal.Shadow.Basic
import Submission.Work.CKFinal.Shadow.Defs

open scoped ContDiff
set_option linter.dupNamespace false

namespace Work.CKFinal.Shadow


/-!
# Polynomial growth in `m` of the derivatives of the interpolation profiles

The profile `psi N c m` of the `m`-th contour integral is the one-variable function

`t ↦ c m ∫_0^1 N (u + i/(m+1)) (t e₁) e^{-2π i m (u + i/(m+1))} du`.

Given the differentiation-under-the-integral formula for its iterated derivatives (the
hypothesis `hderiv`), together with the radial-growth hypothesis for the kernel and the
bound `‖c m‖ ≤ 1`, this file proves the polynomial growth bound

`|t|^k ‖(psi N c m)^{(ℓ)}(t)‖ ≤ C ((m+1)^N)   (m ≥ 1, t ∈ ℝ)`.

The proof is a direct estimate of the contour integral.

* The radial growth hypothesis, transferred to the profile `r ↦ N τ (r e₁)` by
  `profile_iteratedDeriv_bound`, bounds the integrand on the contour `τ = τ_m(u)`,
  `u ∈ [0,1]`; the `k`-th power of `|t|` is carried along by that same estimate.
* On this contour `(Im τ)^{-1} = m + 1` (as `Im τ = y_m = 1/(m+1)`) and `‖τ‖ ≤ 2`, so
  the weight `1 + (Im τ)^{-1} + ‖τ‖` is at most `4 (m+1)`.
* The exponential factor contributes at most `e^{2π}` (`expM_norm_le`), universally.
* The interval integral over `[0,1]` of a function bounded by `K` has norm at most `K`.

## Main result

* `Work.FunctionalEquations.KernelSchwartz.psi_deriv_bound`
-/

namespace Work.FunctionalEquations.KernelSchwartz

open LeanEval.Analysis.CKMRVInterpolation Work.Core Work.FE Filter Topology

noncomputable section

theorem psi_deriv_bound {n : ℕ} [NeZero n]
    (N : ℂ → Work.FE.E n → ℂ) (c : Set.Ici (1:ℕ) → ℂ)
    (hN_radial : ∀ τ : ℂ, LeanEval.Analysis.CKMRVInterpolation.Radial (fun x : Work.FE.E n => N τ x))
    (hN_growth : ∀ k ℓ : ℕ, ∃ C : ℝ, ∃ N' : ℝ, 0 ≤ C ∧ 0 ≤ N' ∧
      ∀ (τ : ℂ) (x : Work.FE.E n), 0 < τ.im →
        ‖x‖ ^ k * ‖Work.FE.radialDeriv ℓ (fun y : Work.FE.E n => N τ y) x‖
          ≤ C * (1 + (τ.im)⁻¹ + ‖τ‖) ^ N')
    (hc : ∀ m : Set.Ici (1:ℕ), ‖c m‖ ≤ 1)
    (hderiv : ∀ (m : Set.Ici (1:ℕ)) (j : ℕ) (t : ℝ),
      iteratedDeriv j (Work.FunctionalEquations.KernelSchwartz.psi N c m) t
        = c m * ∫ u in (0:ℝ)..1,
            iteratedDeriv j (fun r : ℝ => N (Work.FunctionalEquations.KernelSchwartz.tauM m u)
              (LeanEval.Analysis.CKMRVInterpolation.realIncl (n := n) r)) t
              * Work.FunctionalEquations.KernelSchwartz.expM m u) :
    ∀ k ℓ : ℕ, ∃ C : ℝ, ∃ N' : ℕ, 0 ≤ C ∧
      ∀ (m : Set.Ici (1:ℕ)) (t : ℝ),
        |t| ^ k * ‖iteratedDeriv ℓ (Work.FunctionalEquations.KernelSchwartz.psi N c m) t‖
          ≤ C * ((m.1 : ℝ) + 1) ^ N' := by
  intro k ℓ
  obtain ⟨C0, N0, hC0, hN0, hbound⟩ :=
    profile_iteratedDeriv_bound (n := n) N hN_radial hN_growth k ℓ
  refine ⟨C0 * 4 ^ ⌈N0⌉₊ * Real.exp (2 * Real.pi), ⌈N0⌉₊, by positivity, ?_⟩
  intro m t
  have hB1 : (1:ℝ) ≤ (m.1 : ℝ) + 1 := by
    have hm1 : (1 : ℝ) ≤ (m.1 : ℝ) := by exact_mod_cast m.2
    linarith
  have hBpos : (0:ℝ) < (m.1 : ℝ) + 1 := by linarith
  -- The weight `1 + (Im τ)^{-1} + ‖τ‖` on the contour, bound by `4 (m+1)`.
  have hweight : ∀ u ∈ Set.Icc (0:ℝ) 1,
      (1 + ((tauM m u).im)⁻¹ + ‖tauM m u‖) ^ N0 ≤ 4 ^ ⌈N0⌉₊ * ((m.1:ℝ) + 1) ^ ⌈N0⌉₊ := by
    intro u hu
    have hA1 : 1 ≤ 1 + ((tauM m u).im)⁻¹ + ‖tauM m u‖ := by
      have h1 : 0 ≤ ((tauM m u).im)⁻¹ := inv_nonneg.mpr (tauM_im_pos m u).le
      have h2 : 0 ≤ ‖tauM m u‖ := norm_nonneg _
      linarith
    have hAle : 1 + ((tauM m u).im)⁻¹ + ‖tauM m u‖ ≤ 4 * ((m.1:ℝ) + 1) := by
      rw [tauM_im, ym_inv]
      have h2 : ‖tauM m u‖ ≤ 2 := tauM_norm_le m hu
      have hm1 : (1 : ℝ) ≤ (m.1 : ℝ) := by exact_mod_cast m.2
      linarith
    calc (1 + ((tauM m u).im)⁻¹ + ‖tauM m u‖) ^ N0
        ≤ (4 * ((m.1:ℝ) + 1)) ^ N0 := Real.rpow_le_rpow (le_trans zero_le_one hA1) hAle hN0
      _ = 4 ^ N0 * ((m.1:ℝ) + 1) ^ N0 := Real.mul_rpow (by norm_num) hBpos.le
      _ ≤ 4 ^ ⌈N0⌉₊ * ((m.1:ℝ) + 1) ^ ⌈N0⌉₊ := by
          have h4 : (4:ℝ) ^ N0 ≤ (4:ℝ) ^ ((⌈N0⌉₊ : ℕ) : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.le_ceil N0)
          have hB0 : ((m.1:ℝ) + 1) ^ N0 ≤ ((m.1:ℝ) + 1) ^ ((⌈N0⌉₊ : ℕ) : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hB1 (Nat.le_ceil N0)
          have := mul_le_mul h4 hB0 (Real.rpow_nonneg hBpos.le N0) (by positivity)
          simpa [Real.rpow_natCast] using this
  have hcast : ‖((|t| ^ k : ℝ) : ℂ)‖ = |t| ^ k := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  -- Pointwise bound for the integrand on `(0,1]`.
  have hpt : ∀ u ∈ Set.uIoc (0:ℝ) 1,
      ‖((|t| ^ k : ℝ) : ℂ) * (iteratedDeriv ℓ (fun r : ℝ => N (tauM m u) (realIncl (n := n) r)) t * expM m u)‖
        ≤ C0 * 4 ^ ⌈N0⌉₊ * ((m.1:ℝ) + 1) ^ ⌈N0⌉₊ * Real.exp (2 * Real.pi) := by
    intro u hu
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hu
    have huIcc : u ∈ Set.Icc (0:ℝ) 1 := ⟨hu.1.le, hu.2⟩
    have hg := hbound (tauM m u) (tauM_im_pos m u) t
    calc ‖((|t| ^ k : ℝ) : ℂ) * (iteratedDeriv ℓ (fun r : ℝ => N (tauM m u) (realIncl (n := n) r)) t * expM m u)‖
        = |t| ^ k * (‖iteratedDeriv ℓ (fun r : ℝ => N (tauM m u) (realIncl (n := n) r)) t‖ * ‖expM m u‖) := by
          rw [norm_mul, norm_mul, hcast]
      _ ≤ |t| ^ k * (‖iteratedDeriv ℓ (fun r : ℝ => N (tauM m u) (realIncl (n := n) r)) t‖ * Real.exp (2 * Real.pi)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left (expM_norm_le m u) (norm_nonneg _)
      _ = (|t| ^ k * ‖iteratedDeriv ℓ (fun r : ℝ => N (tauM m u) (realIncl (n := n) r)) t‖) * Real.exp (2 * Real.pi) := by ring
      _ ≤ (C0 * (1 + ((tauM m u).im)⁻¹ + ‖tauM m u‖) ^ N0) * Real.exp (2 * Real.pi) :=
          mul_le_mul_of_nonneg_right hg (Real.exp_pos _).le
      _ ≤ (C0 * (4 ^ ⌈N0⌉₊ * ((m.1:ℝ) + 1) ^ ⌈N0⌉₊)) * Real.exp (2 * Real.pi) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hweight u huIcc) hC0) (Real.exp_pos _).le
      _ = C0 * 4 ^ ⌈N0⌉₊ * ((m.1:ℝ) + 1) ^ ⌈N0⌉₊ * Real.exp (2 * Real.pi) := by ring
  have hInt := intervalIntegral.norm_integral_le_of_norm_le_const hpt
  calc |t| ^ k * ‖iteratedDeriv ℓ (psi N c m) t‖
      = |t| ^ k * ‖c m * ∫ u in (0:ℝ)..1, iteratedDeriv ℓ (fun r : ℝ => N (tauM m u) (realIncl (n := n) r)) t * expM m u‖ := by
          rw [hderiv m ℓ t]
    _ ≤ |t| ^ k * (1 * ‖∫ u in (0:ℝ)..1, iteratedDeriv ℓ (fun r : ℝ => N (tauM m u) (realIncl (n := n) r)) t * expM m u‖) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          calc ‖c m * ∫ u in (0:ℝ)..1, iteratedDeriv ℓ (fun r : ℝ => N (tauM m u) (realIncl (n := n) r)) t * expM m u‖
              ≤ ‖c m‖ * ‖∫ u in (0:ℝ)..1, iteratedDeriv ℓ (fun r : ℝ => N (tauM m u) (realIncl (n := n) r)) t * expM m u‖ := norm_mul_le _ _
            _ ≤ 1 * ‖∫ u in (0:ℝ)..1, iteratedDeriv ℓ (fun r : ℝ => N (tauM m u) (realIncl (n := n) r)) t * expM m u‖ :=
                mul_le_mul_of_nonneg_right (hc m) (norm_nonneg _)
    _ = ‖((|t| ^ k : ℝ) : ℂ) * ∫ u in (0:ℝ)..1, iteratedDeriv ℓ (fun r : ℝ => N (tauM m u) (realIncl (n := n) r)) t * expM m u‖ := by
          rw [norm_mul, hcast, one_mul]
    _ = ‖∫ u in (0:ℝ)..1, ((|t| ^ k : ℝ) : ℂ) * (iteratedDeriv ℓ (fun r : ℝ => N (tauM m u) (realIncl (n := n) r)) t * expM m u)‖ := by
          rw [intervalIntegral.integral_const_mul]
    _ ≤ (C0 * 4 ^ ⌈N0⌉₊ * ((m.1:ℝ) + 1) ^ ⌈N0⌉₊ * Real.exp (2 * Real.pi)) * |1 - 0| := hInt
    _ = C0 * 4 ^ ⌈N0⌉₊ * Real.exp (2 * Real.pi) * ((m.1:ℝ) + 1) ^ ⌈N0⌉₊ := by
          rw [show (|(1:ℝ) - 0|) = 1 by norm_num]; ring

end

end Work.FunctionalEquations.KernelSchwartz


end Work.CKFinal.Shadow
