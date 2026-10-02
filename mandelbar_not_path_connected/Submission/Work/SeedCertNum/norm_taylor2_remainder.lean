import Mathlib
import Submission.Work.SeedCertNum.Jet1

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# A quadratic Taylor remainder bound for holomorphic `F : ℂ → ℂ`

This file proves `Work.SeedCertNum.norm_taylor2_remainder`: if `F : ℂ → ℂ` is complex
differentiable, `F z₀ = z₀`, `deriv F z₀ = 1`, `iteratedDeriv 2 F z₀ = 2 * A`, and the third
derivative of `F` is bounded by `K` on the disc of radius `ρ` around `z₀`, then for `‖u‖ ≤ ρ`

  `‖F (z₀ + u) - z₀ - u - A * u ^ 2‖ ≤ (K / 6) * ‖u‖ ^ 3`.

The proof is Taylor's formula with the integral remainder
(`map_add_eq_sum_add_integral_iteratedFDeriv`) applied with `n = 2` to `z₀` and `u`, together
with the comparison of the real and complex iterated Fréchet derivatives
(`ContDiffAt.restrictScalars_iteratedFDeriv`) and the estimate
`∫₀¹ (1 - t)² dt = 1/3`.
-/

namespace Work.SeedCertNum

open MeasureTheory

/-- For a complex differentiable `F : ℂ → ℂ`, the `n`-th *real* iterated Fréchet derivative of `F`
at `w`, evaluated on the constant tuple `(u, …, u)`, equals `u ^ n` times the `n`-th complex
iterated derivative. -/
lemma iteratedFDeriv_real_apply_iteratedDeriv {F : ℂ → ℂ} {w u : ℂ} {n : ℕ}
    (h : ContDiffAt ℂ (n : WithTop ℕ∞) F w) :
    iteratedFDeriv ℝ n F w (fun _ => u) = u ^ n * iteratedDeriv n F w := by
  have hrestrict : ContinuousMultilinearMap.restrictScalars ℝ (iteratedFDeriv ℂ n F w)
      = iteratedFDeriv ℝ n F w := h.restrictScalars_iteratedFDeriv
  have key : iteratedFDeriv ℝ n F w (fun _ => u)
      = iteratedFDeriv ℂ n F w (fun _ => u) := by
    rw [← hrestrict]; rfl
  rw [key, iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, Finset.prod_const,
    Finset.card_fin, smul_eq_mul]

theorem norm_taylor2_remainder {F : ℂ → ℂ} {z₀ A : ℂ} {K ρ : ℝ}
    (hF : ∀ w : ℂ, DifferentiableAt ℂ F w) (hK : 0 ≤ K) (hρ : 0 ≤ ρ)
    (h3 : ∀ w : ℂ, ‖w‖ ≤ ρ → ‖iteratedDeriv 3 F (z₀ + w)‖ ≤ K)
    (h0 : F z₀ = z₀) (h1 : deriv F z₀ = 1) (h2 : iteratedDeriv 2 F z₀ = 2 * A)
    {u : ℂ} (hu : ‖u‖ ≤ ρ) :
    ‖F (z₀ + u) - z₀ - u - A * u ^ 2‖ ≤ (K / 6) * ‖u‖ ^ 3 := by
  -- `F` is complex differentiable everywhere, hence (complex) `C^3`.
  have hcd : ContDiff ℂ (3 : WithTop ℕ∞) F := Differentiable.contDiff hF
  have hcdR : ContDiff ℝ (3 : WithTop ℕ∞) F := hcd.restrict_scalars ℝ
  -- Abbreviate the integral remainder.
  set I : ℂ := ∫ t in 0..1, (1 - t)^2 •
      iteratedFDeriv ℝ 3 F (z₀ + t • u) (fun _ => u) with hIdef
  -- Taylor's formula with integral remainder, second order, at `z₀` in direction `u`.
  have hTaylor := map_add_eq_sum_add_integral_iteratedFDeriv (f := F) (x := z₀) (y := u) (n := 2)
      (fun t _ => hcdR.contDiffAt)
  -- The Taylor polynomial of order two evaluates to `z₀ + u + A * u ^ 2`.
  have hS : (∑ k ∈ Finset.range 3, ((Nat.factorial k : ℝ))⁻¹ •
      (iteratedFDeriv ℝ k F z₀ (fun _ => u))) = z₀ + u + A * u ^ 2 := by
    have hc0 : ContDiffAt ℂ (0 : WithTop ℕ∞) F z₀ := hcd.contDiffAt.of_le (by norm_num)
    have hc1 : ContDiffAt ℂ (1 : WithTop ℕ∞) F z₀ := hcd.contDiffAt.of_le (by norm_num)
    have hc2 : ContDiffAt ℂ (2 : WithTop ℕ∞) F z₀ := hcd.contDiffAt.of_le (by norm_num)
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero,
      zero_add]
    rw [iteratedFDeriv_real_apply_iteratedDeriv (h := hc0),
        iteratedFDeriv_real_apply_iteratedDeriv (h := hc1),
        iteratedFDeriv_real_apply_iteratedDeriv (h := hc2)]
    simp only [iteratedDeriv_zero, iteratedDeriv_one, Nat.factorial_zero, Nat.factorial_one,
      Nat.factorial_two, Nat.cast_one, Nat.cast_ofNat, inv_one, one_smul, pow_zero, pow_one]
    rw [h0, h1, h2, Complex.real_smul]
    push_cast
    ring
  -- Hence the required difference is exactly the scaled integral remainder.
  have hkey : F (z₀ + u) - z₀ - u - A * u ^ 2 = ((Nat.factorial 2 : ℝ))⁻¹ • I := by
    rw [hTaylor, hS, ← hIdef]
    abel
  -- Estimate the integral remainder.
  have hI : ‖I‖ ≤ K * ‖u‖ ^ 3 / 3 := by
    rw [hIdef]
    have hle : ‖∫ t in 0..1, (1 - t)^2 • iteratedFDeriv ℝ 3 F (z₀ + t • u) (fun _ => u)‖
        ≤ ∫ t in 0..1, (K * ‖u‖ ^ 3) * (1 - t)^2 := by
      refine intervalIntegral.norm_integral_le_of_norm_le (by norm_num : (0:ℝ) ≤ 1) ?_ ?_
      · refine Filter.Eventually.of_forall fun t ht => ?_
        have ht1 : (0:ℝ) < t := ht.1
        have ht2 : t ≤ 1 := ht.2
        have hV : ‖iteratedFDeriv ℝ 3 F (z₀ + t • u) (fun _ => u)‖ ≤ K * ‖u‖ ^ 3 := by
          rw [iteratedFDeriv_real_apply_iteratedDeriv (h := hcd.contDiffAt), norm_mul, norm_pow]
          have htw : ‖t • u‖ ≤ ρ := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht1.le]
            calc t * ‖u‖ ≤ 1 * ‖u‖ := by nlinarith [norm_nonneg u]
              _ = ‖u‖ := one_mul _
              _ ≤ ρ := hu
          calc ‖u‖ ^ 3 * ‖iteratedDeriv 3 F (z₀ + t • u)‖ ≤ ‖u‖ ^ 3 * K := by
                gcongr; exact h3 (t • u) htw
            _ = K * ‖u‖ ^ 3 := by ring
        calc ‖(1 - t)^2 • iteratedFDeriv ℝ 3 F (z₀ + t • u) (fun _ => u)‖
            = ‖(1 - t)^2‖ * ‖iteratedFDeriv ℝ 3 F (z₀ + t • u) (fun _ => u)‖ := norm_smul _ _
          _ = (1 - t)^2 * ‖iteratedFDeriv ℝ 3 F (z₀ + t • u) (fun _ => u)‖ := by
                rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
          _ ≤ (1 - t)^2 * (K * ‖u‖ ^ 3) := by gcongr
          _ = (K * ‖u‖ ^ 3) * (1 - t)^2 := by ring
      · exact (by fun_prop : Continuous fun t : ℝ => (K * ‖u‖ ^ 3) * (1 - t)^2).intervalIntegrable _ _
    have hint : (∫ t in 0..1, (1 - t)^2) = 1/3 := by
      rw [intervalIntegral.integral_comp_sub_left (fun x : ℝ => x^2) 1]
      norm_num
    calc ‖∫ t in 0..1, (1 - t)^2 • iteratedFDeriv ℝ 3 F (z₀ + t • u) (fun _ => u)‖
        ≤ ∫ t in 0..1, (K * ‖u‖ ^ 3) * (1 - t)^2 := hle
      _ = (K * ‖u‖ ^ 3) * (∫ t in 0..1, (1 - t)^2) := intervalIntegral.integral_const_mul _ _
      _ = K * ‖u‖ ^ 3 / 3 := by rw [hint]; ring
  calc ‖F (z₀ + u) - z₀ - u - A * u ^ 2‖
      = ‖((Nat.factorial 2 : ℝ))⁻¹ • I‖ := by rw [hkey]
    _ = ‖((Nat.factorial 2 : ℝ))⁻¹‖ * ‖I‖ := norm_smul _ _
    _ = (1/2) * ‖I‖ := by norm_num
    _ ≤ (1/2) * (K * ‖u‖^3 / 3) := by gcongr
    _ = (K/6)*‖u‖^3 := by ring

end Work.SeedCertNum
