/-
# The `r`-seminorm of the compact `Aexp` piece `tangA` of the tangency layer

`tangA ℓ d τ x = ∫_1^{3/2} Aexp (Gcusp ℓ d) τ t · e^{-πxt} dt` is an integral of a bounded
amplitude over a compact interval, so every iterated `x`-derivative is bounded by
`C (1+x)^{-N}`: differentiating under the integral sign multiplies the amplitude by
`(-πt)^m` (bounded by `(3π/2)^m` on `[1,3/2]`) and the remaining factor `e^{-πx}` decays
faster than any power.  The differentiation-under-the-integral lemma is
`Work.Asymptotics.HalfFunnel.iteratedDeriv_intervalIntegral_exp_of_bound`
(`lowBad_Phi12_deriv.lean`); the boundedness of `Aexp` on the compact `ctanCl × [-3/2,3/2]` is
`continuous_Aexp_tang` (`tangTailExpansion.lean`).
-/
import Mathlib
import Submission.Work.Asymptotics.HalfFunnel.tangLayerDefs
import Submission.Work.HFN.HalfFunnel.tangTailExpansion
import Submission.Work.HFN.HalfFunnel.lowBad_Phi12_deriv

set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory Filter UpperHalfPlane
open scoped Topology

namespace Work.HFN.HalfFunnel
open Work.Asymptotics Work.Asymptotics.HalfFunnel  -- ck-hfn-fix: fork moved out of Work.Asymptotics

open Work.Kernels

/-- `e^{-πx}` decays faster than any negative power of `1 + x`, for a *real* exponent `N ≥ 0`. -/
lemma exp_neg_le_rpow_neg (N : ℝ) (hN : 0 ≤ N) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, 0 ≤ x → Real.exp (-(Real.pi * x)) ≤ K * (1 + x) ^ (-N) := by
  obtain ⟨K, hK0, hK⟩ := exists_exp_neg_le_pow (c := Real.pi) Real.pi_pos (Nat.ceil N)
  refine ⟨K, hK0, fun x hx => ?_⟩
  refine le_trans (hK x hx) (mul_le_mul_of_nonneg_left ?_ hK0)
  refine Real.rpow_le_rpow_of_exponent_le (by linarith) ?_
  have h : N ≤ ((Nat.ceil N : ℕ) : ℝ) := Nat.le_ceil N
  linarith

/-- **The `r`-seminorm of the compact `Aexp` piece.** -/
theorem tangADeriv (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∀ m : ℕ, ∀ N : ℝ, 0 ≤ N → ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ : UpperHalfPlane) (x : ℝ),
      τ ∈ ctanRegion → 0 ≤ x →
      ‖iteratedDeriv m (tangA ℓ d τ) x‖
        ≤ C * (1 + x) ^ (-N) := by
  intro m N hN
  obtain ⟨B, hB⟩ := (isCompact_ctanCl.prod
      (isCompact_Icc (a := (-(3 / 2) : ℝ)) (b := (3 / 2 : ℝ)))).exists_bound_of_continuousOn
    (continuous_Aexp_tang ℓ d hd).continuousOn
  obtain ⟨Kc, hKc0, hKc⟩ := exp_neg_le_rpow_neg N hN
  refine ⟨max B 0 * (Real.pi * (3 / 2)) ^ m * (1 / 2) * Kc, by positivity,
    fun τ x hτ hx => ?_⟩
  have hτcl : τ ∈ ctanCl := ctanRegion_subset_ctanCl hτ
  have hfuneq : tangA ℓ d τ = fun y : ℝ => ∫ t in (1 : ℝ)..(3 / 2),
      Aexp (Gcusp ℓ d) τ t * (Real.exp (-(Real.pi * y * t)) : ℂ) := by
    funext y
    rw [tangA]
    refine intervalIntegral.integral_congr ?_
    intro t ht
    simp only
    congr 1
    rw [tangGauss, Complex.ofReal_exp]
    push_cast
    ring
  rw [hfuneq]
  have hcont : Continuous (fun t : ℝ => Aexp (Gcusp ℓ d) τ t) :=
    (continuous_Aexp_tang ℓ d hd).comp (continuous_const.prodMk continuous_id)
  have hbd : ∀ᵐ t ∂(volume.restrict (Set.Ioc (1 : ℝ) (3 / 2))),
      ‖Aexp (Gcusp ℓ d) τ t‖ ≤ max B 0 := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
    exact le_trans (hB (τ, t) ⟨hτcl, ⟨by linarith [ht.1], ht.2⟩⟩) (le_max_left _ _)
  rw [iteratedDeriv_intervalIntegral_exp_of_bound (fun t : ℝ => Aexp (Gcusp ℓ d) τ t)
    (1 : ℝ) (3 / 2) (by norm_num) hcont.aestronglyMeasurable (le_max_right B 0) hbd m x]
  have hstep : ‖∫ t in (1 : ℝ)..(3 / 2), Aexp (Gcusp ℓ d) τ t
        * (((-(Real.pi * t) : ℝ)) : ℂ) ^ m
        * (Real.exp (-(Real.pi * x * t)) : ℂ)‖
      ≤ max B 0 * (Real.pi * (3 / 2)) ^ m * Real.exp (-(Real.pi * x)) * (1 / 2) := by
    refine le_trans (intervalIntegral.norm_integral_le_of_norm_le_const
      (C := max B 0 * (Real.pi * (3 / 2)) ^ m * Real.exp (-(Real.pi * x)))
      (a := 1) (b := 3 / 2) ?_) ?_
    · intro t ht
      rw [Set.uIoc_of_le (by norm_num : (1 : ℝ) ≤ 3 / 2)] at ht
      have ht1 : (1 : ℝ) ≤ t := le_of_lt ht.1
      have ht2 : t ≤ 3 / 2 := ht.2
      have h1 : ‖Aexp (Gcusp ℓ d) τ t‖ ≤ max B 0 :=
        le_trans (hB (τ, t) ⟨hτcl, ⟨by linarith, ht2⟩⟩) (le_max_left _ _)
      have h2 : ‖((( -(Real.pi * t)) : ℝ) : ℂ) ^ m‖ ≤ (Real.pi * (3 / 2)) ^ m := by
        rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos (by positivity)]
        exact pow_le_pow_left₀ (by positivity) (by nlinarith [Real.pi_pos]) m
      have h3 : ‖(Real.exp (-(Real.pi * x * t)) : ℂ)‖ ≤ Real.exp (-(Real.pi * x)) := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        refine Real.exp_le_exp.mpr ?_
        have hxt : Real.pi * x ≤ Real.pi * x * t := by
          have := mul_le_mul_of_nonneg_left ht1 (mul_nonneg Real.pi_pos.le hx)
          linarith
        linarith
      rw [norm_mul, norm_mul]
      exact mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) (le_trans (norm_nonneg _) h1))
        h3 (norm_nonneg _)
        (mul_nonneg (le_trans (norm_nonneg _) h1)
          (pow_nonneg (mul_nonneg Real.pi_pos.le (by norm_num)) m))
    · rw [show (3 : ℝ) / 2 - 1 = (1 : ℝ) / 2 by norm_num, abs_of_pos (by norm_num)]
  refine le_trans hstep ?_
  have hc0 : (0 : ℝ) ≤ max B 0 * (Real.pi * (3 / 2)) ^ m * (1 / 2) := by positivity
  calc max B 0 * (Real.pi * (3 / 2)) ^ m * Real.exp (-(Real.pi * x)) * (1 / 2)
      = (max B 0 * (Real.pi * (3 / 2)) ^ m * (1 / 2)) * Real.exp (-(Real.pi * x)) := by ring
    _ ≤ (max B 0 * (Real.pi * (3 / 2)) ^ m * (1 / 2)) * (Kc * (1 + x) ^ (-N)) :=
        mul_le_mul_of_nonneg_left (hKc x hx) hc0
    _ = (max B 0 * (Real.pi * (3 / 2)) ^ m * (1 / 2) * Kc) * (1 + x) ^ (-N) := by ring

end Work.HFN.HalfFunnel
