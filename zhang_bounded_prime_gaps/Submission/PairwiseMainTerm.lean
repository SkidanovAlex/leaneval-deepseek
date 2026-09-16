import Mathlib
import Submission.PairwiseFourier
import Submission.MainTerm

open scoped BigOperators Topology FourierTransform SchwartzMap
open Filter MeasureTheory

set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-!
# The main term of the pairwise Lemma 4.1

The `ξ`-integral of the pairwise kernel is, up to the vanishing comparison error
(handled in the truncation step), the integral of the inverse pole factors

    ∫_{ℝ^{2k}} (∏_j [poleFactor_j]⁻¹) · ∏_j 𝓕(eᵘF_j)(ξ_j)·𝓕(eᵘG_j)(ξ′_j)
      = prefactor^k · ∏_j ∫₀^∞ F_j′(t)G_j′(t) dt ,

the `k`-fold product of the one-coordinate main term
`MainTerm.poleFactor_mainTerm`.  This is the value of the pairwise main term of
Theorem 3.6(i).

All kernel-verified, zero `sorry`.
-/

namespace Commons.NumberTheory.MaynardSieve

/-- **Measurability of the one-coordinate pole integrand.** -/
lemma aestronglyMeasurable_poleInv_mul_fourierCut (F G : ℝ → ℝ)
    (hcsF : HasCompactSupport F) (hsmF : ContDiff ℝ (↑(⊤ : ℕ∞)) F)
    (hcsG : HasCompactSupport G) (hsmG : ContDiff ℝ (↑(⊤ : ℕ∞)) G)
    (W N : ℕ → ℕ) (hW : ∀ x, W x ≠ 0) (hN : ∀ x, N x ≠ 0) (x : ℕ)
    (hlog : Real.log (x : ℝ) ≠ 0) :
    AEStronglyMeasurable (fun q : ℝ × ℝ =>
      (poleFactor (W x) (N x) (-(2 * Real.pi * q.1)) (-(2 * Real.pi * q.2)) x)⁻¹ *
        (fourierCut F q.1 * fourierCut G q.2)) := by
  have hFc : Continuous (fourierCut F) := by
    have h2 := (schwartzCut F hcsF hsmF).continuous
    rw [schwartzCut_coe F hcsF hsmF] at h2
    exact h2
  have hGc : Continuous (fourierCut G) := by
    have h2 := (schwartzCut G hcsG hsmG).continuous
    rw [schwartzCut_coe G hcsG hsmG] at h2
    exact h2
  have h1 : Continuous fun q : ℝ × ℝ => fourierCut F q.1 := by fun_prop (disch := exact hFc)
  have h2 : Continuous fun q : ℝ × ℝ => fourierCut G q.2 := by fun_prop (disch := exact hGc)
  have hfg : Measurable fun q : ℝ × ℝ => fourierCut F q.1 * fourierCut G q.2 :=
    (h1.mul h2).measurable
  have hp : Measurable fun q : ℝ × ℝ =>
      (poleFactor (W x) (N x) (-(2 * Real.pi * q.1)) (-(2 * Real.pi * q.2)) x)⁻¹ := by
    have key : (fun q : ℝ × ℝ =>
        (poleFactor (W x) (N x) (-(2 * Real.pi * q.1)) (-(2 * Real.pi * q.2)) x)⁻¹) =
        fun q : ℝ × ℝ => ((N x : ℂ) / ((((W x).totient : ℂ) / (W x : ℂ)) *
            (Real.log (x : ℝ) : ℂ) * ((N x).totient : ℂ))) *
          ((1 - 2 * Real.pi * Complex.I * q.1) * (1 - 2 * Real.pi * Complex.I * q.2) /
            (2 - 2 * Real.pi * Complex.I * (q.1 + q.2))) := by
      funext q
      exact poleInv_eq (W x) (N x) (hW x) (hN x) hlog q.1 q.2
    rw [key]
    fun_prop
  exact (hp.mul hfg).aestronglyMeasurable

/-- **Integrability of the one-coordinate pole integrand.** -/
lemma integrable_poleInv_mul_fourierCut (F G : ℝ → ℝ) (hcsF : HasCompactSupport F)
    (hsmF : ContDiff ℝ (↑(⊤ : ℕ∞)) F) (hcsG : HasCompactSupport G) (hsmG : ContDiff ℝ (↑(⊤ : ℕ∞)) G)
    (W N : ℕ → ℕ) (hW : ∀ x, W x ≠ 0) (hN : ∀ x, N x ≠ 0) (x : ℕ)
    (hlog : Real.log (x : ℝ) ≠ 0) (hlogpos : 0 < Real.log (x : ℝ)) :
    Integrable (fun q : ℝ × ℝ =>
      (poleFactor (W x) (N x) (-(2 * Real.pi * q.1)) (-(2 * Real.pi * q.2)) x)⁻¹ *
        (fourierCut F q.1 * fourierCut G q.2)) := by
  set cst : ℝ := ((N x : ℝ) / ((N x).totient : ℝ)) * ((W x : ℝ) / ((W x).totient : ℝ)) *
    ((Real.log (x : ℝ))⁻¹) with hcst
  have hdom : Integrable (fun q : ℝ × ℝ =>
      cst * (((1 + 2 * Real.pi * |q.1|) * ‖fourierCut F q.1‖) *
          ((1 + 2 * Real.pi * |q.2|) * ‖fourierCut G q.2‖))) := by
    rw [show (volume : Measure (ℝ × ℝ)) = Measure.prod volume volume from rfl]
    exact ((integrable_one_add_abs_mul_norm_fourierCut F hcsF hsmF).mul_prod
      (integrable_one_add_abs_mul_norm_fourierCut G hcsG hsmG)).const_mul _
  refine Integrable.mono' hdom
    (aestronglyMeasurable_poleInv_mul_fourierCut F G hcsF hsmF hcsG hsmG W N hW hN x hlog) ?_
  filter_upwards with q
  rw [norm_mul, norm_mul]
  have hgrowth := norm_poleInv_le (W x) (N x) (hW x) (hN x) hlog hlogpos q.1 q.2
  have hc0 : 0 ≤ cst := by
    rw [hcst]
    have h1 : (0 : ℝ) < ((N x).totient : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (hN x))
    have h2 : (0 : ℝ) < ((W x).totient : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (hW x))
    positivity
  refine (mul_le_mul_of_nonneg_right hgrowth (mul_nonneg (norm_nonneg _) (norm_nonneg _))).trans
    (le_of_eq ?_)
  rw [hcst]
  ring


/-! ## The `k`-fold main term -/

/-- **The main term of the pairwise Lemma 4.1.**  The `2k`-fold integral of the
inverse pole factors against the Fourier transforms of the cutoffs equals
`prefactor^k` times the product of the one-dimensional main terms. -/
theorem pairPoleMainTerm {k : ℕ} (F G : Fin k → ℝ → ℝ)
    (hcsF : ∀ j, HasCompactSupport (F j)) (hsmF : ∀ j, ContDiff ℝ (↑(⊤ : ℕ∞)) (F j))
    (hcsG : ∀ j, HasCompactSupport (G j)) (hsmG : ∀ j, ContDiff ℝ (↑(⊤ : ℕ∞)) (G j))
    (W N : ℕ → ℕ) (hW : ∀ x, W x ≠ 0) (hN : ∀ x, N x ≠ 0) (x : ℕ)
    (hlog : Real.log (x : ℝ) ≠ 0) (hlogpos : 0 < Real.log (x : ℝ)) :
    (∫ p : Fin k → ℝ × ℝ,
        (∏ j : Fin k, (poleFactor (W x) (N x) (-(2 * Real.pi * (p j).1))
            (-(2 * Real.pi * (p j).2)) x)⁻¹) *
        (∏ j : Fin k, (fourierCut (F j) (p j).1 * fourierCut (G j) (p j).2)))
      = ((prefactor W N x : ℝ) : ℂ) ^ k *
        ∏ j : Fin k, (∫ t : ℝ in Set.Ioi 0,
          ((deriv (F j) t : ℝ) : ℂ) * ((deriv (G j) t : ℝ) : ℂ)) := by
  have hsplit : (fun p : Fin k → ℝ × ℝ =>
        (∏ j : Fin k, (poleFactor (W x) (N x) (-(2 * Real.pi * (p j).1))
            (-(2 * Real.pi * (p j).2)) x)⁻¹) *
        (∏ j : Fin k, (fourierCut (F j) (p j).1 * fourierCut (G j) (p j).2))) =
      fun p : Fin k → ℝ × ℝ => ∏ j : Fin k,
        ((poleFactor (W x) (N x) (-(2 * Real.pi * (p j).1))
            (-(2 * Real.pi * (p j).2)) x)⁻¹ *
          (fourierCut (F j) (p j).1 * fourierCut (G j) (p j).2)) := by
    funext p
    simp only [Finset.prod_mul_distrib]
  rw [hsplit]
  rw [show (∫ p : Fin k → ℝ × ℝ, ∏ j : Fin k,
        ((poleFactor (W x) (N x) (-(2 * Real.pi * (p j).1))
            (-(2 * Real.pi * (p j).2)) x)⁻¹ *
          (fourierCut (F j) (p j).1 * fourierCut (G j) (p j).2)))
      = ∏ j : Fin k, ∫ q : ℝ × ℝ,
        ((poleFactor (W x) (N x) (-(2 * Real.pi * q.1)) (-(2 * Real.pi * q.2)) x)⁻¹ *
          (fourierCut (F j) q.1 * fourierCut (G j) q.2)) from
    MeasureTheory.integral_fintype_prod_volume_eq_prod
      (fun j (q : ℝ × ℝ) => (poleFactor (W x) (N x) (-(2 * Real.pi * q.1))
          (-(2 * Real.pi * q.2)) x)⁻¹ *
        (fourierCut (F j) q.1 * fourierCut (G j) q.2))]
  have h1 : ∀ j : Fin k, (∫ q : ℝ × ℝ,
        (poleFactor (W x) (N x) (-(2 * Real.pi * q.1)) (-(2 * Real.pi * q.2)) x)⁻¹ *
          (fourierCut (F j) q.1 * fourierCut (G j) q.2))
      = ((prefactor W N x : ℝ) : ℂ) * (∫ t : ℝ in Set.Ioi 0,
          ((deriv (F j) t : ℝ) : ℂ) * ((deriv (G j) t : ℝ) : ℂ)) := by
    intro j
    have hiter : (∫ q : ℝ × ℝ,
          (poleFactor (W x) (N x) (-(2 * Real.pi * q.1)) (-(2 * Real.pi * q.2)) x)⁻¹ *
            (fourierCut (F j) q.1 * fourierCut (G j) q.2))
        = ∫ ξ : ℝ, ∫ ξ' : ℝ,
            (poleFactor (W x) (N x) (-(2 * Real.pi * ξ)) (-(2 * Real.pi * ξ')) x)⁻¹ *
              (fourierCut (F j) ξ * fourierCut (G j) ξ') := by
      rw [show (volume : Measure (ℝ × ℝ)) = Measure.prod volume volume from rfl]
      exact integral_prod _ (integrable_poleInv_mul_fourierCut (F j) (G j) (hcsF j) (hsmF j)
        (hcsG j) (hsmG j) W N hW hN x hlog hlogpos)
    rw [hiter]
    have hsc : (∫ ξ : ℝ, ∫ ξ' : ℝ,
          (poleFactor (W x) (N x) (-(2 * Real.pi * ξ)) (-(2 * Real.pi * ξ')) x)⁻¹ *
            (fourierCut (F j) ξ * fourierCut (G j) ξ'))
        = ∫ ξ : ℝ, ∫ ξ' : ℝ,
            (poleFactor (W x) (N x) (-(2 * Real.pi * ξ)) (-(2 * Real.pi * ξ')) x)⁻¹ *
              (SchwartzMap.fourierTransformCLM ℂ (V := ℝ)
                  (expCutoffSchwartz (F j) (hcsF j) (hsmF j))) ξ *
              (SchwartzMap.fourierTransformCLM ℂ (V := ℝ)
                  (expCutoffSchwartz (G j) (hcsG j) (hsmG j))) ξ' := by
      refine integral_congr_ae (Filter.Eventually.of_forall (fun ξ => ?_))
      refine integral_congr_ae (Filter.Eventually.of_forall (fun ξ' => ?_))
      dsimp only
      rw [fourierCut_eq_fourierTransformCLM (hcsF j) (hsmF j) ξ,
        fourierCut_eq_fourierTransformCLM (hcsG j) (hsmG j) ξ']
      ring
    rw [hsc, poleFactor_mainTerm (W x) (N x) (hW x) (hN x) x hlog
      (expCutoffSchwartz (F j) (hcsF j) (hsmF j))
      (expCutoffSchwartz (G j) (hcsG j) (hsmG j))]
    rw [prefactor_eq_poleConstant W N (hW x) (hN x) hlog]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
    dsimp only
    rw [exp_neg_mul_deriv_sub (hcsF j) (hsmF j) t, exp_neg_mul_deriv_sub (hcsG j) (hsmG j) t]
  rw [Finset.prod_congr rfl (fun j _ => h1 j), Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

end Commons.NumberTheory.MaynardSieve

