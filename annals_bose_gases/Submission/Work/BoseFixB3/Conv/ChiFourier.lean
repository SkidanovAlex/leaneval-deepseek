import Mathlib.Tactic.Have
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.BoseFixB3.Scaling.chiSq_mult_bound
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseFixB3/Conv/ChiFourier`

Fourier facts about the profile `φ = χ²` (`Work.BoseFixB3.Scaling.phi`) used by the
high-frequency decay of the localisation window `χ_Λ²` (`Conv/chi_highpass_decay.lean`):

* `kinInv_kinFT_phiC` — Fourier inversion in the corpus's `p`-convention;
* `kinFT_phiC_decay` — Schwartz decay of `φ̂`;
* `kinFT_phiC_integrable` — integrability of `φ̂`;
* `rpow_neg_natCast` — the `rpow`/nat-power bridge used by the arithmetic.
-/

noncomputable section

open MeasureTheory Filter Metric
open scoped Real Topology BigOperators FourierTransform SchwartzMap

namespace Work.BoseFixB3.Conv

open Work.BoseFixB3.Scaling

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ### 1. Fourier inversion for the profile `φ = χ²` in the `p`-convention -/

/-- The complex Fourier inversion in the corpus's `p`-convention: for the profile `φ = χ²`,

`(2π)⁻³ ∫_p e^{i⟪p,x⟫} φ̂(p) dp = φ(x)`. -/
lemma kinInv_kinFT_phiC (x : E3) :
    ((((2 * π) ^ 3)⁻¹ : ℝ) : ℂ) *
        ∫ p : E3, Complex.exp (Complex.I * (inner ℝ p x : ℂ)) *
          Submission.BoseGases.kinFT phiC p
      = (phi x : ℂ) := by
  have hpi : (0:ℝ) < 2*π := by positivity
  have hne : (2*π : ℝ) ≠ 0 := ne_of_gt hpi
  have hfin : Module.finrank ℝ E3 = 3 := by simp [EuclideanSpace]
  set F : E3 → ℂ := fun ξ => Complex.exp (Complex.I * (inner ℝ ((2*π) • ξ) x : ℂ)) *
    (𝓕 phiSch) ξ with hF
  have h1 : (∫ p : E3, Complex.exp (Complex.I * (inner ℝ p x : ℂ)) *
        Submission.BoseGases.kinFT phiC p) = ∫ p : E3, F ((2*π)⁻¹ • p) := by
    apply integral_congr_ae
    filter_upwards with p
    rw [hF]
    simp only
    rw [kinFT_phiC_fourier, smul_inv_smul₀ hne p]
  have h2 : (∫ p : E3, F ((2*π)⁻¹ • p)) = (↑(2*π) : ℂ)^3 * ∫ ξ : E3, F ξ := by
    have hsub := Measure.integral_comp_inv_smul_of_nonneg volume F hpi.le
    rw [hfin] at hsub
    rw [hsub, Complex.real_smul, Complex.ofReal_pow]
  have h3 : (∫ ξ : E3, F ξ) = (phi x : ℂ) := by
    have hco : (∫ ξ : E3, F ξ) = 𝓕⁻ ((𝓕 phiSch : 𝓢(E3, ℂ)) : E3 → ℂ) x := by
      rw [Real.fourierInv_eq]
      apply integral_congr_ae
      filter_upwards with ξ
      rw [hF]
      simp only
      rw [Circle.smul_def]
      congr 1
      rw [Real.fourierChar_apply, real_inner_smul_left]
      push_cast
      ring_nf
    rw [hco, ← SchwartzMap.fourierInv_coe (𝓕 phiSch), FourierTransform.fourierInv_fourier_eq]
    rw [phiSch_apply]; rfl
  rw [h1, h2, h3]
  have h3ne : (↑(2*π) : ℂ)^3 ≠ 0 :=
    pow_ne_zero 3 (by rw [Complex.ofReal_ne_zero]; exact hne)
  rw [← mul_assoc, Complex.ofReal_inv, Complex.ofReal_pow, inv_mul_cancel₀ h3ne, one_mul]

/-! ### 2. Schwartz decay of `φ̂` -/

/-- A Schwartz function decays like `(1 + ‖ξ‖)^{-k}`: elementary consequence of the two
seminorms `k = 0` and `k`. -/
lemma schwartz_norm_mul_pow_le (f : 𝓢(E3, ℂ)) (k : ℕ) (ξ : E3) :
    ‖f ξ‖ * (1 + ‖ξ‖)^k
      ≤ 2^k * max ((SchwartzMap.seminorm ℂ 0 0) f) ((SchwartzMap.seminorm ℂ k 0) f) := by
  have hS0 : 0 ≤ (SchwartzMap.seminorm ℂ 0 0) f := by positivity
  rcases lt_or_ge ‖ξ‖ 1 with h | h
  · have h1 : (1 + ‖ξ‖)^k ≤ 2^k := by
      apply pow_le_pow_left₀ (by positivity)
      linarith
    have h2 := SchwartzMap.norm_le_seminorm ℂ f ξ
    calc ‖f ξ‖ * (1+‖ξ‖)^k ≤ (SchwartzMap.seminorm ℂ 0 0) f * 2^k :=
          mul_le_mul h2 h1 (by positivity) hS0
      _ ≤ max ((SchwartzMap.seminorm ℂ 0 0) f) ((SchwartzMap.seminorm ℂ k 0) f) * 2^k :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ = 2^k * max ((SchwartzMap.seminorm ℂ 0 0) f) ((SchwartzMap.seminorm ℂ k 0) f) := by ring
  · have h1 : (1 + ‖ξ‖)^k ≤ 2^k * ‖ξ‖^k := by
      have h2 : 1 + ‖ξ‖ ≤ 2 * ‖ξ‖ := by linarith
      calc (1+‖ξ‖)^k ≤ (2*‖ξ‖)^k := pow_le_pow_left₀ (by positivity) h2 k
        _ = 2^k * ‖ξ‖^k := by rw [mul_pow]
    have h3 := SchwartzMap.norm_pow_mul_le_seminorm ℂ f k ξ
    calc ‖f ξ‖ * (1+‖ξ‖)^k ≤ ‖f ξ‖ * (2^k * ‖ξ‖^k) :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = 2^k * (‖ξ‖^k * ‖f ξ‖) := by ring
      _ ≤ 2^k * (SchwartzMap.seminorm ℂ k 0) f := mul_le_mul_of_nonneg_left h3 (by positivity)
      _ ≤ 2^k * max ((SchwartzMap.seminorm ℂ 0 0) f) ((SchwartzMap.seminorm ℂ k 0) f) :=
          mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity)

/-- `x ^ (-(n:ℝ)) = (x^n)⁻¹` for `x ≥ 0`. -/
lemma rpow_neg_natCast (x : ℝ) (hx : 0 ≤ x) (n : ℕ) :
    x ^ (-(n:ℝ)) = (x^n)⁻¹ := by
  rw [Real.rpow_neg hx]
  exact congrArg Inv.inv (Real.rpow_natCast x n)

/-- `φ̂` decays like `(1 + ‖q‖)^{-44}`. -/
lemma kinFT_phiC_decay :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : E3,
      ‖Submission.BoseGases.kinFT phiC q‖ ≤ C * (1 + ‖q‖) ^ (-(44:ℝ)) := by
  refine ⟨2^44 * max ((SchwartzMap.seminorm ℂ 0 0) (𝓕 phiSch))
      ((SchwartzMap.seminorm ℂ 44 0) (𝓕 phiSch)) * (2*π)^44, by positivity, ?_⟩
  intro q
  set B : ℝ := 2^44 * max ((SchwartzMap.seminorm ℂ 0 0) (𝓕 phiSch))
    ((SchwartzMap.seminorm ℂ 44 0) (𝓕 phiSch)) with hB
  have hpi : (0:ℝ) < 2*π := by positivity
  have hdec := schwartz_norm_mul_pow_le (𝓕 phiSch) 44 ((2*π)⁻¹ • q)
  have hnorm : ‖(2*π)⁻¹ • q‖ = (2*π)⁻¹ * ‖q‖ := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
  have hkey : (1 + ‖q‖)^44 ≤ (2*π)^44 * (1 + ‖(2*π)⁻¹ • q‖)^44 := by
    have h1 : 1 + ‖q‖ ≤ 2*π * (1 + ‖(2*π)⁻¹ • q‖) := by
      rw [hnorm]
      have h2 : 2*π * (1 + (2*π)⁻¹ * ‖q‖) = 2*π + ‖q‖ := by
        rw [mul_add, mul_one, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hpi), one_mul]
      rw [h2]
      linarith [Real.pi_gt_three]
    calc (1+‖q‖)^44 ≤ (2*π * (1 + ‖(2*π)⁻¹ • q‖))^44 := pow_le_pow_left₀ (by positivity) h1 44
      _ = (2*π)^44 * (1 + ‖(2*π)⁻¹ • q‖)^44 := by rw [mul_pow]
  have hrpow : (1 + ‖q‖) ^ (-(44:ℝ)) = ((1+‖q‖)^44)⁻¹ := rpow_neg_natCast _ (by positivity) 44
  rw [kinFT_phiC_fourier, hrpow, le_mul_inv_iff₀ (by positivity : (0:ℝ) < (1+‖q‖)^44)]
  calc ‖(FourierTransform.fourier phiSch) ((2*π)⁻¹ • q)‖ * (1 + ‖q‖)^44
      ≤ ‖(FourierTransform.fourier phiSch) ((2*π)⁻¹ • q)‖ *
          ((2*π)^44 * (1 + ‖(2*π)⁻¹ • q‖)^44) :=
        mul_le_mul_of_nonneg_left hkey (norm_nonneg _)
      _ = (2*π)^44 * (‖(FourierTransform.fourier phiSch) ((2*π)⁻¹ • q)‖ *
            (1 + ‖(2*π)⁻¹ • q‖)^44) := by ring
      _ ≤ (2*π)^44 * B := mul_le_mul_of_nonneg_left (by simpa [hB] using hdec) (by positivity)
      _ = 2^44 * max ((SchwartzMap.seminorm ℂ 0 0) (𝓕 phiSch))
            ((SchwartzMap.seminorm ℂ 44 0) (𝓕 phiSch)) * (2*π)^44 := by rw [hB]; ring

/-- `φ̂` is continuous (it is the Fourier transform of a Schwartz function). -/
lemma continuous_kinFT_phiC : Continuous (Submission.BoseGases.kinFT phiC) := by
  have hfun : Submission.BoseGases.kinFT phiC
      = fun q : E3 => (FourierTransform.fourier phiSch : E3 → ℂ) ((2*π)⁻¹ • q) := by
    funext q; rw [kinFT_phiC_fourier]
  rw [hfun]
  have hc : Continuous fun q : E3 => (2*π)⁻¹ • q := by fun_prop
  exact (SchwartzMap.continuous (𝓕 phiSch)).comp hc

/-- `φ̂` is integrable. -/
lemma kinFT_phiC_integrable : Integrable (Submission.BoseGases.kinFT phiC) := by
  obtain ⟨C, hC, hdec⟩ := kinFT_phiC_decay
  have hg : Integrable (fun q : E3 => C * (1 + ‖q‖) ^ (-(44:ℝ))) :=
    (integrable_one_add_norm (E := E3) (by simp [EuclideanSpace]; norm_num)).const_mul C
  refine hg.mono' continuous_kinFT_phiC.aestronglyMeasurable (Eventually.of_forall fun q => ?_)
  simpa using hdec q

end Work.BoseFixB3.Conv
