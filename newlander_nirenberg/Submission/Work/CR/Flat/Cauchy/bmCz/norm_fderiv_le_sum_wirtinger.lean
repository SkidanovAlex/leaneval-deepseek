import Mathlib
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.CR.Flat.Cauchy.bmCz.fderiv_eq_sum_wirtinger

namespace Work.CR.Flat.Cauchy.bmCz

theorem norm_fderiv_le_sum_wirtinger {n : ℕ} (u : (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) :
    ‖fderiv ℝ u z‖
      ≤ 2 * ∑ k, (‖Work.CR.Flat.dCoord k u z‖ + ‖Work.CR.Flat.dbarCoord k u z‖) := by
  set S : ℝ := ∑ k, (‖Work.CR.Flat.dCoord k u z‖ + ‖Work.CR.Flat.dbarCoord k u z‖) with hS
  have key : ∀ v : Fin n → ℂ, ‖fderiv ℝ u z v‖ ≤ (2 * S) * ‖v‖ := by
    intro v
    -- The pairing of the two basis vectors in the `k`-th coordinate direction
    -- is controlled by the Wirtinger derivatives.
    have hc : ∀ k, ‖fderiv ℝ u z (Pi.single k (1 : ℂ))‖
        ≤ ‖Work.CR.Flat.dCoord k u z‖ + ‖Work.CR.Flat.dbarCoord k u z‖ := by
      intro k
      have h : fderiv ℝ u z (Pi.single k (1 : ℂ))
          = Work.CR.Flat.dCoord k u z + Work.CR.Flat.dbarCoord k u z := by
        rw [Work.CR.Flat.dCoord, Work.CR.Flat.dbarCoord]; ring
      rw [h]; exact norm_add_le _ _
    have hcI : ∀ k, ‖fderiv ℝ u z (Pi.single k Complex.I)‖
        ≤ ‖Work.CR.Flat.dCoord k u z‖ + ‖Work.CR.Flat.dbarCoord k u z‖ := by
      intro k
      have h : fderiv ℝ u z (Pi.single k Complex.I)
          = Complex.I * (Work.CR.Flat.dCoord k u z - Work.CR.Flat.dbarCoord k u z) := by
        rw [Work.CR.Flat.dCoord, Work.CR.Flat.dbarCoord]
        rw [show (1 / 2 : ℂ) * (fderiv ℝ u z (Pi.single k (1 : ℂ))
                - Complex.I * fderiv ℝ u z (Pi.single k Complex.I))
              - (1 / 2 : ℂ) * (fderiv ℝ u z (Pi.single k (1 : ℂ))
                + Complex.I * fderiv ℝ u z (Pi.single k Complex.I))
            = -(Complex.I * fderiv ℝ u z (Pi.single k Complex.I)) by ring]
        rw [mul_neg, ← mul_assoc, Complex.I_mul_I]
        ring
      rw [h, norm_mul, Complex.norm_I, one_mul]
      exact norm_sub_le _ _
    rw [fderiv_eq_sum_wirtinger u z v]
    have hterm : ∀ k, ‖(v k).re * fderiv ℝ u z (Pi.single k (1 : ℂ))
          + (v k).im * fderiv ℝ u z (Pi.single k Complex.I)‖
        ≤ ‖v‖ * (2 * (‖Work.CR.Flat.dCoord k u z‖ + ‖Work.CR.Flat.dbarCoord k u z‖)) := by
      intro k
      have hre : |(v k).re| ≤ ‖v‖ :=
        le_trans (Complex.abs_re_le_norm (v k)) (norm_le_pi_norm v k)
      have him : |(v k).im| ≤ ‖v‖ :=
        le_trans (Complex.abs_im_le_norm (v k)) (norm_le_pi_norm v k)
      have h1 : |(v k).re| * ‖fderiv ℝ u z (Pi.single k (1 : ℂ))‖
          ≤ ‖v‖ * (‖Work.CR.Flat.dCoord k u z‖ + ‖Work.CR.Flat.dbarCoord k u z‖) :=
        mul_le_mul hre (hc k) (norm_nonneg _) (norm_nonneg v)
      have h2 : |(v k).im| * ‖fderiv ℝ u z (Pi.single k Complex.I)‖
          ≤ ‖v‖ * (‖Work.CR.Flat.dCoord k u z‖ + ‖Work.CR.Flat.dbarCoord k u z‖) :=
        mul_le_mul him (hcI k) (norm_nonneg _) (norm_nonneg v)
      calc ‖(v k).re * fderiv ℝ u z (Pi.single k (1 : ℂ))
              + (v k).im * fderiv ℝ u z (Pi.single k Complex.I)‖
          ≤ ‖(v k).re * fderiv ℝ u z (Pi.single k (1 : ℂ))‖
              + ‖(v k).im * fderiv ℝ u z (Pi.single k Complex.I)‖ := norm_add_le _ _
        _ = |(v k).re| * ‖fderiv ℝ u z (Pi.single k (1 : ℂ))‖
              + |(v k).im| * ‖fderiv ℝ u z (Pi.single k Complex.I)‖ := by
              simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        _ ≤ ‖v‖ * (‖Work.CR.Flat.dCoord k u z‖ + ‖Work.CR.Flat.dbarCoord k u z‖)
              + ‖v‖ * (‖Work.CR.Flat.dCoord k u z‖ + ‖Work.CR.Flat.dbarCoord k u z‖) :=
              add_le_add h1 h2
        _ = ‖v‖ * (2 * (‖Work.CR.Flat.dCoord k u z‖ + ‖Work.CR.Flat.dbarCoord k u z‖)) := by
              ring
    have hsum : ∑ k, ‖(v k).re * fderiv ℝ u z (Pi.single k (1 : ℂ))
            + (v k).im * fderiv ℝ u z (Pi.single k Complex.I)‖
        ≤ ∑ k, ‖v‖ * (2 * (‖Work.CR.Flat.dCoord k u z‖ + ‖Work.CR.Flat.dbarCoord k u z‖)) :=
      Finset.sum_le_sum fun k _ => hterm k
    have heq : ∑ k, ‖v‖ * (2 * (‖Work.CR.Flat.dCoord k u z‖ + ‖Work.CR.Flat.dbarCoord k u z‖))
        = (2 * S) * ‖v‖ := by
      rw [hS, ← Finset.mul_sum, ← Finset.mul_sum]; ring
    exact le_trans (le_trans (norm_sum_le Finset.univ _) hsum) (le_of_eq heq)
  have hM : (0 : ℝ) ≤ 2 * S := by rw [hS]; positivity
  exact ContinuousLinearMap.opNorm_le_bound _ hM key

end Work.CR.Flat.Cauchy.bmCz
