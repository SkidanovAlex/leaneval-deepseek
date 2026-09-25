import Mathlib
import Submission.Work.CR.Flat.Polydisc

namespace Work.CR.Flat.Cauchy.bmCz

/-- Decompose a complex vector into its real and imaginary components along the
standard coordinate directions, viewed as real basis vectors. -/
private lemma decompose_complex_vector {n : ℕ} (v : Fin n → ℂ) :
    v = ∑ k, ((v k).re • ((Pi.single k (1 : ℂ) : Fin n → ℂ))
        + (v k).im • ((Pi.single k Complex.I : Fin n → ℂ))) := by
  funext j
  rw [Finset.sum_apply]
  rw [Finset.sum_eq_single j]
  · simp [Complex.real_smul]
  · intro k _ hk
    simp [Pi.single_eq_of_ne (Ne.symm hk)]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

/-- The difference of the real differentials decomposes along the real basis
`{e_k, i e_k}` with Wirtinger-derivative coefficients. -/
private lemma fderiv_sub_eq_sum_wirtinger {n : ℕ} (u : (Fin n → ℂ) → ℂ) (z z' v : Fin n → ℂ) :
    (fderiv ℝ u z - fderiv ℝ u z') v
      = ∑ k, ((v k).re * ((fderiv ℝ u z - fderiv ℝ u z') (Pi.single k (1 : ℂ)))
          + (v k).im * ((fderiv ℝ u z - fderiv ℝ u z') (Pi.single k Complex.I))) := by
  conv_lhs => rw [decompose_complex_vector v]
  rw [map_sum]
  simp only [map_add, map_smul, Complex.real_smul]

theorem norm_fderiv_sub_le_sum_wirtinger {n : ℕ} (u : (Fin n → ℂ) → ℂ) (z z' : Fin n → ℂ) :
    ‖fderiv ℝ u z - fderiv ℝ u z'‖
      ≤ 2 * ∑ k, (‖Work.CR.Flat.dCoord k u z - Work.CR.Flat.dCoord k u z'‖
          + ‖Work.CR.Flat.dbarCoord k u z - Work.CR.Flat.dbarCoord k u z'‖) := by
  set S : ℝ := ∑ k, (‖Work.CR.Flat.dCoord k u z - Work.CR.Flat.dCoord k u z'‖
          + ‖Work.CR.Flat.dbarCoord k u z - Work.CR.Flat.dbarCoord k u z'‖) with hS
  have key : ∀ v : Fin n → ℂ, ‖(fderiv ℝ u z - fderiv ℝ u z') v‖ ≤ (2 * S) * ‖v‖ := by
    intro v
    -- The pairing of the two basis vectors in the `k`-th coordinate direction
    -- is controlled by the Wirtinger derivative differences.
    have hc : ∀ k, ‖(fderiv ℝ u z - fderiv ℝ u z') (Pi.single k (1 : ℂ))‖
        ≤ ‖Work.CR.Flat.dCoord k u z - Work.CR.Flat.dCoord k u z'‖
          + ‖Work.CR.Flat.dbarCoord k u z - Work.CR.Flat.dbarCoord k u z'‖ := by
      intro k
      have h1 : fderiv ℝ u z (Pi.single k (1 : ℂ))
          = Work.CR.Flat.dCoord k u z + Work.CR.Flat.dbarCoord k u z := by
        rw [Work.CR.Flat.dCoord, Work.CR.Flat.dbarCoord]; ring
      have h2 : fderiv ℝ u z' (Pi.single k (1 : ℂ))
          = Work.CR.Flat.dCoord k u z' + Work.CR.Flat.dbarCoord k u z' := by
        rw [Work.CR.Flat.dCoord, Work.CR.Flat.dbarCoord]; ring
      rw [sub_apply, h1, h2]
      rw [show (Work.CR.Flat.dCoord k u z + Work.CR.Flat.dbarCoord k u z)
              - (Work.CR.Flat.dCoord k u z' + Work.CR.Flat.dbarCoord k u z')
            = (Work.CR.Flat.dCoord k u z - Work.CR.Flat.dCoord k u z')
              + (Work.CR.Flat.dbarCoord k u z - Work.CR.Flat.dbarCoord k u z') by ring]
      exact norm_add_le _ _
    have hcI : ∀ k, ‖(fderiv ℝ u z - fderiv ℝ u z') (Pi.single k Complex.I)‖
        ≤ ‖Work.CR.Flat.dCoord k u z - Work.CR.Flat.dCoord k u z'‖
          + ‖Work.CR.Flat.dbarCoord k u z - Work.CR.Flat.dbarCoord k u z'‖ := by
      intro k
      have h1 : fderiv ℝ u z (Pi.single k Complex.I)
          = Complex.I * (Work.CR.Flat.dCoord k u z - Work.CR.Flat.dbarCoord k u z) := by
        rw [Work.CR.Flat.dCoord, Work.CR.Flat.dbarCoord]
        rw [show (1 / 2 : ℂ) * (fderiv ℝ u z (Pi.single k (1 : ℂ))
                - Complex.I * fderiv ℝ u z (Pi.single k Complex.I))
              - (1 / 2 : ℂ) * (fderiv ℝ u z (Pi.single k (1 : ℂ))
                + Complex.I * fderiv ℝ u z (Pi.single k Complex.I))
            = -(Complex.I * fderiv ℝ u z (Pi.single k Complex.I)) by ring]
        rw [mul_neg, ← mul_assoc, Complex.I_mul_I]
        ring
      have h2 : fderiv ℝ u z' (Pi.single k Complex.I)
          = Complex.I * (Work.CR.Flat.dCoord k u z' - Work.CR.Flat.dbarCoord k u z') := by
        rw [Work.CR.Flat.dCoord, Work.CR.Flat.dbarCoord]
        rw [show (1 / 2 : ℂ) * (fderiv ℝ u z' (Pi.single k (1 : ℂ))
                - Complex.I * fderiv ℝ u z' (Pi.single k Complex.I))
              - (1 / 2 : ℂ) * (fderiv ℝ u z' (Pi.single k (1 : ℂ))
                + Complex.I * fderiv ℝ u z' (Pi.single k Complex.I))
            = -(Complex.I * fderiv ℝ u z' (Pi.single k Complex.I)) by ring]
        rw [mul_neg, ← mul_assoc, Complex.I_mul_I]
        ring
      rw [sub_apply, h1, h2]
      rw [show Complex.I * (Work.CR.Flat.dCoord k u z - Work.CR.Flat.dbarCoord k u z)
            - Complex.I * (Work.CR.Flat.dCoord k u z' - Work.CR.Flat.dbarCoord k u z')
          = Complex.I * ((Work.CR.Flat.dCoord k u z - Work.CR.Flat.dCoord k u z')
              - (Work.CR.Flat.dbarCoord k u z - Work.CR.Flat.dbarCoord k u z')) by ring]
      rw [norm_mul, Complex.norm_I, one_mul]
      exact norm_sub_le _ _
    rw [fderiv_sub_eq_sum_wirtinger u z z' v]
    have hterm : ∀ k, ‖(v k).re * ((fderiv ℝ u z - fderiv ℝ u z') (Pi.single k (1 : ℂ)))
          + (v k).im * ((fderiv ℝ u z - fderiv ℝ u z') (Pi.single k Complex.I))‖
        ≤ ‖v‖ * (2 * (‖Work.CR.Flat.dCoord k u z - Work.CR.Flat.dCoord k u z'‖
          + ‖Work.CR.Flat.dbarCoord k u z - Work.CR.Flat.dbarCoord k u z'‖)) := by
      intro k
      have hre : |(v k).re| ≤ ‖v‖ :=
        le_trans (Complex.abs_re_le_norm (v k)) (norm_le_pi_norm v k)
      have him : |(v k).im| ≤ ‖v‖ :=
        le_trans (Complex.abs_im_le_norm (v k)) (norm_le_pi_norm v k)
      have h1 : |(v k).re| * ‖(fderiv ℝ u z - fderiv ℝ u z') (Pi.single k (1 : ℂ))‖
          ≤ ‖v‖ * (‖Work.CR.Flat.dCoord k u z - Work.CR.Flat.dCoord k u z'‖
              + ‖Work.CR.Flat.dbarCoord k u z - Work.CR.Flat.dbarCoord k u z'‖) :=
        mul_le_mul hre (hc k) (norm_nonneg _) (norm_nonneg v)
      have h2 : |(v k).im| * ‖(fderiv ℝ u z - fderiv ℝ u z') (Pi.single k Complex.I)‖
          ≤ ‖v‖ * (‖Work.CR.Flat.dCoord k u z - Work.CR.Flat.dCoord k u z'‖
              + ‖Work.CR.Flat.dbarCoord k u z - Work.CR.Flat.dbarCoord k u z'‖) :=
        mul_le_mul him (hcI k) (norm_nonneg _) (norm_nonneg v)
      calc ‖(v k).re * ((fderiv ℝ u z - fderiv ℝ u z') (Pi.single k (1 : ℂ)))
              + (v k).im * ((fderiv ℝ u z - fderiv ℝ u z') (Pi.single k Complex.I))‖
          ≤ ‖(v k).re * ((fderiv ℝ u z - fderiv ℝ u z') (Pi.single k (1 : ℂ)))‖
              + ‖(v k).im * ((fderiv ℝ u z - fderiv ℝ u z') (Pi.single k Complex.I))‖ :=
              norm_add_le _ _
        _ = |(v k).re| * ‖(fderiv ℝ u z - fderiv ℝ u z') (Pi.single k (1 : ℂ))‖
              + |(v k).im| * ‖(fderiv ℝ u z - fderiv ℝ u z') (Pi.single k Complex.I)‖ := by
              simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        _ ≤ ‖v‖ * (‖Work.CR.Flat.dCoord k u z - Work.CR.Flat.dCoord k u z'‖
                + ‖Work.CR.Flat.dbarCoord k u z - Work.CR.Flat.dbarCoord k u z'‖)
              + ‖v‖ * (‖Work.CR.Flat.dCoord k u z - Work.CR.Flat.dCoord k u z'‖
                + ‖Work.CR.Flat.dbarCoord k u z - Work.CR.Flat.dbarCoord k u z'‖) :=
              add_le_add h1 h2
        _ = ‖v‖ * (2 * (‖Work.CR.Flat.dCoord k u z - Work.CR.Flat.dCoord k u z'‖
                + ‖Work.CR.Flat.dbarCoord k u z - Work.CR.Flat.dbarCoord k u z'‖)) := by
              ring
    have hsum : ∑ k, ‖(v k).re * ((fderiv ℝ u z - fderiv ℝ u z') (Pi.single k (1 : ℂ)))
            + (v k).im * ((fderiv ℝ u z - fderiv ℝ u z') (Pi.single k Complex.I))‖
        ≤ ∑ k, ‖v‖ * (2 * (‖Work.CR.Flat.dCoord k u z - Work.CR.Flat.dCoord k u z'‖
                + ‖Work.CR.Flat.dbarCoord k u z - Work.CR.Flat.dbarCoord k u z'‖)) :=
      Finset.sum_le_sum fun k _ => hterm k
    have heq : ∑ k, ‖v‖ * (2 * (‖Work.CR.Flat.dCoord k u z - Work.CR.Flat.dCoord k u z'‖
              + ‖Work.CR.Flat.dbarCoord k u z - Work.CR.Flat.dbarCoord k u z'‖))
        = (2 * S) * ‖v‖ := by
      rw [hS, ← Finset.mul_sum, ← Finset.mul_sum]; ring
    exact le_trans (le_trans (norm_sum_le Finset.univ _) hsum) (le_of_eq heq)
  have hM : (0 : ℝ) ≤ 2 * S := by rw [hS]; positivity
  exact ContinuousLinearMap.opNorm_le_bound _ hM key

end Work.CR.Flat.Cauchy.bmCz
