import Mathlib
import Submission.Work.GM.Affine.WinMass_fejer_defs
import Submission.Work.GM.Affine.region_II_vocab
import Submission.Work.GM.Affine.fine_setup
import Submission.Work.GM.Affine.setup
import Submission.Work.GM.Affine.WinMass_basic
import Submission.Work.GM.Affine.autocorr_eq_spectral
import Submission.Work.GM.Affine.integral_Bsum_sq_cos
import Submission.Work.GM.Affine.sum_Icc_neg_self

/-!
# The Fejér pairing identity for `Bsum` (GM §9, region II)

The Fejér kernel `fejerK M₃` is a `1`-periodic trigonometric polynomial whose `k`-th cosine
coefficient is `1 - |k|/N` (`N = fejerN M₃`).  Since `Bsum f M₂ = Fhat (Hprof f M₂)` is the
Fourier transform of the real profile `Hprof f M₂`, Wiener–Khinchin
(`autocorr_eq_spectral`) identifies the `k`-th Fourier coefficient of `‖Bsum f M₂‖²` with the
autocorrelation `∫ v, Hprof f M₂ v * Hprof f M₂ (v + k)`.  Summing against the Fejér
coefficients gives the stated pairing identity.
-/

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

set_option autoImplicit false

namespace Work.GM.Affine

noncomputable section

/-- The Fejér kernel written as a symmetric trigonometric sum over `ℤ`:
`fejerK M₃ x = Σ_{k=-(N-1)}^{N-1} (1 - |k|/N) cos (2π k x)`, `N = fejerN M₃`. -/
lemma fejerK_eq_sum_over_symm_range (M₃ x : ℝ) :
    fejerK M₃ x = ∑ k ∈ Finset.Icc (-((fejerN M₃ : ℤ) - 1)) ((fejerN M₃ : ℤ) - 1),
        (1 - |(k : ℝ)| / (fejerN M₃)) * Real.cos (2 * Real.pi * (k : ℝ) * x) := by
  have hN : 1 ≤ fejerN M₃ := fejerN_pos M₃
  set A : ℤ → ℝ := fun k => (1 - |(k : ℝ)| / (fejerN M₃)) * Real.cos (2 * Real.pi * (k : ℝ) * x)
    with hA
  have hAeven : ∀ k : ℤ, A (-k) = A k := by
    intro k
    simp only [hA]
    have h1 : (((-k : ℤ)) : ℝ) = -((k : ℝ)) := by push_cast; ring
    rw [h1, show (2 : ℝ) * Real.pi * (-(k : ℝ)) * x = -(2 * Real.pi * (k : ℝ) * x) by ring,
      Real.cos_neg, abs_neg]
  have hcast : ((fejerN M₃ : ℤ) - 1) = ((fejerN M₃ - 1 : ℕ) : ℤ) := (Nat.cast_sub hN).symm
  have hK : (∑ k ∈ Finset.Icc (-((fejerN M₃ : ℤ) - 1)) ((fejerN M₃ : ℤ) - 1), A k)
      = A 0 + 2 * ∑ k ∈ Finset.Icc 1 (fejerN M₃ - 1), A (k : ℤ) := by
    rw [hcast]
    exact sum_Icc_neg_self (fejerN M₃ - 1) A hAeven
  rw [hK]
  have hA0 : A 0 = 1 := by simp [hA]
  have hAk : ∀ k : ℕ,
      A (k : ℤ) = (1 - (k : ℝ) / (fejerN M₃)) * Real.cos (2 * Real.pi * (k : ℝ) * x) := by
    intro k
    simp only [hA]
    have h1 : (((k : ℤ)) : ℝ) = (k : ℝ) := by push_cast; ring
    rw [h1, abs_of_nonneg (Nat.cast_nonneg k)]
  rw [hA0, Finset.sum_congr rfl (fun k _ => hAk k)]
  unfold fejerK
  rfl

theorem fejerK_pairing {C₀ : ℝ} (hC₀ : 1 ≤ C₀) :
    ∀ f : ℝ → ℝ, Continuous f → (∀ u, 0 ≤ f u) → SuppHyp C₀ f →
      ∀ M₂ : ℝ, 0 ≤ M₂ → ∀ M₃ : ℝ, 1 ≤ M₃ →
        (∫ x : ℝ, ‖Bsum f M₂ x‖ ^ 2 * fejerK M₃ x)
          = ∑ k ∈ Finset.Icc (-((fejerN M₃ : ℤ) - 1)) ((fejerN M₃ : ℤ) - 1),
              (1 - |(k : ℝ)| / (fejerN M₃)) *
                ∫ v : ℝ, Hprof f M₂ v * Hprof f M₂ (v + (k : ℝ)) := by
  intro f hf hfnn hsup M₂ hM₂ M₃ hM₃
  rcases eq_or_lt_of_le hM₂ with hM₂0 | hM₂pos
  · -- degenerate case `M₂ = 0`: both `R2 0`, hence `Bsum` and `Hprof`, vanish identically
    subst hM₂0
    have hR2 : R2 (0 : ℝ) = ∅ := by
      unfold R2
      norm_num
    simp [Bsum, Hprof, hR2]
  · -- main case `M₂ > 0`
    have hHc : Continuous (Hprof f M₂) := Hprof_continuous hf M₂
    have hHcs : HasCompactSupport (Hprof f M₂) := Hprof_hasCompactSupport hsup hC₀ hM₂pos.le
    have hIntF : Integrable (fun x : ℝ => ‖Fhat (Hprof f M₂) x‖ ^ 2) :=
      integrable_Fhat_sq hHc hHcs
    have hIntB : Integrable (fun x : ℝ => ‖Bsum f M₂ x‖ ^ 2) :=
      hIntF.congr (Filter.Eventually.of_forall (fun x => by
        show ‖Fhat (Hprof f M₂) x‖ ^ 2 = ‖Bsum f M₂ x‖ ^ 2
        rw [Bsum_eq_Fhat_Hprof hf hsup hC₀ hM₂pos x]))
    set A : ℤ → ℝ := fun k => ∫ v : ℝ, Hprof f M₂ v * Hprof f M₂ (v + (k : ℝ)) with hA
    -- each term of the Fejér sum is integrable
    have hIntCos : ∀ k : ℤ,
        Integrable (fun x : ℝ => ‖Bsum f M₂ x‖ ^ 2 * Real.cos (2 * Real.pi * (k : ℝ) * x)) := by
      intro k
      refine Integrable.mono' hIntB ?_ ?_
      · exact hIntB.aestronglyMeasurable.mul
          ((Real.continuous_cos.comp (by fun_prop : Continuous
            fun x : ℝ => 2 * Real.pi * (k : ℝ) * x)).aestronglyMeasurable)
      · filter_upwards with x
        calc ‖‖Bsum f M₂ x‖ ^ 2 * Real.cos (2 * Real.pi * (k : ℝ) * x)‖
            = ‖Bsum f M₂ x‖ ^ 2 * |Real.cos (2 * Real.pi * (k : ℝ) * x)| := by
              rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _)]
          _ ≤ ‖Bsum f M₂ x‖ ^ 2 * 1 :=
              mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (sq_nonneg _)
          _ = ‖Bsum f M₂ x‖ ^ 2 := by ring
    have hIntTerm : ∀ k : ℤ, Integrable (fun x : ℝ =>
        ‖Bsum f M₂ x‖ ^ 2 *
          ((1 - |(k : ℝ)| / (fejerN M₃)) * Real.cos (2 * Real.pi * (k : ℝ) * x))) := by
      intro k
      refine ((hIntCos k).const_mul (1 - |(k : ℝ)| / (fejerN M₃))).congr
        (Filter.Eventually.of_forall (fun x => by ring))
    have hL2 : (∫ x : ℝ, ∑ k ∈ Finset.Icc (-((fejerN M₃ : ℤ) - 1)) ((fejerN M₃ : ℤ) - 1),
          ‖Bsum f M₂ x‖ ^ 2 *
            ((1 - |(k : ℝ)| / (fejerN M₃)) * Real.cos (2 * Real.pi * (k : ℝ) * x)))
        = ∑ k ∈ Finset.Icc (-((fejerN M₃ : ℤ) - 1)) ((fejerN M₃ : ℤ) - 1),
            ∫ x : ℝ, ‖Bsum f M₂ x‖ ^ 2 *
              ((1 - |(k : ℝ)| / (fejerN M₃)) * Real.cos (2 * Real.pi * (k : ℝ) * x)) :=
      integral_finsetSum _ (fun k _ => hIntTerm k)
    -- the `k`-th Fourier coefficient of `‖Bsum‖²` is the autocorrelation of `Hprof`
    have hTerm : ∀ k ∈ Finset.Icc (-((fejerN M₃ : ℤ) - 1)) ((fejerN M₃ : ℤ) - 1),
        (∫ x : ℝ, ‖Bsum f M₂ x‖ ^ 2 *
            ((1 - |(k : ℝ)| / (fejerN M₃)) * Real.cos (2 * Real.pi * (k : ℝ) * x)))
          = (1 - |(k : ℝ)| / (fejerN M₃)) * A k := by
      intro k _
      rw [show (∫ x : ℝ, ‖Bsum f M₂ x‖ ^ 2 *
              ((1 - |(k : ℝ)| / (fejerN M₃)) * Real.cos (2 * Real.pi * (k : ℝ) * x)))
            = ∫ x : ℝ, (1 - |(k : ℝ)| / (fejerN M₃)) *
                (‖Bsum f M₂ x‖ ^ 2 * Real.cos (2 * Real.pi * (k : ℝ) * x)) from
          integral_congr_ae (Filter.Eventually.of_forall (fun x => by ring))]
      rw [integral_const_mul, integral_Bsum_sq_cos hC₀ hf hsup hM₂pos k]
    have hLHS : (∫ x : ℝ, ‖Bsum f M₂ x‖ ^ 2 * fejerK M₃ x)
        = ∑ k ∈ Finset.Icc (-((fejerN M₃ : ℤ) - 1)) ((fejerN M₃ : ℤ) - 1),
            (1 - |(k : ℝ)| / (fejerN M₃)) * A k := by
      rw [show (∫ x : ℝ, ‖Bsum f M₂ x‖ ^ 2 * fejerK M₃ x)
            = ∫ x : ℝ, ∑ k ∈ Finset.Icc (-((fejerN M₃ : ℤ) - 1)) ((fejerN M₃ : ℤ) - 1),
                ‖Bsum f M₂ x‖ ^ 2 *
                  ((1 - |(k : ℝ)| / (fejerN M₃)) * Real.cos (2 * Real.pi * (k : ℝ) * x)) from
          integral_congr_ae (Filter.Eventually.of_forall (fun x => by
            show ‖Bsum f M₂ x‖ ^ 2 * fejerK M₃ x
                = ∑ k ∈ Finset.Icc (-((fejerN M₃ : ℤ) - 1)) ((fejerN M₃ : ℤ) - 1),
                    ‖Bsum f M₂ x‖ ^ 2 *
                      ((1 - |(k : ℝ)| / (fejerN M₃)) * Real.cos (2 * Real.pi * (k : ℝ) * x))
            rw [fejerK_eq_sum_over_symm_range M₃ x, Finset.mul_sum]))]
      rw [hL2]
      exact Finset.sum_congr rfl hTerm
    rw [hLHS]

end

end Work.GM.Affine
