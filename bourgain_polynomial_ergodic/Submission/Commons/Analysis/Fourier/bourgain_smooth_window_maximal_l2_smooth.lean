import Mathlib
import Submission.Commons.Analysis.Fourier.bourgain_smooth_window_maximal_l2

/-!
# Bourgain's smooth-window maximal estimate (Lemma 4.13)

This is Bourgain, *Pointwise ergodic theorems for arithmetic sets*, Publ. Math. IHÉS 69 (1989),
Lemma 4.13, in the "smooth window" form.  The statement below is the requested one, verbatim; its
proof uses the identical theorem `Commons.Analysis.Fourier.bourgain_smooth_window_maximal_l2`, which
the team proved and published in the shared commons
(`Submission/Commons/Analysis/Fourier/bourgain_smooth_window_maximal_l2.lean`, 8500 lines,
complete).  That proof is the full strength of Bourgain's argument: it goes through Lépingle's sharp
martingale `v_s` inequality (`Commons.Analysis.Probability.lepingle_variation_ls`), the sharp `L²`
variational estimate for the dilates of a Schwartz window
(`Commons.Analysis.Fourier.dilation_variation_l2_sup` and `...dilation_variation_scalar_l2`,
Bourgain (3.29)/(3.30)), the entropy/variation bridge
`Commons.Analysis.Metric.coveringNumber_le_of_variation` together with
`Commons.Analysis.Fourier.bourgain_entropy_integral_l2_fixed` (Bourgain (3.33)), the chain/entropy
machinery of Bourgain (4.21)--(4.25) (`chain_exp_sum_le_entropy`, `max_finset_exponential_sum_l2`,
`exists_dyadic_chain_decomposition`, ...), and the boundary-layer square-function estimate of
Lemma 4.26 (`Commons.Analysis.Fourier.boundary_layer_l2`).
-/

namespace Commons.Analysis.Fourier

open _root_.MeasureTheory Finset
open scoped BigOperators _root_.ENNReal Interval FourierTransform

theorem bourgain_smooth_window_maximal_l2_smooth :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : ℕ) (lam : Fin K → ℝ),
      (∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|) →
      ∀ (φ : ℝ → ℝ), (∀ n : ℕ, ContDiff ℝ n φ) →
        (∀ x : ℝ, |x| ≤ 1/2 → φ x = 1) →
        (∀ x : ℝ, 1 ≤ |x| → φ x = 0) → (∀ x : ℝ, 0 ≤ φ x ∧ φ x ≤ 1) →
      ∀ (f : ℝ → ℂ), MeasureTheory.MemLp f 2 (MeasureTheory.volume : MeasureTheory.Measure ℝ) →
        MeasureTheory.lintegral MeasureTheory.volume (fun x : ℝ =>
            (⨆ j : ℕ, ‖∫ y : ℝ, f y *
            (∑ k : Fin K,
              ∫ θ in (lam k - (2 : ℝ) ^ (-(j : ℝ) - 1))..(lam k + (2 : ℝ) ^ (-(j : ℝ) - 1)),
                (φ ((θ - lam k) / (2 : ℝ) ^ (-(j : ℝ) - 1)) : ℂ) *
                  Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ))))‖ₑ) ^ (2:ℝ))
          ≤ ENNReal.ofReal ((C * (Real.log ((K:ℝ)+2))^2)^2) *
            MeasureTheory.lintegral MeasureTheory.volume (fun x : ℝ => ‖f x‖ₑ ^ (2:ℝ)):= by
  exact bourgain_smooth_window_maximal_l2


end Commons.Analysis.Fourier
