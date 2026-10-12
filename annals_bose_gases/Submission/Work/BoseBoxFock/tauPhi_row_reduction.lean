import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.KinRowQuant
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.tauPhi_row_reduction` — reducing the kinetic row to the **sharp** row

The assigned node `Work.BoseBoxFock.tauPhi_row_closedBall` asks for

    (T)   Σ_n ℓ⁻³ · c²·tauPhi(‖k_n‖/c) · ‖kinFT g (k_n)‖²  ≤  (2π)⁻³ ∫_p [‖p‖−c]₊² ‖kinFT g p‖²
          (k_n = kmomInt ℓ n, cℓ ≥ 4π, g smooth with tsupport g ⊆ closedBall 0 (ℓ/2)).

`FINDING_tauPhi_row_closedBall.md` shows that the *sharp* row at a *shifted* cutoff,

    (S_λ) Σ_n ℓ⁻³ · [‖k_n‖−λ]₊² · ‖kinFT g (k_n)‖²  ≤  (2π)⁻³ ∫_p [‖p‖−c]₊² ‖kinFT g p‖² ,

for `λ ∈ [5c/4, 7c/4]`, is strictly stronger than `(T)`.  This file makes the reduction formal and
*elementary*:

* `tauPhi_scaled_le_fsKinCoeff` : the **pointwise** bound `c²·tauPhi(r/c) ≤ [r − 5c/4]₊²`
  (`= fsKinCoeff (5c/4) r`), from `tauPhi(r) = ∫ K(t) (r−3/2−t)₊² dt`, `K = tauKer ≥ 0`, `∫K = 1`
  and `supp K ⊆ [−1/4,1/4]` (so `λ_t = c(3/2+t) ≥ 5c/4`, and `(·−λ)₊²` is *decreasing* in `λ`);
* `tauPhi_row_of_sharpShiftRow` : `(T)` follows from `(S_{5c/4})` by the termwise comparison of the
  two `tsum`s (both summand families are nonnegative; the comparison family is summable, which is
  the separate input `Summable` used as a hypothesis here).

The pointwise constant `5c/4` is *sharp*: `tauPhi(r) = 0` for `r ≤ 5/4`, so the bound is an
equality on `r ≤ 5c/4` and asymptotically `c²·tauPhi(r/c) = (r−3c/2)² + c₀c² ≤ (r−5c/4)²` for
`r ≥ 7c/4`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. The pointwise bound -/

/-- **The pointwise bound.**  For `c > 0` and `r ≥ 0`,
`c²·tauPhi(r/c) ≤ (max 0 (r − 5c/4))²`; this is the sharp constant of the profile (`tauPhi`
vanishes on `(−∞, 5/4]`). -/
lemma tauPhi_scaled_le_conv {c r : ℝ} (hc : 0 < c) (hr : 0 ≤ r) :
    c ^ 2 * tauPhi (r / c) ≤ (max 0 (r - 5 * c / 4)) ^ 2 := by
  have hin : tauPhi (r / c) ≤ (max 0 (r / c - 5 / 4)) ^ 2 := by
    have hpt : ∀ t : ℝ,
        tauH (r / c - 3 / 2 - t) * tauKer t ≤ (max 0 (r / c - 5 / 4)) ^ 2 * tauKer t := by
      intro t
      rcases eq_or_ne (tauKer t) 0 with h0 | h0
      · rw [h0, mul_zero, mul_zero]
      · have ht : |t| < 1 / 4 := tauKer_abs_lt t h0
        have h : (r / c - 3 / 2 - t) ≤ (r / c - 5 / 4) := by
          have h1 : -(1 / 4 : ℝ) < t := (abs_lt.mp ht).1
          linarith
        exact mul_le_mul_of_nonneg_right (tauH_mono h) (tauKer_nonneg t)
    have hM : (∫ t, (max 0 (r / c - 5 / 4)) ^ 2 * tauKer t) = (max 0 (r / c - 5 / 4)) ^ 2 := by
      rw [integral_const_mul, tauKer_integral, mul_one]
    rw [tauPhi_eq_integral, ← hM]
    exact integral_mono (tauKer_mul_integrable _ (tauH_continuous.comp (by fun_prop)))
      (tauKer_integrable.const_mul _) hpt
  have hstep : c ^ 2 * (max 0 (r / c - 5 / 4)) ^ 2 = (max 0 (r - 5 * c / 4)) ^ 2 := by
    have h1 : c * (r / c - 5 / 4) = r - 5 * c / 4 := by
      field_simp
    have h2 : c * max 0 (r / c - 5 / 4) = max 0 (r - 5 * c / 4) := by
      rw [mul_max_of_nonneg _ _ (le_of_lt hc), h1, mul_zero]
    rw [← h2, mul_pow]
  exact (mul_le_mul_of_nonneg_left hin (sq_nonneg c)).trans (le_of_eq hstep)

/-- The same bound in the vocabulary of the row: `c²·tauPhi(r/c) ≤ fsKinCoeff (5c/4) r`. -/
lemma tauPhi_scaled_le_fsKinCoeff {c r : ℝ} (hc : 0 < c) (hr : 0 ≤ r) :
    c ^ 2 * tauPhi (r / c) ≤ Submission.BoseGases.fsKinCoeff (5 * c / 4) r := by
  refine (tauPhi_scaled_le_conv hc hr).trans ?_
  rw [Submission.BoseGases.fsKinCoeff, max_comm]

/-! ## 2. The assembly: the sharp row at `5c/4` implies the smoothed row -/

/-- **The reduction.**  If the sharp row holds at the cutoff `5c/4` (with the *same* right-hand
side `(2π)⁻³∫[‖p‖−c]₊²‖ĝ‖²`) and the sharp row's lattice family is summable, then the smoothed row
`(T)` holds.  The proof is the termwise pointwise bound of §1 plus `Summable.tsum_le_tsum`. -/
theorem tauPhi_row_of_sharpShiftRow
    {ℓ c : ℝ} (hℓ : 0 < ℓ) (hc : 0 < c) (hcℓ : 4 * Real.pi ≤ c * ℓ)
    {g : E3 → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g) (hgc : HasCompactSupport g)
    (hgsupp : tsupport g ⊆ Metric.closedBall 0 (ℓ / 2))
    (hSumm : Summable (fun n : Fin 3 → ℤ =>
      (ℓ ^ 3)⁻¹ * Submission.BoseGases.fsKinCoeff (5 * c / 4) ‖kmomInt ℓ n‖ *
        ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2))
    (hSharp : (∑' n : Fin 3 → ℤ,
        (ℓ ^ 3)⁻¹ * Submission.BoseGases.fsKinCoeff (5 * c / 4) ‖kmomInt ℓ n‖ *
          ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2)
      ≤ ((2 * Real.pi) ^ 3)⁻¹ *
        (∫ p : E3,
          Submission.BoseGases.fsKinCoeff c ‖p‖ * ‖Submission.BoseGases.kinFT g p‖ ^ 2)) :
    (∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ *
        (c ^ 2 * tauPhi (‖kmomInt ℓ n‖ / c)) *
        ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2)
      ≤ ((2 * Real.pi) ^ 3)⁻¹ *
        (∫ p : E3,
          Submission.BoseGases.fsKinCoeff c ‖p‖ * ‖Submission.BoseGases.kinFT g p‖ ^ 2) := by
  have hpt : ∀ n : Fin 3 → ℤ,
      (ℓ ^ 3)⁻¹ * (c ^ 2 * tauPhi (‖kmomInt ℓ n‖ / c)) *
          ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2
        ≤ (ℓ ^ 3)⁻¹ * Submission.BoseGases.fsKinCoeff (5 * c / 4) ‖kmomInt ℓ n‖ *
            ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2 := by
    intro n
    have h1 : c ^ 2 * tauPhi (‖kmomInt ℓ n‖ / c)
        ≤ Submission.BoseGases.fsKinCoeff (5 * c / 4) ‖kmomInt ℓ n‖ :=
      tauPhi_scaled_le_fsKinCoeff hc (norm_nonneg _)
    have h2 : (0 : ℝ) ≤ (ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2 :=
      mul_nonneg (by positivity) (by positivity)
    calc (ℓ ^ 3)⁻¹ * (c ^ 2 * tauPhi (‖kmomInt ℓ n‖ / c)) *
          ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2
        = (c ^ 2 * tauPhi (‖kmomInt ℓ n‖ / c)) *
            ((ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2) := by ring
      _ ≤ Submission.BoseGases.fsKinCoeff (5 * c / 4) ‖kmomInt ℓ n‖ *
            ((ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2) :=
          mul_le_mul_of_nonneg_right h1 h2
      _ = (ℓ ^ 3)⁻¹ * Submission.BoseGases.fsKinCoeff (5 * c / 4) ‖kmomInt ℓ n‖ *
            ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2 := by ring
  have hSummW : Summable (fun n : Fin 3 → ℤ =>
      (ℓ ^ 3)⁻¹ * (c ^ 2 * tauPhi (‖kmomInt ℓ n‖ / c)) *
        ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2) := by
    refine Summable.of_nonneg_of_le (fun n => ?_) hpt hSumm
    have hA : (0 : ℝ) ≤ (ℓ ^ 3)⁻¹ := by
      have : (0 : ℝ) < ℓ ^ 3 := by positivity
      positivity
    have hB : (0 : ℝ) ≤ c ^ 2 * tauPhi (‖kmomInt ℓ n‖ / c) :=
      mul_nonneg (sq_nonneg c) (tauPhi_nonneg _)
    have hC : (0 : ℝ) ≤ ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2 := sq_nonneg _
    calc (0 : ℝ) ≤ ((ℓ ^ 3)⁻¹ * (c ^ 2 * tauPhi (‖kmomInt ℓ n‖ / c))) *
          ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2 := mul_nonneg (mul_nonneg hA hB) hC
      _ = (ℓ ^ 3)⁻¹ * (c ^ 2 * tauPhi (‖kmomInt ℓ n‖ / c)) *
          ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2 := rfl
  exact (hSummW.tsum_le_tsum hpt hSumm).trans hSharp

end Work.BoseBoxFock
