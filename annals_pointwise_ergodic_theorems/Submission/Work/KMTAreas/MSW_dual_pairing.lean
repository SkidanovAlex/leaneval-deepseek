import Mathlib
import Submission.Work.KMTAreas.MSW_extremal_mul_conj
import Submission.Work.KMTAreas.MSW_extremal_enorm
import Submission.Work.KMTAreas.MSW_finsupp_eLpNorm
import Submission.Work.KMTAreas.MSW_dual_algebra
import Submission.Work.Analysis.Interpolation.eLpNorm_eq_iSup_simpleFunc_integral
import Submission.Port.Aesm

/-!
# The `ℓ^q` duality pairing bound used in the `MSW` (single-torsion sampling) reduction

`Work.KMTAreas.MSW_dual_pairing` upgrades a bound on the *duality pairing*
`∑_n X n · conj (g n)` against all finitely supported test functions `g` to a bound on the
`ℓ^q` norm of `X` itself.  It is the step that converts the `ℓ^{q'}`-estimate for the
de Leeuw transfer of `MSW_single_torsion` into an `ℓ^q` estimate for `X`.

The proof is the standard "extremal test function" computation, done on finite sets so that
no Bochner-integral theory for the (possibly non-summable) pairing is needed: for a finite
`s : Finset ℤ` one tests with `g n = X n · ‖X n‖^{q-2}` on `s`, for which
`X n · conj (g n) = ‖X n‖^q` and `‖g n‖^{q'} = ‖X n‖^q`.  The hypothesis then gives
`Q ≤ A · Q^{1/q'}` for `Q = ∑_{n∈s} ‖X n‖^q`, whence `Q ≤ A^q` by `MSW_dual_algebra`.
-/

set_option linter.unusedVariables false

open MeasureTheory
open scoped ENNReal NNReal

namespace Work.KMTAreas

theorem MSW_dual_pairing {X : ℤ → ℂ} {A : NNReal} {q : ℝ} (hq : 1 < q)
    (hX : AEMeasurable X MeasureTheory.Measure.count)
    (h : ∀ g : ℤ → ℂ, (Function.support g).Finite →
      enorm (tsum (fun n : ℤ => X n * starRingEnd ℂ (g n)))
        ≤ ENNReal.ofReal (A : ℝ) * MeasureTheory.eLpNorm g (ENNReal.ofReal (q / (q - 1)))
            MeasureTheory.Measure.count) :
    MeasureTheory.eLpNorm X (ENNReal.ofReal q) MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (A : ℝ) := by
  have hq0 : (0 : ℝ) < q := by linarith
  have hq'0 : (0 : ℝ) < q / (q - 1) := by positivity
  have h1q : (0 : ℝ) < 1 / q := by positivity
  have hA0 : (0 : ℝ) ≤ (A : ℝ) := A.coe_nonneg
  rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm)
        (ENNReal.ofReal_ne_zero_iff.mpr hq0) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hq0.le]
  have hmain : (∫⁻ n : ℤ, enorm (X n) ^ q ∂MeasureTheory.Measure.count)
      ≤ (ENNReal.ofReal (A : ℝ)) ^ q := by
    rw [MeasureTheory.lintegral_count, ENNReal.tsum_eq_iSup_sum]
    refine iSup_le fun s => ?_
    set Q : ℝ := ∑ n ∈ s, ‖X n‖ ^ q with hQ
    have hQ0 : 0 ≤ Q := by
      rw [hQ]; exact Finset.sum_nonneg fun n _ => Real.rpow_nonneg (norm_nonneg _) _
    have hP : ENNReal.ofReal Q = ∑ n ∈ s, enorm (X n) ^ q := by
      rw [hQ, ENNReal.ofReal_sum_of_nonneg (fun n _ => Real.rpow_nonneg (norm_nonneg _) _)]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [← ofReal_norm, ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg (X n)) hq0.le]
    set g : ℤ → ℂ := (fun n => if n ∈ s then X n * Complex.ofReal ((‖X n‖ : ℝ) ^ (q - 2))
      else 0) with hg
    have hgsupp : ∀ n ∉ s, g n = 0 := by intro n hn; rw [hg]; simp [hn]
    have hfin : (Function.support g).Finite := by
      refine (Finset.finite_toSet s).subset ?_
      intro n hn
      by_contra hns
      exact (Function.mem_support.mp hn) (hgsupp n hns)
    have hg0 := h g hfin
    have hL : enorm (tsum (fun n : ℤ => X n * starRingEnd ℂ (g n))) = ENNReal.ofReal Q := by
      have hF0 : ∀ n ∉ s, X n * starRingEnd ℂ (g n) = 0 := by
        intro n hn; rw [hgsupp n hn, map_zero, mul_zero]
      rw [tsum_eq_sum hF0]
      have hterm : ∀ n ∈ s, X n * starRingEnd ℂ (g n) = Complex.ofReal (‖X n‖ ^ q) := by
        intro n hn
        rw [hg]
        simp only [hn, if_true]
        exact MSW_extremal_mul_conj hq (X n)
      rw [Finset.sum_congr rfl hterm, ← Complex.ofReal_sum, ← ofReal_norm]
      congr 1
      rw [show ∀ r : ℝ, ‖(r : ℂ)‖ = |r| from RCLike.norm_ofReal, hQ]
      exact abs_of_nonneg (Finset.sum_nonneg fun n _ => Real.rpow_nonneg (norm_nonneg _) _)
    have hR : MeasureTheory.eLpNorm g (ENNReal.ofReal (q / (q - 1))) MeasureTheory.Measure.count
        = ENNReal.ofReal (Q ^ (1 / (q / (q - 1)))) := by
      rw [MSW_finsupp_eLpNorm hgsupp hq'0]
      have hsum : (∑ n ∈ s, enorm (g n) ^ (q / (q - 1))) = ENNReal.ofReal Q := by
        have hterm : ∀ n ∈ s, enorm (g n) ^ (q / (q - 1)) = enorm (X n) ^ q := by
          intro n hn
          rw [hg]
          simp only [hn, if_true]
          exact MSW_extremal_enorm hq (X n)
        rw [Finset.sum_congr rfl hterm, ← hP]
      rw [hsum, ENNReal.ofReal_rpow_of_nonneg hQ0 (by positivity : (0:ℝ) ≤ 1 / (q / (q - 1)))]
    rw [hL, hR, ← ENNReal.ofReal_mul hA0] at hg0
    have hQle : Q ≤ (A : ℝ) * Q ^ (1 / (q / (q - 1))) :=
      (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hA0 (Real.rpow_nonneg hQ0 _))).mp hg0
    have hAq := MSW_dual_algebra hQ0 hA0 hq hQle
    calc ∑ n ∈ s, enorm (X n) ^ q = ENNReal.ofReal Q := hP.symm
      _ ≤ ENNReal.ofReal ((A : ℝ) ^ q) := ENNReal.ofReal_le_ofReal hAq
      _ = (ENNReal.ofReal (A : ℝ)) ^ q := (ENNReal.ofReal_rpow_of_nonneg hA0 hq0.le).symm
  calc (∫⁻ n : ℤ, enorm (X n) ^ q ∂MeasureTheory.Measure.count) ^ (1 / q)
      ≤ ((ENNReal.ofReal (A : ℝ)) ^ q) ^ (1 / q) := ENNReal.rpow_le_rpow hmain h1q.le
    _ = (ENNReal.ofReal (A : ℝ)) ^ (q * (1 / q)) := (ENNReal.rpow_mul _ _ _).symm
    _ = (ENNReal.ofReal (A : ℝ)) ^ (1 : ℝ) := by rw [mul_one_div_cancel (ne_of_gt hq0)]
    _ = ENNReal.ofReal (A : ℝ) := ENNReal.rpow_one _

end Work.KMTAreas
