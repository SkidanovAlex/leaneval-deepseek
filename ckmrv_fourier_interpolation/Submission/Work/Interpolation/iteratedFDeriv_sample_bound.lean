import Mathlib
import Submission.Work.Core.Basic
import Submission.Work.Sampling.rapidlyDecreasing_coeffs

namespace Work.Interpolation

open LeanEval.Analysis.CKMRVInterpolation
open scoped FourierTransform SchwartzMap

/-- For a complex Schwartz function `g` on `R^n`, the `r`-th Fréchet derivative of `g` at the
sample point `realIncl (sqrt (2 k))` (whose norm is `sqrt (2 k)`) is bounded by the Schwartz
seminorms of order `(2 * L, r)` and `(0, r)`, with the polynomial weight `(1 + k)^L`.

Indeed, for `k ≥ 1` the weight `(1 + k)^L` is dominated by `‖realIncl (sqrt (2 k))‖^(2 L) =
(2 k)^L`, and the seminorm `seminorm ℂ (2 * L) r` controls the corresponding weighted
derivative; the `k = 0` case is handled by the unweighted seminorm `seminorm ℂ 0 r`. -/
lemma iteratedFDeriv_sample_bound (n : ℕ) [NeZero n] (g : 𝓢(EuclideanSpace ℝ (Fin n), ℂ))
    (r L k : ℕ) :
    ‖iteratedFDeriv ℝ r (⇑g) (realIncl (n:=n) (Real.sqrt (2*(k:ℝ))))‖ * (1 + (k:ℝ))^L
      ≤ (SchwartzMap.seminorm ℂ (2*L) r) g + (SchwartzMap.seminorm ℂ 0 r) g := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    have hkey : ‖iteratedFDeriv ℝ r (⇑g) (realIncl (n:=n) (Real.sqrt (2*((0:ℕ):ℝ))))‖ *
        (1 + ((0:ℕ):ℝ))^L
        = ‖iteratedFDeriv ℝ r (⇑g) (realIncl (n:=n) (Real.sqrt (2*((0:ℕ):ℝ))))‖ := by
      norm_num
    rw [hkey]
    exact le_trans (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ g r _)
      (le_add_of_nonneg_left (apply_nonneg _ _))
  · have hk1 : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
    set x := realIncl (n:=n) (Real.sqrt (2*(k:ℝ))) with hxdef
    have hxnorm : ‖x‖ = Real.sqrt (2*(k:ℝ)) := by
      rw [hxdef, Work.Sampling.realIncl_norm, abs_of_nonneg (Real.sqrt_nonneg _)]
    have hsq : ‖x‖^(2*L) = (2*(k:ℝ))^L := by
      rw [hxnorm, pow_mul, Real.sq_sqrt (by positivity)]
    have hle : (1 + (k:ℝ))^L ≤ ‖x‖^(2*L) := by
      rw [hsq]
      exact pow_le_pow_left₀ (by positivity) (by linarith) L
    calc ‖iteratedFDeriv ℝ r (⇑g) x‖ * (1 + (k:ℝ))^L
        ≤ ‖iteratedFDeriv ℝ r (⇑g) x‖ * ‖x‖^(2*L) :=
          mul_le_mul_of_nonneg_left hle (norm_nonneg _)
      _ = ‖x‖^(2*L) * ‖iteratedFDeriv ℝ r (⇑g) x‖ := by ring
      _ ≤ (SchwartzMap.seminorm ℂ (2*L) r) g := SchwartzMap.le_seminorm ℂ (2*L) r g x
      _ ≤ (SchwartzMap.seminorm ℂ (2*L) r) g + (SchwartzMap.seminorm ℂ 0 r) g :=
          le_add_of_nonneg_right (apply_nonneg _ _)

end Work.Interpolation
