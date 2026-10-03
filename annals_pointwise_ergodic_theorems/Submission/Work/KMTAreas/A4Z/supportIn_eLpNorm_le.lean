import Mathlib
import Submission.Work.KMTAreas.A4Z.Defs
import Submission.Port.Aesm

/-!
# The `ℓ^r` bound for a `1`-bounded function supported in `[-M,M]`

If `f : ℤ → ℂ` vanishes outside `[-M,M]` (`f.SupportIn M`) and is pointwise bounded
by `1`, then for every `r ≥ 1`

`eLpNorm f (ofReal r) count ≤ ofReal ((2M+1)^(1/r))`,

i.e. `‖f‖_{ℓ^r(ℤ)} ≤ (2M+1)^{1/r}`: the support has at most `2M+1` points and on each of them
`|f| ≤ 1`.

The proof computes `eLpNorm` as the `(1/r)`-th power of the counting-measure integral
(`MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal`), turns that integral into the `ℓ^r`-sum
(`MeasureTheory.lintegral_count`), notes that the sum has only the `2M+1` terms of the support
(`tsum_eq_sum`), bounds each term by `1` and counts.
-/

namespace Work.KMTAreas.A4Z

open MeasureTheory ENNReal

theorem supportIn_eLpNorm_le {f : ℤ → ℂ} {M : ℕ} (hs : Work.Analysis.InverseTheory.SupportIn f M) (hb : ∀ x : ℤ, ‖f x‖ ≤ 1) {r : ℝ} (hr : 1 ≤ r) : MeasureTheory.eLpNorm f (ENNReal.ofReal r) MeasureTheory.Measure.count ≤ ENNReal.ofReal (((2 * M + 1 : ℕ) : ℝ) ^ (1 / r)) := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have h1r : 0 ≤ 1 / r := by positivity
  -- Step 1: rewrite `eLpNorm` as the `(1/r)`-th power of the `ℓ^r`-sum over `ℤ`.
  have h1 : MeasureTheory.eLpNorm f (ENNReal.ofReal r) MeasureTheory.Measure.count
      = (∑' x : ℤ, ENNReal.ofReal (‖f x‖ ^ r)) ^ (1 / r) := by
    rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm)
      (ENNReal.ofReal_pos.mpr hrpos).ne' ENNReal.ofReal_ne_top]
    rw [ENNReal.toReal_ofReal hrpos.le, MeasureTheory.lintegral_count]
    congr 1
    exact tsum_congr fun x => by
      rw [enorm_eq_nnnorm, ← ENNReal.ofReal_coe_nnreal, coe_nnnorm]
      exact ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hrpos.le
  -- Step 2: the `ℓ^r`-sum is concentrated on the support `[-M,M]`.
  have hfinite : ∀ x : ℤ, x ∉ Finset.Icc (-(M : ℤ)) (M : ℤ) →
      ENNReal.ofReal (‖f x‖ ^ r) = 0 := by
    intro x hx
    have hfx : f x = 0 := by
      by_contra h
      exact hx (Work.Analysis.InverseTheory.SupportIn.mem_Icc hs h)
    rw [hfx, norm_zero, Real.zero_rpow hrpos.ne', ENNReal.ofReal_zero]
  -- Step 3: the sum is at most the number of points of the support.
  have hsum : ∑' x : ℤ, ENNReal.ofReal (‖f x‖ ^ r)
      ≤ ENNReal.ofReal (((2 * M + 1 : ℕ) : ℝ)) := by
    rw [tsum_eq_sum hfinite]
    calc ∑ x ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), ENNReal.ofReal (‖f x‖ ^ r)
        ≤ ∑ x ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), (1 : ENNReal) := by
          refine Finset.sum_le_sum fun x _ => ?_
          rw [← ENNReal.ofReal_one]
          exact (ENNReal.ofReal_le_ofReal_iff (by norm_num)).mpr
            (Real.rpow_le_one (norm_nonneg _) (hb x) hrpos.le)
      _ = ((Finset.Icc (-(M : ℤ)) (M : ℤ)).card : ENNReal) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ = (((2 * M + 1 : ℕ)) : ENNReal) := by
          rw [Int.card_Icc]
          congr 1
          omega
      _ = ENNReal.ofReal (((2 * M + 1 : ℕ) : ℝ)) := (ENNReal.ofReal_natCast _).symm
  -- Step 4: take the `(1/r)`-th power.
  calc MeasureTheory.eLpNorm f (ENNReal.ofReal r) MeasureTheory.Measure.count
      = (∑' x : ℤ, ENNReal.ofReal (‖f x‖ ^ r)) ^ (1 / r) := h1
    _ ≤ (ENNReal.ofReal (((2 * M + 1 : ℕ) : ℝ))) ^ (1 / r) := ENNReal.rpow_le_rpow hsum h1r
    _ = ENNReal.ofReal ((((2 * M + 1 : ℕ) : ℝ)) ^ (1 / r)) :=
        ENNReal.ofReal_rpow_of_nonneg (by positivity) h1r

end Work.KMTAreas.A4Z
