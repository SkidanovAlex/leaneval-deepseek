import Mathlib
import Submission.Work.NumberTheory.Chen.BTermCount.BLodUnweightedDefs
import Submission.Work.NumberTheory.Chen.BTermCount.BLodSmallRSum
import Submission.Work.NumberTheory.Chen.BTermCount.bRemUNwSmallRNamed
import Submission.Work.NumberTheory.Chen.BTermCount.sumInvTotientLogBound

namespace Work.NumberTheory.Chen.BTermCount

open Finset Filter
open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-!
# The unweighted small-conductor sum, with a prescribed conductor exponent

`BLodSmallRSum` bounds the `3^{ω}`-weighted small-conductor double sum by

  `C · x · (log x + 2)^{2C' + 20} · log log x / (log x)^{A'}`,

where `C' > 0` is the exponent of the conductor threshold `R₀ ≤ (log x)^{C'}` and
`A'` is the exponent chosen for the level.  Here `C'` is treated as a *parameter*:
for arbitrary `C' > 0` and target exponent `A > 0` we absorb the overhead
`(log x)^{2C'+20} log log x` into a level exponent `A' = A + 2C' + 23`, using only
that `(log x)^{2C'+20} log log x ≪ (log x)^{2C'+23}`.
-/

/-- **Absorption of the weighted-bound overhead, parameterised by `C'`.**  For
`A, C', C > 0`, eventually

  `C x (log x + 2)^{2C'+20} log log x / (log x)^{A + 2C' + 23} ≤ x / (log x)^A`. -/
lemma bls_absorb_param (A C' C : ℝ) (hA : 0 < A) (hC' : 0 < C') (hC : 0 < C) :
    ∀ᶠ x : ℕ in Filter.atTop,
      C * (x : ℝ) * (Real.log (x : ℝ) + 2) ^ (2 * C' + 20) *
          Real.log (Real.log (x : ℝ) + 3) / (Real.log (x : ℝ)) ^ (A + (2 * C' + 23))
        ≤ (x : ℝ) / (Real.log (x : ℝ)) ^ A := by
  have hlogtop : Filter.Tendsto (fun x : ℕ => Real.log (x : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hKpos : 0 < C * 2 ^ (2 * C' + 21) :=
    mul_pos hC (Real.rpow_pos_of_pos (by norm_num) _)
  have hev := hlogtop.eventually
    (Filter.eventually_ge_atTop (max 3 (Real.sqrt (C * 2 ^ (2 * C' + 21)) + 1)))
  filter_upwards [hev, Filter.eventually_ge_atTop (1 : ℕ)] with x hLx hx1
  set L : ℝ := Real.log (x : ℝ) with hLdef
  have hL3 : 3 ≤ L := le_trans (le_max_left _ _) hLx
  have hLsqrt : Real.sqrt (C * 2 ^ (2 * C' + 21)) + 1 ≤ L :=
    le_trans (le_max_right _ _) hLx
  have hL2 : 2 ≤ L := by linarith
  have hLpos : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hxpos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
  have hexp : 0 ≤ 2 * C' + 20 := by linarith
  have hbase : (0 : ℝ) ≤ L + 2 := by linarith
  have hL2L : L + 2 ≤ 2 * L := by linarith
  have hKnn : (0 : ℝ) ≤ C * 2 ^ (2 * C' + 21) := le_of_lt hKpos
  have hsqrt1 : (0 : ℝ) ≤ Real.sqrt (C * 2 ^ (2 * C' + 21)) + 1 := by positivity
  have hLsq : C * 2 ^ (2 * C' + 21) ≤ L ^ (2 : ℕ) := by
    have h1 : C * 2 ^ (2 * C' + 21) ≤
        (Real.sqrt (C * 2 ^ (2 * C' + 21)) + 1) ^ (2 : ℕ) := by
      nlinarith [Real.sq_sqrt hKnn, Real.sqrt_nonneg (C * 2 ^ (2 * C' + 21))]
    exact le_trans h1 (pow_le_pow_left₀ hsqrt1 hLsqrt 2)
  have hlog3 : Real.log (L + 3) ≤ L + 2 := by
    have h := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < L + 3)
    linarith
  have hstepA : (L + 2) ^ (2 * C' + 20) * Real.log (L + 3)
      ≤ (2 * L) ^ (2 * C' + 20) * (2 * L) := by
    calc (L + 2) ^ (2 * C' + 20) * Real.log (L + 3)
        ≤ (L + 2) ^ (2 * C' + 20) * (L + 2) :=
          mul_le_mul_of_nonneg_left hlog3 (Real.rpow_nonneg hbase _)
      _ ≤ (2 * L) ^ (2 * C' + 20) * (2 * L) :=
          mul_le_mul (Real.rpow_le_rpow hbase hL2L hexp) hL2L hbase
            (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ 2 * L) _)
  have h2pow : (2 : ℝ) ^ (2 * C' + 20) * 2 = 2 ^ (2 * C' + 21) := by
    have h := Real.rpow_add (show (0 : ℝ) < 2 by norm_num) (2 * C' + 20) 1
    rw [Real.rpow_one] at h
    rw [show 2 * C' + 20 + 1 = 2 * C' + 21 by ring] at h
    exact h.symm
  have hLpow : L ^ (2 * C' + 20) * L = L ^ (2 * C' + 21) := by
    have h := Real.rpow_add hLpos (2 * C' + 20) 1
    rw [Real.rpow_one] at h
    rw [show 2 * C' + 20 + 1 = 2 * C' + 21 by ring] at h
    exact h.symm
  have hmul : (2 * L) ^ (2 * C' + 20) * (2 * L) =
      2 ^ (2 * C' + 21) * L ^ (2 * C' + 21) := by
    rw [Real.mul_rpow (show (0 : ℝ) ≤ 2 by norm_num) (by linarith : (0 : ℝ) ≤ L)]
    rw [show (2 : ℝ) ^ (2 * C' + 20) * L ^ (2 * C' + 20) * (2 * L)
          = ((2 : ℝ) ^ (2 * C' + 20) * 2) * (L ^ (2 * C' + 20) * L) by ring]
    rw [h2pow, hLpow]
  have h2Lpow : L ^ (2 : ℕ) * L ^ (2 * C' + 21) = L ^ (2 * C' + 23) := by
    rw [← Real.rpow_natCast L 2, ← Real.rpow_add hLpos ((2 : ℕ) : ℝ) (2 * C' + 21)]
    congr 1
    push_cast
    ring
  have hcore : C * (L + 2) ^ (2 * C' + 20) * Real.log (L + 3) ≤ L ^ (2 * C' + 23) := by
    have hfin : C * 2 ^ (2 * C' + 21) * L ^ (2 * C' + 21) ≤ L ^ (2 * C' + 23) := by
      calc C * 2 ^ (2 * C' + 21) * L ^ (2 * C' + 21)
          = (C * 2 ^ (2 * C' + 21)) * L ^ (2 * C' + 21) := by ring
        _ ≤ L ^ (2 : ℕ) * L ^ (2 * C' + 21) :=
            mul_le_mul_of_nonneg_right hLsq (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ L) _)
        _ = L ^ (2 * C' + 23) := h2Lpow
    calc C * (L + 2) ^ (2 * C' + 20) * Real.log (L + 3)
        = C * ((L + 2) ^ (2 * C' + 20) * Real.log (L + 3)) := by ring
      _ ≤ C * ((2 * L) ^ (2 * C' + 20) * (2 * L)) := mul_le_mul_of_nonneg_left hstepA hC.le
      _ = C * (2 ^ (2 * C' + 21) * L ^ (2 * C' + 21)) := by rw [hmul]
      _ = C * 2 ^ (2 * C' + 21) * L ^ (2 * C' + 21) := by ring
      _ ≤ L ^ (2 * C' + 23) := hfin
  have hLpowadd : L ^ (A + (2 * C' + 23)) = L ^ A * L ^ (2 * C' + 23) :=
    Real.rpow_add hLpos A _
  calc C * (x : ℝ) * (L + 2) ^ (2 * C' + 20) * Real.log (L + 3) /
          L ^ (A + (2 * C' + 23))
      = (x : ℝ) * (C * (L + 2) ^ (2 * C' + 20) * Real.log (L + 3)) /
          L ^ (A + (2 * C' + 23)) := by ring
    _ ≤ (x : ℝ) * L ^ (2 * C' + 23) / L ^ (A + (2 * C' + 23)) := by
        refine div_le_div_of_nonneg_right ?_ (Real.rpow_pos_of_pos hLpos _).le
        exact mul_le_mul_of_nonneg_left hcore hxpos.le
    _ = (x : ℝ) / L ^ A := by
        rw [hLpowadd]
        exact mul_div_mul_right _ _ (ne_of_gt (Real.rpow_pos_of_pos hLpos _))

/-- **The unweighted small-conductor sum, parameterised by the conductor exponent.**
For every `A > 0` and `C' > 0` there is `C > 0` with, eventually in `x`, for all
`M Y D R₀` with `x^{1/14} ≤ M`, `2 ≤ D` and `R₀ ≤ ⌊(log x)^{C'}⌋`,

  `blodSmallUnw x M Y D R₀ ≤ C x / (log x)^A`. -/
theorem bRemUNwSmallRParam (A C' : ℝ) (hA : 0 < A) (hC' : 0 < C') :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℕ in Filter.atTop,
      ∀ (M Y D R₀ : ℕ), (x : ℝ) ^ ((1 : ℝ) / 14) ≤ M → 2 ≤ D →
        R₀ ≤ ⌊(Real.log (x : ℝ)) ^ C'⌋₊ →
        blodSmallUnw x M Y D R₀ ≤ C * (x : ℝ) / (Real.log (x : ℝ)) ^ A := by
  have hA'pos : 0 < A + (2 * C' + 23) := by linarith
  have hle : C' ≤ A + (2 * C' + 23) := by linarith
  obtain ⟨C₀, hC₀pos, hBL⟩ := BLodSmallRSum (A + (2 * C' + 23)) C' hA'pos hC' hle
  refine ⟨1, by norm_num, ?_⟩
  filter_upwards [hBL, bls_absorb_param A C' C₀ hA hC' hC₀pos] with x hx habs
  intro M Y D R₀ hM hD hR₀
  calc blodSmallUnw x M Y D R₀
      ≤ blodSmallWtd x M Y D R₀ := bls_unw_le_wtd x M Y D R₀
    _ ≤ C₀ * (x : ℝ) * (Real.log (x : ℝ) + 2) ^ (2 * C' + 20) *
          Real.log (Real.log (x : ℝ) + 3) / (Real.log (x : ℝ)) ^ (A + (2 * C' + 23)) :=
        hx M Y D R₀ hM hR₀ hD
    _ ≤ (x : ℝ) / (Real.log (x : ℝ)) ^ A := habs
    _ = 1 * (x : ℝ) / (Real.log (x : ℝ)) ^ A := by rw [one_mul]

end Work.NumberTheory.Chen.BTermCount
