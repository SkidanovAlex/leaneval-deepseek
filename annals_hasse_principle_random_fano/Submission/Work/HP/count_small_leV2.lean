import Mathlib
import Submission.Work.HP.ArchDefs
import Submission.Work.HP.ArchGlueV2
import Submission.Work.HP.tau_basic

namespace Work.HP

open MeasureTheory MvPolynomial
open scoped ENNReal

theorem count_small_le (d n : ℕ) (hn : 3 ≤ n)
    (hpack : ∀ (s : Set (Mon d n → ℤ)) (Y : Set (Mon d n → ℝ)), s.Finite →
        (∀ a ∈ s, {w : Mon d n → ℝ | rNorm (w - toR a) ≤ (1 / 2 : ℝ)} ⊆ Y) →
        (s.ncard : ENNReal) * volume {w : Mon d n → ℝ | rNorm w ≤ (1 / 2 : ℝ)} ≤ volume Y)
    (hfin : ∀ R : ℝ, {a : Mon d n → ℤ | eNorm a ≤ R}.Finite)
    (hball : ∀ (r : ℝ) (x : Mon d n → ℝ), 0 ≤ r →
        volume {w : Mon d n → ℝ | rNorm (w - x) ≤ r}
          = ENNReal.ofReal (r ^ NN d n) * volume {w : Mon d n → ℝ | rNorm w ≤ 1})
    (R : ℝ) (hR : 0 ≤ R) :
    (({a : Mon d n → ℤ | eNorm a ≤ R}.ncard : ℝ))
      * (volume {w : Mon d n → ℝ | rNorm w ≤ (1 / 2 : ℝ)}).toReal
      ≤ (R + 1) ^ NN d n * (volume {w : Mon d n → ℝ | rNorm w ≤ 1}).toReal := by
  classical
  -- The height ball is finite and each of its half-balls lands in the ball of radius `R + 1`.
  have hsfin : ({a : Mon d n → ℤ | eNorm a ≤ R}).Finite := hfin R
  have hsub : ∀ a ∈ ({a : Mon d n → ℤ | eNorm a ≤ R}),
      {w : Mon d n → ℝ | rNorm (w - toR a) ≤ (1 / 2 : ℝ)} ⊆
        {w : Mon d n → ℝ | rNorm w ≤ R + 1} := by
    intro a ha w hw
    simp only [Set.mem_ofPred_eq] at ha hw ⊢
    have h := rNorm_le_add_sub w (toR a)
    rw [rNorm_toR_eq_eNorm] at h
    linarith
  have hpack' := hpack ({a : Mon d n → ℤ | eNorm a ≤ R}) {w : Mon d n → ℝ | rNorm w ≤ R + 1}
    hsfin hsub
  -- Rewrite the volume of the target ball using the ball-volume hypothesis.
  have hY : volume {w : Mon d n → ℝ | rNorm w ≤ R + 1}
      = ENNReal.ofReal ((R + 1) ^ NN d n) * volume {w : Mon d n → ℝ | rNorm w ≤ 1} := by
    have h := hball (R + 1) 0 (by linarith)
    simpa using h
  rw [hY] at hpack'
  -- Split off the degenerate case in which the unit ball has infinite volume.
  by_cases hV : volume {w : Mon d n → ℝ | rNorm w ≤ 1} = ⊤
  · -- Then the half-ball also has infinite volume and both sides of the goal vanish.
    have hv0 : volume {w : Mon d n → ℝ | rNorm w ≤ (1 / 2 : ℝ)} = ⊤ := by
      have h2 : volume {w : Mon d n → ℝ | rNorm w ≤ (1 / 2 : ℝ)}
          = ENNReal.ofReal ((1 / 2 : ℝ) ^ NN d n) * volume {w : Mon d n → ℝ | rNorm w ≤ 1} := by
        have h := hball (1 / 2) 0 (by norm_num)
        simpa using h
      rw [h2, hV]
      exact ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.mpr (pow_pos (by norm_num) _))
    rw [hv0, hV, ENNReal.toReal_top]
    simp
  · -- Otherwise the right-hand side is finite and `toReal` may be pulled through.
    have hB : ENNReal.ofReal ((R + 1) ^ NN d n) * volume {w : Mon d n → ℝ | rNorm w ≤ 1} ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hV
    have hmain := ENNReal.toReal_mono hB hpack'
    rwa [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (pow_nonneg (by linarith) _)] at hmain

end Work.HP
