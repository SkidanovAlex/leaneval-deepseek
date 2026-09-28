import Mathlib
import Submission.Work.HP.Defs

/-!
# Volume of `rNorm`-balls in `ℝ^ι`

The closed ball of radius `r ≥ 0` for the Euclidean norm `rNorm` has volume
`r ^ card ι` times the volume of the unit ball.  The centre is irrelevant because
Lebesgue measure on `ι → ℝ` is translation invariant.

The computation goes through Mathlib's `MeasureTheory.volume_sum_rpow_le`, which gives the
volume of the centred `L²`-ball `{x | (∑ i, |x i| ^ p) ^ (1 / p) ≤ r}` on `ι → ℝ`
(for `Nonempty ι` and `1 ≤ p`); with `p = 2` the `L²` expression is exactly `rNorm`.
-/

namespace Work.HP

open MeasureTheory

theorem volume_rNorm_ball {ι : Type*} [Fintype ι] [Nonempty ι] (x : ι → ℝ) (r : ℝ) (hr : 0 ≤ r) :
    MeasureTheory.volume {w : ι → ℝ | Work.HP.rNorm (w - x) ≤ r}
      = ENNReal.ofReal (r ^ Fintype.card ι)
        * MeasureTheory.volume {w : ι → ℝ | Work.HP.rNorm w ≤ 1} := by
  -- `rNorm` is the `L²`-norm expression appearing in `volume_sum_rpow_le` with `p = 2`.
  have hconv : ∀ v : ι → ℝ, (∑ i, |v i| ^ (2:ℝ)) ^ ((1:ℝ)/2) = rNorm v := by
    intro v
    rw [← Real.sqrt_eq_rpow, rNorm]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by rw [Real.rpow_ofNat, sq_abs]
  -- Lebesgue measure on `ι → ℝ` is translation invariant, so the centre does not matter.
  have htrans : MeasureTheory.volume {w : ι → ℝ | rNorm (w - x) ≤ r}
      = MeasureTheory.volume {w : ι → ℝ | rNorm w ≤ r} := by
    have h := MeasureTheory.measure_preimage_add_right MeasureTheory.volume (-x)
      {v : ι → ℝ | rNorm v ≤ r}
    simpa [sub_eq_add_neg] using h
  have hset (s : ℝ) : {u : ι → ℝ | rNorm u ≤ s}
      = {u : ι → ℝ | (∑ i, |u i| ^ (2:ℝ)) ^ ((1:ℝ)/2) ≤ s} := by
    ext w
    simp only [Set.mem_ofPred_eq]
    rw [← hconv w]
  -- The explicit value of the volume of a ball, from the `L²`-ball formula.
  have hvol (s : ℝ) : MeasureTheory.volume {w : ι → ℝ | rNorm w ≤ s}
      = ENNReal.ofReal s ^ Fintype.card ι *
        ENNReal.ofReal ((2 * Real.Gamma (1 / (2:ℝ) + 1)) ^ Fintype.card ι
          / Real.Gamma ((Fintype.card ι : ℝ) / (2:ℝ) + 1)) := by
    rw [hset s]
    exact MeasureTheory.volume_sum_rpow_le ι (p := 2) (by norm_num) s
  rw [htrans, hvol r]
  have h1 : MeasureTheory.volume {w : ι → ℝ | rNorm w ≤ 1}
      = ENNReal.ofReal ((2 * Real.Gamma (1 / (2:ℝ) + 1)) ^ Fintype.card ι
          / Real.Gamma ((Fintype.card ι : ℝ) / (2:ℝ) + 1)) := by
    rw [hvol 1, ENNReal.ofReal_one, one_pow, one_mul]
  rw [h1, ENNReal.ofReal_pow hr]

end Work.HP
