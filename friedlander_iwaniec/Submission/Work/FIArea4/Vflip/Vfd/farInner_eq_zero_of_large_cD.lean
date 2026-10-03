import Mathlib
import Submission.Work.FIArea4.Vflip.Vfd.farInner_eq_zero_of_range
import Submission.Work.FIArea4.Vflip.Vfd.FarSepDefs

namespace Work.FIArea4.Vflip.Vfd

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- If the whole flipped range is already *below* the separation scale, i.e. `8RS < cD`, then
there is no `q'` compatible with the box: the upper range bound `c D q' ≤ 8 R S` of a nonvanishing
summand (`farRange_bounds`) leaves `q' < 1`, contradicting `q' ≥ 1`.  Hence the piece vanishes. -/
theorem farInner_eq_zero_of_large_cD {D R S m c Q1 Q2 : ℕ} {a b H : ℝ} {α : ℕ → ℕ → ℂ}
    (hD : 0 < D) (hH : 0 < H) (ha : 0 < a) (haH : a * H * (R:ℝ) = 2*(S:ℝ))
    (hbig : 8*(R:ℝ)*(S:ℝ) < (c:ℝ)*(D:ℝ)) :
    farInner D R S a b α m c Q1 Q2 = 0 := by
  rw [farInner]
  refine Finset.sum_eq_zero (fun i hi => ?_)
  have hw0 : farWeight D a b c i = 0 := by
    by_contra hw
    have h2 := (farRange_bounds hi hD hH ha haH hw).2
    have hq : Q1 < i.1.1 := (mem_farSet.mp hi).1
    have hcDpos : (0 : ℝ) < (c : ℝ) * (D : ℝ) := by
      have h8 : (0 : ℝ) ≤ 8 * (R : ℝ) * (S : ℝ) := by positivity
      linarith
    have hlt : (c : ℝ) * (D : ℝ) * (i.1.1 : ℝ) < (c : ℝ) * (D : ℝ) :=
      lt_of_le_of_lt h2 hbig
    have hreal : (i.1.1 : ℝ) < 1 :=
      by nlinarith [hlt, hcDpos]
    have hnat : i.1.1 < 1 := by exact_mod_cast hreal
    omega
  rw [hw0, mul_zero]

end

end Work.FIArea4.Vflip.Vfd
