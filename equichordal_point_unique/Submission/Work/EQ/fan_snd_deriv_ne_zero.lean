import Mathlib
import Submission.Work.EQ.charVal_main

namespace Work.EQ

open Complex Filter _root_.Topology

noncomputable section

/-- **The second fan coordinate has nonvanishing derivative at the centre.**  For every finite
branch word `ε`, `deriv (fun u => (fan a h ε u).2) 0 ≠ 0`.  This is Rychlik's product formula
for the vertical multiplier (his (110)): the derivative is a nonzero product of vertical step
factors, since the fan centres lie in `-1/2 + 2ℤ` so `stQ a n ≠ 1`. -/
theorem fan_snd_deriv_ne_zero {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) (ε : List Bool) :
    deriv (fun u => (fan a h ε u).2) 0 ≠ 0 := by
  obtain ⟨-, -, -, hderiv⟩ := fan_aux ha0 ha1 hh ε
  obtain ⟨-, -, hd, -⟩ := germC_diff_at_zero ha0 ha1 hh
  obtain ⟨-, -, -, -, -, -, -, -, -, wb10, -, -, -, wb14, -⟩ := walk_bounds (a := a) ha0 ha1
  have hD0 : deriv (fun u => (germC a h u).2) 0 ≠ 0 := by
    rw [hd, ← Complex.ofReal_zero, Ne, Complex.ofReal_inj]
    linarith
  have hrp : rprod a ε ≠ 0 := by
    rw [rprod_eq_sgnAux, wb14]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (ne_of_gt (wb10 ε.reverse 0))
  rw [hderiv]
  refine mul_ne_zero ?_ hD0
  intro hcon
  exact hrp (Complex.ofReal_injective (by simpa using hcon))

end

end Work.EQ
