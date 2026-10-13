import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.R1G.AnG

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.R1G

/-- For `z ≥ 0`, `θ ∈ [0,π/2]` the weighted angular factor
`Tf θ · w z / sin(2θ)^{η/2}` is (in absolute value) at most `w z`, because
`s = sin(2θ) ∈ [0,1]` and `s/s^{η/2} = s^{1-η/2} ≤ 1` (`η/2 < 1`). Consequently
its square is bounded by `(w z)²`, i.e. the `i = 1` summand of `HkIntegrand`
is dominated by `(w z)²`. -/
theorem gA_dz_slice_le {z θ : ℝ} (hz : 0 ≤ z) (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.R1G.Tf θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      ≤ (Work.Spaces.w z) ^ 2 := by
  rw [Work.Spaces.Iθ] at hθ
  simp only [Work.R1G.Tf]
  set s := Real.sin (2 * θ)
  -- `s = sin(2θ) ∈ [0,1]`.
  have hs0 : 0 ≤ s := by
    apply Real.sin_nonneg_of_mem_Icc
    constructor <;> linarith [hθ.1, hθ.2, Real.pi_pos]
  have hs1 : s ≤ 1 := Real.sin_le_one _
  -- `w z ≥ 0` for `z ≥ 0` (also at `z = 0`, where the division is junk `0`).
  have hw0 : 0 ≤ Work.Spaces.w z := by
    rw [Work.Spaces.w]; exact div_nonneg (by positivity) (by positivity)
  rcases eq_or_lt_of_le hs0 with hs_eq | hs_pos
  · -- Degenerate case `s = 0`: both sides collapse (the quotient is `0`).
    have hsz : s = 0 := hs_eq.symm
    rw [hsz]
    have he : Work.Spaces.eta / 2 ≠ 0 := by rw [Work.Spaces.eta]; norm_num
    rw [Real.zero_rpow he]
    simp
    positivity
  · -- Case `s > 0`: `s / s^{η/2} = s^{1-η/2} ≤ 1` and `w z ≥ 0`.
    have hspos : 0 < s ^ (Work.Spaces.eta / 2) := Real.rpow_pos_of_pos hs_pos _
    have hA : s * (Work.Spaces.w z / s ^ (Work.Spaces.eta / 2)) ≤ Work.Spaces.w z := by
      have hrw : s / s ^ (Work.Spaces.eta / 2) = s ^ (1 - Work.Spaces.eta / 2) := by
        rw [Real.rpow_sub hs_pos, Real.rpow_one]
      have hle1 : s ^ (1 - Work.Spaces.eta / 2) ≤ 1 :=
        Real.rpow_le_one (le_of_lt hs_pos) hs1 (by rw [Work.Spaces.eta]; norm_num)
      calc s * (Work.Spaces.w z / s ^ (Work.Spaces.eta / 2))
          = Work.Spaces.w z * (s / s ^ (Work.Spaces.eta / 2)) := by ring
        _ = Work.Spaces.w z * s ^ (1 - Work.Spaces.eta / 2) := by rw [hrw]
        _ ≤ Work.Spaces.w z * 1 := mul_le_mul_of_nonneg_left hle1 hw0
        _ = Work.Spaces.w z := by ring
    -- `0 ≤ A ≤ w z` hence `A² ≤ (w z)²`.
    have hA0 : 0 ≤ s * (Work.Spaces.w z / s ^ (Work.Spaces.eta / 2)) :=
      mul_nonneg hs0 (div_nonneg hw0 (le_of_lt hspos))
    exact sq_le_sq' (by linarith) hA

end Work.R1G
