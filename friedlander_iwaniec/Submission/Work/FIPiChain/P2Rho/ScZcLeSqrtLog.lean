import Mathlib
import Submission.Work.FIChain.RhoWin2Defs
import Submission.Work.FIChain.scale_factsC

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIPiChain.P2Rho

open Filter

/-- `0 < sc x B`: the dyadic scale is a positive power of two. -/
private lemma sc_pos' (x : ℕ) (B : ℝ) : 0 < Work.FIChain.sc x B := by
  rw [Work.FIChain.sc]; positivity

/-- `0 ≤ Yc x B` whenever `0 ≤ log x`. -/
private lemma Yc_nonneg' (x : ℕ) (B : ℝ) (hL : 0 ≤ Real.log (x : ℝ)) :
    0 ≤ Work.FIChain.Yc x B := by
  rw [Work.FIChain.Yc]
  exact div_nonneg (Real.sqrt_nonneg _)
    (mul_nonneg (sc_pos' x B).le (Real.rpow_nonneg hL _))

/-- `zc x B ≤ Yc x B`, since `zc x B = ⌊Yc x B⌋₊`. -/
private lemma zc_le_Yc' (x : ℕ) (B : ℝ) (hL : 0 ≤ Real.log (x : ℝ)) :
    Work.FIChain.zc x B ≤ Work.FIChain.Yc x B := by
  rw [Work.FIChain.zc, Work.FIChain.Zc]
  exact Nat.floor_le (Yc_nonneg' x B hL)

/-- The exact value of the window product: `sc x B · Yc x B = √x/(log x)^{B+2}`. -/
private lemma sc_mul_Yc' (x : ℕ) (B : ℝ) (hL : 0 < Real.log (x : ℝ)) :
    Work.FIChain.sc x B * Work.FIChain.Yc x B
      = Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ (B + 2) := by
  rw [Work.FIChain.Yc]
  have h1 : Work.FIChain.sc x B ≠ 0 := ne_of_gt (sc_pos' x B)
  have h2 : (Real.log (x : ℝ)) ^ (B + 2) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hL _)
  field_simp

/-- The window product `sc·zc` sits below `√x·(log x)^{-(B+2)}`, because
`sc·zc ≤ sc·Yc = √x/(log x)^{B+2}`. -/
theorem ScZcLeSqrtLog (B : ℝ) :
    ∀ᶠ x : ℕ in Filter.atTop,
      Work.FIChain.sc x B * Work.FIChain.zc x B ≤
        (x : ℝ) ^ ((1 : ℝ) / 2) * (Real.log (x : ℝ)) ^ (-(B + 2)) := by
  filter_upwards [eventually_ge_atTop 3] with x hx
  have hx1 : (1 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 1 < x)
  have hLpos : 0 < Real.log (x : ℝ) := Real.log_pos hx1
  calc Work.FIChain.sc x B * Work.FIChain.zc x B
      ≤ Work.FIChain.sc x B * Work.FIChain.Yc x B :=
        mul_le_mul_of_nonneg_left (zc_le_Yc' x B hLpos.le) (sc_pos' x B).le
    _ = Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ (B + 2) := sc_mul_Yc' x B hLpos
    _ = (x : ℝ) ^ ((1 : ℝ) / 2) * (Real.log (x : ℝ)) ^ (-(B + 2)) := by
        rw [Real.sqrt_eq_rpow, Real.rpow_neg hLpos.le (B + 2), div_eq_mul_inv]

end Work.FIPiChain.P2Rho
