import Mathlib
import Submission.Work.HP.MM2.Defs
import Submission.Work.HP.DeltaXY_gcd_detL
import Submission.Work.HP.EE_lower2
import Submission.Work.HP.Lat.detL_ge_one
import Submission.Work.HP.MDEstimates.veronese_linIndep

namespace Work.HP.MM2

open Work.HP

/-- `wedgeNorm v w` is nonnegative. -/
private lemma wedgeNorm_nonneg' {ι : Type*} [Fintype ι] (v w : ι → ℤ) :
    0 ≤ wedgeNorm v w := Real.sqrt_nonneg _

/-- The covolume `wedgeNorm (ν(x)) (ν(y))` is positive for linearly independent primitive `x,y`.

If it vanished, then by `Δ(x,y)·𝓖(x,y) = ‖ν(x)‖‖ν(y)‖ / det Γ_{x,y}` the left-hand side would be
`0`, while the right-hand side is strictly positive. -/
private lemma wedgeNorm_veronese_pos (d n : ℕ) [DecidableEq (Mon d n)] (hd : 2 ≤ d) (hn : 1 ≤ n)
    (x y : Fin (n + 1) → ℤ) (hx : IsPrim x) (hy : IsPrim y)
    (hLI : LinearIndependent ℤ ![x, y]) :
    0 < wedgeNorm (veronese d n x) (veronese d n y) := by
  have hD := DeltaXY_gcd_detL d n hd hn x y hx hy hLI
  have hEx : 0 < eNorm (veronese d n x) :=
    eNorm_pos_iff.mpr (MDEstimates.veronese_ne_zero (isPrim_ne_zero hx))
  have hEy : 0 < eNorm (veronese d n y) :=
    eNorm_pos_iff.mpr (MDEstimates.veronese_ne_zero (isPrim_ne_zero hy))
  have hdet : 0 < detL (Gam d n x y) := lt_of_lt_of_le zero_lt_one (Lat.detL_ge_one _)
  have hwne : wedgeNorm (veronese d n x) (veronese d n y) ≠ 0 := by
    intro h0
    have h2 : DeltaXY d n x y = 0 := by rw [DeltaXY, h0, div_zero]
    have h3 : DeltaXY d n x y * (gcdMinors2 x y : ℝ) = 0 := by rw [h2, zero_mul]
    rw [h3] at hD
    have h1 : 0 < eNorm (veronese d n x) * eNorm (veronese d n y) / detL (Gam d n x y) :=
      div_pos (mul_pos hEx hEy) hdet
    linarith
  exact lt_of_le_of_ne (wedgeNorm_nonneg' _ _) (Ne.symm hwne)

/-- `1 ≤ Δ(x,y)`: the covolume `wedgeNorm (ν(x)) (ν(y))` of `ℤν(x) ⊕ ℤν(y)` is at most
`‖ν(x)‖‖ν(y)‖`, and it is positive for linearly independent primitive `x,y`. -/
theorem one_le_DeltaXY (d n : ℕ) [DecidableEq (Work.HP.Mon d n)] (hd : 2 ≤ d) (hn : 1 ≤ n)
    (x y : Fin (n + 1) → ℤ) (hx : Work.HP.IsPrim x) (hy : Work.HP.IsPrim y)
    (hLI : LinearIndependent ℤ ![x, y]) : 1 ≤ Work.HP.DeltaXY d n x y := by
  have hwp := wedgeNorm_veronese_pos d n hd hn x y hx hy hLI
  rw [DeltaXY, le_div_iff₀ hwp]
  have h := wedgeNorm_le_mul (veronese d n x) (veronese d n y)
  linarith

end Work.HP.MM2
