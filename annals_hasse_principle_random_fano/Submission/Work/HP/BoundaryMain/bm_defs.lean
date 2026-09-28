import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.ArchDefs

set_option autoImplicit false

noncomputable section

open Classical

namespace Work.HP.BoundaryMain

open Work.HP

/-- The integer coefficient vector with the `n+1` special monomials `smon d n hd j ·` set to
zero.  This is the "free part" of `a`: the data that survives after the special coefficients
`a (smon d n hd j i)` are peeled off. -/
def zeroSInt (d n : ℕ) (hd : 1 ≤ d) (j : Fin (n + 1)) (a : Mon d n → ℤ) : Mon d n → ℤ :=
  fun m => if m ∈ Sset d n hd j then 0 else a m

/-- `zeroSInt` is the integer model of `zeroS`. -/
theorem toR_zeroSInt (d n : ℕ) (hd : 1 ≤ d) (j : Fin (n + 1)) (a : Mon d n → ℤ) :
    toR (zeroSInt d n hd j a) = zeroS d n hd j (toR a) := by
  funext m
  by_cases hm : m ∈ Sset d n hd j
  · simp only [zeroSInt, zeroS, hm, ↓reduceIte, toR, Int.cast_zero]
  · simp only [zeroSInt, zeroS, hm, ↓reduceIte, toR]

end Work.HP.BoundaryMain
