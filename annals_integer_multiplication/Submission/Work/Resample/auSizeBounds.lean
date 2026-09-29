import Mathlib
import Submission.Work.Resample.auKit
import Submission.Work.Resample.auPrepDefs
import Submission.Work.Resample.auMLe
import Submission.Work.Resample.auKArith
import Submission.Work.Resample.auCNatAbs
import Submission.Work.Resample.auOffCop

/-!
# Size bounds for the static parameters of the resampling word (paper Lemma 4.9)

Every integer value that the table word `Work.Resample.auPrep` computes inside one of its
`mapList` rounds has to fit under the uniform bound `auSZ p = 10p + 400`; this module assembles
that fact from the individual arithmetic bounds.

* `auM p α = (⌈√p⌉)·α ≤ 2p` and `auL p α = 2·auM p α + 1 ≤ 4p + 1` (`auMLe`),
* `auK s t k < 2^p` and `auK s t k ≤ auK s t (k+1) ≤ auK s t k + 1` (`auKArith`),
* `(auC p α s t k).natAbs ≤ 2^(2p+2)` (`auCNatAbs`),
* `auOff p α s < 2^p` and `auCop p α s ≤ 4p + 3` (`auOffCop`),

together with the two conversions from a bound on a natural number (or on `natAbs`) to a bound
on `HvdH.isz`.
-/

set_option autoImplicit false

namespace Work.Resample

open HvdH

/-! ## From bounds on `natAbs` to bounds on `isz` -/

/-- If `|z| ≤ 2^k` and `k + 3 ≤ auSZ p` then `isz z ≤ auSZ p`. -/
theorem isz_le_of_natAbs_le {z : ℤ} {k p : ℕ} (h : z.natAbs ≤ 2 ^ k) (hk : k + 3 ≤ auSZ p) :
    isz z ≤ auSZ p := by
  have h1 : z.natAbs < 2 ^ (k + 1) :=
    lt_of_le_of_lt h (Nat.pow_lt_pow_right one_lt_two (by omega))
  have h2 : z.natAbs.size ≤ k + 1 := Nat.size_le.mpr h1
  simp only [HvdH.isz, auSZ] at *
  exact le_trans (Nat.add_le_add_right h2 2) (by omega)

/-- If `m ≤ 2^k` and `k + 3 ≤ auSZ p` then `isz (m : ℤ) ≤ auSZ p`. -/
theorem isz_nat_le_of_le_pow {m k p : ℕ} (h : m ≤ 2 ^ k) (hk : k + 3 ≤ auSZ p) :
    isz ((m : ℤ)) ≤ auSZ p :=
  isz_le_of_natAbs_le (z := (m : ℤ)) (by simpa using h) hk

/-- `4p + 3 < 2^(p+3)`: a linear quantity is dominated by a power of two. -/
theorem four_mul_add_three_lt (p : ℕ) : 4 * p + 3 < 2 ^ (p + 3) := by
  have hp : p ≤ 2 ^ p := le_of_lt (Nat.lt_two_pow_self)
  have h1 : (2:ℕ) ^ (p + 3) = 8 * 2 ^ p := by rw [pow_add]; ring
  have h2 : 1 ≤ 2 ^ p := Nat.one_le_two_pow
  omega

/-- `isz (m : ℤ) ≤ auSZ p` for any `m ≤ 4p + 3` (the sizes of `auCop` and of the small
parameters). -/
theorem isz_le_of_le_lin {m p : ℕ} (h : m ≤ 4 * p + 3) : isz ((m : ℤ)) ≤ auSZ p := by
  have h4 : m < 2 ^ (p + 3) := lt_of_le_of_lt h (four_mul_add_three_lt p)
  have h5 : m.size ≤ p + 3 := Nat.size_le.mpr h4
  simp only [HvdH.isz, auSZ, Int.natAbs_natCast] at *
  exact le_trans (Nat.add_le_add_right h5 2) (by omega)

/-! ## The bound -/

theorem auSizeBounds (p α s t k : ℕ) (hs : 2 ≤ s) (hst : s < t) (htp : t < 2 ^ p)
    (hα : 2 ≤ α) (hp : 100 ≤ p) (hαp : α ^ 2 < p) (hk : k < t) :
    Work.Resample.auM p α ≤ 2 * p ∧ Work.Resample.auL p α ≤ 4 * p + 1 ∧
      HvdH.isz ((Work.Resample.auK s t k : ℕ) : ℤ) ≤ Work.Resample.auSZ p ∧
      HvdH.isz (Work.Resample.auC p α s t k) ≤ Work.Resample.auSZ p ∧
      HvdH.isz ((Work.Resample.auOff p α s : ℕ) : ℤ) ≤ Work.Resample.auSZ p ∧
      HvdH.isz ((Work.Resample.auCop p α s : ℕ) : ℤ) ≤ Work.Resample.auSZ p ∧
      0 ≤ ((Work.Resample.auK s t (k + 1) : ℕ) : ℤ) - ((Work.Resample.auK s t k : ℕ) : ℤ) ∧
      ((Work.Resample.auK s t (k + 1) : ℕ) : ℤ) - ((Work.Resample.auK s t k : ℕ) : ℤ) ≤ 1 := by
  obtain ⟨hM, hL⟩ := auMLe p α hα hαp
  obtain ⟨hK1, hKmono, hKstep⟩ := auKArith p s t k hs hst htp hk
  have hC := auCNatAbs p α s t k hs hst htp hα hp hαp hk
  have hs2p : s < 2 ^ p := lt_trans hst htp
  have hs1 : 1 ≤ s := by omega
  obtain ⟨hOff, hCop⟩ := auOffCop p α s hα hαp hp hs1 hs2p
  refine ⟨hM, hL, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the window centre is a `p`-bit number
    exact isz_le_pow2 (le_of_lt hK1)
  · -- the distance `C` is `≤ 2^(2p+2)`
    exact isz_le_of_natAbs_le (k := 2 * p + 2) hC (by simp only [auSZ]; omega)
  · -- the offset is `< 2^p`
    exact isz_le_pow2 (le_of_lt hOff)
  · -- the number of copies is `≤ 4p+3`
    exact isz_le_of_le_lin hCop
  · -- the slides are nonnegative ...
    have h : ((auK s t k : ℕ) : ℤ) ≤ ((auK s t (k + 1) : ℕ) : ℤ) := by exact_mod_cast hKmono
    omega
  · -- ... and increase by at most one
    have h : ((auK s t (k + 1) : ℕ) : ℤ) ≤ ((auK s t k : ℕ) : ℤ) + 1 := by
      exact_mod_cast hKstep
    omega

end Work.Resample
