import Mathlib
import Submission.Work.FIArea2.TsumDefs
import Submission.Work.FIArea2.TsumDefs2
import Submission.Work.FIArea2.ramanujan_primepow
import Submission.Work.FIArea2.ramanujan_setup
import Submission.Work.FIArea2.TsumD_lift
import Submission.Work.FIArea2.TsumD_recursion
import Submission.Work.FIArea2.Tup_eq_sum_range_ram

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea2

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- An odd integer is a unit modulo `2^ν` (`ν ≥ 1`). -/
lemma two_pow_isUnit_of_odd (ν : ℕ) (hν : 1 ≤ ν) (a : ℤ) (ha : Odd a) :
    IsUnit (a : ZMod (2 ^ ν)) := by
  have hgen : ∀ b : ℤ, IsUnit (b : ZMod (2 ^ ν)) ↔ IsUnit ((b.natAbs : ℕ) : ZMod (2 ^ ν)) := by
    intro b
    have hbc : ((b.natAbs : ℕ) : ZMod (2 ^ ν)) = (b : ZMod (2 ^ ν)) ∨
        ((b.natAbs : ℕ) : ZMod (2 ^ ν)) = -(b : ZMod (2 ^ ν)) := by
      rcases Int.natAbs_eq b with he | he
      · left
        have := congrArg (fun z : ℤ => (z : ZMod (2 ^ ν))) he
        simpa using this.symm
      · right
        have := congrArg (fun z : ℤ => (z : ZMod (2 ^ ν))) he
        simp only [Int.cast_neg, Int.cast_natCast] at this
        rw [this, neg_neg]
    rcases hbc with hc | hc
    · rw [hc]
    · rw [hc, IsUnit.neg_iff]
  rw [hgen a, ZMod.isUnit_iff_coprime]
  have hodd : ¬ (2 ∣ a.natAbs) := by
    have hiff : (2 ∣ a.natAbs) ↔ ((2 : ℤ) ∣ a) := by
      have := Int.natAbs_dvd_natAbs (a := (2 : ℤ)) (b := a)
      simpa using this
    rw [hiff]
    intro h2
    exact (Int.not_even_iff_odd.mpr ha) (even_iff_two_dvd.mpr h2)
  exact Nat.Prime.coprime_pow_of_not_dvd Nat.prime_two hodd

/-- **The two-power recursion for the reduced sum `T` of *FI* (6.10)/(8.2).**

For `ν ≥ 2`, `a` odd and all `h₁, h₂ : ℤ`, the sum over the solutions `(x,y)` of `y² ≡ a x²`
modulo `2^ν` splits into the stratum where `x` is a unit — in which `y = ρ x` for a square root
`ρ` of `a` and the inner sum over the unit `x` is the Ramanujan sum `ram (2^ν) (h₁ + ρ.val h₂)` —
and the stratum where `x` is even, in which case `y` is even too and writing `x = 2x'`, `y = 2y'`
the sum becomes `Tsum (2^(ν-2))` with the halved characters, multiplied by `4`. -/
theorem Tsum_two_pow_recursion (ν : ℕ) (hν : 2 ≤ ν) (a h1 h2 : ℤ) (ha : Odd a) :
    Tsum (2 ^ ν) a h1 h2
      = (∑ r ∈ (Finset.range (2 ^ ν)).filter
            (fun r : ℕ => ((2 ^ ν : ℕ) : ℤ) ∣ (r : ℤ) ^ 2 - a),
          ram (2 ^ ν) (h1 + (r : ℤ) * h2))
        + (if (2 : ℤ) ∣ h1 ∧ (2 : ℤ) ∣ h2 then
            4 * Tsum (2 ^ (ν - 2)) a (h1 / 2) (h2 / 2) else 0) := by
  have hIU := two_pow_isUnit_of_odd ν (by omega) a ha
  have hrec := TsumD_recursion 2 ν Nat.prime_two hν a h1 h2 hIU
  have hself := TsumD_self 2 ν a h1 h2
  have hup := Tup_eq_sum_range_ram 2 ν Nat.prime_two a h1 h2
  have hlift := TsumD_lift 2 (ν - 1) (ν - 2) Nat.prime_two (by omega) a h1 h2
  rw [← hself, hrec, hup, hlift]
  have hsub : ν - 1 - (ν - 2) = 1 := by omega
  rw [hsub]
  norm_num

end

end Work.FIArea2
