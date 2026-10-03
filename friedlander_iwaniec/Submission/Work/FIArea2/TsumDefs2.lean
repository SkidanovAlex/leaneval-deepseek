import Mathlib
import Submission.Work.FIArea2.TsumDefs
import Submission.Work.FIArea2.ramanujan_primepow

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea2

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## The local (prime-power) recursion for `T`

`Tsum (p^ν) a h₁ h₂` is the sum over the solutions `(x,y)` of `y² = a x²` in `ZMod (p^ν)` of the
character `e((x h₁ + y h₂)/p^ν)`.  Classifying the solutions by the `p`-adic valuation of `x` splits
it into

* the **unit part** `Tup p ν a h₁ h₂`, where `x` is a unit and `y = ρ x` for a square root `ρ` of
  `a`; it is a sum of Ramanujan sums `ram (p^ν) (h₁ + ρ.val h₂)` over the roots `ρ`, and
* the **non-unit part**, where `p ∣ x` and `p ∣ y`: writing `x = p x'`, `y = p y'` this is a sum of
  the same shape with modulus `p^(ν-1)` and congruence `p^(ν-2)`; since that congruence only
  depends on `x', y'` modulo `p^(ν-2)`, it equals `p² Tsum (p^(ν-2))` on the divided characters
  once `p ∣ h₁, p ∣ h₂`.

We also introduce the intermediate sum `TsumD p j m`, over `(x,y) ∈ (ZMod (p^j))²` with the weaker
congruence `p^m ∣ y² - a x²`, for which the "lifting" identity
`TsumD p j m = p^(2(j-m)) [p^(j-m) ∣ h₁][p^(j-m) ∣ h₂] Tsum (p^m)` is clean.
-/

/-- The local sum with the congruence `p^m ∣ y² - a x²` in the exponents `(x,y) ∈ (ZMod (p^j))²`. -/
noncomputable def TsumD (p j m : ℕ) [NeZero (p ^ j)] (a h1 h2 : ℤ) : ℂ :=
  ∑ x : ZMod (p ^ j), ∑ y : ZMod (p ^ j),
    (if ((p ^ m : ℕ) : ℤ) ∣ ((y.val : ℤ) ^ 2 - a * (x.val : ℤ) ^ 2) then
      E ((((x.val : ℤ) * h1 + (y.val : ℤ) * h2 : ℤ) : ℝ) / ((p ^ j : ℕ) : ℝ))
     else 0)

/-- The `x`-unit part of the local sum: a sum of Ramanujan sums over the square roots of `a`. -/
noncomputable def Tup (p ν : ℕ) [NeZero (p ^ ν)] (a h1 h2 : ℤ) : ℂ :=
  ∑ ρ ∈ (Finset.univ.filter (fun ρ : ZMod (p ^ ν) => ρ ^ 2 = (a : ZMod (p ^ ν)))),
    ram (p ^ ν) (h1 + (ρ.val : ℤ) * h2)

/-- `n ∣ y.val² - a x.val²` (in `ℤ`) is the congruence `y² = a x²` in `ZMod n`. -/
lemma zmod_cond_iff (n : ℕ) [NeZero n] (a : ℤ) (x y : ZMod n) :
    ((n : ℤ) ∣ ((y.val : ℤ) ^ 2 - a * (x.val : ℤ) ^ 2)) ↔ y ^ 2 = (a : ZMod n) * x ^ 2 := by
  have h1 : ((y.val : ℕ) : ZMod n) = y := ZMod.natCast_zmod_val y
  have h2 : ((x.val : ℕ) : ZMod n) = x := ZMod.natCast_zmod_val x
  constructor
  · intro h
    have h' : (((y.val : ℤ) ^ 2 - a * (x.val : ℤ) ^ 2 : ℤ) : ZMod n) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact h
    push_cast at h'
    rw [h1, h2] at h'
    linear_combination h'
  · intro h
    have h' : (((y.val : ℤ) ^ 2 - a * (x.val : ℤ) ^ 2 : ℤ) : ZMod n) = 0 := by
      push_cast
      rw [h1, h2]
      linear_combination h
    rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at h'

/-- `TsumD` at `m = j` is the original sum `Tsum`. -/
theorem TsumD_self (p j : ℕ) [NeZero (p ^ j)] (a h1 h2 : ℤ) :
    TsumD p j j a h1 h2 = Tsum (p ^ j) a h1 h2 := by
  unfold TsumD Tsum
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  by_cases h : ((p ^ j : ℕ) : ℤ) ∣ ((y.val : ℤ) ^ 2 - a * (x.val : ℤ) ^ 2)
  · rw [if_pos h, if_pos ((zmod_cond_iff (p ^ j) a x y).mp h)]
  · rw [if_neg h, if_neg (fun hh => h ((zmod_cond_iff (p ^ j) a x y).mpr hh))]

/-- `Tsum` at the modulus `1`. -/
lemma Tsum_one (a h1 h2 : ℤ) : Tsum 1 a h1 h2 = 1 := by
  unfold Tsum
  have h : (∑ x : ZMod 1, ∑ y : ZMod 1,
      (if y ^ 2 = (a : ZMod 1) * x ^ 2 then
        E ((((x.val : ℤ) * h1 + (y.val : ℤ) * h2 : ℤ) : ℝ) / ((1 : ℕ) : ℝ)) else 0))
      = ∑ _x : ZMod 1, ∑ _y : ZMod 1, (1 : ℂ) := by
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    have hx : x = 0 := Subsingleton.elim x 0
    have hy : y = 0 := Subsingleton.elim y 0
    subst hx; subst hy
    simp [E_zero]
  rw [h]
  simp

end

end Work.FIArea2
