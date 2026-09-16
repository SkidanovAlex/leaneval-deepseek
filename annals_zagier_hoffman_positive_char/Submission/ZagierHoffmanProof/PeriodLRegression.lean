import Submission.ZagierHoffmanProof.PeriodL

/-!
# Regression tests for the Anderson–Thakur period function over `F((y))`

Concrete instances of `PeriodL.lean` over the prime fields `ZMod 2` (`q = 2`, `d = 1`) and
`ZMod 3` (`q = 3`, `d = 2`).
-/

set_option autoImplicit false
open Filter Polynomial RatFunc
open scoped WithZero Topology
open LaurentSeries HahnSeries

namespace ZagierHoffmanPositiveChar

namespace PeriodLRegression

instance factCardZMod2 : Fact (Nat.Prime (Nat.card (ZMod 2))) :=
  ⟨by rw [Nat.card_eq_fintype_card, ZMod.card]; exact Nat.prime_two⟩

instance factCardZMod3 : Fact (Nat.Prime (Nat.card (ZMod 3))) :=
  ⟨by rw [Nat.card_eq_fintype_card, ZMod.card]; exact Nat.prime_three⟩

example : periodCard (ZMod 2) = 2 := by
  rw [periodCard, Nat.card_eq_fintype_card, ZMod.card]

example : periodD (ZMod 2) = 1 := by
  rw [periodD, Nat.card_eq_fintype_card, ZMod.card]; norm_num

example : periodD (ZMod 3) = 2 := by
  rw [periodD, Nat.card_eq_fintype_card, ZMod.card]; norm_num

example : Valued.v (kummerTheta (ZMod 2)) = WithZero.exp (1 : ℤ) := by
  rw [v_kummerTheta, Nat.card_eq_fintype_card, ZMod.card]; norm_num

example : Valued.v (kummerMu (ZMod 2)) = WithZero.exp (-2 : ℤ) := by
  rw [v_kummerMu, Nat.card_eq_fintype_card, ZMod.card]; norm_num

example : kummerMu (ZMod 2) ^ (Nat.card (ZMod 2) - 1)
    * kummerTheta (ZMod 2) ^ Nat.card (ZMod 2) = -1 :=
  kummerMu_pow_mul_theta_pow (ZMod 2)

/-- The period function over `F₂((y))` satisfies the functional equation. -/
example : (PowerSeries.X - PowerSeries.C ((kummerTheta (ZMod 2)) ^ periodCard (ZMod 2)))
    * frobTwist (R := LaurentSeries (ZMod 2)) (p := periodCard (ZMod 2)) 1
        (periodOmega (ZMod 2))
  = periodOmega (ZMod 2) :=
  periodDatum_twist_L (ZMod 2)

example : IsSmall (periodOmega (ZMod 2)) := isSmall_periodDatum_L (ZMod 2)

example : IsUnit (periodOmegaTate (ZMod 2)) := isUnit_periodOmegaTate (ZMod 2)

example : IsUnit (periodOmegaTate (ZMod 3)) := isUnit_periodOmegaTate (ZMod 3)

example : periodOmega (ZMod 2) * periodOmegaInv (ZMod 2) = 1 := periodOmega_mul_inv (ZMod 2)

end PeriodLRegression

end ZagierHoffmanPositiveChar
