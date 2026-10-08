import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE3.Case1bEightNineDefs

/-!
# Bender (6) for `n = 3`: the inversion set of a `3`-coset

Bender 1981, §3, p. 224.  If `Ĥ` is a subgroup, `y ∉ Ĥ` an involution and the left coset `y Ĥ`
contains exactly three involutions, then the inverted set `I_Ĥ(y) = {z ∈ Ĥ | y z y = z⁻¹}`
equals `{1, x, x⁻¹}` with `orderOf x = 3`.

Equivalently (the form needed by the `J₃`-argument): an involution `y ∉ Ĥ` whose coset contains
exactly three involutions inverts a *unique* subgroup of order three of `Ĥ`, and nothing else
of `Ĥ` except that subgroup's elements.

The counting input `(invSetIn Hh y).ncard = cosetInvCount Hh y` and the structural analysis of a
three-element inverted set (`Work.CORE3.invSetIn_eq_three_of_ncard_three`) are the work of
`Submission/Work/CORE3/Case1bEightNineDefs.lean`; this module only assembles them into the
`J₃`-shape used downstream (`Work.CORE3.JthreeStructure`, `Work.CORE3.Case1bThree`).
-/

namespace Work.CORE3

open Work.GW2

/-- Bender 1981 §3, (6) for `n = 3`.  An involution `y ∉ Hh` whose coset `y Hh` contains exactly
three involutions inverts exactly one cyclic subgroup of order three of `Hh`. -/
theorem InvSetThreeSubgroup : ∀ {G : Type} [Group G] [Finite G] (Hh : Subgroup G) (y : G),
    y * y = 1 → y ∉ Hh → Work.GW2.cosetInvCount Hh y = 3 →
    ∃ x ∈ Hh, orderOf x = 3 ∧ y * x * y = x⁻¹ ∧
      ∀ z ∈ Hh, y * z * y = z⁻¹ → z = 1 ∨ z = x ∨ z = x⁻¹ := by
  intro G _ _ Hh y hy hyH hcount
  -- `cosetInvCount = 3` is `|I_Ĥ(y)| = 3`
  have h3 : (invSetIn Hh y).ncard = 3 := by
    rw [ncard_invSetIn_eq_cosetInvCount Hh y hy hyH]
    exact hcount
  -- a three-element inverted set is `{1, a, a²}` with `a³ = 1`, `a ≠ 1`
  obtain ⟨a, ha1, ha3, hI⟩ := invSetIn_eq_three_of_ncard_three (Hh := Hh) hy h3
  have hamem : a ∈ invSetIn Hh y := by rw [hI]; simp
  have hainv : a⁻¹ = a * a :=
    inv_eq_of_mul_eq_one_right (a := a) (b := a * a) (by rw [← mul_assoc]; exact ha3)
  have hprime3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf a = 3 := by
    have hp : a ^ 3 = 1 := by
      rw [pow_succ, pow_two]
      exact ha3
    exact orderOf_eq_prime (p := 3) (hp := hprime3) hp ha1
  refine ⟨a, hamem.1, hord, hamem.2, ?_⟩
  intro z hzH hzy
  have hzm : z ∈ invSetIn Hh y := ⟨hzH, hzy⟩
  rw [hI] at hzm
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hzm
  rcases hzm with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (by rw [h]; exact hainv.symm))

end Work.CORE3
