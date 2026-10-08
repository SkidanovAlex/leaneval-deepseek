import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.ASM.Defs
import Submission.Work.CORE2A.Defs
import Submission.Work.CORE3.Case1bEightNineDefs

set_option linter.unusedVariables false

namespace Work.CORE3

/-!
# `Work.CORE3.Case1bLeFourV1`

The first of the two alternatives in the `n = 6` analysis of `Work.CORE3.Case1bSevenLeFour`.

Setting: `Case1 B` in the subcase `V = O₂(Ĥ)` of type `(2,2)` with `|U| = 3`; `y` an involution
outside `Ĥ` whose coset carries six involutions, so `I := I_Ĥ(y) = {x ∈ Ĥ | y x y = x⁻¹}` has
six elements.  Given `a ∈ I` of order `3` and two distinct involutions `b₁, b₂ ∈ I` with
`b₁ b₂ = a` or `b₁ b₂ = a²`, we must derive a contradiction ("`v = 1`" in the design note).

The argument is elementary and uses nothing about `B` beyond
`invSetIn Hh y = {x | x ∈ Hh ∧ y * x * y = x⁻¹}`:

* since `y` inverts the involutions `b₁`, `b₂`, conjugation by `y` *fixes* their product,
  `y (b₁b₂) y = b₁⁻¹ b₂⁻¹ = b₁ b₂`;
* since `b₁b₂ ∈ {a, a²}` and `y` inverts both `a` and `a²`, conjugation by `y` *inverts* that
  product as well;
* hence `c := b₁b₂` satisfies `c = c⁻¹`, so `c² = 1` and `orderOf c ∣ 2`; but `c` has order `3`.
-/

/-- An element of order `2` is its own inverse, i.e. `x * x = 1`. -/
private lemma sq_eq_one_of_orderOf_two {G : Type} [Group G] {x : G} (h : orderOf x = 2) :
    x * x = 1 :=
  ((orderOf_eq_two_iff_mul_self x).mp h).1

/-- The square of an element of order `3` again has order `3`. -/
private theorem orderOf_sq_of_orderOf_three {G : Type} [Group G] {a : G} (ha : orderOf a = 3) :
    orderOf (a * a) = 3 := by
  have ha3p : a * a * a = 1 := by
    have h : a ^ 3 = 1 := by rw [← ha]; exact pow_orderOf_eq_one a
    rwa [pow_three, ← mul_assoc] at h
  have h6 : (a * a) ^ 3 = 1 := by
    rw [pow_three]
    have hkey : a * a * (a * a * (a * a)) = a * a * a * (a * a * a) := by group
    rw [hkey, ha3p, one_mul]
  have hdvd : orderOf (a * a) ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr h6
  have hne : orderOf (a * a) ≠ 1 := by
    intro h
    have h1 : a * a = 1 := orderOf_eq_one_iff.mp h
    have h2 : orderOf a ∣ 2 := by
      rw [orderOf_dvd_iff_pow_eq_one, pow_two]
      exact h1
    rw [ha] at h2
    exact absurd h2 (by decide)
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
  · exact absurd h hne
  · exact h

/-- If `orderOf a = 3` then neither `a` nor `a * a` is its own inverse: `c = c⁻¹` forces
`c * c = 1`, hence `orderOf c ∣ 2`, but `orderOf a = orderOf (a * a) = 3`. -/
private lemma not_inv_eq_of_orderOf_three {G : Type} [Group G] {a c : G} (ha : orderOf a = 3)
    (hc : c = a ∨ c = a * a) : c ≠ c⁻¹ := by
  intro h
  have hcc : c * c = 1 := (mul_self_eq_one_iff_eq_inv c).mpr h
  have hdvd : orderOf c ∣ 2 := by
    rw [orderOf_dvd_iff_pow_eq_one, pow_two]
    exact hcc
  rcases hc with h1 | h1
  · rw [h1, ha] at hdvd
    exact absurd hdvd (by decide)
  · rw [h1, orderOf_sq_of_orderOf_three ha] at hdvd
    exact absurd hdvd (by decide)

theorem Case1bLeFourV1 (G : Type) [Group G] [Finite G] (I : Work.CORE3.Case1Inputs)
    (hBc : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G) (h1 : Work.GW2.Case1 B)
    (D : Work.GW2.Case1bData B) (hU3 : Nat.card B.U = 3)
    {y : G} (hy2 : orderOf y = 2) (hyH : y ∉ B.Hhat)
    (h6 : Work.GW2.cosetInvCount B.Hhat y = 6)
    {a b1 b2 : G} (ha : a ∈ Work.CORE3.invSetIn B.Hhat y) (ha3 : orderOf a = 3)
    (hb1 : b1 ∈ Work.CORE3.invSetIn B.Hhat y) (hb1o : orderOf b1 = 2)
    (hb2 : b2 ∈ Work.CORE3.invSetIn B.Hhat y) (hb2o : orderOf b2 = 2) (h12 : b1 ≠ b2)
    (hv : b1 * b2 = a ∨ b1 * b2 = a * a) : False := by
  have hy : y * y = 1 := sq_eq_one_of_orderOf_two hy2
  have hb1sq : b1 * b1 = 1 := sq_eq_one_of_orderOf_two hb1o
  have hb2sq : b2 * b2 = 1 := sq_eq_one_of_orderOf_two hb2o
  have hb1inv : b1⁻¹ = b1 := inv_eq_of_mul_eq_one_right hb1sq
  have hb2inv : b2⁻¹ = b2 := inv_eq_of_mul_eq_one_right hb2sq
  -- `y` inverts `a` and `a * a`
  have hcy : ∀ c : G, (c = a ∨ c = a * a) → y * c * y = c⁻¹ := by
    intro c hc
    rcases hc with rfl | rfl
    · exact ha.2
    · calc y * (a * a) * y = (y * a * y) * (y * a * y) := by
            have h2 : (y * a * y) * (y * a * y) = y * a * (y * y) * a * y := by group
            rw [h2, hy, mul_one]
            group
        _ = a⁻¹ * a⁻¹ := by rw [ha.2]
        _ = (a * a)⁻¹ := by rw [mul_inv_rev]
  -- `y` fixes `b1 * b2`, since it inverts the involutions `b1`, `b2`
  have hfix : y * (b1 * b2) * y = b1 * b2 := by
    have h2 : (y * b1 * y) * (y * b2 * y) = y * b1 * (y * y) * b2 * y := by group
    have h3 : (y * b1 * y) * (y * b2 * y) = y * (b1 * b2) * y := by
      rw [h2, hy, mul_one]
      group
    rw [← h3, hb1.2, hb2.2, hb1inv, hb2inv]
  -- but `y` inverts `b1 * b2`, which is `a` or `a * a`
  have hinv' : y * (b1 * b2) * y = (b1 * b2)⁻¹ := by
    rcases hv with h | h
    · rw [h]; exact hcy a (Or.inl rfl)
    · rw [h]; exact hcy (a * a) (Or.inr rfl)
  have hcne : (b1 * b2) ≠ (b1 * b2)⁻¹ := by
    rcases hv with h | h
    · rw [h]; exact not_inv_eq_of_orderOf_three ha3 (Or.inl rfl)
    · rw [h]; exact not_inv_eq_of_orderOf_three ha3 (Or.inr rfl)
  exact hcne (hfix.symm.trans hinv')

end Work.CORE3
