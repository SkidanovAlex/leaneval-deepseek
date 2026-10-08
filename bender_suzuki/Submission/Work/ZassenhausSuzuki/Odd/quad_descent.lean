import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Quadratic descent: `X ^ 2 + Y ^ 2 + 8 = K * X * Y + 4 * X + 4 * Y` has no solutions for `K ≥ 6`

This is the arithmetic (Vieta-jumping) heart of the Suzuki/Bender numerical obstruction: the
fixed-point equation of the quadratic map `f(t) = t^2 - K t + 4` (equivalently the descent on
solutions of `x^2 + y^2 + 8 = K x y + 4 x + 4 y`) admits no positive integer solution once
`K ≥ 6`.

The argument: a minimal positive solution (ordered so that `Y ≤ X`) is replaced, in the regime
`Y ≥ 3`, by the conjugate root `X' = K Y + 4 - X` of the quadratic in `X`.  Since
`X · X' = Y^2 - 4Y + 8` and `Y^2 - 4Y + 8 < X^2`, one gets `0 < X' < X`, contradicting
minimality.  The remaining cases `Y = 1, 2` are finite (they force `X ∣ 5`, resp. `X ∣ 4`).
-/

namespace Work.ZassenhausSuzuki.Odd

/-- The conjugate-root descent step.  If `(A, B)` is a positive solution with `B ≥ 3` and
`B ≤ A`, then the conjugate root `A' = K * B + 4 - A` of the quadratic `t^2 - (K*B+4)t + B^2 - 4B + 8`
is again a positive solution with a strictly smaller coordinate sum. -/
private lemma descent (A B K : ℕ) (hA : 1 ≤ A) (hB : 3 ≤ B) (hBA : B ≤ A)
    (h : A ^ 2 + B ^ 2 + 8 = K * A * B + 4 * A + 4 * B) :
    ∃ A' : ℕ, 1 ≤ A' ∧ A' + B < A + B ∧ A' ^ 2 + B ^ 2 + 8 = K * A' * B + 4 * A' + 4 * B := by
  have hkey : (A : ℤ) * ((K : ℤ) * (B:ℤ) + 4 - (A:ℤ)) = (B : ℤ) ^ 2 - 4 * (B:ℤ) + 8 := by
    have hz : ((A:ℤ))^2 + (B:ℤ)^2 + 8 = (K:ℤ)*(A:ℤ)*(B:ℤ) + 4*(A:ℤ)+4*(B:ℤ) := by
      exact_mod_cast h
    nlinarith [hz]
  have hltz : (A:ℤ) < (K:ℤ)*(B:ℤ)+4 := by
    have hp : (0:ℤ) < (B:ℤ)^2 - 4*(B:ℤ)+8 := by nlinarith [hB]
    have hA0 : (0:ℤ) < (A:ℤ) := by exact_mod_cast hA
    nlinarith [hkey, hp, hA0]
  have hlt : A < K*B+4 := by exact_mod_cast hltz
  have hA'z : (((K*B+4-A : ℕ)):ℤ) = (K:ℤ)*(B:ℤ)+4 - (A:ℤ) := by
    rw [Nat.cast_sub (le_of_lt hlt)]
    push_cast
    ring
  refine ⟨K*B+4-A, ?_, ?_, ?_⟩
  · omega
  · have hsq : (B:ℤ)^2 - 4*(B:ℤ) + 8 < (A:ℤ)^2 := by nlinarith [hBA, hB]
    have hmul : (A:ℤ)*(((K*B+4-A : ℕ)):ℤ) = (B:ℤ)^2 - 4*(B:ℤ)+8 := by
      rw [hA'z]; exact hkey
    have hlt2z : (((K*B+4-A : ℕ)):ℤ) < (A:ℤ) := by
      have hA0 : (0:ℤ) < (A:ℤ) := by exact_mod_cast hA
      nlinarith [hmul, hsq, hA0]
    have hlt2 : K*B+4-A < A := by exact_mod_cast hlt2z
    omega
  · have key2 : (((K*B+4-A : ℕ)):ℤ)^2 + (B:ℤ)^2 + 8
        = (K:ℤ)*(((K*B+4-A : ℕ)):ℤ)*(B:ℤ) + 4*(((K*B+4-A : ℕ)):ℤ) + 4*(B:ℤ) := by
      rw [hA'z]
      nlinarith [hkey]
    exact_mod_cast key2

/-- No positive integer solution of the quadratic descent equation exists for `K ≥ 6`.

Proof by strong induction on `X + Y`: a minimal solution is conjugated to a smaller one
(`descent`), and the base region `Y ≤ 2` is finite. -/
private lemma no_sol : ∀ m, ∀ X Y K : ℕ, X + Y = m → 1 ≤ X → 1 ≤ Y → 6 ≤ K →
    X ^ 2 + Y ^ 2 + 8 ≠ K * X * Y + 4 * X + 4 * Y := by
  intro m
  refine Nat.strong_induction_on m ?_
  intro n ih X Y K hsum hX hY hK h
  have core : ∀ A B : ℕ, 1 ≤ A → 1 ≤ B → B ≤ A → A + B = n →
      6 ≤ K → A ^ 2 + B ^ 2 + 8 ≠ K * A * B + 4 * A + 4 * B := by
    intro A B hA hB hBA hsumAB hK hAB
    by_cases hB2 : B ≤ 2
    · interval_cases B
      · -- `B = 1`: the equation forces `A ∣ 5`, hence `A ≤ 5` and `K = 2`.
        have heq : (K+4)*A = A^2 + 5 := by nlinarith [hAB]
        have hdiv5 : A ∣ 5 := by
          have h5 : A ∣ A^2 + 5 := by rw [← heq]; exact dvd_mul_left A (K+4)
          have h3 : A ∣ A^2 := ⟨A, by ring⟩
          have := Nat.dvd_sub h5 h3
          simpa using this
        have hAle : A ≤ 5 := Nat.le_of_dvd (by norm_num) hdiv5
        interval_cases A <;> omega
      · -- `B = 2`: the equation forces `A ∣ 4`, hence `A ≤ 4`, again impossible.
        have heq : (2*K+4)*A = A^2 + 4 := by nlinarith [hAB]
        have hdiv4 : A ∣ 4 := by
          have h4 : A ∣ A^2 + 4 := by rw [← heq]; exact dvd_mul_left A (2*K+4)
          have h3 : A ∣ A^2 := ⟨A, by ring⟩
          have := Nat.dvd_sub h4 h3
          simpa using this
        have hAle : A ≤ 4 := Nat.le_of_dvd (by norm_num) hdiv4
        interval_cases A <;> omega
    · -- `B ≥ 3`: descend to the conjugate root and contradict minimality.
      have hB3 : 3 ≤ B := by omega
      obtain ⟨A', hA'1, hsumlt, hA'eq⟩ := descent A B K hA hB3 hBA hAB
      exact ih (A' + B) (by omega) A' B K rfl hA'1 hB hK hA'eq
  rcases le_total Y X with hyx | hxy
  · exact core X Y hX hY hyx hsum hK h
  · -- the equation is symmetric, so swap to put the larger coordinate first.
    have hs : Y ^ 2 + X ^ 2 + 8 = K * Y * X + 4 * Y + 4 * X := by nlinarith [h]
    exact core Y X hY hX hxy (by omega) hK hs

lemma quad_descent (X Y K : ℕ) (hX : 1 ≤ X) (hY : 1 ≤ Y) (hK : 6 ≤ K)
    (h : X ^ 2 + Y ^ 2 + 8 = K * X * Y + 4 * X + 4 * Y) : False :=
  no_sol (X + Y) X Y K rfl hX hY hK h

end Work.ZassenhausSuzuki.Odd
