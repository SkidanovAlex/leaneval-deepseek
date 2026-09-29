import Mathlib

namespace Work.C17

open Polynomial

/-- **Riccati denominators are squarefree.**

Suppose `A/B` (in lowest terms, `IsCoprime A B`, `B` monic) is a rational solution of the Riccati
equation `P2 * y' + P2 * y^2 + P1 * y + P0 = 0`, written in the cleared form

`P2 * (A' * B - A * B') + P2 * A^2 + P1 * A * B + P0 * B^2 = 0`,

and suppose that `P2` is squarefree (`rootMultiplicity α P2 ≤ 1` for every `α`). Then also `B` is
squarefree.

The proof is an order-of-vanishing argument. Assume `(X - C α)^2 ∣ B`, so that `B` has a pole of
order `m ≥ 2` at `α`. Writing `v = rootMultiplicity α`, and noting that `q := X - C α` satisfies
`q ∤ A` (coprimality) and `q ∣ B'` (derivative lowers the order), every one of the five cleared
terms except `P2 * A^2` is divisible by `q^(v P2 + 1)`:

* `P2 * A' * B` is divisible by `q^(v P2 + 2)`,
* `P2 * A * B'` is divisible by `q^(v P2 + 1)` (uses `q ∣ B'`),
* `P1 * A * B` and `P0 * B^2` are divisible by `q^(n+1)` because `n + 1 ≤ 2 ≤ 2m`.

Hence `q^(v P2 + 1) ∣ P2 * A^2`. But `v (P2 * A^2) = v P2 + 2 * v A = v P2`, since `q ∤ A`, so
`q^(v P2 + 1) ∤ P2 * A^2` — a contradiction. -/
theorem riccati_denom_squarefree {K : Type*} [Field K] [CharZero K]
    (P2 P1 P0 A B : Polynomial K) (hB : B.Monic) (hP2 : P2 ≠ 0) (hcop : IsCoprime A B)
    (hroot : ∀ α : K, Polynomial.rootMultiplicity α P2 ≤ 1)
    (h : P2 * (A.derivative * B - A * B.derivative) + P2 * A ^ 2 + P1 * A * B + P0 * B ^ 2 = 0)
    (α : K) : Polynomial.rootMultiplicity α B ≤ 1 := by
  rw [Polynomial.rootMultiplicity_le_iff hB.ne_zero α 1]
  intro hq2
  set q : Polynomial K := Polynomial.X - Polynomial.C α with hq
  set n : ℕ := Polynomial.rootMultiplicity α P2 with hn
  have hn1 : n ≤ 1 := by rw [hn]; exact hroot α
  have hBdvd : q ^ 2 ∣ B := by rw [hq]; simpa using hq2
  have hq_dvd_B : q ∣ B := by
    have h : q ^ 1 ∣ B := (pow_dvd_pow q (by norm_num : 1 ≤ 2)).trans hBdvd
    simpa using h
  have hBeval : B.eval α = 0 := by
    rw [hq, Polynomial.dvd_iff_isRoot] at hq_dvd_B
    exact hq_dvd_B
  have hAeval : A.eval α ≠ 0 := by
    rcases Polynomial.aeval_ne_zero_of_isCoprime hcop α with hA | hB'
    · simpa using hA
    · exact absurd hBeval hB'
  have hvmA : rootMultiplicity α A = 0 := by
    apply Polynomial.rootMultiplicity_eq_zero
    intro hr
    exact hAeval (Polynomial.IsRoot.def.mp hr)
  have hn1' : n + 1 ≤ 2 := by omega
  have hq_pow_n_dvd_B : q ^ (n + 1) ∣ B := (pow_dvd_pow q hn1').trans hBdvd
  have hB' : q ∣ B.derivative := by
    have h := Polynomial.pow_sub_one_dvd_derivative_of_pow_dvd (n := 2) hBdvd
    simpa using h
  have hq_pow_n : q ^ n ∣ P2 := by rw [hq, hn]; exact Polynomial.pow_rootMultiplicity_dvd P2 α
  have hT1 : q ^ (n + 1) ∣ P2 * (A.derivative * B) := by
    have h1 : q ^ n ∣ P2 := hq_pow_n
    have h2 : q ^ 2 ∣ A.derivative * B := dvd_mul_of_dvd_right hBdvd _
    have hh := mul_dvd_mul h1 h2
    rw [← pow_add] at hh
    exact (pow_dvd_pow q (by omega : n + 1 ≤ n + 2)).trans hh
  have hT2 : q ^ (n + 1) ∣ P2 * (A * B.derivative) := by
    have h1 : q ^ n ∣ P2 := hq_pow_n
    have h2 : q ^ 1 ∣ A * B.derivative := by simpa using dvd_mul_of_dvd_right hB' A
    have hh := mul_dvd_mul h1 h2
    rwa [← pow_add] at hh
  have hT3 : q ^ (n + 1) ∣ P1 * A * B := by
    have h := dvd_mul_of_dvd_right hq_pow_n_dvd_B (P1 * A)
    simpa [mul_assoc] using h
  have hT4 : q ^ (n + 1) ∣ P0 * B ^ 2 := by
    have h : q ^ (n+1) ∣ B * B := dvd_mul_of_dvd_left hq_pow_n_dvd_B B
    have h2 : q ^ (n+1) ∣ P0 * (B * B) := dvd_mul_of_dvd_right h P0
    simpa [pow_two] using h2
  have hsum : q ^ (n + 1) ∣
      -(P2 * (A.derivative * B - A * B.derivative) + P1 * A * B + P0 * B ^ 2) := by
    apply dvd_neg.mpr
    rw [mul_sub]
    exact dvd_add (dvd_add (dvd_sub hT1 hT2) hT3) hT4
  have heq : P2 * A ^ 2 =
      -(P2 * (A.derivative * B - A * B.derivative) + P1 * A * B + P0 * B ^ 2) := by
    linear_combination h
  have hP2A2 : q ^ (n + 1) ∣ P2 * A ^ 2 := by
    rw [heq]; exact hsum
  have hAne : A ≠ 0 := fun h0 => hAeval (by rw [h0]; simp)
  have hP2A2ne : P2 * A ^ 2 ≠ 0 := mul_ne_zero hP2 (pow_ne_zero 2 hAne)
  have hvm : rootMultiplicity α (P2 * A ^ 2) = n := by
    rw [Polynomial.rootMultiplicity_mul hP2A2ne]
    rw [pow_two, Polynomial.rootMultiplicity_mul (mul_ne_zero hAne hAne), hvmA, hn]
    ring
  have hnotdvd : ¬ (Polynomial.X - Polynomial.C α) ^ (n + 1) ∣ P2 * A ^ 2 :=
    (Polynomial.rootMultiplicity_le_iff hP2A2ne α n).mp (le_of_eq hvm)
  rw [hq] at hP2A2
  exact hnotdvd hP2A2

end Work.C17
