import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.gaussSum_normSq_eq_conductor

set_option linter.unusedVariables false

namespace Commons.NumberTheory.DirichletCharacter

/-- A Dirichlet character `χ` of level `q` can be recovered from its primitive character by
Möbius inversion over the divisors of `q / χ.conductor`: the coprimality indicator of `n` with
`q` differs from that with `q / χ.conductor` only where the primitive character already vanishes,
so
`χ(n) = ∑_{c ∣ q / χ.conductor} μ(c) · χ.primitiveCharacter(n) · [c ∣ n]`. -/
theorem char_eq_moebius_sum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (n : ℕ) :
    (χ (n : ZMod q) : ℂ)
      = ∑ c ∈ (q / χ.conductor).divisors,
          (ArithmeticFunction.moebius c : ℂ) * (χ.primitiveCharacter (n : ZMod χ.conductor) : ℂ)
            * (if c ∣ n then (1 : ℂ) else 0) := by
  have hdvd : χ.conductor ∣ q := χ.conductor_dvd_level
  have hmul : χ.conductor * (q / χ.conductor) = q := Nat.mul_div_cancel' hdvd
  have hm0 : q / χ.conductor ≠ 0 := by
    intro h; rw [h, mul_zero] at hmul
    exact (NeZero.ne q) hmul.symm
  rw [coe_char_eq q χ n]
  rw [show (∑ c ∈ (q / χ.conductor).divisors,
        (ArithmeticFunction.moebius c : ℂ) * (χ.primitiveCharacter (n : ZMod χ.conductor) : ℂ)
          * (if c ∣ n then (1 : ℂ) else 0))
      = (χ.primitiveCharacter (n : ZMod χ.conductor) : ℂ)
        * (∑ c ∈ (q / χ.conductor).divisors,
            (ArithmeticFunction.moebius c : ℂ) * (if c ∣ n then (1 : ℂ) else 0)) from by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun c _ => by ring]
  rw [sum_moebius_mul_ite_dvd n (q / χ.conductor) hm0]
  have hψ0 : ¬ Nat.Coprime n χ.conductor →
      (χ.primitiveCharacter (n : ZMod χ.conductor) : ℂ) = 0 := by
    intro hnf
    rw [MulChar.map_nonunit]
    rwa [ZMod.isUnit_iff_coprime]
  by_cases hm : Nat.Coprime n (q / χ.conductor)
  · rw [if_pos hm]
    by_cases hq : Nat.Coprime n q
    · rw [if_pos hq]
    · rw [if_neg hq, hψ0 (by
        intro hf'
        exact hq (by rw [← hmul]; exact hf'.mul_right hm))]
      ring
  · rw [if_neg hm]
    by_cases hq : Nat.Coprime n q
    · exact absurd (hq.coprime_dvd_right (Nat.div_dvd_of_dvd hdvd)) hm
    · rw [if_neg hq]

end Commons.NumberTheory.DirichletCharacter
