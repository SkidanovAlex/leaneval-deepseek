import Mathlib
import Submission.Work.FIArea7.FIsymbols

namespace Work.FIArea7

/-- ***FI* (17.1), second step: `φ(d)/d = Σ_{b ∣ d} μ(b)/b`.**

The reflected weight of §17 (`Work.FIArea7.Wcut_reflection`) is `(φ(m)/m)(z₂/z₁|m)` with
`m = M/(4e)`; the paper replaces it by `Σ_{b ∣ m} μ(b)/b`, which is what turns the sum over the
complementary divisors `e < X` into the congruence condition `Δ ≡ 0 (mod 4bd)` of (17.9).

Stated over the reals: for `d ≥ 1`,

  `φ(d)/d = Σ_{b ∈ d.divisors} μ(b)/b`.

(Equivalently `φ(d) = Σ_{b ∣ d} μ(b)·(d/b)`, the Möbius inversion of `Σ_{c ∣ d} φ(c) = d`,
Mathlib's `Nat.sum_totient`; `Nat.totient d` is the `ℕ`-valued totient and the equality is in `ℝ`,
where `d ≠ 0` lets one cancel.  `ArithmeticFunction.moebius : ArithmeticFunction ℤ` coerces to `ℝ`
as in `ArithmeticFunction.sum_moebius_mul_log_eq`.)  In the application the divisor is
`m = M/(4e)`, so the `b`-sum is over the `b` with `4be ∣ M` — exactly the summation condition
of (17.1). -/
theorem totient_div_eq_sum_moebius {d : ℕ} (hd : 0 < d) :
    (Nat.totient d : ℝ) / d
      = ∑ b ∈ d.divisors, (ArithmeticFunction.moebius b : ℝ) / b := by
  -- Möbius inversion of `∑_{c ∣ n} φ c = n` (`Nat.sum_totient`): over `ℝ`,
  -- `φ n = ∑_{b ∣ n} μ b · α(n/b)`, where `α` is the identity.
  have hmoeb : ∀ n > 0, ∑ x ∈ n.divisorsAntidiagonal,
      (ArithmeticFunction.moebius x.fst : ℝ) * (x.snd : ℝ) = (Nat.totient n : ℝ) :=
    (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
      (f := fun n => (Nat.totient n : ℝ)) (g := fun n => (n : ℝ))).1
      (fun n _ => by exact_mod_cast Nat.sum_totient n)
  -- Rewrite the antidiagonal sum as a sum over `b ∣ d` of `μ b · (d/b)`.
  have hkey : ∑ b ∈ d.divisors, (ArithmeticFunction.moebius b : ℝ) * ((d / b : ℕ) : ℝ)
      = (Nat.totient d : ℝ) := by
    have h := hmoeb d hd
    rw [Nat.sum_divisorsAntidiagonal
      (fun i j => (ArithmeticFunction.moebius i : ℝ) * (j : ℝ))] at h
    exact h
  rw [eq_comm]
  calc
    ∑ b ∈ d.divisors, (ArithmeticFunction.moebius b : ℝ) / b
        = ∑ b ∈ d.divisors, (ArithmeticFunction.moebius b : ℝ) * ((d / b : ℕ) : ℝ) / d := by
          apply Finset.sum_congr rfl
          intro b hb
          have hbd : b ∣ d := (Nat.mem_divisors.1 hb).1
          have hbpos : 0 < b := Nat.pos_of_dvd_of_pos hbd hd
          have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast hbpos.ne'
          have hcast : ((d / b : ℕ) : ℝ) = (d : ℝ) / (b : ℝ) :=
            Nat.cast_div hbd hb0
          rw [hcast]
          field_simp
    _ = (∑ b ∈ d.divisors, (ArithmeticFunction.moebius b : ℝ) * ((d / b : ℕ) : ℝ)) / d := by
          rw [Finset.sum_div]
    _ = (Nat.totient d : ℝ) / d := by rw [hkey]

end Work.FIArea7
