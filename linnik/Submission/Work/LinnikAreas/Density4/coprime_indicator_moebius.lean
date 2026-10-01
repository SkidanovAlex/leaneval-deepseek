import Mathlib

namespace Work.LinnikAreas.Density4

open Finset

/-- The Möbius sum over the divisors of `n`, as a real number: `Σ_{d ∣ n} μ(d) = [n = 1]`.
This is `μ * ζ = 1` evaluated at `n`, since `(f * ζ) n = Σ_{d ∣ n} f d`. -/
lemma sum_moebius_divisors_eq_indicator (n : ℕ) :
    (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ)) = if n = 1 then 1 else 0 := by
  have h := congrArg (fun (f : ArithmeticFunction ℝ) => f n)
    (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℝ))
  simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply,
    ArithmeticFunction.intCoe_apply] at h
  exact h

/-- The Möbius expansion of the coprimality indicator: for `r ≥ 1` and any real `F`,
`[m ⊥ r]·F = Σ_{d ∣ r} [d ∣ m]·μ(d)·F`. (The sum over `d ∣ r` with `d ∣ m` is the sum over the
divisors of `gcd m r`, whose Möbius sum is `[gcd m r = 1]`.) -/
theorem coprime_indicator_moebius (m r : ℕ) (hr : 1 ≤ r) (F : ℝ) :
    (if Nat.Coprime m r then F else 0)
      = ∑ d ∈ r.divisors, if d ∣ m then (ArithmeticFunction.moebius d : ℝ) * F else 0 := by
  have hr0 : r ≠ 0 := by omega
  have hg0 : Nat.gcd m r ≠ 0 := (Nat.gcd_pos_of_pos_right m (by omega)).ne'
  -- the divisors of `r` that also divide `m` are exactly the divisors of `gcd m r`
  have hfilter : r.divisors.filter (· ∣ m) = (Nat.gcd m r).divisors := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
    constructor
    · rintro ⟨⟨hdvdr, _⟩, hdvdm⟩
      exact ⟨⟨hdvdm, hdvdr⟩, hg0⟩
    · rintro ⟨⟨hdvdm, hdvdr⟩, _⟩
      exact ⟨⟨hdvdr, hr0⟩, hdvdm⟩
  -- factor `F` out of the summand
  have h1 : (∑ d ∈ r.divisors, (if d ∣ m then (ArithmeticFunction.moebius d : ℝ) * F else 0))
      = ∑ d ∈ r.divisors, (if d ∣ m then (ArithmeticFunction.moebius d : ℝ) else 0) * F := by
    refine Finset.sum_congr rfl (fun d _ => ?_)
    by_cases h : d ∣ m <;> simp [h]
  rw [h1, ← Finset.sum_mul, ← Finset.sum_filter, hfilter, sum_moebius_divisors_eq_indicator]
  by_cases h : Nat.gcd m r = 1 <;> simp [Nat.coprime_iff_gcd_eq_one, h]

end Work.LinnikAreas.Density4
