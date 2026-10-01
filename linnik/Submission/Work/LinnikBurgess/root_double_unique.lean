import Mathlib
import Submission.Work.LinnikBurgess.cubic_phase_defs

namespace Work.LinnikBurgess

/-- A double root of the quadratic `linCoeff β γ δ` modulo a prime `p` is unique,
provided that the leading coefficient `3δ` is a unit modulo `p`.

Writing `f(X) = β + 2γX + 3δX²` for `linCoeff`, the Taylor expansion at the root `r`
gives the integer identity
`f(t) = f(r) + 2(γ + 3δr)(t - r) + 3δ(t - r)²`.
Since `p ∣ f(r)` (`hroot`) and `p ∣ γ + 3δr` (`hdbl`), we find `p ∣ 3δ(r' - r)²`
for any other root `r'`; as `p` is prime and `p ∤ 3δ`, this forces `p ∣ r' - r`, and
`r' = r` follows from `0 ≤ r, r' < p`. -/
theorem root_double_unique (p : ℕ) [Fact p.Prime] (β γ δ : ℤ) (h3δ : ¬ (p : ℤ) ∣ 3 * δ)
    (r : ℕ) (hr : r < p) (hroot : (p : ℤ) ∣ Work.LinnikBurgess.linCoeff β γ δ r)
    (hdbl : (p : ℤ) ∣ Work.LinnikBurgess.quadCoeff γ δ r) :
    ∀ r' ∈ Finset.range p, (p : ℤ) ∣ Work.LinnikBurgess.linCoeff β γ δ r' → r' = r := by
  intro r' hr' hroot'
  rw [Finset.mem_range] at hr'
  have hpprime : Prime (p : ℤ) := (Nat.prime_iff_prime_int.mp (Fact.out : p.Prime))
  have hγ : (p : ℤ) ∣ γ + 3 * δ * (r : ℤ) := by simpa only [quadCoeff] using hdbl
  -- Taylor expansion of `f` at `r`
  have hkey : linCoeff β γ δ r'
      = 3 * δ * ((r' : ℤ) - (r : ℤ)) ^ 2
        + 2 * (γ + 3 * δ * (r : ℤ)) * ((r' : ℤ) - (r : ℤ)) + linCoeff β γ δ r := by
    simp only [linCoeff]; ring
  have hB : (p : ℤ) ∣ 2 * (γ + 3 * δ * (r : ℤ)) * ((r' : ℤ) - (r : ℤ)) :=
    dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hγ 2) _
  -- the leading term is divisible by `p`
  have hA : (p : ℤ) ∣ 3 * δ * ((r' : ℤ) - (r : ℤ)) ^ 2 := by
    have heq : 3 * δ * ((r' : ℤ) - (r : ℤ)) ^ 2
        = linCoeff β γ δ r' - 2 * (γ + 3 * δ * (r : ℤ)) * ((r' : ℤ) - (r : ℤ))
          - linCoeff β γ δ r := by rw [hkey]; ring
    rw [heq]
    exact dvd_sub (dvd_sub hroot' hB) hroot
  rcases (hpprime.dvd_mul.mp hA) with h3 | hsq
  · exact absurd h3 h3δ
  · -- `p ∣ (r' - r)²`, hence `p ∣ r' - r`
    have hlin : (p : ℤ) ∣ ((r' : ℤ) - (r : ℤ)) := by
      rcases (hpprime.dvd_mul.mp (by simpa only [pow_two] using hsq)) with h | h
      · exact h
      · exact h
    have hmod : r' ≡ r [MOD p] := by
      rw [Nat.modEq_iff_dvd]
      have : (r : ℤ) - (r' : ℤ) = -((r' : ℤ) - (r : ℤ)) := by ring
      rw [this]
      exact dvd_neg.mpr hlin
    exact Nat.ModEq.eq_of_lt_of_lt hmod hr' hr

end Work.LinnikBurgess
