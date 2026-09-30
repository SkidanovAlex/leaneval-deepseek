import Mathlib
import Submission.Work.BMF.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

/-- **Primes dividing the modulus contribute nothing.**  For every real `P`, every modulus
`q ≥ 1`, every Dirichlet character `χ` mod `q` and every real `t`, the sum over the primes of
`[P,2P]` that do **not** divide `q` equals the sum over all primes of `[P,2P]`:
`Σ_{p ∈ primesIn P (2P), p ∤ q} χ(p)p^{it} = Σ_{p ∈ primesIn P (2P)} χ(p)p^{it}`.

Reason: if `p` is a prime with `p ∣ q` then `(p : ZMod q)` is not a unit
(`ZMod.isUnit_iff_coprime` with `Nat.gcd_eq_left`, `p` prime so `p ≠ 1`), so `χ p = 0`
(`MulChar.map_nonunit` — note that in Mathlib a `DirichletCharacter`/`MulChar` is `0` on
non-units, even the trivial character); when `q = 1` no prime divides `q`.  Hence the
complementary sum vanishes termwise and `Finset.sum_filter_add_sum_filter_not` finishes. -/
theorem n4wa_filter_prime_not_dvd (P : ℝ) (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (t : ℝ) :
    ∑ p ∈ (Work.BMF.primesIn P (2 * P)).filter (fun p ↦ ¬ p ∣ q),
        χ (p : ZMod q) * (p : ℂ) ^ (Complex.I * t)
      = ∑ p ∈ Work.BMF.primesIn P (2 * P), χ (p : ZMod q) * (p : ℂ) ^ (Complex.I * t) := by
  -- The two sums have the same summand; enlarge the filtered range to the full range,
  -- the terms added back vanishing because a prime `p ∣ q` is not a unit modulo `q`.
  apply Finset.sum_subset (Finset.filter_subset (fun p => ¬ p ∣ q) _)
  intro p hp hnot
  -- `p` lies in the full range and was filtered out, so necessarily `p ∣ q`.
  have hdvd : p ∣ q := by
    by_contra hcon
    exact hnot (Finset.mem_filter.mpr ⟨hp, hcon⟩)
  have hp1 : p ∈ (Work.BMF.natIcc P (2 * P)).filter Nat.Prime := by
    simpa only [Work.BMF.primesIn] using hp
  have hprime : p.Prime := (Finset.mem_filter.mp hp1).2
  have hnu : ¬ IsUnit (p : ZMod q) := by
    rw [ZMod.isUnit_iff_coprime]
    intro hc
    exact ((hprime.coprime_iff_not_dvd).mp hc) hdvd
  rw [MulChar.map_nonunit χ hnu, zero_mul]

end Work.BMF
