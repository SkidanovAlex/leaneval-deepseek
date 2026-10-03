/-
The arithmetic bridge between the workspace's concrete Ionescu–Wainger frequency set
`iwArithFreqs ρ l` and Tao's major arc parameter set `Σ_{≤κ}` at the *large* scales
`l > C⁰_ρ`.

For `l > C⁰_ρ` the IW denominator set is

  `P_{≤l} = { Q w : Q ∣ Q_0^{(l)} = (N_0^{(l)}!)^{D_ρ}, w ∈ W_{≤l} }`,

where `W_{≤l}` consists of the products of at most `D_ρ` *distinct* primes from
`(N_0^{(l)}, 2^l]`, each to a power in `[1, D_ρ]`.

Hence a frequency `α ∈ (ℚ/ℤ)_{≤l}` is killed by some `q = Q w` of that shape.  The Tao
denominator set

  `S = {Q_0^{(l)}} ∪ {p^{D_ρ} : p ∈ (N_0^{(l)}, 2^l] prime}`

then contains the subset

  `A = {Q_0^{(l)}} ∪ {p^{D_ρ} : p ∣ w}`,

of cardinality at most `1 + (number of distinct prime factors of w) ≤ 1 + D_ρ`, whose
product `Q_0^{(l)} · ∏_{p ∣ w} p^{D_ρ}` is a multiple of `Q w` (because `Q ∣ Q_0^{(l)}`
and `w ∣ ∏_{p ∣ w} p^{D_ρ}`, the exponents of `w` being at most `D_ρ`).  Therefore
`α ∈ Σ_{≤D_ρ+1}(S)`, which is the asserted containment.

The complementary regime `l ≤ C⁰_ρ` (where `P_{≤l} = [2^l]`) is
`Work.KMTAreas.iwArithFreqs_subset_sigmaLe_small` in `tao_bridge.lean`.
-/
import Mathlib
import Submission.Work.KMTAreas.iw_family

namespace Work.KMTAreas

open Work.Analysis.IonescuWainger

/-- `N_0^{(l)} = ⌊2^{ρl/2}⌋ + 1` is positive. -/
theorem iwN0_one_le (ρ : ℝ) (l : ℕ) : 1 ≤ iwN0 ρ l := Nat.le_add_left 1 _

/-- The product `Q_0^{(l)} = (N_0^{(l)}!)^{D_ρ}` is never a prime power `p^{D_ρ}` with
`p` a prime of the range `(N_0^{(l)}, 2^l]`.  This is what makes the element `Q_0^{(l)}`
of the Tao denominator set `S` disjoint from the elements `p^{D_ρ}`, `p` prime in the
range (so that `A` above really has cardinality `1 + #(primes of w)`). -/
theorem iwQ0_ne_pow_iwD {ρ : ℝ} {l p : ℕ} (hp : p ∈ iwPrimeRange ρ l) :
    iwQ0 ρ l ≠ p ^ iwD ρ := by
  intro h
  have hD : iwD ρ ≠ 0 := Nat.succ_ne_zero _
  rw [iwQ0] at h
  have hp_eq : p = (iwN0 ρ l).factorial := Nat.pow_left_injective hD h.symm
  have hgt : iwN0 ρ l < p := (IwMono.mem_iwPrimeRange_iff.mp hp).1
  have hprime : p.Prime := (IwMono.mem_iwPrimeRange_iff.mp hp).2.2
  by_cases h1 : iwN0 ρ l ≤ 1
  · have hfac : (iwN0 ρ l).factorial = 1 := by
      have hge : 1 ≤ iwN0 ρ l := iwN0_one_le ρ l
      interval_cases iwN0 ρ l <;> simp
    rw [hfac] at hp_eq
    exact hprime.ne_one hp_eq
  · have h2 : 2 ≤ iwN0 ρ l := by omega
    have h2dvd : 2 ∣ p := by
      rw [hp_eq]
      exact Nat.dvd_factorial (by norm_num) h2
    have h2p : 2 = p := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hprime).mp h2dvd
    omega

end Work.KMTAreas
