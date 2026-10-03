/-
Copyright (c) 2026 The AnnalsChallenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AnnalsChallenge team
-/
import Mathlib
import Submission.Work.Analysis.IonescuWainger.Pset

/-!
# Coprimality of `∏_{p ∈ S} p^{D_ρ}` with a divisor of `Q_0^{(l)}`

Any `Q` dividing `Q_0^{(l)} = (N_0^{(l)}!)^{D_ρ}` has all its prime factors `≤ N_0^{(l)}`,
whereas every prime of the range `(N_0^{(l)}, 2^l]` is `> N_0^{(l)}`.  Hence
`∏_{p ∈ S} p^{D_ρ}` is coprime to `Q` for every `S` consisting of primes of that range.

This is the arithmetic fact behind the decomposition `q = Q w` of an element of `P_{≤l}`
with `Q ∣ Q_0^{(l)}` and `w ∈ W_{≤l}` (Appendix A of Krause–Mirek–Tao).
-/

namespace Work.KMTAreas

/-- The product `∏_{p ∈ S} p^{D_ρ}` of prime powers over a set of primes in the range
`(N_0^{(l)}, 2^l]` is coprime to every divisor `Q` of `Q_0^{(l)} = (N_0^{(l)}!)^{D_ρ}`. -/
theorem coprime_prod_primePow_iwQ0 {ρ : ℝ} {l : ℕ} {S : Finset ℕ}
    (hS : S ⊆ Work.Analysis.IonescuWainger.iwPrimeRange ρ l) {Q : ℕ}
    (hQ : Q ∣ Work.Analysis.IonescuWainger.iwQ0 ρ l) :
    Nat.Coprime (S.prod (fun p => p ^ Work.Analysis.IonescuWainger.iwD ρ)) Q := by
  apply Nat.Coprime.prod_left
  intro p hp
  -- `p` is a prime of the range `(N_0^{(l)}, 2^l]`.
  have hp' := hS hp
  rw [Work.Analysis.IonescuWainger.iwPrimeRange, Finset.mem_filter, Finset.mem_Icc] at hp'
  obtain ⟨⟨h1, _h2⟩, hprime⟩ := hp'
  have hN0 : Work.Analysis.IonescuWainger.iwN0 ρ l < p := Nat.lt_of_succ_le h1
  -- `p` cannot divide `Q_0^{(l)} = (N_0^{(l)}!)^{D_ρ}`, since it is larger than `N_0^{(l)}`.
  have hnot : ¬ p ∣ Work.Analysis.IonescuWainger.iwQ0 ρ l := by
    intro hdvd
    rw [Work.Analysis.IonescuWainger.iwQ0] at hdvd
    have hfac : p ∣ (Work.Analysis.IonescuWainger.iwN0 ρ l).factorial :=
      hprime.dvd_of_dvd_pow hdvd
    have hle : p ≤ Work.Analysis.IonescuWainger.iwN0 ρ l := (hprime.dvd_factorial).mp hfac
    exact absurd hle (Nat.not_le.mpr hN0)
  -- hence `p` is coprime to `Q_0^{(l)}`, to its divisor `Q`, and so is `p ^ D_ρ`.
  have hcop : Nat.Coprime p (Work.Analysis.IonescuWainger.iwQ0 ρ l) :=
    hprime.coprime_iff_not_dvd.mpr hnot
  exact (hcop.coprime_dvd_right hQ).pow_left _

end Work.KMTAreas
