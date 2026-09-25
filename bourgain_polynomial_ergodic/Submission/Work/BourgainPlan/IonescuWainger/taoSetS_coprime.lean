import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.TaoDefs

namespace Work.BourgainPlan.IonescuWainger

open Finset
open scoped BigOperators

/-- Membership characterisation of Tao's set of large prime powers. -/
private lemma mem_largePrimePowers {ρ : ℝ} {N x : ℕ} :
    x ∈ largePrimePowers ρ N ↔
      ∃ p : ℕ, Nat.Prime p ∧ ⌊(N : ℝ) ^ (ρ / 2)⌋₊ + 1 ≤ p ∧ p ≤ N ∧
        p ^ ⌊Real.log N / Real.log p⌋₊ = x := by
  rw [largePrimePowers, Finset.mem_image]
  constructor
  · rintro ⟨p, hp, hpx⟩
    simp only [Finset.mem_filter, Finset.mem_Icc] at hp
    exact ⟨p, hp.2, hp.1.1, hp.1.2, hpx⟩
  · rintro ⟨p, hprim, h1, h2, hpx⟩
    exact ⟨p, by
      simp only [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨h1, h2⟩, hprim⟩, hpx⟩

/-- Every element of `largePrimePowers ρ N` is coprime to `smallPrimePowerProd ρ N`: the latter is a
product of powers of primes `≤ ⌊N^{ρ/2}⌋₊`, each of them strictly below the prime underlying the
former. -/
private lemma coprime_smallPrimePowerProd_large {ρ : ℝ} {N b : ℕ}
    (hb : b ∈ largePrimePowers ρ N) :
    Nat.Coprime (smallPrimePowerProd ρ N) b := by
  obtain ⟨p, hpp, hpM, -, rfl⟩ := mem_largePrimePowers.mp hb
  rw [smallPrimePowerProd]
  refine Nat.Coprime.prod_left ?_
  intro q hq
  simp only [Finset.mem_filter, Finset.mem_Icc] at hq
  obtain ⟨⟨-, hqM⟩, hqp⟩ := hq
  have hqne : q ≠ p := by omega
  have hcop : Nat.Coprime q p := (Nat.coprime_primes hqp hpp).mpr hqne
  exact (hcop.pow_left _).pow_right _

/-- Distinct elements of `largePrimePowers ρ N` are coprime: each of them is a positive power of a
(unique) prime, and distinct elements come from distinct primes. -/
private lemma coprime_largePrimePowers {ρ : ℝ} {N a b : ℕ}
    (ha : a ∈ largePrimePowers ρ N) (hb : b ∈ largePrimePowers ρ N) (hab : a ≠ b) :
    Nat.Coprime a b := by
  obtain ⟨p, hpp, -, -, rfl⟩ := mem_largePrimePowers.mp ha
  obtain ⟨q, hqq, -, -, rfl⟩ := mem_largePrimePowers.mp hb
  have hpq : p ≠ q := by
    intro h
    exact hab (by rw [h])
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hpp hqq).mpr hpq
  exact (hcop.pow_left _).pow_right _

/-- The elements of Tao's major-arc set `taoSetS ρ N` are pairwise coprime (Tao, arXiv:2008.05066, Lemma `iwac`: "Clearly the elements of `S` are pairwise coprime"): every element other than `smallPrimePowerProd ρ N` is a power of a single prime, and `smallPrimePowerProd ρ N` is a product of powers of the primes `≤ N^{ρ/2}`, all of which are strictly smaller than the primes occurring in the other elements. -/
theorem taoSetS_coprime (ρ : ℝ) (N : ℕ) :
    ∀ a ∈ Work.BourgainPlan.IonescuWainger.taoSetS ρ N,
      ∀ b ∈ Work.BourgainPlan.IonescuWainger.taoSetS ρ N, a ≠ b → Nat.Coprime a b := by
  intro a ha b hb hab
  rw [taoSetS, Finset.mem_insert] at ha hb
  rcases ha with rfl | ha
  · rcases hb with rfl | hb
    · exact absurd rfl hab
    · exact coprime_smallPrimePowerProd_large hb
  · rcases hb with rfl | hb
    · exact (coprime_smallPrimePowerProd_large ha).symm
    · exact coprime_largePrimePowers ha hb hab

end Work.BourgainPlan.IonescuWainger
