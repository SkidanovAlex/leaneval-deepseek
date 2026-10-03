import Mathlib
import Submission.Work.FIArea4.A4c.Defs
import Submission.Work.FIArea4.GaussMoebiusCore
import Submission.Work.S15psiAlt.fiber_card_le_four
import Submission.Work.FIArea4.A4c.card_normalizedFactors_le_primeFactors_card
import Submission.Work.FIArea4.A4c.pow_two_primeFactors_card_le_divisors_card

namespace Work.FIArea4.A4c

/-- **The divisor count of the Möbius summation.** Every finite set of divisors of a non-zero
Gaussian integer `z` with `Squarefree (|z|²)` has at most `4·τ(|z|²)` elements.

Proof route (the one that works): `card W' ≤ 4 · #(image of w ↦ normalizedFactors w)`, because each
fibre of `w ↦ UniqueFactorizationMonoid.normalizedFactors w` inside a set of divisors of the
non-zero `z` has at most `4` elements — the four units of `ℤ[i]` (`Work.S15psiAlt.fiber_card_le_four`
gives exactly this, and `Work.S15psiAlt.sum_comp_le_four_mul_sum_image` the corresponding sum
bound).  The image is a set of sub-multisets of `normalizedFactors z`, so
`#(image) ≤ 2 ^ (normalizedFactors z).card`.

The squarefreeness of `gnorm z` is what makes `2 ^ (normalizedFactors z).card ≤ (gnorm z).divisors.card`:
each prime factor `p` of `z` has `gnorm p ∣ gnorm z`, and `gnorm p ≠ 1` (`p` is not a unit); if two
*distinct* `p p' ∈ normalizedFactors z` had a common rational prime `r` dividing `gnorm p`,
`gnorm p'`, then `gnorm p * gnorm p' = gnorm (p p') ∣ gnorm z` (using `p * p' ∣ z` for the two
non-associate primes) would contain `r²`, contradicting `Squarefree (gnorm z)`.  Hence the norms
`gnorm p` (`p ∈ normalizedFactors z`) are pairwise coprime non-one naturals, so
`ω (gnorm z) = Σ_{p} ω (gnorm p) ≥ (normalizedFactors z).card` whenever the multiplicities in
`normalizedFactors z` are `1`, which squarefreeness also gives (`p² ∣ z ⟹ gnorm p ^ 2 ∣ gnorm z ⟹
gnorm p = 1`).  Therefore `2 ^ (normalizedFactors z).card ≤ 2 ^ ω ≤ (gnorm z).divisors.card`.

The `4 *` on the right is harmless slack: proving `(W'.card : ℝ) ≤ 4 * τ` including it is enough.
`Work.FIPlan.gnorm` is an `ℕ`-valued multiplicative norm on `GaussianInt = ℤ[i]`
(`Work.FIArea4.gnorm_mul`, `gnorm_dvd`, `gnorm_pos`, ...), and `ℤ[i]` is a `EuclideanDomain`
(`Mathlib/NumberTheory/Zsqrtd/GaussianInt.lean`), hence a UFD, so `normalizedFactors`,
`UniqueFactorizationMonoid.associated_iff_normalizedFactors_eq_normalizedFactors`,
`UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors` are all available.

Counterexamples to be aware of: without `Squarefree (gnorm z)` the statement is false
(`z = 5` has `16 > 4·τ(25) = 12` divisors). -/
theorem card_dvd_finset_le (z : GaussianInt) (hz : z ≠ 0)
    (hsq : Squarefree (Work.FIPlan.gnorm z)) (W' : Finset GaussianInt)
    (hW : ∀ w ∈ W', w ∣ z) :
    (W'.card : ℝ) ≤ 4 * (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) := by
  classical
  set f : GaussianInt → Multiset GaussianInt :=
    fun w => UniqueFactorizationMonoid.normalizedFactors w with hf
  -- every element of `W'` is nonzero (it divides the nonzero `z`)
  have hw0 : ∀ w ∈ W', w ≠ 0 := by
    intro w hw hwz
    have hd := hW w hw
    rw [hwz, zero_dvd_iff] at hd
    exact hz hd
  -- fibres of `f` over `W'` have at most four elements
  have hfib : ∀ S : Multiset GaussianInt, (W'.filter (fun w => f w = S)).card ≤ 4 := by
    intro S
    show (W'.filter (fun w => UniqueFactorizationMonoid.normalizedFactors w = S)).card ≤ 4
    exact Work.S15psiAlt.fiber_card_le_four z W' hz hW S
  -- (1) `W'.card ≤ 4 * #(W'.image f)`
  have hmaps : Set.MapsTo f (↑W') (↑(W'.image f)) := fun w hw => Finset.mem_image_of_mem f hw
  have h1 : W'.card ≤ 4 * (W'.image f).card := by
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    calc ∑ b ∈ W'.image f, (W'.filter (fun a => f a = b)).card
        ≤ ∑ b ∈ W'.image f, (4 : ℕ) := Finset.sum_le_sum (fun b _ => hfib b)
      _ = (W'.image f).card * 4 := by rw [Finset.sum_const, smul_eq_mul]
      _ = 4 * (W'.image f).card := Nat.mul_comm _ _
  -- (2) the image sits inside the powerset of `normalizedFactors z`
  have himage_sub : W'.image f ⊆
      (UniqueFactorizationMonoid.normalizedFactors z).powerset.toFinset := by
    intro S hS
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hS
    rw [Multiset.mem_toFinset, Multiset.mem_powerset]
    show UniqueFactorizationMonoid.normalizedFactors w
        ≤ UniqueFactorizationMonoid.normalizedFactors z
    exact (UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors
      (hw0 w hw) hz).mp (hW w hw)
  have h2 : (W'.image f).card
      ≤ 2 ^ (UniqueFactorizationMonoid.normalizedFactors z).card := by
    calc (W'.image f).card
        ≤ (UniqueFactorizationMonoid.normalizedFactors z).powerset.toFinset.card :=
          Finset.card_le_card himage_sub
      _ ≤ (UniqueFactorizationMonoid.normalizedFactors z).powerset.card :=
          Multiset.toFinset_card_le _
      _ = 2 ^ (UniqueFactorizationMonoid.normalizedFactors z).card :=
          Multiset.card_powerset _
  -- (3) `2 ^ (normalizedFactors z).card ≤ τ (gnorm z)`
  have hc1 : (UniqueFactorizationMonoid.normalizedFactors z).card
      ≤ (Work.FIPlan.gnorm z).primeFactors.card :=
    card_normalizedFactors_le_primeFactors_card z hz hsq
  have hc2 : 2 ^ (Work.FIPlan.gnorm z).primeFactors.card
      ≤ (Work.FIPlan.gnorm z).divisors.card :=
    pow_two_primeFactors_card_le_divisors_card (Work.FIPlan.gnorm z)
      (Work.FIArea4.gnorm_ne_zero hz)
  have h3 : 2 ^ (UniqueFactorizationMonoid.normalizedFactors z).card
      ≤ (Work.FIPlan.gnorm z).divisors.card :=
    le_trans (Nat.pow_le_pow_right (by norm_num) hc1) hc2
  have h4 : W'.card ≤ 4 * (Work.FIPlan.gnorm z).divisors.card :=
    le_trans h1 (Nat.mul_le_mul_left 4 (le_trans h2 h3))
  exact_mod_cast h4

end Work.FIArea4.A4c
