/-
# `Submission.Work.FIArea1.card_primes_dvd_le`

**The number of Gaussian prime divisors of a non-zero Gaussian integer `W` is at most eight
times the number of distinct rational primes dividing its norm `|W|²`.**

This is the *count* that turns the prime-substitution step of *FI* §5 into an estimate in terms of
`ω(|W|²)` (rather than a logarithmic loss): the paper's substitution `W ↦ W/π` over Gaussian
primes `π` with `π ∣ W` at most multiplies the number of configurations by `♯{primes dividing W}`,
and `♯{primes dividing W} ≪ ω(|W|²)` with an *absolute* implied constant.

More precisely, if `S` is a finset of Gaussian primes each dividing `W ≠ 0`, then

`♯S ≤ 8 · ω(|W|²)`,

where `ω(n)` is the number of distinct rational primes dividing `n`.

## The mathematics

Work in the Euclidean domain `ℤ[i]` (`|z|² = gnorm z = z.re ^ 2 + z.im ^ 2`).

1. **Every Gaussian prime divides a rational prime.**  A prime `π` divides
   `|π|² = π * conj π`; factoring the natural number `|π|²` into rational primes and using
   primality of `π` (with a strong induction on `|π|²`) produces a rational prime `p` with
   `π ∣ p` (`exists_natPrime_dvd_gauss_prime`).
2. **Multiplicity of the norm.**  For such a `π`, `π ∣ p` gives `|π|² ∣ p ^ 2`, and `π` is not a
   unit, so `p ∣ |π|²` and `p ≤ |π|²`: the norm of `π` is `p` or `p²`
   (`prime_dvd_and_le_gnorm`).
3. **At most eight primes above a rational prime `p`.**  If `π₁, π₂, π₃` are pairwise
   non-associated primes all dividing `(p : ℤ[i])`, then writing `p = π₁ π₂ π₃ k` (using primality
   to push the divisibilities through the factors) and comparing norms gives
   `p³ ≤ |π₁|² |π₂|² |π₃|² |k|² = p²`, impossible (`false_of_three_pairwise_not_associated_dvd_natPrime`).
   Since a fixed Gaussian integer has at most four associates (`card_filter_associated_le_four`,
   from `Work.FIArea1.gauss_prime_dvd_card_le`), a finset of primes all dividing `p` has at most
   `4 + 4 = 8` elements (`card_le_eight_of_prime_dvd_natPrime`).
4. **Assembly.**  Each `π ∈ S` is assigned a rational prime `p(π) ∣ |π|²` with `π ∣ p(π)`; then
   `p(π) ∣ |W|²`, and the fibers of `π ↦ p(π)` have at most eight elements by (3).  Summing the
   fibers of `S` over `S.image p(·)` gives the claim.

## Layout

* `gnorm_cast_dvd`, `gnorm_dvd_gnorm_of_dvd`, `gnorm_natCast`, `gnorm_eq_zero_iff` — elementary
  norm calculus;
* `exists_natPrime_dvd_of_prime_dvd_natCast`, `exists_natPrime_dvd_gauss_prime` — step 1;
* `prime_dvd_and_le_gnorm` — step 2;
* `false_of_three_pairwise_not_associated_dvd_natPrime`,
  `card_le_eight_of_prime_dvd_natPrime` — step 3;
* `card_primes_dvd_le` — step 4.
-/
import Mathlib
import Submission.Work.FIArea1.conjunct2_defs
import Submission.Work.FIArea1.Helpers
import Submission.Work.FIArea1.gauss_prime_dvd_card_le

set_option autoImplicit false

namespace Work.FIArea1

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. Elementary norm calculus -/

/-- `gnorm` of a rational prime, as a Gaussian integer: `|(p : ℤ[i])|² = p²`. -/
lemma gnorm_natCast (p : ℕ) : Work.FIPlan.gnorm ((p : ℕ) : GaussianInt) = p ^ 2 := by
  rw [show ((p : ℕ) : GaussianInt) = ((p : ℤ) : GaussianInt) from by push_cast; rfl]
  rw [Work.FIArea1.gnorm_intCast]
  simp

/-- `gnorm` vanishes only at `0`. -/
lemma gnorm_eq_zero_iff (z : GaussianInt) : Work.FIPlan.gnorm z = 0 ↔ z = 0 := by
  rw [Work.FIPlan.gnorm, Int.natAbs_eq_zero, GaussianInt.norm_eq_zero]

/-- `gnorm` is monotone for divisibility. -/
lemma gnorm_dvd_gnorm_of_dvd {a b : GaussianInt} (h : a ∣ b) :
    Work.FIPlan.gnorm a ∣ Work.FIPlan.gnorm b := by
  obtain ⟨c, rfl⟩ := h
  rw [gnorm_mul]
  exact dvd_mul_right _ _

/-- A Gaussian integer divides `|z|²` (namely through `z * conj z`). -/
lemma gnorm_cast_dvd (π : GaussianInt) : π ∣ ((Work.FIPlan.gnorm π : ℕ) : GaussianInt) := by
  have h1 : ((Work.FIPlan.gnorm π : ℕ) : ℤ) = Zsqrtd.norm π := by
    rw [Work.FIPlan.gnorm]
    exact Int.natAbs_of_nonneg (Zsqrtd.norm_nonneg (by norm_num : (-1 : ℤ) ≤ 0) π)
  have h2 : ((Work.FIPlan.gnorm π : ℕ) : GaussianInt) = ((Zsqrtd.norm π : ℤ) : GaussianInt) := by
    exact_mod_cast h1
  exact ⟨star π, by rw [h2, Zsqrtd.norm_eq_mul_conj]⟩

/-! ## 2. Every Gaussian prime divides a rational prime -/

/-- **The induction step.**  If a Gaussian prime `π` divides the Gaussian integer `(m : ℤ[i])`
for a non-zero natural `m`, then `π` divides a rational prime dividing `m`.

The proof is a strong induction on `m`: pick a rational prime `q ∣ m`, write `m = q m'` and split
`π ∣ (q : ℤ[i]) * (m' : ℤ[i])` by primality of `π`. -/
lemma exists_natPrime_dvd_of_prime_dvd_natCast (π : GaussianInt) (hπ : Prime π) :
    ∀ m : ℕ, m ≠ 0 → π ∣ (m : GaussianInt) →
      ∃ q : ℕ, q.Prime ∧ q ∣ m ∧ π ∣ (q : GaussianInt) := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro hm0 hm
    rcases m with _ | _ | m
    · exact absurd rfl hm0
    · exact absurd (by simpa using hm) hπ.not_dvd_one
    · obtain ⟨q, hq, hqm⟩ := Nat.exists_prime_and_dvd (show m + 2 ≠ 1 by omega)
      have hqm' : q ∣ m + 2 := hqm
      obtain ⟨m', hm'⟩ := hqm
      have hcast : ((m + 2 : ℕ) : GaussianInt) = (q : GaussianInt) * (m' : GaussianInt) := by
        rw [hm']; push_cast; ring
      rw [hcast] at hm
      rcases hπ.dvd_or_dvd hm with h | h
      · exact ⟨q, hq, hqm', h⟩
      · have hm'0 : m' ≠ 0 := by
          intro h0
          rw [h0, mul_zero] at hm'
          omega
        have hlt : m' < m + 2 := by
          by_contra hcon
          push Not at hcon
          have h1 : q * m' ≥ 2 * m' := Nat.mul_le_mul_right _ hq.two_le
          have h2 : 2 * m' ≥ 2 * (m + 2) := Nat.mul_le_mul_left 2 hcon
          omega
        obtain ⟨q', hq', hq'm', hq'dvd⟩ := ih m' hlt hm'0 h
        exact ⟨q', hq', hq'm'.trans ⟨q, by rw [hm', mul_comm]⟩, hq'dvd⟩

/-- **Every Gaussian prime divides a rational prime.** -/
lemma exists_natPrime_dvd_gauss_prime (π : GaussianInt) (hπ : Prime π) :
    ∃ p : ℕ, p.Prime ∧ π ∣ (p : GaussianInt) := by
  have h1 : π ∣ ((Work.FIPlan.gnorm π : ℕ) : GaussianInt) := gnorm_cast_dvd π
  have h0 : Work.FIPlan.gnorm π ≠ 0 := fun h => hπ.ne_zero ((gnorm_eq_zero_iff π).mp h)
  obtain ⟨q, hq, _hqm, hd⟩ := exists_natPrime_dvd_of_prime_dvd_natCast π hπ _ h0 h1
  exact ⟨q, hq, hd⟩

/-! ## 3. The norm of a prime above `p` -/

/-- **The norm of a Gaussian prime `π ∣ p` is `p` or `p²`.**  Consequently `p ∣ |π|²` and
`p ≤ |π|²`. -/
lemma prime_dvd_and_le_gnorm {π : GaussianInt} {p : ℕ} (hp : p.Prime) (hπ : Prime π)
    (h : π ∣ (p : GaussianInt)) : p ∣ Work.FIPlan.gnorm π ∧ p ≤ Work.FIPlan.gnorm π := by
  have hgn : Work.FIPlan.gnorm π ∣ p ^ 2 := by
    have := gnorm_dvd_gnorm_of_dvd h
    rwa [gnorm_natCast] at this
  have hne1 : Work.FIPlan.gnorm π ≠ 1 := by
    intro h1
    exact hπ.not_isUnit (Zsqrtd.norm_eq_one_iff.mp h1)
  obtain ⟨k, _hk2, hk⟩ := (Nat.dvd_prime_pow hp).mp hgn
  have hk0 : k ≠ 0 := by
    intro h0
    exact hne1 (by rw [hk, h0]; simp)
  have hk12 : k = 1 ∨ k = 2 := by omega
  rcases hk12 with h1 | h2
  · rw [hk, h1]; exact ⟨by simpa using dvd_refl p, by simp⟩
  · rw [hk, h2]
    exact ⟨by simpa [pow_two] using dvd_mul_right p p, by nlinarith [hp.two_le]⟩

/-! ## 4. At most two associate classes of primes above a rational prime -/

/-- **There are no three pairwise non-associated Gaussian primes above one rational prime.**
If `a, b, c` are pairwise non-associated primes dividing `(p : ℤ[i])`, then pushing the
divisibilities through the factors writes `p = a b c k`; comparing norms with
`|a|², |b|², |c|² ≥ p` and `|k|² ≥ 1` gives `p³ ≤ p²`, impossible. -/
lemma false_of_three_pairwise_not_associated_dvd_natPrime
    (p : ℕ) (hp : p.Prime) (a b c : GaussianInt)
    (ha : Prime a) (hb : Prime b) (hc : Prime c)
    (hab : ¬ Associated a b) (hac : ¬ Associated a c) (hbc : ¬ Associated b c)
    (hda : a ∣ (p : GaussianInt)) (hdb : b ∣ (p : GaussianInt)) (hdc : c ∣ (p : GaussianInt)) :
    False := by
  have h2p : 2 ≤ p := hp.two_le
  have hga : p ≤ Work.FIPlan.gnorm a := (prime_dvd_and_le_gnorm hp ha hda).2
  have hgb : p ≤ Work.FIPlan.gnorm b := (prime_dvd_and_le_gnorm hp hb hdb).2
  have hgc : p ≤ Work.FIPlan.gnorm c := (prime_dvd_and_le_gnorm hp hc hdc).2
  have hp0 : (p : GaussianInt) ≠ 0 := by
    intro h
    have hre : ((p : GaussianInt)).re = 0 := by rw [h]; rfl
    rw [Zsqrtd.re_natCast] at hre
    exact hp.ne_zero (by exact_mod_cast hre)
  obtain ⟨k, hk⟩ := hda
  have hbk : b ∣ k := by
    rcases hb.dvd_or_dvd (show b ∣ a * k by rw [← hk]; exact hdb) with h | h
    · exact absurd (Prime.associated_of_dvd hb ha h).symm hab
    · exact h
  obtain ⟨k1, hk1⟩ := hbk
  have hpeq : (p : GaussianInt) = a * b * k1 := by rw [hk, hk1]; ring
  have hck1 : c ∣ k1 := by
    rcases hc.dvd_or_dvd (show c ∣ a * b * k1 by rw [← hpeq]; exact hdc) with h | h
    · rcases hc.dvd_or_dvd h with h2 | h2
      · exact absurd (Prime.associated_of_dvd hc ha h2).symm hac
      · exact absurd (Prime.associated_of_dvd hc hb h2).symm hbc
    · exact h
  obtain ⟨k2, hk2⟩ := hck1
  have hpeq2 : (p : GaussianInt) = a * b * c * k2 := by rw [hpeq, hk2]; ring
  have hk2ne : k2 ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hpeq2
    exact hp0 hpeq2
  have hgk2 : 1 ≤ Work.FIPlan.gnorm k2 := by
    rw [Nat.one_le_iff_ne_zero]
    intro h0
    exact hk2ne ((gnorm_eq_zero_iff k2).mp h0)
  have hnorm : p ^ 3 ≤ p ^ 2 := by
    have h := congrArg Work.FIPlan.gnorm hpeq2
    rw [gnorm_natCast] at h
    rw [gnorm_mul, gnorm_mul, gnorm_mul] at h
    have h1 : p * p * p ≤ Work.FIPlan.gnorm a * Work.FIPlan.gnorm b * Work.FIPlan.gnorm c :=
      Nat.mul_le_mul (Nat.mul_le_mul hga hgb) hgc
    have h2 : p * p * p * Work.FIPlan.gnorm k2 ≤
        Work.FIPlan.gnorm a * Work.FIPlan.gnorm b * Work.FIPlan.gnorm c * Work.FIPlan.gnorm k2 :=
      Nat.mul_le_mul h1 (le_refl _)
    have h3 : p ^ 3 ≤
        Work.FIPlan.gnorm a * Work.FIPlan.gnorm b * Work.FIPlan.gnorm c * Work.FIPlan.gnorm k2 := by
      calc p ^ 3 = p * p * p * 1 := by ring
        _ ≤ p * p * p * Work.FIPlan.gnorm k2 := Nat.mul_le_mul_left _ hgk2
        _ ≤ _ := h2
    calc p ^ 3 ≤ _ := h3
      _ = p ^ 2 := h.symm
  have h2 : p ^ 2 * p ≤ p ^ 2 * 1 := by
    rw [pow_succ] at hnorm
    simpa using hnorm
  have hp2 : 0 < p ^ 2 := pow_pos (by omega) 2
  have := Nat.le_of_mul_le_mul_left h2 hp2
  omega

/-- **At most eight Gaussian primes divide a fixed rational prime.**  Split the finset by the
associate class of a fixed member: each class contributes at most four elements, and by
`false_of_three_pairwise_not_associated_dvd_natPrime` there are at most two classes. -/
lemma card_le_eight_of_prime_dvd_natPrime (F : Finset GaussianInt) (p : ℕ) (hp : p.Prime)
    (hprime : ∀ π ∈ F, Prime π) (hdvd : ∀ π ∈ F, π ∣ (p : GaussianInt)) : F.card ≤ 8 := by
  by_cases hF : F.Nonempty
  · obtain ⟨π₀, hπ₀⟩ := hF
    have hA4 : (F.filter (fun π => Associated π π₀)).card ≤ 4 :=
      card_filter_associated_le_four π₀ F
    have hB4 : (F.filter (fun π => ¬ Associated π π₀)).card ≤ 4 := by
      by_cases hB0 : (F.filter (fun π => ¬ Associated π π₀)).Nonempty
      · obtain ⟨b, hb⟩ := hB0
        have hbF : b ∈ F := (Finset.mem_filter.mp hb).1
        have hbna : ¬ Associated b π₀ := (Finset.mem_filter.mp hb).2
        have hsub : F.filter (fun π => ¬ Associated π π₀) ⊆ F.filter (fun π => Associated π b) := by
          intro π hπ
          rw [Finset.mem_filter] at hπ ⊢
          refine ⟨hπ.1, ?_⟩
          by_contra hnab
          exact false_of_three_pairwise_not_associated_dvd_natPrime p hp π b π₀
            (hprime π hπ.1) (hprime b hbF) (hprime π₀ hπ₀)
            hnab hπ.2 hbna (hdvd π hπ.1) (hdvd b hbF) (hdvd π₀ hπ₀)
        calc (F.filter (fun π => ¬ Associated π π₀)).card
            ≤ (F.filter (fun π => Associated π b)).card := Finset.card_le_card hsub
          _ ≤ 4 := card_filter_associated_le_four b F
      · rw [Finset.not_nonempty_iff_eq_empty.mp hB0]; simp
    have hcard : F.card = (F.filter (fun π => Associated π π₀)).card +
        (F.filter (fun π => ¬ Associated π π₀)).card :=
      (Finset.card_filter_add_card_filter_not (s := F) (p := fun π => Associated π π₀)).symm
    omega
  · rw [Finset.not_nonempty_iff_eq_empty.mp hF]; simp

/-! ## 5. The count -/

/-- **The number of Gaussian prime divisors of `W ≠ 0` is at most `8 ω(|W|²)`.**

Assign to each `π ∈ S` a rational prime `p(π)` with `π ∣ p(π)`; then `p(π) ∣ |W|²`, and each fiber
`{π : p(π) = p}` consists of Gaussian primes dividing `(p : ℤ[i])`, hence has at most eight
elements.  Summing the fibers over `S.image p(·)` gives `♯S ≤ 8 · ♯(S.image p(·)) ≤ 8 ω(|W|²)`. -/
theorem card_primes_dvd_le (W : GaussianInt) (hW : W ≠ 0) (S : Finset GaussianInt)
    (hprime : ∀ π ∈ S, Prime π) (hdvd : ∀ π ∈ S, π ∣ W) :
    (S.card : ℝ) ≤ 8 * ((Work.FIPlan.gnorm W).primeFactors.card : ℝ) := by
  have hmain : S.card ≤ 8 * (Work.FIPlan.gnorm W).primeFactors.card := by
    classical
    -- choose, for every `π ∈ S`, a rational prime `p(π)` with `π ∣ p(π)`
    let f : GaussianInt → ℕ := fun π =>
      if h : π ∈ S then Classical.choose (exists_natPrime_dvd_gauss_prime π (hprime π h)) else 0
    have hf : ∀ π ∈ S, (f π).Prime ∧ π ∣ (f π : GaussianInt) := by
      intro π hπ
      have hfeq : f π = Classical.choose (exists_natPrime_dvd_gauss_prime π (hprime π hπ)) :=
        dif_pos hπ
      rw [hfeq]
      exact Classical.choose_spec (exists_natPrime_dvd_gauss_prime π (hprime π hπ))
    -- the fibers have at most eight elements
    have hfiber : ∀ b ∈ S.image f, (S.filter (fun π => f π = b)).card ≤ 8 := by
      intro b hb
      have hbprime : b.Prime := by
        obtain ⟨π, hπS, hπb⟩ := Finset.mem_image.mp hb
        rw [← hπb]
        exact (hf π hπS).1
      refine card_le_eight_of_prime_dvd_natPrime (S.filter (fun π => f π = b)) b hbprime ?_ ?_
      · intro π hπ
        exact hprime π (Finset.mem_filter.mp hπ).1
      · intro π hπ
        have hπS : π ∈ S := (Finset.mem_filter.mp hπ).1
        have hfeq : f π = b := (Finset.mem_filter.mp hπ).2
        have h' := (hf π hπS).2
        rwa [← hfeq]
    have hsum := Finset.card_eq_sum_card_fiberwise (f := f) (s := S) (t := S.image f)
      (fun π hπ => Finset.mem_image_of_mem f hπ)
    have hbound : S.card ≤ 8 * (S.image f).card := by
      rw [hsum]
      calc ∑ b ∈ S.image f, (S.filter (fun π => f π = b)).card
          ≤ ∑ _b ∈ S.image f, 8 := Finset.sum_le_sum hfiber
        _ = 8 * (S.image f).card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    -- the chosen primes all divide `|W|²`
    have himage : (S.image f).card ≤ (Work.FIPlan.gnorm W).primeFactors.card := by
      refine Finset.card_le_card ?_
      intro b hb
      rw [Nat.mem_primeFactors]
      obtain ⟨π, hπS, rfl⟩ := Finset.mem_image.mp hb
      refine ⟨(hf π hπS).1, ?_, ?_⟩
      · exact ((prime_dvd_and_le_gnorm (hf π hπS).1 (hprime π hπS) (hf π hπS).2).1).trans
          (gnorm_dvd_gnorm_of_dvd (hdvd π hπS))
      · intro hzero
        exact hW ((gnorm_eq_zero_iff W).mp hzero)
    exact hbound.trans (Nat.mul_le_mul_left 8 himage)
  exact_mod_cast hmain

end

end Work.FIArea1
