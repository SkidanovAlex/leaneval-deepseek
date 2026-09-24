import Mathlib
import Submission.Work.ChenPlan.LinearSieve.JR2.Defs
import Submission.Work.ChenPlan.LinearSieve.RI.basic
import Submission.Work.ChenPlan.LinearSieve.RI.lamMinus_sieve_lower
import Submission.Work.ChenPlan.LinearSieve.RI.support_lt

/-!
# The structure of the `Q`-split (lower `Q`-trick)

`Q := Qmod A u₀ = ∏_{p ∣ P, p < u₀} p` and `Qz := Pz (subSieve A Q hQ) Z`, where
`subSieve A Q hQ` is the same sieve problem with `prodPrimes = P/Q`.

Since `P` is squarefree with prime factors the (finite) set `s`, splitting `s` into the primes
below `u₀` and those above gives

* `Q = ∏_{p ∈ s, p < u₀} p`, `(P/Q) = ∏_{p ∈ s, u₀ ≤ p} p`,
* `Pz (subSieve …) Z = ∏_{p ∈ s, u₀ ≤ p < Z} p`, and `Q · Pz (subSieve …) Z = Pz A Z` when
  `u₀ ≤ Z`;
* `Q` and `Pz (subSieve …) Z` are coprime.

Also included: the injectivity of `(q,d) ↦ q·d` on `q ∣ Q`, `d ∣ Pz (subSieve …) Z`, which is what
keeps the `Q`-trick from inflating the remainder term.
-/

namespace Work.ChenPlan.LinearSieve.JR2

open Finset
open scoped BigOperators

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

open Classical

/-- **The structure of the `Q`-split.**  `s := A.prodPrimes.primeFactors`.  All five structural
facts of the `Q`-trick, at once. -/
theorem Qmod_structure (A : BoundingSieve) (u₀ Z : ℝ) (hu₀ : 2 ≤ u₀) (hu₀Z : u₀ ≤ Z) :
    (Qmod A u₀ * Pz (subSieve A (Qmod A u₀) (Qmod_dvd A u₀)) Z = Pz A Z)
    ∧ Nat.Coprime (Qmod A u₀) (Pz (subSieve A (Qmod A u₀) (Qmod_dvd A u₀)) Z)
    ∧ (Qmod A u₀).primeFactors = A.prodPrimes.primeFactors.filter (fun p : ℕ => (p : ℝ) < u₀)
    ∧ (Pz (subSieve A (Qmod A u₀) (Qmod_dvd A u₀)) Z).primeFactors
        = A.prodPrimes.primeFactors.filter (fun p : ℕ => u₀ ≤ (p : ℝ) ∧ (p : ℝ) < Z)
    ∧ (subSieve A (Qmod A u₀) (Qmod_dvd A u₀)).prodPrimes
        = ∏ p ∈ A.prodPrimes.primeFactors.filter (fun p : ℕ => u₀ ≤ (p : ℝ)), p := by
  classical
  set s := A.prodPrimes.primeFactors with hs
  set t := s.filter (fun p : ℕ => (p : ℝ) < u₀) with ht
  set t' := s.filter (fun p : ℕ => ¬ (p : ℝ) < u₀) with ht'
  set M := ∏ p ∈ t', p with hM
  have hspr : ∀ p ∈ s, p.Prime := fun p hp => (Nat.mem_primeFactors.mp hp).1
  have hsprt : ∀ p ∈ t, p.Prime := fun p hp =>
    hspr p (Finset.mem_of_mem_filter p (by rw [ht] at hp; exact hp))
  have hsprt' : ∀ p ∈ t', p.Prime := fun p hp =>
    hspr p (Finset.mem_of_mem_filter p (by rw [ht'] at hp; exact hp))
  -- `Qmod A u₀ = ∏_{p ∈ t} p`
  have hQeq : Qmod A u₀ = ∏ p ∈ t, p := rfl
  have hQpf : (Qmod A u₀).primeFactors = t := by
    rw [hQeq]
    exact Nat.primeFactors_prod hsprt
  have hQpos : 0 < Qmod A u₀ := by
    rw [hQeq]
    exact Finset.prod_pos (fun p hp => (hsprt p hp).pos)
  have hQne : Qmod A u₀ ≠ 0 := Nat.pos_iff_ne_zero.mp hQpos
  have hMpf : M.primeFactors = t' := by
    rw [hM]
    exact Nat.primeFactors_prod hsprt'
  -- decomposition `A.prodPrimes = Q * M`
  have hPprod : A.prodPrimes = ∏ p ∈ s, p :=
    (Nat.prod_primeFactors_of_squarefree A.prodPrimes_squarefree).symm
  have hsplit : s = t ∪ t' :=
    (Finset.filter_union_filter_not_eq (fun p : ℕ => (p : ℝ) < u₀) s).symm
  have hdisj : Disjoint t t' := by
    rw [Finset.disjoint_left]
    intro a ha ha'
    rw [ht] at ha
    rw [ht'] at ha'
    rw [Finset.mem_filter] at ha ha'
    exact absurd ha.2 ha'.2
  have hP_split : A.prodPrimes = (∏ p ∈ t, p) * M := by
    rw [hPprod, hsplit, Finset.prod_union hdisj, hM]
  have hdiv : A.prodPrimes / Qmod A u₀ = M := by
    rw [hQeq, hP_split]
    exact Nat.mul_div_cancel_left M hQpos
  have hBpp : (subSieve A (Qmod A u₀) (Qmod_dvd A u₀)).prodPrimes = M := hdiv
  -- `Pz (subSieve …) Z` as a product and its prime factors
  have hQzeq : Pz (subSieve A (Qmod A u₀) (Qmod_dvd A u₀)) Z
      = ∏ p ∈ t'.filter (fun p : ℕ => (p : ℝ) < Z), p := by
    unfold Pz
    rw [hBpp, hMpf]
  have hQzpf : (Pz (subSieve A (Qmod A u₀) (Qmod_dvd A u₀)) Z).primeFactors
      = A.prodPrimes.primeFactors.filter (fun p : ℕ => u₀ ≤ (p : ℝ) ∧ (p : ℝ) < Z) := by
    rw [RI.Pz_primeFactors, hBpp, hMpf, ht', Finset.filter_filter]
    refine Finset.filter_congr (fun p _ => ?_)
    exact ⟨fun h => ⟨not_lt.mp h.1, h.2⟩, fun h => ⟨not_lt.mpr h.1, h.2⟩⟩
  have hQzpos : 0 < Pz (subSieve A (Qmod A u₀) (Qmod_dvd A u₀)) Z :=
    Nat.pos_iff_ne_zero.mpr (RI.Pz_ne_zero _ _)
  -- coprimality
  have hdisjPF : Disjoint (Qmod A u₀).primeFactors
      (Pz (subSieve A (Qmod A u₀) (Qmod_dvd A u₀)) Z).primeFactors := by
    rw [hQpf, hQzpf, Finset.disjoint_left]
    intro a ha ha'
    rw [ht] at ha
    rw [Finset.mem_filter] at ha ha'
    exact absurd ha.2 (not_lt.mpr ha'.2.1)
  -- product
  have hPzA : Pz A Z = ∏ p ∈ s.filter (fun p : ℕ => (p : ℝ) < Z), p := rfl
  have hunion : t ∪ (t'.filter (fun p : ℕ => (p : ℝ) < Z)) = s.filter (fun p : ℕ => (p : ℝ) < Z) := by
    rw [ht, ht']
    ext a
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨ha, h1⟩ | ⟨⟨ha, h1⟩, h2⟩)
      · exact ⟨ha, lt_of_lt_of_le h1 hu₀Z⟩
      · exact ⟨ha, h2⟩
    · rintro ⟨ha, h2⟩
      by_cases h : (a : ℝ) < u₀
      · exact Or.inl ⟨ha, h⟩
      · exact Or.inr ⟨⟨ha, h⟩, h2⟩
  have hdisjU : Disjoint t (t'.filter (fun p : ℕ => (p : ℝ) < Z)) := by
    rw [Finset.disjoint_left]
    intro a ha ha'
    rw [ht] at ha
    rw [ht'] at ha'
    have hlt : (a : ℝ) < u₀ := (Finset.mem_filter.mp ha).2
    have hnot : ¬ (a : ℝ) < u₀ := (Finset.mem_filter.mp (Finset.mem_filter.mp ha').1).2
    exact hnot hlt
  have hprod : Qmod A u₀ * Pz (subSieve A (Qmod A u₀) (Qmod_dvd A u₀)) Z = Pz A Z := by
    rw [hQzeq, hQeq, hPzA, ← hunion, Finset.prod_union hdisjU]
  refine ⟨hprod, ?_, hQpf, hQzpf, ?_⟩
  · exact (Nat.disjoint_primeFactors hQne (Nat.pos_iff_ne_zero.mp hQzpos)).mp hdisjPF
  · rw [hBpp, hM, ht']
    congr 1
    exact Finset.filter_congr (fun p _ => not_lt)

/-- The primes of `Pz (subSieve A Q hQ) Z` lie in `[u₀, Z)`. -/
theorem Qmod_Qz_prime_bound (A : BoundingSieve) (u₀ Z : ℝ) (hu₀ : 2 ≤ u₀) (hu₀Z : u₀ ≤ Z) :
    ∀ p ∈ (Pz (subSieve A (Qmod A u₀) (Qmod_dvd A u₀)) Z).primeFactors,
      (p : ℝ) < Z ∧ u₀ ≤ (p : ℝ) := by
  have h := (Qmod_structure A u₀ Z hu₀ hu₀Z).2.2.2.1
  intro p hp
  rw [h] at hp
  exact ⟨(Finset.mem_filter.mp hp).2.2, (Finset.mem_filter.mp hp).2.1⟩

/-- **`(q,d) ↦ q·d` is injective** on `q ∣ Q`, `d ∣ Qz` when `Q ⊥ Qz`.  This is what keeps the
`Q`-trick from multiplying the remainder term by `2^{ω(Q)}`. -/
theorem mul_injOn_divisors {Q Qz : ℕ} (h : Nat.Coprime Q Qz) :
    Set.InjOn (fun p : ℕ × ℕ => p.1 * p.2) ↑(Q.divisors ×ˢ Qz.divisors) := by
  rintro ⟨q₁, d₁⟩ h1 ⟨q₂, d₂⟩ h2 heq
  change q₁ * d₁ = q₂ * d₂ at heq
  simp only [Finset.mem_coe, Finset.mem_product, Nat.mem_divisors] at h1 h2
  obtain ⟨⟨hq1dvd, hQ0⟩, hd1dvd, -⟩ := h1
  obtain ⟨⟨hq2dvd, -⟩, hd2dvd, -⟩ := h2
  have hcop12 : Nat.Coprime q₁ d₂ := (h.coprime_dvd_left hq1dvd).coprime_dvd_right hd2dvd
  have hcop21 : Nat.Coprime q₂ d₁ := (h.coprime_dvd_left hq2dvd).coprime_dvd_right hd1dvd
  have hq1q2 : q₁ ∣ q₂ := hcop12.dvd_of_dvd_mul_right (by rw [← heq]; exact dvd_mul_right q₁ d₁)
  have hq2q1 : q₂ ∣ q₁ := hcop21.dvd_of_dvd_mul_right (heq.symm ▸ dvd_mul_right q₂ d₂)
  have hq : q₁ = q₂ := Nat.dvd_antisymm hq1q2 hq2q1
  have hq1pos : 0 < q₁ := Nat.pos_of_ne_zero (fun h0 => hQ0 (Nat.eq_zero_of_zero_dvd (h0 ▸ hq1dvd)))
  have hd : d₁ = d₂ := by
    rw [← hq] at heq
    exact Nat.mul_left_cancel hq1pos heq
  simp [hq, hd]

end

end Work.ChenPlan.LinearSieve.JR2
