import Mathlib
import Submission.Commons.NumberTheory.Robin.caLogN_mono
import Submission.Commons.NumberTheory.Robin.caLogN_le

namespace Commons.NumberTheory.Robin

open scoped BigOperators

/-- General combinatorial identity: the logarithm of a product of prime powers, with the
exponents summed level by level via Chebyshev's `θ` function.

For `f : ℕ → ℕ` whose level sets `{p prime : k ≤ f p}` are downward closed among primes
(`hanti`) and whose values are bounded by `N` (`hbdd`),

`log ∏_{p < N, p prime} p ^ (f p) = ∑_{k=1}^{N} θ (max {p < N prime : k ≤ f p})`.

Indeed both sides equal `∑_{p < N, p prime} f p · log p`: the level set `{p : k ≤ f p}` is
exactly the set of primes `≤` its own maximum, so `θ` of that maximum is the sum of `log p`
over the level set, and then the sums are interchanged. -/
theorem log_prod_pow_eq_sum_theta (N : ℕ) (f : ℕ → ℕ)
    (hanti : ∀ k p q, 1 ≤ k → p.Prime → q.Prime → q ≤ p → k ≤ f p → k ≤ f q)
    (hbdd : ∀ p, p.Prime → p < N → f p ≤ N) :
    Real.log ((((Finset.range N).filter Nat.Prime).prod (fun p => p ^ f p) : ℕ) : ℝ) =
      ∑ k ∈ Finset.Icc 1 N,
        Chebyshev.theta ((((((Finset.range N).filter Nat.Prime).filter (fun p => k ≤ f p)).sup id : ℕ)) : ℝ) := by
  classical
  set s : Finset ℕ := (Finset.range N).filter Nat.Prime with hs
  have hmem : ∀ p ∈ s, p.Prime ∧ p < N := by
    intro p hp
    rw [hs] at hp
    rw [Finset.mem_filter, Finset.mem_range] at hp
    exact ⟨hp.2, hp.1⟩
  have hlog : Real.log (((s.prod (fun p => p ^ f p) : ℕ)) : ℝ)
      = ∑ p ∈ s, (f p : ℝ) * Real.log (p : ℝ) := by
    rw [Nat.cast_prod]
    simp only [Nat.cast_pow]
    rw [Real.log_prod]
    · apply Finset.sum_congr rfl
      intro p hp
      rw [Real.log_pow]
    · intro p hp
      exact pow_ne_zero _ (Nat.cast_ne_zero.mpr (hmem p hp).1.pos.ne')
  have hkey : ∑ k ∈ Finset.Icc 1 N,
        Chebyshev.theta ((((s.filter (fun p => k ≤ f p)).sup id : ℕ)) : ℝ)
      = ∑ p ∈ s, (f p : ℝ) * Real.log (p : ℝ) := by
    have hA : ∀ k ∈ Finset.Icc 1 N,
        Chebyshev.theta ((((s.filter (fun p => k ≤ f p)).sup id : ℕ)) : ℝ)
          = ∑ p ∈ s.filter (fun p => k ≤ f p), Real.log (p : ℝ) := by
      intro k hk
      rw [Finset.mem_Icc] at hk
      obtain ⟨hk1, hkN⟩ := hk
      have hset : Nat.primesLE ((s.filter (fun p => k ≤ f p)).sup id)
          = s.filter (fun p => k ≤ f p) := by
        ext q
        rw [Nat.mem_primesLE]
        constructor
        · intro hq
          obtain ⟨hqle, hqprime⟩ := hq
          by_cases hne : (s.filter (fun p => k ≤ f p)).Nonempty
          · have hAmem : (s.filter (fun p => k ≤ f p)).sup id
                ∈ s.filter (fun p => k ≤ f p) := by
              rw [← Finset.sup'_eq_sup hne id, ← Finset.max'_eq_sup' _ hne]
              exact Finset.max'_mem _ hne
            obtain ⟨hAs, hAk⟩ := Finset.mem_filter.mp hAmem
            obtain ⟨hAprime, hAltN⟩ := hmem _ hAs
            have hkq : k ≤ f q := hanti k _ q hk1 hAprime hqprime hqle hAk
            exact Finset.mem_filter.mpr
              ⟨Finset.mem_filter.mpr
                ⟨Finset.mem_range.mpr (lt_of_le_of_lt hqle hAltN), hqprime⟩, hkq⟩
          · have hempty : s.filter (fun p => k ≤ f p) = ∅ :=
              Finset.not_nonempty_iff_eq_empty.mp hne
            have hA0 : (s.filter (fun p => k ≤ f p)).sup id = 0 := by
              rw [hempty, Finset.sup_empty]
              rfl
            rw [hA0] at hqle
            exact absurd (Nat.le_zero.mp hqle ▸ hqprime) Nat.not_prime_zero
        · intro hq
          obtain ⟨hqs, hqk⟩ := Finset.mem_filter.mp hq
          obtain ⟨hqprime, _⟩ := hmem _ hqs
          exact ⟨Finset.le_sup (f := id) hq, hqprime⟩
      rw [Chebyshev.theta_eq_sum_primesLE_log, hset]
    have hswap : (∑ k ∈ Finset.Icc 1 N, ∑ p ∈ s.filter (fun p => k ≤ f p), Real.log (p : ℝ))
        = ∑ p ∈ s, ∑ k ∈ Finset.Icc 1 N, (if k ≤ f p then Real.log (p : ℝ) else 0) := by
      have h1 : (∑ k ∈ Finset.Icc 1 N, ∑ p ∈ s.filter (fun p => k ≤ f p), Real.log (p : ℝ))
          = ∑ k ∈ Finset.Icc 1 N, ∑ p ∈ s,
              (if k ≤ f p then Real.log (p : ℝ) else 0) := by
        refine Finset.sum_congr rfl ?_
        intro k _
        rw [Finset.sum_filter]
      rw [h1, Finset.sum_comm]
    rw [Finset.sum_congr rfl hA, hswap]
    apply Finset.sum_congr rfl
    intro p hp
    obtain ⟨hpprime, hpN⟩ := hmem p hp
    have hfb : f p ≤ N := hbdd p hpprime hpN
    have hcount : ∑ k ∈ Finset.Icc 1 N, (if k ≤ f p then (1 : ℝ) else 0) = (f p : ℝ) := by
      rw [Finset.sum_boole]
      have hfil : (Finset.Icc 1 N).filter (fun k => k ≤ f p) = Finset.Icc 1 (f p) := by
        ext k
        rw [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Icc]
        constructor
        · rintro ⟨⟨hk1, _⟩, hk2⟩; exact ⟨hk1, hk2⟩
        · rintro ⟨hk1, hk2⟩; exact ⟨⟨hk1, le_trans hk2 hfb⟩, hk2⟩
      rw [hfil, Nat.card_Icc]
      simp
    calc ∑ k ∈ Finset.Icc 1 N, (if k ≤ f p then Real.log (p : ℝ) else 0)
        = ∑ k ∈ Finset.Icc 1 N, (if k ≤ f p then (1 : ℝ) else 0) * Real.log (p : ℝ) := by
          apply Finset.sum_congr rfl
          intro k _
          split <;> simp
      _ = (∑ k ∈ Finset.Icc 1 N, (if k ≤ f p then (1 : ℝ) else 0)) * Real.log (p : ℝ) := by
          rw [Finset.sum_mul]
      _ = (f p : ℝ) * Real.log (p : ℝ) := by rw [hcount]
  rw [hlog, hkey]

/-- Lagarias/Nicolas: the logarithm of the colossally-abundant product `N_ε` rewritten as a
sum of Chebyshev `θ` values indexed by the exponent levels. -/
theorem caLogN_eq_sum_theta (ε : ℝ) (hε : 0 < ε) :
    Real.log (((Finset.prod ((Finset.range (Nat.ceil (Real.exp (2 / ε)) + 2)).filter Nat.Prime)
        (fun p => p ^ ⌊Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / ((((p : ℝ) ^ (1 + ε))) - (p : ℝ))) / Real.log (p : ℝ)⌋₊)) : ℕ) : ℝ)
      = Finset.sum (Finset.Icc 1 (Nat.ceil (Real.exp (2 / ε)) + 2))
          (fun k => Chebyshev.theta (((((Finset.range (Nat.ceil (Real.exp (2 / ε)) + 2)).filter Nat.Prime).filter
            (fun p : ℕ => k ≤ ⌊Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / ((((p : ℝ) ^ (1 + ε))) - (p : ℝ))) / Real.log (p : ℝ)⌋₊)).sup id : ℕ) : ℝ)) := by
  refine log_prod_pow_eq_sum_theta (Nat.ceil (Real.exp (2 / ε)) + 2)
    (fun p => ⌊Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / ((((p : ℝ) ^ (1 + ε))) - (p : ℝ))) / Real.log (p : ℝ)⌋₊) ?_ ?_
  · intro k p q hk hp hq hqp h
    exact caLogN_mono ε hε hk hp hq hqp h
  · intro p hp _
    exact caLogN_le ε hε hp.two_le

end Commons.NumberTheory.Robin
