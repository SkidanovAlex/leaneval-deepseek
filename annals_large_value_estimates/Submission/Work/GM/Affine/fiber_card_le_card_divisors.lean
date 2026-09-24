import Mathlib

namespace Work.GM.Affine

/-- **Fiber bound.** For a finite set `P` of integer pairs all of whose first coordinates satisfy
`M₁ ≤ |p.1|` with `M₁ > 0`, the number of pairs in `P` with a fixed non-zero product `n` is at most
twice the number of positive divisors of `|n|`. -/
lemma fiber_card_le_card_divisors {M₁ : ℝ} (hM₁ : 0 < M₁) (P : Finset (ℤ × ℤ))
    (hM : ∀ p ∈ P, M₁ ≤ |(p.1 : ℝ)|) (n : ℤ) (hn : n ≠ 0) :
    (P.filter (fun p => p.1 * p.2 = n)).card ≤ 2 * n.natAbs.divisors.card := by
  classical
  set S := P.filter (fun p => p.1 * p.2 = n) with hS
  -- every `p ∈ S` has a non-zero first coordinate, which divides `n`
  have hne : ∀ p ∈ S, p.1 ≠ 0 := by
    intro p hp h0
    have hpn : p.1 * p.2 = n := (Finset.mem_filter.mp hp).2
    rw [h0, zero_mul] at hpn
    exact hn hpn.symm
  have hdvd : ∀ p ∈ S, p.1 ∣ n := by
    intro p hp
    exact ⟨p.2, ((Finset.mem_filter.mp hp).2).symm⟩
  -- two elements of `S` with the same `|·|` and the same sign coincide
  have hinj_fib : ∀ b, Set.InjOn (fun p : ℤ × ℤ => decide (0 < p.1))
      ↑({a ∈ S | a.1.natAbs = b} : Finset (ℤ × ℤ)) := by
    intro b p hp q hq heq
    simp only [Finset.mem_filter, Finset.mem_coe] at hp hq
    have hnat : p.1.natAbs = q.1.natAbs := by rw [hp.2, hq.2]
    rcases Int.natAbs_eq_natAbs_iff.mp hnat with h | h
    · have hpn : p.1 * p.2 = n := (Finset.mem_filter.mp hp.1).2
      have hqn : q.1 * q.2 = n := (Finset.mem_filter.mp hq.1).2
      have h2 : p.2 = q.2 := by
        apply mul_left_cancel₀ (hne p hp.1)
        rw [hpn, ← hqn, ← h]
      exact Prod.ext h h2
    · have hsign : (0 < p.1) ↔ (0 < q.1) := decide_eq_decide.mp heq
      have h1 : 0 < p.1 → 0 < q.1 := hsign.mp
      have h2 : 0 < q.1 → 0 < p.1 := hsign.mpr
      have hqne : q.1 ≠ 0 := hne q hq.1
      omega
  -- each fiber over `p ↦ |p.1|` has at most two elements
  have hfib : ∀ b ∈ S.image (fun p => p.1.natAbs), {a ∈ S | a.1.natAbs = b}.card ≤ 2 := by
    intro b hb
    have := Finset.card_le_card_of_injOn (fun p : ℤ × ℤ => decide (0 < p.1))
      (t := (Finset.univ : Finset Bool)) (fun p _ => Finset.mem_univ _) (hinj_fib b)
    simpa using this
  calc S.card ≤ 2 * (S.image (fun p => p.1.natAbs)).card :=
        Finset.card_le_mul_card_image S 2 hfib
    _ ≤ 2 * n.natAbs.divisors.card := by
        apply Nat.mul_le_mul_left
        apply Finset.card_le_card
        intro b hb
        rw [Finset.mem_image] at hb
        obtain ⟨p, hp, rfl⟩ := hb
        rw [Nat.mem_divisors]
        exact ⟨Int.natAbs_dvd_natAbs.mpr (hdvd p hp), Int.natAbs_ne_zero.mpr hn⟩

end Work.GM.Affine
