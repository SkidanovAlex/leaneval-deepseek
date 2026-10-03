import Submission.Work.FIArea6Road.DivisorWindowDefs

namespace Work.FIArea6Road

open Finset
open scoped BigOperators

/-- `lcm m n = m * (n / gcd m n)` (for positive `m, n`). -/
private lemma lcm_eq_mul_div_gcd' {m n : ℕ} (hm : 0 < m) (_hn : 0 < n) :
    m.lcm n = m * (n / m.gcd n) := by
  have hg : 0 < m.gcd n := Nat.gcd_pos_of_pos_left n hm
  have h : m.gcd n * m.lcm n = m * n := Nat.gcd_mul_lcm m n
  have h1 : m.gcd n * (m * (n / m.gcd n)) = m * n := by
    rw [← mul_assoc, mul_comm (m.gcd n) m, mul_assoc,
      Nat.mul_div_cancel' (Nat.gcd_dvd_right m n)]
  have h2 : m.gcd n * (m * (n / m.gcd n)) = m.gcd n * m.lcm n := by
    rw [h1, ← h]
  exact (Nat.eq_of_mul_eq_mul_left hg h2).symm

/-- Pointwise bound `τ(n)² ≤ (τ * τ)(n)`.  Equivalently: the number of pairs of divisors of `n`
is at most the number of ordered factorisations of `n` into four factors. -/
theorem tau_sq_le_d4 (n : ℕ) : tauR n ^ 2 ≤ d4 n := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp [tauR, d4]
  have hn0 : n ≠ 0 := by omega
  set T : Finset (Σ A : ℕ, ℕ × ℕ) :=
    n.divisors.sigma (fun A => A.divisors ×ˢ (n / A).divisors) with hT
  set S : Finset (ℕ × ℕ) := n.divisors ×ˢ n.divisors with hS
  have hcard : S.card ≤ T.card := by
    apply Finset.card_le_card_of_injOn
      (fun pq : ℕ × ℕ => (⟨pq.1, (Nat.gcd pq.1 pq.2, pq.2 / Nat.gcd pq.1 pq.2)⟩ : Σ A : ℕ, ℕ × ℕ))
    · intro pq hpq
      simp only [Finset.mem_coe, hS, Finset.mem_product] at hpq
      obtain ⟨hp, hq⟩ := hpq
      have hpn : pq.1 ∣ n := (Nat.mem_divisors.mp hp).1
      have hqn : pq.2 ∣ n := (Nat.mem_divisors.mp hq).1
      have hp0 : 0 < pq.1 := Nat.pos_of_dvd_of_pos hpn (Nat.pos_of_ne_zero hn0)
      have hq0 : 0 < pq.2 := Nat.pos_of_dvd_of_pos hqn (Nat.pos_of_ne_zero hn0)
      rw [hT, Finset.mem_coe, Finset.mem_sigma]
      refine ⟨hp, ?_⟩
      rw [Finset.mem_product]
      refine ⟨Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left _ _, ne_of_gt hp0⟩, ?_⟩
      refine Nat.mem_divisors.mpr ⟨?_, ?_⟩
      · rw [Nat.dvd_div_iff_mul_dvd hpn]
        have hlcm : pq.1 * (pq.2 / Nat.gcd pq.1 pq.2) = pq.1.lcm pq.2 :=
          (lcm_eq_mul_div_gcd' hp0 hq0).symm
        rw [hlcm]
        exact Nat.lcm_dvd hpn hqn
      · have hle : pq.1 ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hpn
        exact ne_of_gt (Nat.div_pos hle hp0)
    · intro a ha b hb heq
      have h1 : a.1 = b.1 := congrArg (fun t : (Σ A : ℕ, ℕ × ℕ) => t.1) heq
      have hg : Nat.gcd a.1 a.2 = Nat.gcd b.1 b.2 :=
        congrArg (fun t : (Σ A : ℕ, ℕ × ℕ) => t.2.1) heq
      have h2 : a.2 / Nat.gcd a.1 a.2 = b.2 / Nat.gcd b.1 b.2 :=
        congrArg (fun t : (Σ A : ℕ, ℕ × ℕ) => t.2.2) heq
      have ha2 : a.2 = Nat.gcd a.1 a.2 * (a.2 / Nat.gcd a.1 a.2) :=
        (Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)).symm
      have hb2 : b.2 = Nat.gcd b.1 b.2 * (b.2 / Nat.gcd b.1 b.2) :=
        (Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)).symm
      have : a.2 = b.2 := by rw [ha2, hb2, h2, hg]
      exact Prod.ext h1 this
  have hScard : (S.card : ℝ) = tauR n ^ 2 := by
    rw [hS, Finset.card_product]
    simp only [tauR]
    push_cast
    ring
  have hTcard : (T.card : ℝ) = d4 n := by
    rw [hT, Finset.card_sigma]
    rw [d4]
    push_cast
    apply Finset.sum_congr rfl
    intro A hA
    rw [Finset.card_product]
    simp only [tauR]
    push_cast
    ring
  calc tauR n ^ 2 = (S.card : ℝ) := hScard.symm
    _ ≤ (T.card : ℝ) := by exact_mod_cast hcard
    _ = d4 n := hTcard

end Work.FIArea6Road
