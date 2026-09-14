import Mathlib.Data.Nat.Squarefree

set_option autoImplicit false
open scoped BigOperators

namespace Commons.NumberTheory.Nat

/-- If a prime divides `b` then its square divides `b ^ 3`. -/
private lemma sq_dvd_pow_three_of_dvd {p b : ℕ} (h : p ∣ b) : p ^ 2 ∣ b ^ 3 := by
  have hb2 : p ^ 2 ∣ b ^ 2 := pow_dvd_pow_of_dvd h 2
  have hb3 : b ^ 2 ∣ b ^ 3 := ⟨b, by ring⟩
  exact dvd_trans hb2 hb3

/-- `(a^2 * b^3)` with `b` squarefree is squarefull.  (reverse direction) -/
private lemma squarefull_of_sq_mul_cube {a b N : ℕ} (hN : N = a ^ 2 * b ^ 3) :
    ∀ p : ℕ, Nat.Prime p → p ∣ N → p ^ 2 ∣ N := by
  intro p pp hpd
  have hpd' : p ∣ a ^ 2 * b ^ 3 := by simpa [hN] using hpd
  rcases (Nat.Prime.dvd_mul pp).1 hpd' with hpa | hpb
  · have hpa' : p ∣ a := pp.dvd_of_dvd_pow hpa
    have hpsq : p ^ 2 ∣ a ^ 2 := pow_dvd_pow_of_dvd hpa' 2
    simpa [hN] using (dvd_trans hpsq (⟨b ^ 3, rfl⟩ : a ^ 2 ∣ a ^ 2 * b ^ 3))
  · have hpb' : p ∣ b := pp.dvd_of_dvd_pow hpb
    have hpsq : p ^ 2 ∣ b ^ 3 := sq_dvd_pow_three_of_dvd hpb'
    have hb3dvd : b ^ 3 ∣ a ^ 2 * b ^ 3 := ⟨a ^ 2, by rw [mul_comm]⟩
    simpa [hN] using (dvd_trans hpsq hb3dvd)

/-- `(p ^ k) ^ 2 = p ^ (2 * k)` -/
private lemma pow_sq_eq_pow_two_mul (p k : ℕ) : (p ^ k) ^ 2 = p ^ (2 * k) := by
  symm
  rw [mul_comm, pow_mul]

/-- A squarefull (every prime divisor to at least the second power) positive natural
  number is of the form `a ^ 2 * b ^ 3` with `b` squarefree.  (forward direction,
  proved by strong induction stripping off one exact prime power at a time) -/
private lemma exists_sq_mul_cube_of_squarefull (N : ℕ) (hN : N ≠ 0)
    (hsq : ∀ p : ℕ, Nat.Prime p → p ∣ N → p ^ 2 ∣ N) :
    ∃ a b : ℕ, Squarefree b ∧ N = a ^ 2 * b ^ 3 := by
  let P : ℕ → Prop := fun m => m ≠ 0 →
      (∀ p : ℕ, Nat.Prime p → p ∣ m → p ^ 2 ∣ m) → ∃ a b : ℕ, Squarefree b ∧ m = a ^ 2 * b ^ 3
  have hmain : ∀ n : ℕ, (∀ k : ℕ, k < n → P k) → P n := by
    intro n ih hn0 hsqn
    by_cases hn1 : n = 1
    · subst n
      refine ⟨1, 1, ?_, ?_⟩
      · exact squarefree_one
      · norm_num
    · obtain ⟨p, pp, hpdn⟩ := Nat.exists_prime_and_dvd hn1
      let e := n.factorization p
      have he1 : 1 ≤ e := by
        dsimp [e]
        exact (pp.dvd_iff_one_le_factorization hn0).mp hpdn
      have hsq2 : p ^ 2 ∣ n := hsqn p pp hpdn
      have he2 : 2 ≤ e := by
        dsimp [e]
        exact (pp.pow_dvd_iff_le_factorization (k := 2) hn0).mp hsq2
      have hxdn : p ^ e ∣ n := by
        simpa [e] using (Nat.ordProj_dvd n p)
      let M := n / p ^ e
      have hxM : p ^ e * M = n := by
        dsimp [M]
        exact Nat.mul_div_cancel' hxdn
      have hM0 : M ≠ 0 := by
        intro hM0
        exact hn0 (by simpa [hM0] using hxM.symm)
      have hx1 : 1 < p ^ e := by
        exact Nat.one_lt_pow (ne_of_gt (by omega : 0 < e)) pp.one_lt
      have hMlt : M < n := by
        dsimp [M]
        exact Nat.div_lt_self (Nat.pos_of_ne_zero hn0) hx1
      have hMdn : M ∣ n := by
        exact ⟨p ^ e, by rw [mul_comm, hxM]⟩
      -- the prime `p` no longer divides `M`
      have hpnM : ¬ p ∣ M := by
        intro hpd
        have hdiv : p ^ e * p ∣ n := (Nat.dvd_div_iff_mul_dvd hxdn).mp (by simpa [M] using hpd)
        have hpows : p ^ e * p = p ^ (e + 1) := (pow_succ p e).symm
        have hpd3 : p ^ (e + 1) ∣ n := by simpa [hpows] using hdiv
        exact (Nat.pow_succ_factorization_not_dvd hn0 pp) (by simpa [e] using hpd3)
      -- `M` is still squarefull
      have hMsq : ∀ q : ℕ, Nat.Prime q → q ∣ M → q ^ 2 ∣ M := by
        intro q qq hqM
        have hqn : q ∣ n := dvd_trans hqM hMdn
        have hq2n : q ^ 2 ∣ n := hsqn q qq hqn
        have hq2xM : q ^ 2 ∣ p ^ e * M := by simpa [← hxM] using hq2n
        by_cases hqp : q = p
        · subst q
          exact False.elim (hpnM hqM)
        · have hcop1 : q.Coprime p := (Nat.coprime_primes qq pp).2 hqp
          have hcop2 : q.Coprime (p ^ e) := hcop1.pow_right e
          have hcop3 : (q ^ 2).Coprime (p ^ e) := hcop2.pow_left 2
          have hq2Mp : q ^ 2 ∣ M * p ^ e := by simpa [mul_comm] using hq2xM
          exact hcop3.dvd_of_dvd_mul_right hq2Mp
      obtain ⟨aM, bM, hbM, hMb⟩ := ih M hMlt hM0 hMsq
      rcases Nat.even_or_odd e with heven | hodd
      · rcases heven with ⟨k, hk⟩
        refine ⟨aM * p ^ k, bM, hbM, ?_⟩
        calc
          n = p ^ e * M := hxM.symm
          _ = p ^ (k + k) * M := by rw [hk]
          _ = (p ^ k) ^ 2 * M := by rw [pow_add, ← pow_two]
          _ = (p ^ k) ^ 2 * (aM ^ 2 * bM ^ 3) := by rw [hMb]
          _ = (aM * p ^ k) ^ 2 * bM ^ 3 := by rw [mul_pow]; ring
      · rcases hodd with ⟨k, hk⟩
        have hk1 : 1 ≤ k := by omega
        have hbM_dvd_M : bM ^ 3 ∣ M := by
          exact ⟨aM ^ 2, by rw [hMb, mul_comm]⟩
        have hpnbM : ¬ p ∣ bM := by
          intro hpd
          have hpd3 : p ∣ bM ^ 3 := dvd_pow hpd (by norm_num : 3 ≠ 0)
          exact hpnM (dvd_trans hpd3 hbM_dvd_M)
        have hcopbMp : bM.Coprime p := by
          exact ((pp.coprime_iff_not_dvd).2 hpnbM).symm
        have hsqp : Squarefree p := by
          simpa using (Prime.squarefree (Nat.prime_iff.mp pp))
        refine ⟨aM * p ^ (k - 1), bM * p, ?_, ?_⟩
        · exact (Nat.squarefree_mul hcopbMp).2 ⟨hbM, hsqp⟩
        · calc
            n = p ^ e * M := hxM.symm
            _ = p ^ (2 * k + 1) * M := by rw [hk]
            _ = p ^ (2 * (k - 1) + 3) * M := by
              exact congrArg (fun z : ℕ => p ^ z * M) (by omega)
            _ = p ^ (2 * (k - 1)) * p ^ 3 * M := by rw [pow_add]
            _ = (p ^ (k - 1)) ^ 2 * p ^ 3 * M := by rw [← pow_sq_eq_pow_two_mul]
            _ = (p ^ (k - 1)) ^ 2 * p ^ 3 * (aM ^ 2 * bM ^ 3) := by rw [hMb]
            _ = (aM * p ^ (k - 1)) ^ 2 * (bM * p) ^ 3 := by
              rw [mul_pow, mul_pow]
              ring
  exact Nat.strong_induction_on N hmain hN hsq

theorem squarefull_iff_exists_sq_mul_cube (N : ℕ) (hN : N ≠ 0) :
    (∀ p : ℕ, Nat.Prime p → p ∣ N → p ^ 2 ∣ N) ↔
      ∃ a b : ℕ, Squarefree b ∧ N = a ^ 2 * b ^ 3 := by
  constructor
  · exact exists_sq_mul_cube_of_squarefull N hN
  · rintro ⟨a, b, hb, hNab⟩
    exact squarefull_of_sq_mul_cube hNab

end Commons.NumberTheory.Nat