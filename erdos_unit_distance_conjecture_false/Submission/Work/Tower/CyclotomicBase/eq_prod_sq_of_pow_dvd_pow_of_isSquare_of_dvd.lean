import Mathlib

namespace Work.Tower.CyclotomicBase

theorem eq_prod_sq_of_pow_dvd_pow_of_isSquare_of_dvd {ℓ n : ℕ} {r : Fin ℓ → ℕ} {m : ℕ}
    (hn : 0 < n) (hr : ∀ i, Nat.Prime (r i)) (hrinj : Function.Injective r)
    (hsq : IsSquare m) (hdvd : ∀ i, r i ∣ m)
    (hpow : m ^ n ∣ (∏ i, r i ^ 2) ^ n) :
    m = ∏ i, r i ^ 2 := by
  -- Write `m = k * k` using that `m` is a square.
  obtain ⟨k, hk⟩ := hsq
  -- From `m ^ n ∣ (∏ i, r i ^ 2) ^ n` and `n ≠ 0` we get `m ∣ ∏ i, r i ^ 2`.
  have hle1 : m ∣ ∏ i, r i ^ 2 := (Nat.pow_dvd_pow_iff hn.ne').mp hpow
  -- Each prime `r i ∣ m = k * k` divides `k`.
  have hdk : ∀ i, r i ∣ k := by
    intro i
    have h := hdvd i
    rw [hk] at h
    rcases (hr i).dvd_mul.mp h with h | h <;> exact h
  -- The product of the distinct primes `∏ i, r i` divides `k`.
  have hPk : (∏ i, r i) ∣ k := by
    have himg : (∏ i, r i) = ∏ p ∈ Finset.image r Finset.univ, p :=
      (Finset.prod_image (f := fun p : ℕ => p) (s := Finset.univ) (g := r) hrinj.injOn).symm
    rw [himg]
    apply Finset.prod_primes_dvd k
    · intro a ha
      rw [Finset.mem_image] at ha
      obtain ⟨i, _, rfl⟩ := ha
      exact (hr i).prime
    · intro a ha
      rw [Finset.mem_image] at ha
      obtain ⟨i, _, rfl⟩ := ha
      exact hdk i
  -- Hence `∏ i, r i ^ 2 = (∏ i, r i) ^ 2 ∣ k ^ 2 = m`.
  have hle2 : (∏ i, r i ^ 2) ∣ m := by
    have h2 : (∏ i, r i) ^ 2 ∣ k ^ 2 := pow_dvd_pow_of_dvd hPk 2
    have e1 : (∏ i, r i) ^ 2 = ∏ i, r i ^ 2 := by
      rw [sq, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i _
      rw [sq]
    have e2 : k ^ 2 = m := by rw [sq, hk]
    rwa [e1, e2] at h2
  -- Both sides are positive, so divisibility both ways gives equality.
  have hP : 0 < ∏ i, r i ^ 2 := Finset.prod_pos fun i _ => pow_pos (hr i).pos 2
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · exfalso
      rw [h0] at hle1
      exact hP.ne' (Nat.eq_zero_of_zero_dvd hle1)
    · exact hpos
  exact Nat.le_antisymm (Nat.le_of_dvd hP hle1) (Nat.le_of_dvd hm hle2)

end Work.Tower.CyclotomicBase
