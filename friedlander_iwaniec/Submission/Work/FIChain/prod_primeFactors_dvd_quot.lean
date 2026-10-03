import Mathlib

namespace Work.FIChain

/-- If `g : ℕ → ℝ` is multiplicative on coprime arguments with `g 1 = 1`, then its value
on a product of distinct primes is the product of its values. -/
lemma g_prod_of_primes (g : ℕ → ℝ) (hg1 : g 1 = 1)
    (hgmul : ∀ m n : ℕ, Nat.Coprime m n → g (m * n) = g m * g n) :
    ∀ s : Finset ℕ, (∀ p ∈ s, p.Prime) → g (∏ p ∈ s, p) = ∏ p ∈ s, g p := by
  intro s
  induction s using Finset.induction_on with
  | empty => intro _; simp [hg1]
  | insert a s ha ih =>
    intro hs
    have hap : a.Prime := hs a (Finset.mem_insert_self a s)
    have hsp : ∀ p ∈ s, p.Prime := fun p hp => hs p (Finset.mem_insert_of_mem hp)
    have hcop : Nat.Coprime a (∏ p ∈ s, p) :=
      Nat.Coprime.prod_right fun p hp =>
        (Nat.coprime_primes hap (hsp p hp)).mpr (fun h => ha (h ▸ hp))
    rw [Finset.prod_insert ha, Finset.prod_insert ha, hgmul a _ hcop, ih hsp]

theorem prod_primeFactors_dvd_quot (g : ℕ → ℝ) (d N : ℕ)
    (hg1 : g 1 = 1) (hgmul : ∀ m n : ℕ, Nat.Coprime m n → g (m * n) = g m * g n)
    (hN : Squarefree N) :
    ∏ p ∈ N.primeFactors, (if p ∣ d then 1 else g p) = g (N / Nat.gcd N d) := by
  rcases eq_or_ne d 0 with rfl | hd
  · have hN0 : N ≠ 0 := hN.ne_zero
    have hg : Nat.gcd N 0 = N := Nat.gcd_zero_right N
    rw [hg, Nat.div_self (Nat.pos_of_ne_zero hN0), hg1]
    exact Finset.prod_eq_one fun p _ => by rw [if_pos (dvd_zero p)]
  · have hdvd : N / Nat.gcd N d ∣ N :=
      ⟨Nat.gcd N d, (Nat.div_mul_cancel (Nat.gcd_dvd_left N d)).symm⟩
    have hsq : Squarefree (N / Nat.gcd N d) := hN.squarefree_of_dvd hdvd
    have hpf : (N / Nat.gcd N d).primeFactors = N.primeFactors \ d.primeFactors :=
      Nat.primeFactors_div_gcd hN hd
    have hfilter : N.primeFactors.filter (fun p => ¬ p ∣ d) = N.primeFactors \ d.primeFactors := by
      ext p
      rw [Finset.mem_filter, Finset.mem_sdiff]
      constructor
      · rintro ⟨hpS, hpd⟩
        exact ⟨hpS, fun hpT => hpd ((Nat.mem_primeFactors_of_ne_zero hd).mp hpT).2⟩
      · rintro ⟨hpS, hpT⟩
        exact ⟨hpS, fun h => hpT ((Nat.mem_primeFactors_of_ne_zero hd).mpr
          ⟨Nat.prime_of_mem_primeFactors hpS, h⟩)⟩
    have hL : ∏ p ∈ N.primeFactors, (if p ∣ d then 1 else g p)
        = ∏ p ∈ N.primeFactors \ d.primeFactors, g p := by
      rw [← hfilter, Finset.prod_filter]
      apply Finset.prod_congr rfl
      intro p _
      by_cases h : p ∣ d <;> simp [h]
    have hR : g (N / Nat.gcd N d) = ∏ p ∈ N.primeFactors \ d.primeFactors, g p := by
      rw [← Nat.prod_primeFactors_of_squarefree hsq, hpf]
      exact g_prod_of_primes g hg1 hgmul _
        fun p hp => Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp hp).1
    rw [hL, hR]

end Work.FIChain
