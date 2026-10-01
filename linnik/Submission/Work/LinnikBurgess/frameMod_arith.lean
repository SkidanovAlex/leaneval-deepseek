import Mathlib
import Submission.Work.LinnikBurgess.frame_step_defs

namespace Work.LinnikBurgess

/-- `frameMod` is the product over the prime divisors of `d` of
`p ^ max 0 (v_p d - v_p 2 - v_p |a0 - a1|)`, rewritten in terms of `Nat.factorization`. -/
private lemma frameMod_eq_prod (d a0 a1 : ℕ) :
    frameMod d a0 a1
      = ∏ p ∈ d.primeFactors, p ^ (max 0 (d.factorization p
          - (2 : ℕ).factorization p
          - (((a0 : ℤ) - (a1 : ℤ)).natAbs).factorization p)) := by
  unfold frameMod
  refine Finset.prod_congr rfl fun p hp => ?_
  have hp' : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
  congr 1
  rw [← Nat.factorization_def 2 hp', ← Nat.factorization_def (((a0 : ℤ) - (a1 : ℤ)).natAbs) hp']

/-- The prime factorization of `frameMod`: at a prime `q` dividing `d` it is
`max 0 (v_q d - v_q 2 - v_q |a0 - a1|)`, and it vanishes otherwise. -/
private lemma frameMod_factorization (d a0 a1 q : ℕ) :
    (frameMod d a0 a1).factorization q
      = if q ∈ d.primeFactors then
          max 0 (d.factorization q - (2 : ℕ).factorization q
            - (((a0 : ℤ) - (a1 : ℤ)).natAbs).factorization q)
        else 0 := by
  rw [frameMod_eq_prod]
  rw [Nat.factorization_prod_apply (S := d.primeFactors)
        (g := fun p => p ^ (max 0 (d.factorization p - (2 : ℕ).factorization p
              - (((a0 : ℤ) - (a1 : ℤ)).natAbs).factorization p)))
        (fun p hp => pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero)]
  rw [Finset.sum_congr rfl (fun p hp => by
        rw [Nat.Prime.factorization_pow (Nat.prime_of_mem_primeFactors hp),
            Finsupp.single_apply])]
  rw [Finset.sum_ite_eq']

/-- The key exact identity: `frameMod d a0 a1 = d / gcd(d, 2 * |a0 - a1|)`, i.e.
`frameMod d a0 a1 * gcd(d, 2 * |a0 - a1|) = d`. -/
private lemma frameMod_mul_gcd_two_mul {d a0 a1 : ℕ} (hd : 0 < d) (h01 : a0 ≠ a1) :
    frameMod d a0 a1 * Nat.gcd d (2 * ((a0 : ℤ) - (a1 : ℤ)).natAbs) = d := by
  set n : ℕ := ((a0 : ℤ) - (a1 : ℤ)).natAbs with hn
  have hn0 : n ≠ 0 := by
    rw [hn, Int.natAbs_ne_zero]
    omega
  have hfac : ∀ q, (frameMod d a0 a1).factorization q
      = if q ∈ d.primeFactors then max 0 (d.factorization q
          - (2 : ℕ).factorization q - n.factorization q) else 0 := by
    intro q
    rw [frameMod_factorization d a0 a1 q, ← hn]
  have hm0 : frameMod d a0 a1 ≠ 0 := by
    rw [frameMod_eq_prod]
    exact Finset.prod_ne_zero_iff.mpr fun p hp =>
      pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero
  have hg0 : Nat.gcd d (2 * n) ≠ 0 := by
    have h := Nat.gcd_pos_of_pos_left (2 * n) hd
    omega
  rw [Nat.eq_of_factorization_eq (mul_ne_zero hm0 hg0) (Nat.ne_of_gt hd)]
  intro q
  rw [Nat.factorization_mul hm0 hg0, Finsupp.add_apply, hfac q,
      Nat.factorization_gcd (Nat.ne_of_gt hd) (by positivity : 2 * n ≠ 0),
      Finsupp.inf_apply, Nat.factorization_mul (by norm_num : (2:ℕ) ≠ 0) hn0,
      Finsupp.add_apply]
  by_cases hq : q ∈ d.primeFactors
  · rw [if_pos hq]
    omega
  · rw [if_neg hq]
    have hA : d.factorization q = 0 := by
      rw [Nat.factorization_eq_zero_iff]
      by_cases hqp : q.Prime
      · refine Or.inr (Or.inl fun hqd => hq ?_)
        exact Nat.mem_primeFactors.mpr ⟨hqp, hqd, Nat.ne_of_gt hd⟩
      · exact Or.inl hqp
    rw [hA]
    simp

/-- `gcd(d, 2 * n) ≤ gcd(d, n) * 2 ^ ω(d)`. -/
private lemma gcd_two_mul_le (d n : ℕ) (hd : 0 < d) :
    Nat.gcd d (2 * n) ≤ Nat.gcd d n * 2 ^ d.primeFactors.card := by
  rcases eq_or_ne n 0 with hn | hn
  · subst hn
    simp only [mul_zero, Nat.gcd_zero_right]
    exact Nat.le_mul_of_pos_right _ (pow_pos (by norm_num) (d.primeFactors.card))
  · by_cases hd1 : d = 1
    · subst hd1
      simp
    · have hω : 1 ≤ d.primeFactors.card := by
        obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hd1
        exact Finset.card_pos.mpr ⟨p, Nat.mem_primeFactors.mpr ⟨hp, hpd, Nat.ne_of_gt hd⟩⟩
      have h2 : 2 ≤ 2 ^ d.primeFactors.card := by
        have h := Nat.pow_le_pow_right (by norm_num : 0 < 2) hω
        simpa using h
      have hdiv : Nat.gcd d (2 * n) ∣ Nat.gcd d n * 2 := by
        rw [← Nat.factorization_le_iff_dvd (by positivity) (by positivity)]
        intro q
        rw [Nat.factorization_mul (Nat.gcd_pos_of_pos_left n hd).ne' (by norm_num : (2:ℕ) ≠ 0),
            Finsupp.add_apply,
            Nat.factorization_gcd (Nat.ne_of_gt hd) hn, Finsupp.inf_apply,
            Nat.factorization_gcd (Nat.ne_of_gt hd)
              (mul_ne_zero (by norm_num : (2:ℕ) ≠ 0) hn), Finsupp.inf_apply,
            Nat.factorization_mul (by norm_num : (2:ℕ) ≠ 0) hn, Finsupp.add_apply]
        omega
      calc Nat.gcd d (2 * n) ≤ Nat.gcd d n * 2 :=
            Nat.le_of_dvd (Nat.mul_pos (Nat.gcd_pos_of_pos_left n hd) (by norm_num)) hdiv
        _ ≤ Nat.gcd d n * 2 ^ d.primeFactors.card := Nat.mul_le_mul_left _ h2

/-- The frame modulus is at least `d / (gcd(d, |a0-a1|) · 2^ω(d))`: `d / frameMod d a0 a1 = ∏_{p∣d} p^(min(s_p, v_p(a0-a1)+v_p(2))) ≤ gcd(d,|a0-a1|) · 2^(d.primeFactors.card)`.  Hence `H / frameMod + 1 ≤ H·gcd(d,|a0-a1|)·2^ω(d)/d + 1`. -/
theorem frameMod_arith {d H a0 a1 : ℕ} (hd : 0 < d) (h01 : a0 ≠ a1) :
    (H : ℝ) / (frameMod d a0 a1 : ℝ) + 1
      ≤ (H : ℝ) * (Nat.gcd d (((a0 : ℤ) - (a1 : ℤ)).natAbs) : ℝ)
          * (2 : ℝ) ^ (d.primeFactors.card) / (d : ℝ) + 1 := by
  set n : ℕ := ((a0 : ℤ) - (a1 : ℤ)).natAbs with hn
  set m : ℕ := frameMod d a0 a1 with hm
  set g : ℕ := Nat.gcd d n with hg
  set ω : ℕ := d.primeFactors.card with hω
  have hn0 : n ≠ 0 := by
    rw [hn, Int.natAbs_ne_zero]
    omega
  have hm0 : 0 < m := by
    rw [hm, frameMod_eq_prod]
    exact Finset.prod_pos fun p hp => pow_pos (Nat.prime_of_mem_primeFactors hp).pos _
  have h1 : frameMod d a0 a1 * Nat.gcd d (2 * n) = d := by
    rw [hn]
    exact frameMod_mul_gcd_two_mul hd h01
  have h2 : Nat.gcd d (2 * n) ≤ Nat.gcd d n * 2 ^ d.primeFactors.card := gcd_two_mul_le d n hd
  have hineq : d ≤ m * (g * 2 ^ ω) := by
    rw [hm, hg, hω]
    calc d = frameMod d a0 a1 * Nat.gcd d (2 * n) := h1.symm
      _ ≤ frameMod d a0 a1 * (Nat.gcd d n * 2 ^ d.primeFactors.card) := Nat.mul_le_mul_left _ h2
  have hmR : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm0
  have hdR : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd
  have hcast : (d:ℝ) ≤ (m:ℝ) * ((g:ℝ) * (2:ℝ)^ω) := by exact_mod_cast hineq
  have hkey : (1:ℝ)/(m:ℝ) ≤ ((g:ℝ) * (2:ℝ)^ω)/(d:ℝ) := by
    rw [div_le_div_iff₀ hmR hdR]
    simpa [one_mul, mul_comm, mul_left_comm, mul_assoc] using hcast
  have hH : (0:ℝ) ≤ (H:ℝ) := Nat.cast_nonneg H
  calc (H:ℝ)/(m:ℝ) + 1
      = (H:ℝ) * ((1:ℝ)/(m:ℝ)) + 1 := by rw [mul_one_div]
    _ ≤ (H:ℝ) * (((g:ℝ) * (2:ℝ)^ω)/(d:ℝ)) + 1 := by
        exact add_le_add (mul_le_mul_of_nonneg_left hkey hH) le_rfl
    _ = (H:ℝ) * (g:ℝ) * (2:ℝ)^ω / (d:ℝ) + 1 := by ring

end Work.LinnikBurgess
