import Mathlib

namespace Work.ZeroDensity.Montgomery

open Finset Nat

/-- The summand `‖{d ∣ m : Squarefree d}‖` indicator weighted by inverse factors,
used to reindex `∑ 2 ^ ω(m) / m`.  It equals the indicator of `Squarefree d`
times `1/d * 1/k`. -/
noncomputable def Gfun (d k : ℕ) : ℝ := (if Squarefree d then 1 else 0 : ℝ) * (d:ℝ)⁻¹ * (k:ℝ)⁻¹

/-- The number of squarefree divisors of `m` equals `2 ^ ω(m)`, where `ω(m)` is the
number of distinct prime factors of `m`. -/
lemma twoPowOmega_card_sqfree (m : ℕ) (hm : 0 < m) :
    (2 : ℝ) ^ m.primeFactors.card
      = ∑ d ∈ m.divisors, (if Squarefree d then 1 else 0 : ℝ) := by
  have hcardNat : (m.divisors.filter Squarefree).card = 2 ^ m.primeFactors.card := by
    have h1 := sum_divisors_filter_squarefree (n := m) hm.ne' (f := fun _ : ℕ => (1:ℕ))
    simp only [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_powerset] at h1
    rw [h1, (by rw [factors_eq]; simp :
      ((UniqueFactorizationMonoid.normalizedFactors m).toFinset).card = m.primeFactors.card)]
  have hcardR : ((m.divisors.filter Squarefree).card : ℝ) = (2:ℝ) ^ m.primeFactors.card := by
    rw [hcardNat]; push_cast; ring
  rw [← hcardR, Finset.card_filter]
  push_cast
  rfl

/-- Discrete hyperbola (Dirichlet) reindexing:
`∑_{n ≤ N} ∑_{d ∣ n} f d (n/d) = ∑_{d ≤ N} ∑_{k ≤ N/d} f d k`. -/
lemma sum_Ioc_divisors_swap {R : Type*} [AddCommMonoid R] (N : ℕ) (f : ℕ → ℕ → R) :
    (∑ n ∈ Finset.Ioc 0 N, ∑ d ∈ n.divisors, f d (n / d))
      = ∑ d ∈ Finset.Ioc 0 N, ∑ k ∈ Finset.Ioc 0 (N / d), f d k := by
  have hL : (∑ n ∈ Finset.Ioc 0 N, ∑ d ∈ n.divisors, f d (n / d))
      = ∑ x ∈ (Finset.Ioc 0 N).sigma (fun n => n.divisorsAntidiagonal),
          f x.2.1 x.2.2 := by
    rw [Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro n hn
    rw [Nat.sum_divisorsAntidiagonal]
  have hR : (∑ d ∈ Finset.Ioc 0 N, ∑ k ∈ Finset.Ioc 0 (N / d), f d k)
      = ∑ y ∈ (Finset.Ioc 0 N).sigma (fun d => Finset.Ioc 0 (N / d)),
          f y.1 y.2 := by
    rw [Finset.sum_sigma]
  rw [hL, hR]
  refine Finset.sum_bij (fun x _ => (⟨x.2.1, x.2.2⟩ : Sigma (fun _ : ℕ => ℕ))) ?_ ?_ ?_ ?_
  · intro x hx
    obtain ⟨hx1, hx2⟩ := Finset.mem_sigma.mp hx
    obtain ⟨hx1a, hx1b⟩ := Finset.mem_Ioc.mp hx1
    obtain ⟨hmul, hne⟩ := Nat.mem_divisorsAntidiagonal.mp hx2
    have hd : x.2.1 ∈ x.1.divisors := Nat.fst_mem_divisors_of_mem_antidiagonal hx2
    have hk : x.2.2 ∈ x.1.divisors := Nat.snd_mem_divisors_of_mem_antidiagonal hx2
    have hdpos : 0 < x.2.1 := Nat.pos_of_mem_divisors hd
    have hkpos : 0 < x.2.2 := Nat.pos_of_mem_divisors hk
    rw [Finset.mem_sigma]
    refine ⟨?_, ?_⟩
    · rw [Finset.mem_Ioc]
      exact ⟨hdpos, le_trans (Nat.le_of_dvd hx1a (Nat.dvd_of_mem_divisors hd)) hx1b⟩
    · rw [Finset.mem_Ioc]
      refine ⟨hkpos, ?_⟩
      rw [Nat.le_div_iff_mul_le hdpos, mul_comm, hmul]
      exact hx1b
  · intro x hx y hy hxy
    have hxy' : x.2.1 = y.2.1 ∧ x.2.2 = y.2.2 := by
      have h := hxy; rw [Sigma.mk.injEq] at h; exact ⟨h.1, eq_of_heq h.2⟩
    obtain ⟨e1, e2⟩ := hxy'
    obtain ⟨hxm, -⟩ := Nat.mem_divisorsAntidiagonal.mp (Finset.mem_sigma.mp hx).2
    obtain ⟨hym, -⟩ := Nat.mem_divisorsAntidiagonal.mp (Finset.mem_sigma.mp hy).2
    have h1 : x.1 = y.1 := by rw [← hxm, ← hym, e1, e2]
    exact Sigma.ext h1 (heq_of_eq (Prod.ext e1 e2))
  · intro b hb
    obtain ⟨hb1, hb2⟩ := Finset.mem_sigma.mp hb
    obtain ⟨hb1a, hb1b⟩ := Finset.mem_Ioc.mp hb1
    obtain ⟨hb2a, hb2b⟩ := Finset.mem_Ioc.mp hb2
    refine ⟨⟨b.1 * b.2, (b.1, b.2)⟩, ?_, ?_⟩
    · rw [Finset.mem_sigma]
      refine ⟨?_, ?_⟩
      · rw [Finset.mem_Ioc]
        refine ⟨Nat.mul_pos hb1a hb2a, ?_⟩
        rw [Nat.le_div_iff_mul_le hb1a] at hb2b
        calc b.1 * b.2 = b.2 * b.1 := by ring
          _ ≤ N := hb2b
      · rw [Nat.mem_divisorsAntidiagonal]
        exact ⟨rfl, Nat.mul_ne_zero (ne_of_gt hb1a) (ne_of_gt hb2a)⟩
    · rfl
  · intro x hx
    rfl

theorem twoPowOmegaDivSum_le (M : ℕ) :
    ∑ m ∈ Finset.Ioc 0 M, (2 : ℝ) ^ (m.primeFactors.card) / (m : ℝ)
      ≤ (1 + Real.log (M : ℝ)) ^ 2 := by
  rcases Nat.eq_zero_or_pos M with h0 | hM
  · subst h0; simp
  have hterm : ∀ m : ℕ, m ≠ 0 → (2:ℝ)^(m.primeFactors.card) / (m:ℝ)
      = ∑ d ∈ m.divisors, Gfun d (m / d) := by
    intro m hmne
    rw [twoPowOmega_card_sqfree m (Nat.pos_of_ne_zero hmne), Finset.sum_div]
    apply Finset.sum_congr rfl
    intro d hd
    have hdvd : d ∣ m := Nat.dvd_of_mem_divisors hd
    have hinv : (d:ℝ)⁻¹ * ((m/d:ℕ):ℝ)⁻¹ = (m:ℝ)⁻¹ := by
      rw [← mul_inv, ← Nat.cast_mul, Nat.mul_div_cancel' hdvd]
    change (if Squarefree d then (1:ℝ) else 0) / (m:ℝ)
      = (if Squarefree d then (1:ℝ) else 0) * (d:ℝ)⁻¹ * ((m/d:ℕ):ℝ)⁻¹
    rw [div_eq_mul_inv, mul_assoc, hinv]
  have hHle : (∑ k ∈ Finset.Ioc 0 M, (k:ℝ)⁻¹) ≤ 1 + Real.log (M:ℝ) := by
    have hIoc : Finset.Ioc 0 M = Finset.Icc 1 M := by
      ext x; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
    rw [hIoc]
    have hcast : (∑ k ∈ Finset.Icc 1 M, (k:ℝ)⁻¹) = ((harmonic M : ℚ) : ℝ) := by
      rw [harmonic_eq_sum_Icc, Rat.cast_sum]
      apply Finset.sum_congr rfl
      intro k hk
      simp only [Rat.cast_inv, Rat.cast_natCast]
    rw [hcast]
    exact harmonic_le_one_add_log M
  have hHnn : 0 ≤ ∑ k ∈ Finset.Ioc 0 M, (k:ℝ)⁻¹ :=
    Finset.sum_nonneg (fun k hk => by
      have hk0 : (0:ℝ) < (k:ℝ) := by exact_mod_cast (Finset.mem_Ioc.mp hk).1
      exact le_of_lt (inv_pos.mpr hk0))
  have hLnn : 0 ≤ 1 + Real.log (M:ℝ) := by
    have := Real.log_nonneg (show (1:ℝ) ≤ (M:ℝ) by exact_mod_cast hM)
    linarith
  calc ∑ m ∈ Finset.Ioc 0 M, (2:ℝ)^(m.primeFactors.card)/(m:ℝ)
      = ∑ m ∈ Finset.Ioc 0 M, ∑ d ∈ m.divisors, Gfun d (m/d) := by
          apply Finset.sum_congr rfl
          intro m hm
          exact hterm m (Finset.mem_Ioc.mp hm).1.ne'
    _ = ∑ d ∈ Finset.Ioc 0 M, ∑ k ∈ Finset.Ioc 0 (M/d), Gfun d k :=
          sum_Ioc_divisors_swap M Gfun
    _ ≤ ∑ d ∈ Finset.Ioc 0 M, ∑ k ∈ Finset.Ioc 0 (M/d), (d:ℝ)⁻¹ * (k:ℝ)⁻¹ := by
          apply Finset.sum_le_sum
          intro d hd
          apply Finset.sum_le_sum
          intro k hk
          unfold Gfun
          have hind : (if Squarefree d then (1:ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
          have hpos : 0 ≤ (d:ℝ)⁻¹ * (k:ℝ)⁻¹ := by
            have hd0 : (0:ℝ) < (d:ℝ) := by exact_mod_cast (Finset.mem_Ioc.mp hd).1
            have hk0 : (0:ℝ) < (k:ℝ) := by exact_mod_cast (Finset.mem_Ioc.mp hk).1
            positivity
          calc (if Squarefree d then (1:ℝ) else 0) * (d:ℝ)⁻¹ * (k:ℝ)⁻¹
              = (if Squarefree d then (1:ℝ) else 0) * ((d:ℝ)⁻¹ * (k:ℝ)⁻¹) := by ring
            _ ≤ 1 * ((d:ℝ)⁻¹ * (k:ℝ)⁻¹) := mul_le_mul_of_nonneg_right hind hpos
            _ = (d:ℝ)⁻¹ * (k:ℝ)⁻¹ := by ring
    _ ≤ ∑ d ∈ Finset.Ioc 0 M, ∑ k ∈ Finset.Ioc 0 M, (d:ℝ)⁻¹ * (k:ℝ)⁻¹ := by
          apply Finset.sum_le_sum
          intro d hd
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro k hk
            rw [Finset.mem_Ioc] at hk ⊢
            exact ⟨hk.1, le_trans hk.2 (Nat.div_le_self M d)⟩
          · intro k hk hknot
            have hd0 : (0:ℝ) < (d:ℝ) := by exact_mod_cast (Finset.mem_Ioc.mp hd).1
            have hk0 : (0:ℝ) < (k:ℝ) := by exact_mod_cast (Finset.mem_Ioc.mp hk).1
            positivity
    _ = (∑ d ∈ Finset.Ioc 0 M, (d:ℝ)⁻¹) * (∑ k ∈ Finset.Ioc 0 M, (k:ℝ)⁻¹) := by
          rw [Finset.sum_mul_sum]
    _ ≤ (1 + Real.log (M:ℝ)) ^ 2 := by
          have hself : (∑ d ∈ Finset.Ioc 0 M, (d:ℝ)⁻¹) = ∑ k ∈ Finset.Ioc 0 M, (k:ℝ)⁻¹ :=
            Finset.sum_congr rfl (fun _ _ => rfl)
          rw [hself, pow_two]
          exact mul_self_le_mul_self hHnn hHle

end Work.ZeroDensity.Montgomery
