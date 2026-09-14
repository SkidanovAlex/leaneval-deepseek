import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.NumberTheory.Harmonic.Bounds

open scoped BigOperators

namespace Commons.NumberTheory.Nat

/-- The **squarefree kernel** of `n`: the product of the primes dividing `n` to an odd power.
Equivalently, the unique squarefree `a` such that `n / a` is a square. -/
private def sqfreeKernel (n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors, p ^ (n.factorization p % 2)

/-- The **square root part** of `n`: the unique `b` with `n = sqfreeKernel n * b ^ 2`. -/
private def rootPart (n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors, p ^ (n.factorization p / 2)

private lemma sqfreeKernel_mul_rootPart_sq {n : ℕ} (hn : n ≠ 0) :
    sqfreeKernel n * rootPart n ^ 2 = n := by
  conv_rhs => rw [Nat.prod_primeFactors_pow_factorization hn]
  rw [sqfreeKernel, rootPart, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p _
  rw [← pow_mul, ← pow_add, mul_comm (n.factorization p / 2) 2, Nat.mod_add_div]

private lemma one_le_sqfreeKernel (n : ℕ) : 1 ≤ sqfreeKernel n := by
  rw [sqfreeKernel]
  exact Finset.one_le_prod fun p hp =>
    Nat.one_le_pow _ _ (Nat.prime_of_mem_primeFactors hp).pos

private lemma one_le_rootPart (n : ℕ) : 1 ≤ rootPart n := by
  rw [rootPart]
  exact Finset.one_le_prod fun p hp =>
    Nat.one_le_pow _ _ (Nat.prime_of_mem_primeFactors hp).pos

/-- The squarefree kernel of `n` is at most the radical of `n`. -/
private lemma sqfreeKernel_le_radical (n : ℕ) :
    sqfreeKernel n ≤ n.primeFactors.prod id := by
  rw [sqfreeKernel]
  apply Finset.prod_le_prod
  · intro p _; exact Nat.zero_le _
  · intro p hp
    calc p ^ (n.factorization p % 2) ≤ p ^ 1 :=
          Nat.pow_le_pow_right (Nat.prime_of_mem_primeFactors hp).pos (by
            have := Nat.mod_lt (n.factorization p) (by norm_num : 0 < 2); omega)
      _ = p := pow_one p

private lemma sqfreeKernel_le_self {n : ℕ} (hn : n ≠ 0) : sqfreeKernel n ≤ n :=
  (Nat.le_mul_of_pos_right _ (Nat.pow_pos (Nat.lt_of_lt_of_le Nat.zero_lt_one
    (one_le_rootPart n)))).trans_eq (sqfreeKernel_mul_rootPart_sq hn)

private lemma rootPart_sq_le_self {n : ℕ} (hn : n ≠ 0) : rootPart n ^ 2 ≤ n :=
  (Nat.le_mul_of_pos_left _ (Nat.lt_of_lt_of_le Nat.zero_lt_one
    (one_le_sqfreeKernel n))).trans_eq (sqfreeKernel_mul_rootPart_sq hn)

private lemma log_factorial_eq_sum (B : ℕ) :
    Real.log (Nat.factorial B : ℝ) = ∑ b ∈ Finset.Icc 1 B, Real.log (b : ℝ) := by
  induction B with
  | zero => simp
  | succ n ih =>
    rw [Nat.factorial_succ, Finset.sum_Icc_succ_top (Nat.le_add_left 1 n), Nat.cast_mul,
      Real.log_mul (by positivity) (by positivity), ih]
    ring

/-- Stirling-type bound: `B·log(B+1) - log(B!) ≤ B`. -/
private lemma log_factorial_ge (B : ℕ) :
    (B : ℝ) * Real.log ((B : ℝ) + 1) - (B : ℝ) ≤ Real.log (Nat.factorial B : ℝ) := by
  induction B with
  | zero => simp
  | succ n ih =>
    have hfac : (0 : ℝ) < ((Nat.factorial n : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos n
    rw [Nat.factorial_succ, Nat.cast_mul, Real.log_mul (by positivity) hfac.ne']
    push_cast
    have key : ((n : ℝ) + 1) * Real.log ((n : ℝ) + 1 + 1)
        - ((n : ℝ) + 1) * Real.log ((n : ℝ) + 1) ≤ 1 := by
      have hlog : Real.log ((n : ℝ) + 1 + 1) - Real.log ((n : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) := by
        rw [← Real.log_div (by positivity : ((n : ℝ) + 1 + 1) ≠ 0)
          (by positivity : ((n : ℝ) + 1) ≠ 0)]
        have hr : ((n : ℝ) + 1 + 1) / ((n : ℝ) + 1) = 1 + 1 / ((n : ℝ) + 1) := by
          field_simp
        rw [hr]
        simpa using Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 1 + 1 / ((n : ℝ) + 1))
      calc ((n : ℝ) + 1) * Real.log ((n : ℝ) + 1 + 1) - ((n : ℝ) + 1) * Real.log ((n : ℝ) + 1)
          = ((n : ℝ) + 1) * (Real.log ((n : ℝ) + 1 + 1) - Real.log ((n : ℝ) + 1)) := by ring
        _ ≤ ((n : ℝ) + 1) * (1 / ((n : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_left hlog (by positivity)
        _ = 1 := by field_simp
    linarith [ih, key]

private lemma sum_one_add_log_div_sq_le (N : ℕ) :
    (∑ b ∈ Finset.Icc 1 (Nat.sqrt N), (1 + Real.log ((N : ℝ) / (b : ℝ) ^ 2)))
      ≤ 3 * Real.sqrt (N : ℝ) := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp
  have hB1 : 1 ≤ Nat.sqrt N := Nat.le_sqrt.mpr (by omega)
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hterm : ∀ b ∈ Finset.Icc 1 (Nat.sqrt N),
      (1 + Real.log ((N : ℝ) / (b : ℝ) ^ 2)) = 1 + Real.log (N : ℝ) - 2 * Real.log (b : ℝ) := by
    intro b hb
    have hb1 : (0 : ℝ) < (b : ℝ) := by
      exact_mod_cast (Finset.mem_Icc.mp hb).1
    rw [Real.log_div hNpos.ne' (by positivity : (b : ℝ) ^ 2 ≠ 0), Real.log_pow]
    push_cast
    ring
  rw [Finset.sum_congr rfl hterm]
  have hsum : (∑ b ∈ Finset.Icc 1 (Nat.sqrt N),
        (1 + Real.log (N : ℝ) - 2 * Real.log (b : ℝ)))
      = (Nat.sqrt N : ℝ) + (Nat.sqrt N : ℝ) * Real.log (N : ℝ)
        - 2 * Real.log (Nat.factorial (Nat.sqrt N) : ℝ) := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.sum_const, log_factorial_eq_sum, Nat.card_Icc]
    simp
  rw [hsum]
  have hsqrtB : (Nat.sqrt N : ℝ) ≤ Real.sqrt (N : ℝ) := by
    rw [Real.le_sqrt (by positivity) (by positivity)]
    have h : Nat.sqrt N * Nat.sqrt N ≤ N := (Nat.le_sqrt (m := Nat.sqrt N) (n := N)).mp le_rfl
    exact_mod_cast (show Nat.sqrt N ^ 2 ≤ N by simpa [pow_two] using h)
  have hlogN : Real.log (N : ℝ) < 2 * Real.log ((Nat.sqrt N : ℝ) + 1) := by
    have hlt : (N : ℝ) < ((Nat.sqrt N : ℝ) + 1) ^ 2 := by
      have h := Nat.lt_succ_sqrt N
      have h' : (((Nat.sqrt N).succ : ℕ) : ℝ) * (((Nat.sqrt N).succ : ℕ) : ℝ)
          = ((Nat.sqrt N : ℝ) + 1) ^ 2 := by
        push_cast [Nat.succ_eq_add_one]; ring
      rw [← h']
      exact_mod_cast h
    calc Real.log (N : ℝ) < Real.log (((Nat.sqrt N : ℝ) + 1) ^ 2) :=
          Real.log_lt_log hNpos hlt
      _ = 2 * Real.log ((Nat.sqrt N : ℝ) + 1) := by
          rw [Real.log_pow]; push_cast; ring
  have hBpos : (0 : ℝ) < (Nat.sqrt N : ℝ) := by exact_mod_cast hB1
  have key := log_factorial_ge (Nat.sqrt N)
  nlinarith [hlogN, hBpos, key, hsqrtB]

private lemma sum_Icc_one_div_le_one_add_log (M : ℕ) :
    (∑ a ∈ Finset.Icc 1 M, (1 : ℝ) / (a : ℝ)) ≤ 1 + Real.log (M : ℝ) := by
  have h := harmonic_le_one_add_log M
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at h
  simpa [one_div] using h

/-- `∑_{n ≤ N} 1/rad(n) ≤ 3 √N`, where `rad n = ∏_{p | n} p` is the radical.
(The true asymptotic is `(6/π²)·`-normalised `~ ζ(3/2) √N`, so `3√N` is comfortable.) -/
theorem sum_inv_radical_le_sqrt (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / ((n.primeFactors.prod id : ℕ) : ℝ))
      ≤ 3 * Real.sqrt (N : ℝ) := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp
  -- Step 1: replace the radical by the squarefree kernel.
  have step1 : (∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / ((n.primeFactors.prod id : ℕ) : ℝ))
      ≤ ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / (sqfreeKernel n : ℝ) := by
    apply Finset.sum_le_sum
    intro n _
    exact one_div_le_one_div_of_le (by exact_mod_cast one_le_sqfreeKernel n)
      (by exact_mod_cast sqfreeKernel_le_radical n)
  -- Step 2: reindex `n ↦ (sqfreeKernel n, rootPart n)` into a sum over pairs.
  have hinj : Set.InjOn (fun n : ℕ => (sqfreeKernel n, rootPart n)) ↑(Finset.Icc 1 N) := by
    intro x hx y hy hxy
    simp only [Finset.mem_coe, Finset.mem_Icc] at hx hy
    have hx0 : x ≠ 0 := by omega
    have hy0 : y ≠ 0 := by omega
    have h1 : sqfreeKernel x = sqfreeKernel y := by simpa using congrArg Prod.fst hxy
    have h2 : rootPart x = rootPart y := by simpa using congrArg Prod.snd hxy
    calc x = sqfreeKernel x * rootPart x ^ 2 := (sqfreeKernel_mul_rootPart_sq hx0).symm
      _ = sqfreeKernel y * rootPart y ^ 2 := by rw [h1, h2]
      _ = y := sqfreeKernel_mul_rootPart_sq hy0
  have hmem : ∀ n ∈ Finset.Icc 1 N,
      (sqfreeKernel n, rootPart n) ∈ ((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 (Nat.sqrt N))).filter
        (fun p : ℕ × ℕ => p.1 * p.2 ^ 2 ≤ N) := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hn ⊢
    obtain ⟨hn1, hnN⟩ := hn
    have hn0 : n ≠ 0 := by omega
    have hsq : rootPart n ≤ Nat.sqrt N :=
      Nat.le_sqrt.mpr (by simpa [pow_two] using le_trans (rootPart_sq_le_self hn0) hnN)
    exact ⟨⟨⟨one_le_sqfreeKernel n, le_trans (sqfreeKernel_le_self hn0) hnN⟩,
      ⟨one_le_rootPart n, hsq⟩⟩, le_trans (le_of_eq (sqfreeKernel_mul_rootPart_sq hn0)) hnN⟩
  have step2 : (∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / (sqfreeKernel n : ℝ))
      ≤ ∑ p ∈ ((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 (Nat.sqrt N))).filter
            (fun p : ℕ × ℕ => p.1 * p.2 ^ 2 ≤ N), (1 : ℝ) / (p.1 : ℝ) := by
    rw [← Finset.sum_image (f := fun p : ℕ × ℕ => (1 : ℝ) / (p.1 : ℝ)) hinj]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hp
      exact hmem n hn
    · intro p hp _
      have hp1 : 1 ≤ p.1 := (Finset.mem_Icc.mp (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1).1
      have : (0 : ℝ) < (p.1 : ℝ) := by exact_mod_cast hp1
      positivity
  -- Step 3: bound the pair sum by an explicit sum over `b`.
  have step3 : (∑ p ∈ ((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 (Nat.sqrt N))).filter
          (fun p : ℕ × ℕ => p.1 * p.2 ^ 2 ≤ N), (1 : ℝ) / (p.1 : ℝ))
      ≤ ∑ b ∈ Finset.Icc 1 (Nat.sqrt N),
          (1 + Real.log ((N : ℝ) / (b : ℝ) ^ 2)) := by
    rw [Finset.sum_filter, Finset.sum_product, Finset.sum_comm]
    apply Finset.sum_le_sum
    intro b hb
    have hb1 : 1 ≤ b := (Finset.mem_Icc.mp hb).1
    have hbB : b ≤ Nat.sqrt N := (Finset.mem_Icc.mp hb).2
    have hbpos : 0 < b ^ 2 := pow_pos (by omega) 2
    have hb2N : b ^ 2 ≤ N := by
      calc b ^ 2 ≤ (Nat.sqrt N) ^ 2 := Nat.pow_le_pow_left hbB 2
        _ = Nat.sqrt N * Nat.sqrt N := pow_two _
        _ ≤ N := Nat.le_sqrt.mp le_rfl
    calc ∑ a ∈ Finset.Icc 1 N, (if a * b ^ 2 ≤ N then (1 : ℝ) / (a : ℝ) else 0)
        = ∑ a ∈ (Finset.Icc 1 N).filter (fun a => a * b ^ 2 ≤ N), (1 : ℝ) / (a : ℝ) := by
          rw [Finset.sum_filter]
      _ ≤ ∑ a ∈ Finset.Icc 1 (N / b ^ 2), (1 : ℝ) / (a : ℝ) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro a ha
            rw [Finset.mem_filter] at ha
            exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp ha.1).1,
              (Nat.le_div_iff_mul_le hbpos).mpr ha.2⟩
          · intro a ha _
            have ha1 : 1 ≤ a := (Finset.mem_Icc.mp ha).1
            have : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha1
            positivity
      _ ≤ 1 + Real.log ((N : ℝ) / (b : ℝ) ^ 2) := by
          have hpos : 0 < ((N / b ^ 2 : ℕ) : ℝ) := by
            have : 1 ≤ N / b ^ 2 := (Nat.le_div_iff_mul_le hbpos).mpr (by simpa using hb2N)
            exact_mod_cast this
          have hle : ((N / b ^ 2 : ℕ) : ℝ) ≤ (N : ℝ) / (b : ℝ) ^ 2 := by
            rw [← Nat.cast_pow]
            exact Nat.cast_div_le (α := ℝ)
          have := Real.log_le_log hpos hle
          linarith [sum_Icc_one_div_le_one_add_log (N / b ^ 2)]
  calc _ ≤ _ := step1
    _ ≤ _ := step2
    _ ≤ _ := step3
    _ ≤ 3 * Real.sqrt (N : ℝ) := sum_one_add_log_div_sq_le N

end Commons.NumberTheory.Nat