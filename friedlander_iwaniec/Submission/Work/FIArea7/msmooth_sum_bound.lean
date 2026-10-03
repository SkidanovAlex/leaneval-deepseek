import Mathlib
import Submission.Work.FIArea7.MSmoothDefs
import Submission.Work.FIArea7.hfac_mul_of_coprime
import Submission.Work.FIArea7.xp_le_of_prime_le_23
import Submission.Work.FIArea7.sum_divisors_mul_of_coprime
import Submission.Work.FIArea7.summand_eq_hfac
import Submission.Work.FIArea7.geom_pow_sum_bound
import Submission.Work.FIArea7.xp_le_of_prime_ge_29

set_option autoImplicit false

namespace Work.FIArea7

open Finset

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## Part 1: elementary nonnegativity -/

lemma hterm_nonneg (m p i : ℕ) : 0 ≤ hterm m p i := by
  rw [hterm]
  have : 0 ≤ xp p := xp_nonneg p
  positivity

lemma hfac_nonneg (m k : ℕ) : 0 ≤ hfac m k := by
  rw [hfac]
  exact Finset.prod_nonneg fun p _ => hterm_nonneg m p _

/-! ## Part 2: `hfac m` at prime powers -/

lemma hfac_prime_pow (m p i : ℕ) (hp : p ∈ m.primeFactors) :
    hfac m (p ^ i) = hterm m p i := by
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  rw [hfac, Finset.prod_eq_single_of_mem p hp, Nat.factorization_pow_self hpp]
  intro q _ hqp
  have h1 : (p ^ i).factorization q = 0 := by
    rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
    have h2 : p.factorization q = 0 := by
      rw [hpp.factorization, Finsupp.single_eq_of_ne hqp]
    rw [h2, mul_zero]
  rw [h1, hterm_zero]

/-! ## Part 3: the Euler product for the normalised divisor sum -/

lemma Hsum_mul (m a b : ℕ) (h : a.Coprime b) : Hsum m (a * b) = Hsum m a * Hsum m b :=
  sum_divisors_mul_of_coprime h fun _ _ hc => hfac_mul_of_coprime m _ _ hc

lemma Hsum_euler (m J : ℕ) (hm : 1 ≤ m) :
    Hsum m (m ^ J) = ∏ p ∈ (m ^ J).primeFactors,
      ∑ i ∈ Finset.range ((m ^ J).factorization p + 1), hfac m (p ^ i) := by
  have hne : m ^ J ≠ 0 := pow_ne_zero _ (by omega)
  rw [Nat.multiplicative_factorization (Hsum m) (fun x y h => Hsum_mul m x y h) (Hsum_one m) hne,
    Finsupp.prod, Nat.support_factorization]
  refine Finset.prod_congr rfl fun p hp => ?_
  rw [Hsum, Nat.sum_divisors_prime_pow (Nat.prime_of_mem_primeFactors hp)]

/-! ## Part 4: the per-prime bound -/

/-- The unnormalised per-prime inequality (the arithmetic input of (23.11)). -/
lemma xp_pow_sum_le (p M a : ℕ) (hp : p.Prime) (ha : 1 ≤ a) :
    ∑ i ∈ Finset.range (M + 1), (((a + i + 1 : ℕ) : ℝ)) ^ 2 * (xp p) ^ i
      ≤ kconst p * (((a + 1 : ℕ) : ℝ)) ^ 4 := by
  have hr0 : 0 ≤ xp p := xp_nonneg p
  rcases le_or_gt p 23 with h23 | h23
  · have hr : xp p ≤ 841 / 1000 := xp_le_of_prime_le_23 p hp h23
    have h1 : ∑ i ∈ Finset.range (M + 1), (((a + i + 1 : ℕ) : ℝ)) ^ 2 * (xp p) ^ i
        ≤ ∑ i ∈ Finset.range (M + 1), (((a + i + 1 : ℕ) : ℝ)) ^ 2 * ((841 : ℝ) / 1000) ^ i := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr0 hr i) (by positivity)
    have h2 : ∑ i ∈ Finset.range (M + 1), (((a + i + 1 : ℕ) : ℝ)) ^ 2 * ((841 : ℝ) / 1000) ^ i
        ≤ (((a + 1 : ℕ) : ℝ)) ^ 4 *
          (1 / (4 * (1 - (841 : ℝ) / 1000)) + ((841 : ℝ) / 1000) / (4 * (1 - (841 : ℝ) / 1000) ^ 2)
            + ((841 : ℝ) / 1000) * (1 + (841 : ℝ) / 1000) / (16 * (1 - (841 : ℝ) / 1000) ^ 3)) :=
      geom_pow_sum_bound _ (by norm_num) (by norm_num) a M ha
    have h3 : (1 / (4 * (1 - (841 : ℝ) / 1000)) + ((841 : ℝ) / 1000) / (4 * (1 - (841 : ℝ) / 1000) ^ 2)
            + ((841 : ℝ) / 1000) * (1 + (841 : ℝ) / 1000) / (16 * (1 - (841 : ℝ) / 1000) ^ 3)) ≤ 34 := by
      norm_num
    have hk : kconst p = 34 := by simp [kconst, h23]
    calc ∑ i ∈ Finset.range (M + 1), (((a + i + 1 : ℕ) : ℝ)) ^ 2 * (xp p) ^ i
        ≤ (((a + 1 : ℕ) : ℝ)) ^ 4 * 34 := le_trans h1 (le_trans h2 (by
          exact mul_le_mul_of_nonneg_left h3 (by positivity)))
      _ = kconst p * (((a + 1 : ℕ) : ℝ)) ^ 4 := by rw [hk]; ring
  · have hp29 : 29 ≤ p := by
      have h24 : 24 ≤ p := by omega
      by_contra hc
      simp only [not_le] at hc
      interval_cases p <;> exact absurd hp (by decide)
    have hr : xp p ≤ 431 / 1000 := xp_le_of_prime_ge_29 p hp hp29
    have h1 : ∑ i ∈ Finset.range (M + 1), (((a + i + 1 : ℕ) : ℝ)) ^ 2 * (xp p) ^ i
        ≤ ∑ i ∈ Finset.range (M + 1), (((a + i + 1 : ℕ) : ℝ)) ^ 2 * ((431 : ℝ) / 1000) ^ i := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr0 hr i) (by positivity)
    have h2 : ∑ i ∈ Finset.range (M + 1), (((a + i + 1 : ℕ) : ℝ)) ^ 2 * ((431 : ℝ) / 1000) ^ i
        ≤ (((a + 1 : ℕ) : ℝ)) ^ 4 *
          (1 / (4 * (1 - (431 : ℝ) / 1000)) + ((431 : ℝ) / 1000) / (4 * (1 - (431 : ℝ) / 1000) ^ 2)
            + ((431 : ℝ) / 1000) * (1 + (431 : ℝ) / 1000) / (16 * (1 - (431 : ℝ) / 1000) ^ 3)) :=
      geom_pow_sum_bound _ (by norm_num) (by norm_num) a M ha
    have h3 : (1 / (4 * (1 - (431 : ℝ) / 1000)) + ((431 : ℝ) / 1000) / (4 * (1 - (431 : ℝ) / 1000) ^ 2)
            + ((431 : ℝ) / 1000) * (1 + (431 : ℝ) / 1000) / (16 * (1 - (431 : ℝ) / 1000) ^ 3)) ≤ 1 := by
      norm_num
    have hk : kconst p = 1 := by simp [kconst, h23]
    calc ∑ i ∈ Finset.range (M + 1), (((a + i + 1 : ℕ) : ℝ)) ^ 2 * (xp p) ^ i
        ≤ (((a + 1 : ℕ) : ℝ)) ^ 4 * 1 := le_trans h1 (le_trans h2 (by
          exact mul_le_mul_of_nonneg_left h3 (by positivity)))
      _ = kconst p * (((a + 1 : ℕ) : ℝ)) ^ 4 := by rw [hk]; ring

/-- The normalised per-prime sum of `hfac m` over the prime powers of `p` is bounded by
`kconst p · (v_p m + 1)²`. -/
lemma hterm_sum_le (m p M : ℕ) (hp : p ∈ m.primeFactors) :
    ∑ i ∈ Finset.range (M + 1), hterm m p i
      ≤ kconst p * (((m.factorization p + 1 : ℕ)) : ℝ) ^ 2 := by
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have ha : 1 ≤ m.factorization p := by
    have hmem : p ∈ m.factorization.support := by rw [Nat.support_factorization]; exact hp
    have := Finsupp.mem_support_iff.mp hmem
    omega
  have hxp := xp_pow_sum_le p M (m.factorization p) hpp ha
  have hsplit : ∑ i ∈ Finset.range (M + 1), hterm m p i
      = ((((m.factorization p + 1 : ℕ)) : ℝ))⁻¹ ^ 2 *
        ∑ i ∈ Finset.range (M + 1),
          (((m.factorization p + i + 1 : ℕ)) : ℝ) ^ 2 * (xp p) ^ i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hterm]
    field_simp
  rw [hsplit]
  refine (mul_le_mul_of_nonneg_left hxp (by positivity)).trans (le_of_eq ?_)
  field_simp

/-- `(m^J).primeFactors ⊆ m.primeFactors`. -/
lemma primeFactors_pow_subset (m J : ℕ) : (m ^ J).primeFactors ⊆ m.primeFactors := by
  rcases eq_or_ne J 0 with hJ | hJ
  · rw [hJ]; simp
  · rw [Nat.primeFactors_pow m hJ]

lemma one_le_kconst (p : ℕ) : 1 ≤ kconst p := by
  rw [kconst]; split <;> norm_num

/-- At most `24` of the values `kconst p` exceed `1`, so every product of them is `≤ 34^24`. -/
lemma prod_kconst_le (s : Finset ℕ) : ∏ p ∈ s, kconst p ≤ 34 ^ 24 := by
  have h1 : ∏ p ∈ s.filter (fun p => ¬ p ≤ 23), kconst p = 1 := by
    apply Finset.prod_eq_one
    intro p hp
    rw [Finset.mem_filter] at hp
    simp [kconst, hp.2]
  have h2 : ∏ p ∈ s.filter (fun p => p ≤ 23), kconst p
      = 34 ^ (s.filter (fun p => p ≤ 23)).card := by
    rw [← Finset.prod_const (s := s.filter fun p => p ≤ 23) (b := (34:ℝ))]
    exact Finset.prod_congr rfl fun p hp => by
      rw [Finset.mem_filter] at hp
      simp [kconst, hp.2]
  have h3 : (s.filter (fun p => p ≤ 23)).card ≤ 24 := by
    have hsub : s.filter (fun p => p ≤ 23) ⊆ Finset.range 24 := by
      intro p hp
      rw [Finset.mem_filter] at hp
      simp only [Finset.mem_range]
      omega
    calc (s.filter (fun p => p ≤ 23)).card ≤ (Finset.range 24).card := Finset.card_le_card hsub
      _ = 24 := Finset.card_range 24
  calc ∏ p ∈ s, kconst p
      = (∏ p ∈ s.filter (fun p => p ≤ 23), kconst p) *
        ∏ p ∈ s.filter (fun p => ¬ p ≤ 23), kconst p :=
        (Finset.prod_filter_mul_prod_filter_not s (fun p => p ≤ 23) kconst).symm
    _ = 34 ^ (s.filter (fun p => p ≤ 23)).card := by rw [h1, mul_one, h2]
    _ ≤ 34 ^ 24 := pow_le_pow_right₀ (by norm_num) h3

/-! ## Part 5: the target estimate -/

/-- **The `τ(m)^4` arithmetic of *FI* (23.11).**  The `m`-smooth numbers `k ≤ N` (`k | m^∞`) satisfy

  `Σ_{k ≤ N, k | m^∞} k^{-1/4} τ(mk)^2 ≤ C · τ(m)^4`

with an absolute constant `C`; the statement below is the equivalent form in which the smoothness
of `k` is expressed as `k ∣ m^J` for some exponent `J` (uniformly in `J`: for `k ≤ N` and
`k | m^∞` one has `k ∣ m^N`, so `J := N` covers every `m`-smooth `k ≤ N`). -/
theorem msmooth_sum_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (m J N : ℕ), 1 ≤ m →
      ∑ k ∈ (Finset.Icc 1 N).filter (fun k => k ∣ m ^ J),
          ((k : ℝ) ^ ((1 : ℝ) / 4))⁻¹ * (((m * k).divisors.card : ℕ) : ℝ) ^ 2
        ≤ C * (((m.divisors.card : ℕ) : ℝ)) ^ 4 := by
  refine ⟨10 ^ 40, by norm_num, ?_⟩
  intro m J N hm
  have hm0 : m ≠ 0 := by omega
  have hpow0 : m ^ J ≠ 0 := pow_ne_zero _ hm0
  set Tm : ℝ := ((m.divisors.card : ℕ) : ℝ) with hTm
  have hTm1 : (1 : ℝ) ≤ Tm := by
    rw [hTm]
    have h : (1 : ℕ) ≤ m.divisors.card :=
      Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hm0⟩
    exact_mod_cast h
  have hTm0 : (0 : ℝ) ≤ Tm := le_trans zero_le_one hTm1
  have h0 : ∑ k ∈ (Finset.Icc 1 N).filter (fun k => k ∣ m ^ J),
        ((k : ℝ) ^ ((1 : ℝ) / 4))⁻¹ * (((m * k).divisors.card : ℕ) : ℝ) ^ 2
      ≤ ∑ k ∈ (m ^ J).divisors,
        ((k : ℝ) ^ ((1 : ℝ) / 4))⁻¹ * (((m * k).divisors.card : ℕ) : ℝ) ^ 2 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro k hk
      rw [Finset.mem_filter, Finset.mem_Icc] at hk
      exact Nat.mem_divisors.mpr ⟨hk.2, hpow0⟩
    · intro k _ _
      positivity
  have h1 : ∑ k ∈ (m ^ J).divisors,
        ((k : ℝ) ^ ((1 : ℝ) / 4))⁻¹ * (((m * k).divisors.card : ℕ) : ℝ) ^ 2
      = ∑ k ∈ (m ^ J).divisors, Tm ^ 2 * hfac m k := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [hTm]
    exact summand_eq_hfac m k J hm (Nat.mem_divisors.mp hk).1 (Nat.pos_of_mem_divisors hk)
  have h2 : ∑ k ∈ (m ^ J).divisors, Tm ^ 2 * hfac m k = Tm ^ 2 * Hsum m (m ^ J) := by
    rw [Hsum, Finset.mul_sum]
  have h3 : Hsum m (m ^ J) ≤ 34 ^ 24 * Tm ^ 2 := by
    rw [Hsum_euler m J hm]
    have hsub : (m ^ J).primeFactors ⊆ m.primeFactors := primeFactors_pow_subset m J
    have hstep1 : ∏ p ∈ (m ^ J).primeFactors,
          (∑ i ∈ Finset.range ((m ^ J).factorization p + 1), hfac m (p ^ i))
        ≤ ∏ p ∈ (m ^ J).primeFactors,
          kconst p * (((m.factorization p + 1 : ℕ)) : ℝ) ^ 2 := by
      apply Finset.prod_le_prod₀
      · intro p _
        exact Finset.sum_nonneg fun i _ => hfac_nonneg m (p ^ i)
      · intro p hp
        rw [show (∑ i ∈ Finset.range ((m ^ J).factorization p + 1), hfac m (p ^ i))
            = ∑ i ∈ Finset.range ((m ^ J).factorization p + 1), hterm m p i from
          Finset.sum_congr rfl fun i _ => hfac_prime_pow m p i (hsub hp)]
        exact hterm_sum_le m p _ (hsub hp)
    have hstep2 : ∏ p ∈ (m ^ J).primeFactors,
          kconst p * (((m.factorization p + 1 : ℕ)) : ℝ) ^ 2
        ≤ ∏ p ∈ m.primeFactors, kconst p * (((m.factorization p + 1 : ℕ)) : ℝ) ^ 2 := by
      have hfac1 : ∀ p : ℕ, 1 ≤ kconst p * (((m.factorization p + 1 : ℕ)) : ℝ) ^ 2 := by
        intro p
        have hge : (1 : ℝ) ≤ (((m.factorization p + 1 : ℕ)) : ℝ) := by
          have : (1 : ℕ) ≤ m.factorization p + 1 := Nat.succ_le_succ (Nat.zero_le _)
          exact_mod_cast this
        exact one_le_mul_of_one_le_of_one_le (one_le_kconst p) (one_le_pow₀ hge)
      have h1le : (1 : ℝ) ≤ ∏ p ∈ m.primeFactors \ (m ^ J).primeFactors,
          kconst p * (((m.factorization p + 1 : ℕ)) : ℝ) ^ 2 := by
        have h := Finset.prod_le_prod₀
          (s := m.primeFactors \ (m ^ J).primeFactors) (f := fun _ : ℕ => (1 : ℝ))
          (g := fun p => kconst p * (((m.factorization p + 1 : ℕ)) : ℝ) ^ 2)
          (fun p _ => zero_le_one) (fun p _ => hfac1 p)
        simpa using h
      have hnonneg : (0 : ℝ) ≤ ∏ p ∈ (m ^ J).primeFactors,
          kconst p * (((m.factorization p + 1 : ℕ)) : ℝ) ^ 2 :=
        Finset.prod_nonneg fun p _ =>
          mul_nonneg (le_trans zero_le_one (one_le_kconst p)) (sq_nonneg _)
      calc ∏ p ∈ (m ^ J).primeFactors, kconst p * (((m.factorization p + 1 : ℕ)) : ℝ) ^ 2
          ≤ (∏ p ∈ m.primeFactors \ (m ^ J).primeFactors,
              kconst p * (((m.factorization p + 1 : ℕ)) : ℝ) ^ 2) *
            ∏ p ∈ (m ^ J).primeFactors,
              kconst p * (((m.factorization p + 1 : ℕ)) : ℝ) ^ 2 :=
            le_mul_of_one_le_left hnonneg h1le
        _ = ∏ p ∈ m.primeFactors, kconst p * (((m.factorization p + 1 : ℕ)) : ℝ) ^ 2 :=
            Finset.prod_sdiff hsub
    have hstep3 : ∏ p ∈ m.primeFactors, kconst p * (((m.factorization p + 1 : ℕ)) : ℝ) ^ 2
        = (∏ p ∈ m.primeFactors, kconst p) * Tm ^ 2 := by
      rw [Finset.prod_mul_distrib, hTm, Nat.card_divisors hm0, Nat.cast_prod,
        ← Finset.prod_pow]
    have hstep4 : (∏ p ∈ m.primeFactors, kconst p) * Tm ^ 2 ≤ 34 ^ 24 * Tm ^ 2 :=
      mul_le_mul_of_nonneg_right (prod_kconst_le _) (by positivity)
    exact le_trans hstep1 (le_trans hstep2 (hstep3.trans_le hstep4))
  calc ∑ k ∈ (Finset.Icc 1 N).filter (fun k => k ∣ m ^ J),
        ((k : ℝ) ^ ((1 : ℝ) / 4))⁻¹ * (((m * k).divisors.card : ℕ) : ℝ) ^ 2
      ≤ Tm ^ 2 * Hsum m (m ^ J) := h0.trans (h1.trans h2).le
    _ ≤ Tm ^ 2 * (34 ^ 24 * Tm ^ 2) := mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = 34 ^ 24 * Tm ^ 4 := by ring
    _ ≤ 10 ^ 40 * (((m.divisors.card : ℕ) : ℝ)) ^ 4 := by
        rw [hTm]
        exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)

end

end Work.FIArea7
