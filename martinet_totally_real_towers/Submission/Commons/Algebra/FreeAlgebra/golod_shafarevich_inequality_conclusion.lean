import Mathlib

namespace Commons.Algebra.FreeAlgebra

private lemma sum_cond_shift_le {M a : ℕ} {b : ℕ → ℕ} {t : ℝ} (ht : 0 ≤ t) (ha : 1 ≤ a) :
    (∑ k ∈ Finset.range M,
      (if a ≤ k + 1 then (b (k + 1 - a) : ℝ) * t ^ (k + 1) else 0)) ≤
      t ^ a * ∑ j ∈ Finset.range M, (b j : ℝ) * t ^ j := by
  let f : ℕ → ℝ := fun n => if a ≤ n then (b (n - a) : ℝ) * t ^ n else 0
  have hf0 : f 0 = 0 := by
    simp [f, show ¬ a ≤ 0 by omega]
  have hshift : (∑ k ∈ Finset.range M, f (k + 1)) = ∑ n ∈ Finset.range (M + 1), f n := by
    have h := Finset.sum_range_succ' f M
    rw [hf0, add_zero] at h
    exact h.symm
  have hmain : (∑ k ∈ Finset.range M, f (k + 1)) ≤ t ^ a * ∑ j ∈ Finset.range M, (b j : ℝ) * t ^ j := by
    by_cases haM : a ≤ M + 1
    · have hsumadd := Finset.sum_range_add f a (M + 1 - a)
      have haM' : a + (M + 1 - a) = M + 1 := Nat.add_sub_of_le haM
      rw [haM'] at hsumadd
      rw [hshift, hsumadd]
      have hfirst : (∑ x ∈ Finset.range a, f x) = 0 := by
        apply Finset.sum_eq_zero
        intro x hx
        simp [f]
        have hxlt : x < a := Finset.mem_range.mp hx
        omega
      rw [hfirst, zero_add]
      have hsecond_sum : (∑ x ∈ Finset.range (M + 1 - a), f (a + x)) =
          ∑ x ∈ Finset.range (M + 1 - a), (b x : ℝ) * t ^ (a + x) := by
        apply Finset.sum_congr rfl
        intro x hx
        simp [f]
      have hsecond : (∑ x ∈ Finset.range (M + 1 - a), f (a + x)) =
          t ^ a * ∑ x ∈ Finset.range (M + 1 - a), (b x : ℝ) * t ^ x := by
        rw [hsecond_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x hx
        rw [pow_add]
        ring
      rw [hsecond]
      have hsubset : Finset.range (M + 1 - a) ⊆ Finset.range M := by
        intro x hx
        rw [Finset.mem_range] at hx ⊢
        have hle : M + 1 - a ≤ M := by omega
        exact lt_of_lt_of_le hx hle
      have hnonneg : ∀ x ∈ Finset.range M, x ∉ Finset.range (M + 1 - a) →
          0 ≤ (b x : ℝ) * t ^ x := by
        intro x hx hnot
        exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg ht _)
      have hsum_le : (∑ x ∈ Finset.range (M + 1 - a), (b x : ℝ) * t ^ x) ≤
          ∑ x ∈ Finset.range M, (b x : ℝ) * t ^ x :=
        Finset.sum_le_sum_of_subset_of_nonneg hsubset hnonneg
      exact mul_le_mul_of_nonneg_left hsum_le (pow_nonneg ht a)
    · have hsum_zero : (∑ n ∈ Finset.range (M + 1), f n) = 0 := by
        apply Finset.sum_eq_zero
        intro n hn
        simp [f]
        have hnlt : n < M + 1 := Finset.mem_range.mp hn
        have hna : ¬ a ≤ n := by omega
        simp [hna]
      rw [hshift, hsum_zero]
      positivity
  simpa [f] using hmain

private lemma quadratic_necessary {σ : Type*} [Fintype σ] {d : ℕ} (deg : σ → ℕ)
    (hd : 0 < d)
    (hdeg : ∀ r, 2 ≤ deg r)
    (hpos : ∀ t : ℝ, 0 < t → t ≤ 1 → 0 < 1 - (d : ℝ) * t + ∑ r : σ, t ^ deg r) :
    d * d < 4 * Fintype.card σ := by
  let C := Fintype.card σ
  have hdR_ge1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  by_contra hnot
  have hle : 4 * C ≤ d * d := by simpa [C] using Nat.le_of_not_gt hnot
  by_cases hdlt : d < 2 * C
  · let t0 : ℝ := (d : ℝ) / (2 * C : ℝ)
    have hCpos : 0 < C := by
      by_contra hC0
      have hCzero : C = 0 := Nat.eq_zero_of_not_pos hC0
      have hAt1 : 0 < 1 - (d : ℝ) * 1 + ∑ r : σ, (1 : ℝ) ^ deg r := hpos 1 zero_lt_one le_rfl
      have hsum_eq : ∑ r : σ, (1 : ℝ) ^ deg r = (C : ℝ) := by simp [C]
      rw [hsum_eq, hCzero] at hAt1
      nlinarith
    have ht0pos : 0 < t0 := by
      dsimp [t0]
      positivity
    have ht0le1 : t0 ≤ 1 := by
      dsimp [t0]
      rw [div_le_one]
      · exact_mod_cast hdlt.le
      · positivity
    have hAt0 : 0 < 1 - (d : ℝ) * t0 + ∑ r : σ, t0 ^ deg r := hpos t0 ht0pos ht0le1
    have hA_le_q : 1 - (d : ℝ) * t0 + ∑ r : σ, t0 ^ deg r ≤ 1 - (d : ℝ) * t0 + (C : ℝ) * t0 ^ 2 := by
      have hpow : ∀ r, t0 ^ deg r ≤ t0 ^ 2 := by
        intro r
        exact pow_le_pow_of_le_one (le_of_lt ht0pos) ht0le1 (hdeg r)
      have hsum_le : ∑ r : σ, t0 ^ deg r ≤ ∑ r : σ, t0 ^ 2 := by
        exact Finset.sum_le_sum (fun r _ => hpow r)
      have hsum2 : ∑ r : σ, t0 ^ 2 = (C : ℝ) * t0 ^ 2 := by
        simp [C, Finset.sum_const, nsmul_eq_mul]
      rw [hsum2] at hsum_le
      linarith
    have hq_nonpos : 1 - (d : ℝ) * t0 + (C : ℝ) * t0 ^ 2 ≤ 0 := by
      dsimp [t0]
      field_simp [show (2 * C : ℝ) ≠ 0 by positivity]
      ring_nf
      have hleR : (4 : ℝ) * C ≤ (d : ℝ) * d := by exact_mod_cast hle
      nlinarith
    have : 0 < 1 - (d : ℝ) * t0 + (C : ℝ) * t0 ^ 2 := lt_of_lt_of_le hAt0 hA_le_q
    linarith
  · have hdge : 2 * C ≤ d := Nat.le_of_not_gt hdlt
    have hAt1 : 0 < 1 - (d : ℝ) * 1 + ∑ r : σ, (1 : ℝ) ^ deg r := hpos 1 zero_lt_one le_rfl
    have hA1_nonpos : 1 - (d : ℝ) * 1 + ∑ r : σ, (1 : ℝ) ^ deg r ≤ 0 := by
      have hsum_eq : ∑ r : σ, (1 : ℝ) ^ deg r = (C : ℝ) := by
        simp [C]
      rw [hsum_eq]
      simp only [mul_one]
      have hdgeR : (2 : ℝ) * C ≤ d := by exact_mod_cast hdge
      by_cases hC0 : C = 0
      · have hC0R : (C : ℝ) = 0 := by exact_mod_cast hC0
        rw [hC0R]
        linarith
      · have hC_ge1_nat : 1 ≤ C := Nat.succ_le_iff.2 (Nat.pos_of_ne_zero hC0)
        have hC_ge1 : (1 : ℝ) ≤ C := by exact_mod_cast hC_ge1_nat
        have hle' : (1 : ℝ) + C ≤ d := by nlinarith
        linarith
    linarith

private lemma generating_function_positive {σ : Type*} [Fintype σ] {d : ℕ} (deg : σ → ℕ)
    (b : ℕ → ℕ)
    (hb0 : b 0 = 1)
    (hdeg : ∀ r, 2 ≤ deg r)
    (hfund : ∀ n : ℕ, 0 < n →
      d * b (n - 1) ≤ b n + ∑ r : σ, if deg r ≤ n then b (n - deg r) else 0)
    (hfin : ∀ᶠ n : ℕ in Filter.atTop, b n = 0) :
    ∀ t : ℝ, 0 < t → t ≤ 1 → 0 < 1 - (d : ℝ) * t + ∑ r : σ, t ^ deg r := by
  rcases Filter.eventually_atTop.1 hfin with ⟨N, hN⟩
  let M := N + 1
  have hbM : b M = 0 := hN M (Nat.le_succ N)
  intro t htpos htle1
  have ht_nonneg : 0 ≤ t := le_of_lt htpos
  let B : ℝ := ∑ k ∈ Finset.range M, (b k : ℝ) * t ^ k
  have hB_pos : 0 < B := by
    dsimp [B]
    refine Finset.sum_pos' ?_ ⟨0, ?_, ?_⟩
    · intro k hk
      exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg ht_nonneg _)
    · rw [Finset.mem_range]
      omega
    · simp [hb0]
  have hterm : ∀ k ∈ Finset.range M,
      (d : ℝ) * (b k : ℝ) * t ^ (k + 1) ≤
        (b (k + 1) : ℝ) * t ^ (k + 1) +
          ∑ r : σ, (if deg r ≤ k + 1 then (b (k + 1 - deg r) : ℝ) else 0) * t ^ (k + 1) := by
    intro k hk
    have hkpos : 0 < k + 1 := Nat.succ_pos k
    have hfundk := hfund (k + 1) hkpos
    have hfundkR : (d * b k : ℝ) ≤
        (b (k + 1) + ∑ r : σ, if deg r ≤ k + 1 then b (k + 1 - deg r) else 0 : ℝ) := by
      exact_mod_cast hfundk
    have hmul := mul_le_mul_of_nonneg_right hfundkR (pow_nonneg ht_nonneg (k + 1))
    simpa [Nat.cast_add, Nat.cast_mul, add_mul, Finset.sum_mul] using hmul
  have hsum_ineq : (∑ k ∈ Finset.range M, (d : ℝ) * (b k : ℝ) * t ^ (k + 1)) ≤
      ∑ k ∈ Finset.range M, ((b (k + 1) : ℝ) * t ^ (k + 1) +
        ∑ r : σ, (if deg r ≤ k + 1 then (b (k + 1 - deg r) : ℝ) else 0) * t ^ (k + 1)) := by
    exact Finset.sum_le_sum (fun k hk => hterm k hk)
  have hsum_ineq' : (∑ k ∈ Finset.range M, (d : ℝ) * (b k : ℝ) * t ^ (k + 1)) ≤
      (∑ k ∈ Finset.range M, (b (k + 1) : ℝ) * t ^ (k + 1)) +
        ∑ k ∈ Finset.range M, ∑ r : σ,
          (if deg r ≤ k + 1 then (b (k + 1 - deg r) : ℝ) else 0) * t ^ (k + 1) := by
    simpa [Finset.sum_add_distrib] using hsum_ineq
  have hleft : (∑ k ∈ Finset.range M, (d : ℝ) * (b k : ℝ) * t ^ (k + 1)) =
      (d : ℝ) * t * B := by
    calc
      (∑ k ∈ Finset.range M, (d : ℝ) * (b k : ℝ) * t ^ (k + 1))
          = ∑ k ∈ Finset.range M, ((d : ℝ) * t) * ((b k : ℝ) * t ^ k) := by
            apply Finset.sum_congr rfl
            intro k hk
            rw [pow_succ]
            ring
      _ = (d : ℝ) * t * B := by
            dsimp [B]
            rw [Finset.mul_sum]
  have hright1 : (∑ k ∈ Finset.range M, (b (k + 1) : ℝ) * t ^ (k + 1)) = B - 1 := by
    let F : ℕ → ℝ := fun n => (b n : ℝ) * t ^ n
    have hshift := Finset.sum_range_succ' F M
    have hF0 : F 0 = 1 := by simp [F, hb0]
    rw [hF0] at hshift
    have hT : (∑ n ∈ Finset.range (M + 1), F n) = B := by
      dsimp [B, F]
      rw [Finset.sum_range_succ]
      have hbM_R : (b M : ℝ) = 0 := by exact_mod_cast hbM
      simp [hbM_R]
    rw [hT] at hshift
    -- hshift : B = ∑ k range M F(k+1) + 1
    have hshift' : (∑ k ∈ Finset.range M, F (k + 1)) = B - 1 := by
      linarith
    simpa [F] using hshift'
  have hright2 : (∑ k ∈ Finset.range M, ∑ r : σ,
      (if deg r ≤ k + 1 then (b (k + 1 - deg r) : ℝ) else 0) * t ^ (k + 1)) ≤
      ∑ r : σ, t ^ deg r * B := by
    rw [Finset.sum_comm]
    exact Finset.sum_le_sum (fun r hr => by
      have hdeg_r : 1 ≤ deg r := by
        have h2 := hdeg r
        omega
      simpa [B] using
        (sum_cond_shift_le (M := M) (a := deg r) (b := b) (t := t) ht_nonneg hdeg_r))
  have hineq : (d : ℝ) * t * B ≤ (B - 1) + ∑ r : σ, t ^ deg r * B := by
    rw [hleft] at hsum_ineq'
    rw [hright1] at hsum_ineq'
    exact le_trans hsum_ineq' (add_le_add_right hright2 (B - 1))
  have hprod_ge : 1 ≤ (1 - (d : ℝ) * t + ∑ r : σ, t ^ deg r) * B := by
    have hsum_mul : (∑ r : σ, t ^ deg r) * B = ∑ r : σ, t ^ deg r * B := by
      rw [Finset.sum_mul]
    rw [← hsum_mul] at hineq
    nlinarith
  have hAB_pos : 0 < (1 - (d : ℝ) * t + ∑ r : σ, t ^ deg r) * B :=
    lt_of_lt_of_le zero_lt_one hprod_ge
  exact pos_of_mul_pos_left hAB_pos (le_of_lt hB_pos)

theorem golod_shafarevich_inequality_conclusion
    {σ : Type*} [Fintype σ]
    {d : ℕ} (deg : σ → ℕ) (b : ℕ → ℕ)
    (hd : 0 < d)
    (hb0 : b 0 = 1)
    (hdeg : ∀ r, 2 ≤ deg r)
    (hfund : ∀ n : ℕ, 0 < n →
      d * b (n - 1) ≤ b n + ∑ r : σ, if deg r ≤ n then b (n - deg r) else 0)
    (hfin : ∀ᶠ n : ℕ in Filter.atTop, b n = 0) :
    d * d < 4 * Fintype.card σ := by
  exact quadratic_necessary deg hd hdeg (generating_function_positive deg b hb0 hdeg hfund hfin)

end Commons.Algebra.FreeAlgebra
