import Mathlib
import Submission.Commons.NumberTheory.DirichletPolynomial.large_sieve_block_sampled

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Sampled mean-value bound for a Dirichlet polynomial supported in a short range

If `a` is supported in `[N, M]` with `M ≤ N * K` then, for `1`-separated points `t r` of
`[-T, T]`,

`Σ_r ‖Σ_{n ∈ [N,M]} a n · n^{i t_r}‖² ≤ C · (K+1) · (T + M) · Σ_{n ∈ [N,M]} ‖a n‖²`.

This is the discrete (sampled) Montgomery–Vaughan mean value estimate: `[N, M]` is split into
the `K+1` blocks of length `N`, each of which has frequency window `log 2 < 1`, to which the
block large-sieve bound `large_sieve_block_sampled` applies.
-/

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace Work.BMF.mr_direct

open Finset
open scoped BigOperators

theorem sampled_mean_value_blocks :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N M K : ℕ) (a : ℕ → ℂ) (T : ℝ) (R : ℕ) (t : Fin R → ℝ),
        1 ≤ N → 1 ≤ K → 0 ≤ T → M ≤ N * K →
        (∀ n, n ∉ Finset.Icc N M → a n = 0) →
        (∀ i, t i ∈ Set.Icc (-T) T) →
        (∀ i j : Fin R, i ≠ j → 1 ≤ |t i - t j|) →
        (∑ r : Fin R, ‖∑ n ∈ Finset.Icc N M, a n * (n : ℂ) ^ (Complex.I * (t r : ℂ))‖ ^ 2)
          ≤ C * ((K : ℝ) + 1) * (T + (M : ℝ)) * (∑ n ∈ Finset.Icc N M, ‖a n‖ ^ 2) := by
  obtain ⟨C₀, hC₀pos, hblock⟩ :=
    Commons.NumberTheory.DirichletPolynomial.large_sieve_block_sampled
  refine ⟨4 * C₀, by positivity, ?_⟩
  intro N M K a T R t hN hK hT hMK hsupp hIcc hsep
  by_cases hNM : N ≤ M
  swap
  · have hempty : Finset.Icc N M = ∅ := by
      rw [Finset.Icc_eq_empty_iff]
      omega
    rw [hempty]
    simp
  have hNpos : 0 < N := by omega
  set ts : Fin R → ℝ := fun r => t r + T with hts
  have htsI : ∀ i, ts i ∈ Set.Icc 0 (2 * T) := by
    intro i
    obtain ⟨h1, h2⟩ := hIcc i
    constructor <;> simp only [hts] <;> linarith
  have htssep : ∀ i j, i ≠ j → 1 ≤ |ts i - ts j| := by
    intro i j hij
    have h := hsep i j hij
    have heq : ts i - ts j = t i - t j := by simp only [hts]; ring
    rwa [heq]
  set a' : ℕ → ℂ := fun n => a n * (n : ℂ) ^ (-(Complex.I * (T : ℂ))) with ha'
  have ha'supp : ∀ n, n ∉ Finset.Icc N M → a' n = 0 := by
    intro n hn
    simp only [ha']
    rw [hsupp n hn, zero_mul]
  have ha'norm : ∀ n, 1 ≤ n → ‖a' n‖ = ‖a n‖ := by
    intro n hn1
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hcast : ((n : ℂ)) = (((n : ℝ)) : ℂ) := by push_cast; ring
    have h1 : ‖(n : ℂ) ^ (-(Complex.I * (T : ℂ)))‖ = 1 := by
      rw [hcast, Complex.norm_cpow_eq_rpow_re_of_pos hnpos]
      simp [Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.ofReal_re, Complex.ofReal_im]
    change ‖a n * (n : ℂ) ^ (-(Complex.I * (T : ℂ)))‖ = ‖a n‖
    rw [norm_mul, h1, mul_one]
  have hshift : ∀ r, (∑ n ∈ Finset.Icc N M, a n * (n : ℂ) ^ (Complex.I * (t r : ℂ)))
      = (∑ n ∈ Finset.Icc N M, a' n * (n : ℂ) ^ (Complex.I * (ts r : ℂ))) := by
    intro r
    apply Finset.sum_congr rfl
    intro n hn
    have hn1 : 1 ≤ n := le_trans hN (Finset.mem_Icc.mp hn).1
    have hn0 : (n : ℂ) ≠ 0 := by
      simp only [ne_eq, Nat.cast_eq_zero]
      omega
    simp only [ha', hts]
    rw [mul_assoc, ← Complex.cpow_add _ _ hn0]
    rw [show -(Complex.I * (T : ℂ)) + Complex.I * (((t r + T : ℝ)) : ℂ)
          = Complex.I * (((t r : ℝ)) : ℂ) by push_cast; ring]
  set jf : ℕ → ℕ := fun n => n / N with hjf
  have hmap : ∀ n ∈ Finset.Icc N M, jf n ∈ Finset.Icc 1 K := by
    intro n hn
    obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.mp hn
    rw [Finset.mem_Icc, hjf]
    constructor
    · exact (Nat.one_le_div_iff hNpos).mpr hn1
    · exact Nat.div_le_of_le_mul (le_trans hn2 hMK)
  set b : ℕ → ℕ → ℂ := fun j n => if jf n = j then a' n else 0 with hb
  have hbz : ∀ j n, n ∉ Finset.Icc N M → b j n = 0 := by
    intro j n hn
    simp only [hb]
    by_cases h : jf n = j
    · rw [if_pos h, ha'supp n hn]
    · rw [if_neg h]
  have hbsupp : ∀ j n, n ∉ Finset.Icc (j * N) (2 * (j * N)) → b j n = 0 := by
    intro j n hn
    simp only [hb]
    by_cases h : jf n = j
    swap
    · rw [if_neg h]
    rw [if_pos h]
    by_cases hmem : n ∈ Finset.Icc N M
    swap
    · rw [ha'supp n hmem]
    exfalso
    have hn1 : j * N ≤ n := by
      rw [← h, hjf]
      exact Nat.div_mul_le_self n N
    have hj1 : 1 ≤ j := by
      rw [← h, hjf]
      exact (Nat.one_le_div_iff hNpos).mpr (Finset.mem_Icc.mp hmem).1
    have hstep : (j + 1) * N ≤ 2 * (j * N) := by nlinarith [hj1, hNpos]
    have hn2 : n < (j + 1) * N := by
      have hj : n / N = j := by simpa only [hjf] using h
      have hlt : n / N < j + 1 := by omega
      exact (Nat.div_lt_iff_lt_mul hNpos).mp hlt
    exact hn (Finset.mem_Icc.mpr ⟨hn1, by omega⟩)
  have hdecomp : ∀ r, (∑ n ∈ Finset.Icc N M, a' n * (n : ℂ) ^ (Complex.I * (ts r : ℂ)))
      = ∑ j ∈ Finset.Icc 1 K,
          ∑ n ∈ Finset.Icc N M, b j n * (n : ℂ) ^ (Complex.I * (ts r : ℂ)) := by
    intro r
    rw [← Finset.sum_fiberwise_of_maps_to hmap
      (fun n => a' n * (n : ℂ) ^ (Complex.I * (ts r : ℂ)))]
    apply Finset.sum_congr rfl
    intro j _
    have hpt : ∀ n, b j n * (n : ℂ) ^ (Complex.I * (ts r : ℂ))
        = if jf n = j then a' n * (n : ℂ) ^ (Complex.I * (ts r : ℂ)) else 0 := by
      intro n
      rw [hb]
      by_cases h : jf n = j <;> simp [h]
    rw [Finset.sum_congr rfl (fun n _ => hpt n), ← Finset.sum_filter]
  have hb_eq : ∀ j ∈ Finset.Icc 1 K, ∀ r,
      (∑ n ∈ Finset.Icc N M, b j n * (n : ℂ) ^ (Complex.I * (ts r : ℂ)))
        = ∑ n ∈ Finset.Icc (j * N) (2 * (j * N)),
            b j n * (n : ℂ) ^ (Complex.I * (ts r : ℂ)) := by
    intro j hj r
    set rng : Finset ℕ := Finset.range (M + 2 * (j * N) + 1) with hrng
    have hsub1 : Finset.Icc N M ⊆ rng := by
      intro n hn
      rw [hrng, Finset.mem_range]
      have := (Finset.mem_Icc.mp hn).2
      omega
    have hsub2 : Finset.Icc (j * N) (2 * (j * N)) ⊆ rng := by
      intro n hn
      rw [hrng, Finset.mem_range]
      have := (Finset.mem_Icc.mp hn).2
      omega
    have hv1 : ∀ n ∈ rng, n ∉ Finset.Icc N M →
        b j n * (n : ℂ) ^ (Complex.I * (ts r : ℂ)) = 0 :=
      fun n _ hn => by rw [hbz j n hn, zero_mul]
    have hv2 : ∀ n ∈ rng, n ∉ Finset.Icc (j * N) (2 * (j * N)) →
        b j n * (n : ℂ) ^ (Complex.I * (ts r : ℂ)) = 0 :=
      fun n _ hn => by rw [hbsupp j n hn, zero_mul]
    calc (∑ n ∈ Finset.Icc N M, b j n * (n : ℂ) ^ (Complex.I * (ts r : ℂ)))
        = ∑ n ∈ rng, b j n * (n : ℂ) ^ (Complex.I * (ts r : ℂ)) :=
          Finset.sum_subset hsub1 hv1
      _ = ∑ n ∈ Finset.Icc (j * N) (2 * (j * N)),
            b j n * (n : ℂ) ^ (Complex.I * (ts r : ℂ)) :=
          (Finset.sum_subset hsub2 hv2).symm
  have hb_sq : ∀ j ∈ Finset.Icc 1 K,
      (∑ n ∈ Finset.Icc (j * N) (2 * (j * N)), ‖b j n‖ ^ 2)
        = (∑ n ∈ Finset.Icc N M, ‖b j n‖ ^ 2) := by
    intro j hj
    set rng : Finset ℕ := Finset.range (M + 2 * (j * N) + 1) with hrng
    have hsub1 : Finset.Icc N M ⊆ rng := by
      intro n hn
      rw [hrng, Finset.mem_range]
      have := (Finset.mem_Icc.mp hn).2
      omega
    have hsub2 : Finset.Icc (j * N) (2 * (j * N)) ⊆ rng := by
      intro n hn
      rw [hrng, Finset.mem_range]
      have := (Finset.mem_Icc.mp hn).2
      omega
    have hv1 : ∀ n ∈ rng, n ∉ Finset.Icc N M → ‖b j n‖ ^ 2 = 0 :=
      fun n _ hn => by rw [hbz j n hn]; simp
    have hv2 : ∀ n ∈ rng, n ∉ Finset.Icc (j * N) (2 * (j * N)) → ‖b j n‖ ^ 2 = 0 :=
      fun n _ hn => by rw [hbsupp j n hn]; simp
    calc (∑ n ∈ Finset.Icc (j * N) (2 * (j * N)), ‖b j n‖ ^ 2)
        = ∑ n ∈ rng, ‖b j n‖ ^ 2 := Finset.sum_subset hsub2 hv2
      _ = ∑ n ∈ Finset.Icc N M, ‖b j n‖ ^ 2 := (Finset.sum_subset hsub1 hv1).symm
  have hblk : ∀ j ∈ Finset.Icc 1 K,
      (∑ r, ‖∑ n ∈ Finset.Icc (j * N) (2 * (j * N)),
            b j n * (n : ℂ) ^ (Complex.I * (ts r : ℂ))‖ ^ 2)
        ≤ C₀ * (2 * T + ((j * N : ℕ) : ℝ))
            * (∑ n ∈ Finset.Icc (j * N) (2 * (j * N)), ‖b j n‖ ^ 2) := by
    intro j hj
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have hNj : 1 ≤ j * N := by
      have : 0 < j * N := Nat.mul_pos (by omega) hNpos
      omega
    exact hblock (j * N) hNj (2 * T) (by linarith) (b j) R ts htsI htssep
      (fun n hn => hbsupp j n hn)
  have hcs : ∀ r, ‖∑ j ∈ Finset.Icc 1 K,
        ∑ n ∈ Finset.Icc N M, b j n * (n : ℂ) ^ (Complex.I * (ts r : ℂ))‖ ^ 2
      ≤ (K : ℝ) * ∑ j ∈ Finset.Icc 1 K,
          ‖∑ n ∈ Finset.Icc N M, b j n * (n : ℂ) ^ (Complex.I * (ts r : ℂ))‖ ^ 2 := by
    intro r
    set X : ℕ → ℂ := fun j => ∑ n ∈ Finset.Icc N M, b j n * (n : ℂ) ^ (Complex.I * (ts r : ℂ))
    have h1 : ‖∑ j ∈ Finset.Icc 1 K, X j‖ ≤ ∑ j ∈ Finset.Icc 1 K, ‖X j‖ := norm_sum_le _ _
    have h2 := Finset.sum_mul_sq_le_sq_mul_sq (Finset.Icc 1 K) (fun j => ‖X j‖)
      (fun _ => (1 : ℝ))
    simp only [mul_one, one_pow, Finset.sum_const, nsmul_eq_mul] at h2
    have hcard : ((Finset.Icc 1 K).card : ℝ) = (K : ℝ) := by
      rw [Nat.card_Icc]
      norm_num
    rw [hcard] at h2
    calc ‖∑ j ∈ Finset.Icc 1 K, X j‖ ^ 2 ≤ (∑ j ∈ Finset.Icc 1 K, ‖X j‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ (∑ j ∈ Finset.Icc 1 K, ‖X j‖ ^ 2) * (K : ℝ) := h2
      _ = (K : ℝ) * ∑ j ∈ Finset.Icc 1 K, ‖X j‖ ^ 2 := by ring
  have hSzero : ∀ j ∈ Finset.Icc 1 K, ¬ (j * N ≤ M) →
      (∑ n ∈ Finset.Icc (j * N) (2 * (j * N)), ‖b j n‖ ^ 2) = 0 := by
    intro j hj hle
    apply Finset.sum_eq_zero
    intro n hn
    have h1 : b j n = 0 := by
      by_contra hbn
      have hjn : j * N ≤ n := by
        have hmem : n ∈ Finset.Icc (j * N) (2 * (j * N)) := by
          by_contra hnot
          exact hbn (hbsupp j n hnot)
        exact (Finset.mem_Icc.mp hmem).1
      have hnM : n ≤ M := by
        have hmem : n ∈ Finset.Icc N M := by
          by_contra hnot
          exact hbn (hbz j n hnot)
        exact (Finset.mem_Icc.mp hmem).2
      omega
    rw [h1]
    simp
  have hsum_j : (∑ j ∈ Finset.Icc 1 K, ∑ r, ‖∑ n ∈ Finset.Icc N M,
        b j n * (n : ℂ) ^ (Complex.I * (ts r : ℂ))‖ ^ 2)
      ≤ C₀ * 2 * (T + (M : ℝ)) * (∑ n ∈ Finset.Icc N M, ‖a n‖ ^ 2) := by
    have hstep : ∀ j ∈ Finset.Icc 1 K,
        (∑ r, ‖∑ n ∈ Finset.Icc N M, b j n * (n : ℂ) ^ (Complex.I * (ts r : ℂ))‖ ^ 2)
          ≤ C₀ * (2 * (T + (M : ℝ))) * (∑ n ∈ Finset.Icc N M, ‖b j n‖ ^ 2) := by
      intro j hj
      have h1 := hblk j hj
      have h2 : (∑ r, ‖∑ n ∈ Finset.Icc N M, b j n * (n : ℂ) ^ (Complex.I * (ts r : ℂ))‖ ^ 2)
          = (∑ r, ‖∑ n ∈ Finset.Icc (j * N) (2 * (j * N)),
              b j n * (n : ℂ) ^ (Complex.I * (ts r : ℂ))‖ ^ 2) := by
        apply Finset.sum_congr rfl
        intro r _
        rw [hb_eq j hj r]
      rw [h2, ← hb_sq j hj]
      by_cases hle : j * N ≤ M
      · have hle' : (((j * N : ℕ)) : ℝ) ≤ (M : ℝ) := by exact_mod_cast hle
        refine le_trans h1 ?_
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_left _ hC₀pos.le
        linarith
      · have hbzero : ∀ n, b j n = 0 := by
          intro n
          by_cases hn : n ∈ Finset.Icc N M
          swap
          · exact hbz j n hn
          by_cases hnb : n ∈ Finset.Icc (j * N) (2 * (j * N))
          swap
          · exact hbsupp j n hnb
          exfalso
          have h1 : j * N ≤ n := (Finset.mem_Icc.mp hnb).1
          have h2 : n ≤ M := (Finset.mem_Icc.mp hn).2
          omega
        have hzero : ∀ r, (∑ n ∈ Finset.Icc (j * N) (2 * (j * N)),
            b j n * (n : ℂ) ^ (Complex.I * (ts r : ℂ))) = 0 := by
          intro r
          apply Finset.sum_eq_zero
          intro n _
          rw [hbzero n, zero_mul]
        rw [hSzero j hj hle]
        simp only [mul_zero]
        have hsum0 : (∑ r, ‖∑ n ∈ Finset.Icc (j * N) (2 * (j * N)),
            b j n * (n : ℂ) ^ (Complex.I * (ts r : ℂ))‖ ^ 2) = 0 := by
          apply Finset.sum_eq_zero
          intro r _
          rw [hzero r]
          simp
        rw [hsum0]
    calc (∑ j ∈ Finset.Icc 1 K, ∑ r, ‖∑ n ∈ Finset.Icc N M,
            b j n * (n : ℂ) ^ (Complex.I * (ts r : ℂ))‖ ^ 2)
        ≤ ∑ j ∈ Finset.Icc 1 K, C₀ * (2 * (T + (M : ℝ))) * (∑ n ∈ Finset.Icc N M, ‖b j n‖ ^ 2) :=
          Finset.sum_le_sum hstep
      _ = C₀ * (2 * (T + (M : ℝ))) * (∑ j ∈ Finset.Icc 1 K, ∑ n ∈ Finset.Icc N M, ‖b j n‖ ^ 2) := by
          rw [Finset.mul_sum]
      _ = C₀ * (2 * (T + (M : ℝ))) * (∑ n ∈ Finset.Icc N M, ∑ j ∈ Finset.Icc 1 K, ‖b j n‖ ^ 2) := by
          rw [Finset.sum_comm]
      _ = C₀ * (2 * (T + (M : ℝ))) * (∑ n ∈ Finset.Icc N M, ‖a' n‖ ^ 2) := by
          congr 1
          apply Finset.sum_congr rfl
          intro n hn
          rw [Finset.sum_eq_single_of_mem (jf n) (hmap n hn)]
          · rw [hb]
            simp
          · intro j _ hjne
            rw [hb]
            simp [Ne.symm hjne]
      _ = C₀ * (2 * (T + (M : ℝ))) * (∑ n ∈ Finset.Icc N M, ‖a n‖ ^ 2) := by
          congr 1
          apply Finset.sum_congr rfl
          intro n hn
          rw [ha'norm n (le_trans hN (Finset.mem_Icc.mp hn).1)]
      _ = C₀ * 2 * (T + (M : ℝ)) * (∑ n ∈ Finset.Icc N M, ‖a n‖ ^ 2) := by ring
  calc (∑ r, ‖∑ n ∈ Finset.Icc N M, a n * (n : ℂ) ^ (Complex.I * (t r : ℂ))‖ ^ 2)
      = ∑ r, ‖∑ n ∈ Finset.Icc N M, a' n * (n : ℂ) ^ (Complex.I * (ts r : ℂ))‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro r _
        rw [hshift r]
    _ = ∑ r, ‖∑ j ∈ Finset.Icc 1 K,
          ∑ n ∈ Finset.Icc N M, b j n * (n : ℂ) ^ (Complex.I * (ts r : ℂ))‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro r _
        rw [hdecomp r]
    _ ≤ ∑ r, (K : ℝ) * ∑ j ∈ Finset.Icc 1 K,
          ‖∑ n ∈ Finset.Icc N M, b j n * (n : ℂ) ^ (Complex.I * (ts r : ℂ))‖ ^ 2 :=
        Finset.sum_le_sum (fun r _ => hcs r)
    _ = (K : ℝ) * ∑ j ∈ Finset.Icc 1 K, ∑ r,
          ‖∑ n ∈ Finset.Icc N M, b j n * (n : ℂ) ^ (Complex.I * (ts r : ℂ))‖ ^ 2 := by
        rw [Finset.sum_comm]
        rw [Finset.mul_sum]
    _ ≤ (K : ℝ) * (C₀ * 2 * (T + (M : ℝ)) * (∑ n ∈ Finset.Icc N M, ‖a n‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hsum_j (by positivity)
    _ ≤ 4 * C₀ * ((K : ℝ) + 1) * (T + (M : ℝ)) * (∑ n ∈ Finset.Icc N M, ‖a n‖ ^ 2) := by
        have hs : (0 : ℝ) ≤ ∑ n ∈ Finset.Icc N M, ‖a n‖ ^ 2 := by positivity
        have hTM : (0 : ℝ) ≤ T + (M : ℝ) := by positivity
        have hKM : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
        have hX : (0 : ℝ) ≤ C₀ * 2 * (T + (M : ℝ)) * (∑ n ∈ Finset.Icc N M, ‖a n‖ ^ 2) := by
          positivity
        calc (K : ℝ) * (C₀ * 2 * (T + (M : ℝ)) * (∑ n ∈ Finset.Icc N M, ‖a n‖ ^ 2))
            ≤ ((K : ℝ) + 1) * (C₀ * 2 * (T + (M : ℝ)) * (∑ n ∈ Finset.Icc N M, ‖a n‖ ^ 2)) :=
              mul_le_mul_of_nonneg_right (by linarith) hX
          _ ≤ 4 * C₀ * ((K : ℝ) + 1) * (T + (M : ℝ)) * (∑ n ∈ Finset.Icc N M, ‖a n‖ ^ 2) := by
              have hY : (0 : ℝ) ≤ ((K : ℝ) + 1) * (T + (M : ℝ))
                  * (∑ n ∈ Finset.Icc N M, ‖a n‖ ^ 2) := by positivity
              have hC : C₀ * 2 ≤ 4 * C₀ := by linarith [hC₀pos.le]
              calc ((K : ℝ) + 1) * (C₀ * 2 * (T + (M : ℝ)) * (∑ n ∈ Finset.Icc N M, ‖a n‖ ^ 2))
                  = (C₀ * 2) * (((K : ℝ) + 1) * (T + (M : ℝ))
                      * (∑ n ∈ Finset.Icc N M, ‖a n‖ ^ 2)) := by ring
                _ ≤ (4 * C₀) * (((K : ℝ) + 1) * (T + (M : ℝ))
                      * (∑ n ∈ Finset.Icc N M, ‖a n‖ ^ 2)) :=
                    mul_le_mul_of_nonneg_right hC hY
                _ = 4 * C₀ * ((K : ℝ) + 1) * (T + (M : ℝ))
                      * (∑ n ∈ Finset.Icc N M, ‖a n‖ ^ 2) := by ring

end Work.BMF.mr_direct
