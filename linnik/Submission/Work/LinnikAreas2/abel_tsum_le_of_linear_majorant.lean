import Mathlib

namespace Work.LinnikAreas2

/-- Finite Abel summation (summation by parts) with a linear coefficient `1 + c * n`.

For `K ≤ N`,
`∑_{K ≤ n ≤ N} (1 + c n) (f n - f (n+1))
   = (1 + c K) f K + c ∑_{K+1 ≤ n ≤ N} f n - (1 + c N) f (N+1)`. -/
theorem sum_Icc_mul_sub_linear (c : ℝ) (f : ℕ → ℝ) {K N : ℕ} (hKN : K ≤ N) :
    ∑ n ∈ Finset.Icc K N, (1 + c * (n : ℝ)) * (f n - f (n + 1)) =
      (1 + c * (K : ℝ)) * f K + c * (∑ n ∈ Finset.Icc (K + 1) N, f n)
        - (1 + c * (N : ℝ)) * f (N + 1) := by
  induction N, hKN using Nat.le_induction with
  | base =>
      simp only [Finset.Icc_self, Finset.sum_singleton,
        Finset.Icc_eq_empty_of_lt (Nat.lt_succ_self K), Finset.sum_empty]
      ring
  | succ N hKN ih =>
      rw [Finset.sum_Icc_succ_top (show K ≤ N + 1 by omega), ih,
        Finset.sum_Icc_succ_top (show K + 1 ≤ N + 1 by omega)]
      push_cast
      ring

/-- Abel's partial summation identity.  With `A n = ∑_{k ∈ Icc 1 n} a k`,
`∑_{n ∈ Icc 1 N} a n f n = A N * f (N+1) + ∑_{n ∈ Icc 1 N} A n * (f n - f (n+1))`. -/
theorem sum_Icc_mul_eq_partial_summation (a f : ℕ → ℝ) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, a n * f n =
      (∑ k ∈ Finset.Icc 1 N, a k) * f (N + 1)
        + ∑ n ∈ Finset.Icc 1 N, (∑ k ∈ Finset.Icc 1 n, a k) * (f n - f (n + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
      have hk : (1 : ℕ) ≤ N + 1 := by omega
      rw [Finset.sum_Icc_succ_top hk (fun n => a n * f n),
          Finset.sum_Icc_succ_top hk
            (fun n => (∑ k ∈ Finset.Icc 1 n, a k) * (f n - f (n + 1))),
          ih,
          Finset.sum_Icc_succ_top hk (fun k => a k)]
      ring

/-- The partial sums `N ↦ ∑_{n ∈ Icc 1 N} g n` converge to the `tsum` when `g 0 = 0`
and `g` is summable. -/
theorem tendsto_sum_Icc_one_tsum (g : ℕ → ℝ) (h0 : g 0 = 0) (hg : Summable g) :
    Filter.Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, g n) Filter.atTop
      (nhds (∑' n, g n)) := by
  have h1 : Filter.Tendsto (fun N : ℕ => ∑ n ∈ Finset.range (N + 1), g n) Filter.atTop
      (nhds (∑' n, g n)) := by
    have h := hg.hasSum.tendsto_sum_nat
    exact h.comp (Filter.tendsto_add_atTop_nat 1)
  refine h1.congr' ?_
  filter_upwards with N
  have hset : Finset.range (N + 1) = insert 0 (Finset.Icc 1 N) := by
    ext n
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [hset, Finset.sum_insert (by simp [Finset.mem_Icc]), h0, zero_add]

theorem abel_tsum_le_of_linear_majorant (a f : ℕ → ℝ) {c : ℝ} (K : ℕ)
    (ha : ∀ n, 0 ≤ a n) (ha0 : a 0 = 0) (hf : ∀ n, 0 ≤ f n)
    (hmaj : ∀ N : ℕ, (∑ n ∈ Finset.Icc 1 N, a n) ≤ 1 + c * (N : ℝ))
    (hdec : ∀ n : ℕ, K ≤ n → f (n + 1) ≤ f n)
    (hinc : ∀ n : ℕ, n < K → f n ≤ f (n + 1))
    (hsum : Summable (fun n : ℕ => a n * f n)) (hsumf : Summable f)
    (hvan : Filter.Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc 1 N, a n) * f (N + 1)) Filter.atTop (nhds 0)) :
    ∑' n : ℕ, a n * f n ≤ (1 + c * (K : ℝ)) * f K + c * ∑' n : ℕ, f n := by
  have hAnonneg : ∀ n, 0 ≤ ∑ k ∈ Finset.Icc 1 n, a k :=
    fun n => Finset.sum_nonneg fun k _ => ha k
  have hBnn : ∀ n : ℕ, 0 ≤ 1 + c * (n : ℝ) := fun n => by
    have := hmaj n
    linarith [hAnonneg n]
  -- The majorant forces `c ≥ 0`.
  have hc : 0 ≤ c := by
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨n, hn⟩ := exists_nat_gt (1 / (-c))
    have hnc : (1 : ℝ) < (n : ℝ) * (-c) := by
      rw [div_lt_iff₀ (by linarith : (0 : ℝ) < -c)] at hn
      exact hn
    have h2 : c * (n : ℝ) < -1 := by
      have h1 : c * (n : ℝ) = -((n : ℝ) * (-c)) := by ring
      rw [h1]
      linarith [hnc]
    linarith [hBnn n]
  have hfnn : 0 ≤ ∑' n : ℕ, f n := tsum_nonneg hf
  -- The Abel remainder is bounded by the claimed right-hand side, for every `N`.
  have hQle : ∀ N, (∑ n ∈ Finset.Icc 1 N,
        (∑ k ∈ Finset.Icc 1 n, a k) * (f n - f (n + 1)))
      ≤ (1 + c * (K : ℝ)) * f K + c * ∑' n : ℕ, f n := by
    intro N
    rcases le_or_gt K N with hKN | hNK
    · rcases Nat.eq_zero_or_pos K with hK0 | hKpos
      · -- `K = 0`: the whole sum runs over the decreasing region.
        subst hK0
        have hstep1 : (∑ n ∈ Finset.Icc 1 N,
              (∑ k ∈ Finset.Icc 1 n, a k) * (f n - f (n + 1)))
            ≤ ∑ n ∈ Finset.Icc 1 N, (1 + c * (n : ℝ)) * (f n - f (n + 1)) := by
          apply Finset.sum_le_sum
          intro n _
          have hd : 0 ≤ f n - f (n + 1) := by
            have := hdec n (Nat.zero_le n); linarith
          exact mul_le_mul_of_nonneg_right (hmaj n) hd
        have hstep2 : (∑ n ∈ Finset.Icc 1 N, (1 + c * (n : ℝ)) * (f n - f (n + 1)))
            ≤ ∑ n ∈ Finset.Icc 0 N, (1 + c * (n : ℝ)) * (f n - f (n + 1)) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · exact Finset.Icc_subset_Icc_left (Nat.zero_le 1)
          · intro i hi his
            have hi1 : i ≤ N := (Finset.mem_Icc.mp hi).2
            have hi0 : i = 0 := by
              by_contra h
              exact his (Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr h, hi1⟩)
            subst hi0
            have hd : 0 ≤ f 0 - f (0 + 1) := by
              have := hdec 0 (Nat.zero_le 0); linarith
            simpa using hd
        have hstep3 : (∑ n ∈ Finset.Icc 0 N, (1 + c * (n : ℝ)) * (f n - f (n + 1)))
            ≤ (1 + c * ((0 : ℕ) : ℝ)) * f 0 + c * ∑' n : ℕ, f n := by
          rw [sum_Icc_mul_sub_linear c f (Nat.zero_le N)]
          have hble : (∑ n ∈ Finset.Icc ((0 : ℕ) + 1) N, f n) ≤ ∑' n : ℕ, f n :=
            hsumf.sum_le_tsum _ (fun i _ => hf i)
          have h1 : c * (∑ n ∈ Finset.Icc ((0 : ℕ) + 1) N, f n) ≤ c * ∑' n : ℕ, f n :=
            mul_le_mul_of_nonneg_left hble hc
          have h2 : 0 ≤ (1 + c * ((N : ℕ) : ℝ)) * f (N + 1) :=
            mul_nonneg (hBnn N) (hf (N + 1))
          linarith [h1, h2]
        linarith [hstep1, hstep2, hstep3]
      · -- `1 ≤ K ≤ N`: discard the increasing region, keep `K ≤ n ≤ N`.
        have hK1 : 1 ≤ K := hKpos
        have hstep1 : (∑ n ∈ Finset.Icc 1 N,
              (∑ k ∈ Finset.Icc 1 n, a k) * (f n - f (n + 1)))
            ≤ ∑ n ∈ Finset.Icc K N, (∑ k ∈ Finset.Icc 1 n, a k) * (f n - f (n + 1)) := by
          have hsub : Finset.Icc K N ⊆ Finset.Icc 1 N := Finset.Icc_subset_Icc_left hK1
          have hs := Finset.sum_sdiff
            (f := fun n => (∑ k ∈ Finset.Icc 1 n, a k) * (f n - f (n + 1))) hsub
          have hsdiff : (∑ x ∈ Finset.Icc 1 N \ Finset.Icc K N,
              (∑ k ∈ Finset.Icc 1 x, a k) * (f x - f (x + 1))) ≤ 0 := by
            apply Finset.sum_nonpos
            intro n hn
            obtain ⟨hn1, hn2⟩ := Finset.mem_sdiff.mp hn
            have hnN : n ≤ N := (Finset.mem_Icc.mp hn1).2
            have hlt : n < K := by
              by_contra h
              exact hn2 (Finset.mem_Icc.mpr ⟨not_lt.mp h, hnN⟩)
            have hd : f n - f (n + 1) ≤ 0 := by
              have := hinc n hlt; linarith
            exact mul_nonpos_of_nonneg_of_nonpos (hAnonneg n) hd
          linarith [hs, hsdiff]
        have hstep2 : (∑ n ∈ Finset.Icc K N, (∑ k ∈ Finset.Icc 1 n, a k) * (f n - f (n + 1)))
            ≤ ∑ n ∈ Finset.Icc K N, (1 + c * (n : ℝ)) * (f n - f (n + 1)) := by
          apply Finset.sum_le_sum
          intro n hn
          have hnK : K ≤ n := (Finset.mem_Icc.mp hn).1
          have hd : 0 ≤ f n - f (n + 1) := by
            have := hdec n hnK; linarith
          exact mul_le_mul_of_nonneg_right (hmaj n) hd
        have hstep3 : (∑ n ∈ Finset.Icc K N, (1 + c * (n : ℝ)) * (f n - f (n + 1)))
            ≤ (1 + c * (K : ℝ)) * f K + c * ∑' n : ℕ, f n := by
          rw [sum_Icc_mul_sub_linear c f hKN]
          have hble : (∑ n ∈ Finset.Icc (K + 1) N, f n) ≤ ∑' n : ℕ, f n :=
            hsumf.sum_le_tsum _ (fun i _ => hf i)
          have h1 : c * (∑ n ∈ Finset.Icc (K + 1) N, f n) ≤ c * ∑' n : ℕ, f n :=
            mul_le_mul_of_nonneg_left hble hc
          have h2 : 0 ≤ (1 + c * ((N : ℕ) : ℝ)) * f (N + 1) :=
            mul_nonneg (hBnn N) (hf (N + 1))
          linarith [h1, h2]
        linarith [hstep1, hstep2, hstep3]
    · -- `N < K`: every summand is non-positive.
      have hnp : (∑ n ∈ Finset.Icc 1 N,
            (∑ k ∈ Finset.Icc 1 n, a k) * (f n - f (n + 1))) ≤ 0 := by
        apply Finset.sum_nonpos
        intro n hn
        have hnN : n ≤ N := (Finset.mem_Icc.mp hn).2
        have hlt : n < K := lt_of_le_of_lt hnN hNK
        have hd : f n - f (n + 1) ≤ 0 := by
          have := hinc n hlt; linarith
        exact mul_nonpos_of_nonneg_of_nonpos (hAnonneg n) hd
      have hbnn : 0 ≤ (1 + c * (K : ℝ)) * f K + c * ∑' n : ℕ, f n :=
        add_nonneg (mul_nonneg (hBnn K) (hf K)) (mul_nonneg hc hfnn)
      linarith
  -- Pass to the limit `N → ∞` in the Abel identity.
  have hP : Filter.Tendsto (fun N => ∑ n ∈ Finset.Icc 1 N, a n * f n) Filter.atTop
      (nhds (∑' n : ℕ, a n * f n)) :=
    tendsto_sum_Icc_one_tsum (fun n => a n * f n) (by simp [ha0]) hsum
  have hQ : Filter.Tendsto (fun N => ∑ n ∈ Finset.Icc 1 N,
        (∑ k ∈ Finset.Icc 1 n, a k) * (f n - f (n + 1)))
      Filter.atTop (nhds (∑' n : ℕ, a n * f n)) := by
    have hsub : Filter.Tendsto (fun N => (∑ n ∈ Finset.Icc 1 N, a n * f n)
        - (∑ k ∈ Finset.Icc 1 N, a k) * f (N + 1)) Filter.atTop
        (nhds ((∑' n : ℕ, a n * f n) - 0)) :=
      hP.sub hvan
    rw [sub_zero] at hsub
    have hPQ : (fun N => ∑ n ∈ Finset.Icc 1 N,
          (∑ k ∈ Finset.Icc 1 n, a k) * (f n - f (n + 1)))
        = fun N => (∑ n ∈ Finset.Icc 1 N, a n * f n)
            - (∑ k ∈ Finset.Icc 1 N, a k) * f (N + 1) := by
      funext N
      rw [sum_Icc_mul_eq_partial_summation a f N]; ring
    rw [hPQ]; exact hsub
  exact le_of_tendsto' hQ hQle

end Work.LinnikAreas2
