import Mathlib
import Submission.Work.ZeroDensity.Ingham.Defs
import Submission.Work.ZeroDensity.Ingham.dirPolyIntervalMeanValueBound

/-!
# The mean square of the truncated Möbius polynomial on the critical line

We prove `∫_0^T ‖M_K(1/2 + it)‖² dt ≤ C (T + K log(K+2)) log(K+2)` for `K, T ≥ 1`, where
`M_K(s) = Σ_{n ≤ K} μ(n) n^{-s}` is the truncated Möbius polynomial.

The route is Montgomery–Vaughan §28.4.1 (the `q = Q = 1` case):
`M_K(1/2 + it) = Σ_{n ≤ K} b_n n^{-it}` with `b_n = μ(n) n^{-1/2}`, so Montgomery's mean value
bound (`dirPolyIntervalMeanValueBound`, in the sharp `max(m,n)/|m-n|` kernel form) gives

`∫_0^T ‖M_K‖² ≤ T Σ_n ‖b_n‖² + C₁ Σ_{m,n} ‖b_m‖ ‖b_n‖ max(m,n)/|m-n|`,

the first term is `≤ 2T log(K+2)` (`mkCoefNormSqSum_le`, from the harmonic sum and `‖b_n‖ ≤ n^{-1/2}`)
and the second is `≤ C₁ · 24 K log(K+2)` by the off-diagonal kernel estimate `kernBound_local`.

The kernel estimate is the classical `Σ_{m,n ≤ N} max(m,n)/(√(mn)|m-n|) ≪ N log N`: by symmetry
the double sum is twice its lower triangle, and on the lower triangle the diagonal weighting
`M/(M-n)` is split at `n = M/2`, giving
`Σ_{n < M} (1/√n)/(M-n) ≤ 4/√M + √2 (1 + log M)/√M ≤ 12 log(M+2)/√M`.
-/

namespace Work.ZeroDensity.Ingham

open scoped BigOperators

/-! ### Elementary summatory estimates -/

/-- `1/√(n+1) ≤ 2(√(n+1) − √n)`. -/
private lemma inv_sqrt_succ_le (n : ℕ) :
    (1 : ℝ) / Real.sqrt ((n : ℝ) + 1) ≤ 2 * (Real.sqrt ((n : ℝ) + 1) - Real.sqrt (n : ℝ)) := by
  have hpos : (0 : ℝ) < Real.sqrt ((n : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
  rw [div_le_iff₀ hpos]
  have hsq : Real.sqrt ((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 1) = (n : ℝ) + 1 :=
    Real.mul_self_sqrt (by positivity)
  have hsqrt : Real.sqrt ((n : ℝ) * ((n : ℝ) + 1)) =
      Real.sqrt ((n : ℝ) + 1) * Real.sqrt (n : ℝ) := by
    rw [mul_comm]; exact Real.sqrt_mul (by positivity) _
  have hle : Real.sqrt ((n : ℝ) * ((n : ℝ) + 1)) ≤ (2 * (n : ℝ) + 1) / 2 := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith
  nlinarith [hsqrt, hsq, hle]

/-- `Σ_{n ≤ N} 1/√n ≤ 2√N`. -/
private lemma sum_inv_sqrt_le' (N : ℕ) :
    ∑ n ∈ Finset.Ico 1 (N + 1), (1 : ℝ) / Real.sqrt (n : ℝ) ≤ 2 * Real.sqrt (N : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Ico_succ_top (a := 1) (b := N + 1) (by omega)]
    have hk := inv_sqrt_succ_le N
    simp only [Nat.cast_add, Nat.cast_one] at hk ih ⊢
    linarith

/-- `Σ_{a ≤ n < b} 1/(b − n) ≤ 1 + log M` for `1 ≤ a ≤ b ≤ M`. -/
private lemma sum_Ico_inv_sub_le' (a b M : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) (hbM : b ≤ M) :
    ∑ n ∈ Finset.Ico a b, (1 : ℝ) / ((b : ℝ) - (n : ℝ)) ≤ 1 + Real.log (M : ℝ) := by
  have h1 : ∑ n ∈ Finset.Ico a b, (1 : ℝ) / ((b : ℝ) - (n : ℝ))
      = ∑ n ∈ Finset.Ico a b, (1 : ℝ) / (((b - n : ℕ) : ℝ)) := by
    refine Finset.sum_congr rfl ?_
    intro n hn
    have hnb : n ≤ b := le_of_lt (Finset.mem_Ico.mp hn).2
    rw [Nat.cast_sub hnb]
  rw [h1]
  have h2 : ∑ n ∈ Finset.Ico a b, (1 : ℝ) / (((b - n : ℕ) : ℝ))
      = ∑ j ∈ Finset.Ico 1 (b - a + 1), (1 : ℝ) / (j : ℝ) := by
    have h := Finset.sum_Ico_reflect (fun x : ℕ => (1 : ℝ) / (x : ℝ)) a
      (m := b) (n := b) (by omega : b ≤ b + 1)
    rw [show b + 1 - b = 1 by omega, show b + 1 - a = b - a + 1 by omega] at h
    exact h
  rw [h2]
  have hn0le : b - a + 1 ≤ M := by omega
  calc ∑ j ∈ Finset.Ico 1 (b - a + 1), (1 : ℝ) / (j : ℝ)
      ≤ ∑ j ∈ Finset.Icc 1 (b - a + 1), (1 : ℝ) / (j : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.Ico_subset_Icc_self
          (fun i _ _ => by positivity)
    _ ≤ 1 + Real.log ((b - a + 1 : ℕ) : ℝ) := by
        have h := harmonic_le_one_add_log (b - a + 1)
        rw [harmonic_eq_sum_Icc] at h
        push_cast at h
        simpa [one_div] using h
    _ ≤ 1 + Real.log (M : ℝ) := by
        have hle : Real.log (((b - a + 1 : ℕ)) : ℝ) ≤ Real.log (M : ℝ) :=
          Real.log_le_log (by exact_mod_cast (show 0 < b - a + 1 by omega))
            (by exact_mod_cast hn0le)
        linarith

/-! ### The off-diagonal kernel estimate -/

/-- Decomposition of the symmetric kernel summand into the two triangles; the diagonal
`m = n` is `0` on both sides (`|m - m| = 0`). -/
private lemma pair_decomp (f : ℕ → ℝ) (m n : ℕ) :
    f m * f n * max (m : ℝ) (n : ℝ) / |(m : ℝ) - (n : ℝ)|
      = (if n < m then f m * f n * ((m : ℝ) / ((m : ℝ) - (n : ℝ))) else 0)
        + (if m < n then f n * f m * ((n : ℝ) / ((n : ℝ) - (m : ℝ))) else 0) := by
  rcases lt_trichotomy m n with h | h | h
  · have h' : (m : ℝ) < (n : ℝ) := by exact_mod_cast h
    have hmax : max (m : ℝ) (n : ℝ) = (n : ℝ) := max_eq_right (le_of_lt h')
    have habs : |(m : ℝ) - (n : ℝ)| = (n : ℝ) - (m : ℝ) := by
      rw [abs_of_neg (by linarith)]; ring
    rw [hmax, habs, if_neg (show ¬ n < m by omega), if_pos h]
    ring
  · subst h
    simp
  · have h' : (n : ℝ) < (m : ℝ) := by exact_mod_cast h
    have hmax : max (m : ℝ) (n : ℝ) = (m : ℝ) := max_eq_left (le_of_lt h')
    have habs : |(m : ℝ) - (n : ℝ)| = (m : ℝ) - (n : ℝ) := abs_of_pos (by linarith)
    rw [hmax, habs, if_pos h, if_neg (show ¬ m < n by omega)]
    ring

/-- The lower-triangle part, summed by fixing the larger index. -/
private lemma kern_sum_lower (f : ℕ → ℝ) (N : ℕ) :
    (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
        (if n < m then f m * f n * ((m : ℝ) / ((m : ℝ) - (n : ℝ))) else 0))
      = ∑ M ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Ico 1 M,
          f M * f n * ((M : ℝ) / ((M : ℝ) - (n : ℝ))) := by
  apply Finset.sum_congr rfl
  intro m hm
  have hmN : m ≤ N := (Finset.mem_Icc.mp hm).2
  have hset : (Finset.Icc 1 N).filter (fun n => n < m) = Finset.Ico 1 m := by
    ext n; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [← Finset.sum_filter, hset]

/-- The upper-triangle part, reindexed by swapping the two orders of summation. -/
private lemma kern_sum_upper (f : ℕ → ℝ) (N : ℕ) :
    (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
        (if m < n then f n * f m * ((n : ℝ) / ((n : ℝ) - (m : ℝ))) else 0))
      = ∑ M ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Ico 1 M,
          f M * f n * ((M : ℝ) / ((M : ℝ) - (n : ℝ))) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  have hnN : n ≤ N := (Finset.mem_Icc.mp hn).2
  have hset : (Finset.Icc 1 N).filter (fun m => m < n) = Finset.Ico 1 n := by
    ext m; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [← Finset.sum_filter, hset]

/-- **Symmetry reduction.**  The symmetric double sum is twice its lower triangle. -/
private theorem symm_eq_two_tri (f : ℕ → ℝ) (N : ℕ) :
    (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
        f m * f n * max (m : ℝ) (n : ℝ) / |(m : ℝ) - (n : ℝ)|)
      = 2 * ∑ M ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Ico 1 M,
          f M * f n * ((M : ℝ) / ((M : ℝ) - (n : ℝ))) := by
  calc (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
        f m * f n * max (m : ℝ) (n : ℝ) / |(m : ℝ) - (n : ℝ)|)
      = ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
          ((if n < m then f m * f n * ((m : ℝ) / ((m : ℝ) - (n : ℝ))) else 0)
            + (if m < n then f n * f m * ((n : ℝ) / ((n : ℝ) - (m : ℝ))) else 0)) := by
        refine Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun n _ => ?_))
        exact pair_decomp f m n
    _ = (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
            (if n < m then f m * f n * ((m : ℝ) / ((m : ℝ) - (n : ℝ))) else 0))
        + (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
            (if m < n then f n * f m * ((n : ℝ) / ((n : ℝ) - (m : ℝ))) else 0)) := by
        simp only [Finset.sum_add_distrib]
    _ = 2 * ∑ M ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Ico 1 M,
          f M * f n * ((M : ℝ) / ((M : ℝ) - (n : ℝ))) := by
        rw [kern_sum_lower, kern_sum_upper]; ring

/-- **Inner ratio estimate.**  `Σ_{n < M} (1/√n)/(M − n) ≤ 12 log(M+2)/√M`.  Split at `M/2`:
for `n ≤ M/2` the denominator is at least `M/2` (so the weights `1/√n` telescope), while for
`n > M/2` the weight `1/√n` is at most `√2/√M` and the remaining sum is harmonic. -/
private lemma innerSumSqrtBound (M : ℕ) (hM : 1 ≤ M) :
    (∑ n ∈ Finset.Ico 1 M, (1 / Real.sqrt (n : ℝ)) / ((M : ℝ) - (n : ℝ)))
      ≤ 12 * Real.log ((M : ℝ) + 2) / Real.sqrt (M : ℝ) := by
  rcases eq_or_lt_of_le hM with h1 | h2
  · subst h1
    rw [Finset.Ico_self, Finset.sum_empty]
    have h3 : (0 : ℝ) ≤ Real.log ((1 : ℝ) + 2) := Real.log_nonneg (by norm_num)
    positivity
  · have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
    have hsM : 0 < Real.sqrt (M : ℝ) := Real.sqrt_pos.mpr hMpos
    set L : ℝ := Real.log ((M : ℝ) + 2) with hLdef
    have hL1 : 1 ≤ L := by
      rw [hLdef, Real.le_log_iff_exp_le (by linarith : (0 : ℝ) < (M : ℝ) + 2)]
      calc Real.exp 1 ≤ 3 := le_of_lt Real.exp_one_lt_three
        _ ≤ (M : ℝ) + 2 := by
            have : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast h2
            linarith
    have hsplit : (∑ n ∈ Finset.Ico 1 M, (1 / Real.sqrt (n : ℝ)) / ((M : ℝ) - (n : ℝ)))
        = (∑ n ∈ Finset.Ico 1 (M / 2 + 1), (1 / Real.sqrt (n : ℝ)) / ((M : ℝ) - (n : ℝ)))
          + ∑ n ∈ Finset.Ico (M / 2 + 1) M,
              (1 / Real.sqrt (n : ℝ)) / ((M : ℝ) - (n : ℝ)) :=
      (Finset.sum_Ico_consecutive _ (by omega : 1 ≤ M / 2 + 1)
        (by omega : M / 2 + 1 ≤ M)).symm
    rw [hsplit]
    -- small `n`: the denominator is at least `M/2`
    have hA : (∑ n ∈ Finset.Ico 1 (M / 2 + 1),
        (1 / Real.sqrt (n : ℝ)) / ((M : ℝ) - (n : ℝ))) ≤ 4 / Real.sqrt (M : ℝ) := by
      have hterm : ∀ n ∈ Finset.Ico 1 (M / 2 + 1),
          (1 / Real.sqrt (n : ℝ)) / ((M : ℝ) - (n : ℝ))
            ≤ (2 / (M : ℝ)) * (1 / Real.sqrt (n : ℝ)) := by
        intro n hn
        rw [Finset.mem_Ico] at hn
        obtain ⟨hn1, hn2⟩ := hn
        have hnM : n ≤ M / 2 := by omega
        have hnm : n < M := by omega
        have hden : (0 : ℝ) < (M : ℝ) - (n : ℝ) := by
          have : (n : ℝ) < (M : ℝ) := by exact_mod_cast hnm
          linarith
        have hrec : (1 : ℝ) / ((M : ℝ) - (n : ℝ)) ≤ 2 / (M : ℝ) := by
          rw [div_le_div_iff₀ hden hMpos]
          have h2n : 2 * n ≤ M := by
            have h1 : 2 * n ≤ 2 * (M / 2) := Nat.mul_le_mul_left 2 hnM
            have h2' : 2 * (M / 2) ≤ M := Nat.mul_div_le M 2
            omega
          have hc : ((2 * n : ℕ) : ℝ) ≤ (M : ℝ) := by exact_mod_cast h2n
          push_cast at hc
          linarith
        calc (1 / Real.sqrt (n : ℝ)) / ((M : ℝ) - (n : ℝ))
            = (1 / Real.sqrt (n : ℝ)) * (1 / ((M : ℝ) - (n : ℝ))) := by ring
          _ ≤ (1 / Real.sqrt (n : ℝ)) * (2 / (M : ℝ)) :=
              mul_le_mul_of_nonneg_left hrec (by positivity)
          _ = (2 / (M : ℝ)) * (1 / Real.sqrt (n : ℝ)) := by ring
      calc (∑ n ∈ Finset.Ico 1 (M / 2 + 1),
            (1 / Real.sqrt (n : ℝ)) / ((M : ℝ) - (n : ℝ)))
          ≤ ∑ n ∈ Finset.Ico 1 (M / 2 + 1),
              (2 / (M : ℝ)) * (1 / Real.sqrt (n : ℝ)) := Finset.sum_le_sum hterm
        _ = (2 / (M : ℝ)) * ∑ n ∈ Finset.Ico 1 (M / 2 + 1),
              (1 / Real.sqrt (n : ℝ)) := by rw [Finset.mul_sum]
        _ ≤ (2 / (M : ℝ)) * (2 * Real.sqrt ((M / 2 : ℕ) : ℝ)) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact sum_inv_sqrt_le' (M / 2)
        _ ≤ 4 / Real.sqrt (M : ℝ) := by
            have hs : Real.sqrt (M : ℝ) * Real.sqrt (M : ℝ) = (M : ℝ) :=
              Real.mul_self_sqrt hMpos.le
            have hle : Real.sqrt (((M / 2 : ℕ) : ℝ)) ≤ Real.sqrt (M : ℝ) :=
              Real.sqrt_le_sqrt (by exact_mod_cast Nat.div_le_self M 2)
            have h2' : (2 / (M : ℝ)) * (2 * Real.sqrt ((M / 2 : ℕ) : ℝ))
                ≤ (2 / (M : ℝ)) * (2 * Real.sqrt (M : ℝ)) :=
              mul_le_mul_of_nonneg_left (by linarith) (by positivity)
            have heq : (2 / (M : ℝ)) * (2 * Real.sqrt (M : ℝ)) = 4 / Real.sqrt (M : ℝ) := by
              field_simp
              nlinarith [hs]
            linarith [h2', heq.le, heq.ge]
    -- large `n`: the weight is at most `√2/√M`
    have hB : (∑ n ∈ Finset.Ico (M / 2 + 1) M,
        (1 / Real.sqrt (n : ℝ)) / ((M : ℝ) - (n : ℝ)))
        ≤ Real.sqrt 2 * (1 + Real.log (M : ℝ)) / Real.sqrt (M : ℝ) := by
      have hterm : ∀ n ∈ Finset.Ico (M / 2 + 1) M,
          (1 / Real.sqrt (n : ℝ)) / ((M : ℝ) - (n : ℝ))
            ≤ (Real.sqrt 2 / Real.sqrt (M : ℝ)) * (1 / ((M : ℝ) - (n : ℝ))) := by
        intro n hn
        rw [Finset.mem_Ico] at hn
        obtain ⟨hn1, hn2⟩ := hn
        have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
        have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnpos
        have hden : (0 : ℝ) < (M : ℝ) - (n : ℝ) := by
          have : (n : ℝ) < (M : ℝ) := by exact_mod_cast hn2
          linarith
        have hinv : 1 / Real.sqrt (n : ℝ) ≤ Real.sqrt 2 / Real.sqrt (M : ℝ) := by
          rw [div_le_div_iff₀ hsn hsM]
          have hM2n : (M : ℝ) ≤ 2 * (n : ℝ) := by
            have : M < 2 * n := by omega
            have hc : (M : ℝ) < ((2 * n : ℕ) : ℝ) := by exact_mod_cast this
            push_cast at hc
            linarith
          have hs2n : Real.sqrt (M : ℝ) ≤ Real.sqrt (2 * (n : ℝ)) := Real.sqrt_le_sqrt hM2n
          rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) (n : ℝ)] at hs2n
          linarith
        calc (1 / Real.sqrt (n : ℝ)) / ((M : ℝ) - (n : ℝ))
            = (1 / Real.sqrt (n : ℝ)) * (1 / ((M : ℝ) - (n : ℝ))) := by ring
          _ ≤ (Real.sqrt 2 / Real.sqrt (M : ℝ)) * (1 / ((M : ℝ) - (n : ℝ))) :=
              mul_le_mul_of_nonneg_right hinv (div_nonneg zero_le_one hden.le)
      calc (∑ n ∈ Finset.Ico (M / 2 + 1) M,
            (1 / Real.sqrt (n : ℝ)) / ((M : ℝ) - (n : ℝ)))
          ≤ ∑ n ∈ Finset.Ico (M / 2 + 1) M,
              (Real.sqrt 2 / Real.sqrt (M : ℝ)) * (1 / ((M : ℝ) - (n : ℝ))) :=
            Finset.sum_le_sum hterm
        _ = (Real.sqrt 2 / Real.sqrt (M : ℝ)) *
              ∑ n ∈ Finset.Ico (M / 2 + 1) M, (1 / ((M : ℝ) - (n : ℝ))) := by
            rw [Finset.mul_sum]
        _ ≤ (Real.sqrt 2 / Real.sqrt (M : ℝ)) * (1 + Real.log (M : ℝ)) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact sum_Ico_inv_sub_le' (M / 2 + 1) M M (by omega) (by omega) le_rfl
        _ = Real.sqrt 2 * (1 + Real.log (M : ℝ)) / Real.sqrt (M : ℝ) := by ring
    have hfin : 4 / Real.sqrt (M : ℝ) + Real.sqrt 2 * (1 + Real.log (M : ℝ)) / Real.sqrt (M : ℝ)
        ≤ 12 * L / Real.sqrt (M : ℝ) := by
      rw [← add_div]
      apply div_le_div_of_nonneg_right _ hsM.le
      have h2le : Real.sqrt 2 ≤ 2 := by
        have h := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
        nlinarith [Real.sqrt_nonneg 2, h]
      have hlogM : Real.log (M : ℝ) ≤ L := by
        rw [hLdef]
        exact Real.log_le_log hMpos (by linarith)
      have hlogMnn : 0 ≤ Real.log (M : ℝ) := Real.log_nonneg (by exact_mod_cast hM)
      have h1 : Real.sqrt 2 * (1 + Real.log (M : ℝ)) ≤ 2 * (1 + L) := by
        have h2' : Real.sqrt 2 * (1 + Real.log (M : ℝ)) ≤ 2 * (1 + Real.log (M : ℝ)) :=
          mul_le_mul_of_nonneg_right h2le (by linarith)
        linarith
      linarith
    linarith [hA, hB, hfin]

/-- **Off-diagonal kernel estimate.**  There is an absolute `C > 0` with
`Σ_{m,n ≤ N} max(m,n)/(√(mn)|m−n|) ≤ C N log(N+2)`. -/
private theorem kernBound_local : ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
    (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
        (1 / Real.sqrt (m : ℝ)) * (1 / Real.sqrt (n : ℝ))
          * max (m : ℝ) (n : ℝ) / |(m : ℝ) - (n : ℝ)|)
      ≤ C * (N : ℝ) * Real.log ((N : ℝ) + 2) := by
  refine ⟨24, by norm_num, ?_⟩
  intro N hN
  set L : ℝ := Real.log ((N : ℝ) + 2) with hLdef
  have hL1 : 1 ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le (by linarith : (0 : ℝ) < (N : ℝ) + 2)]
    calc Real.exp 1 ≤ 3 := le_of_lt Real.exp_one_lt_three
      _ ≤ (N : ℝ) + 2 := by
          have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
          linarith
  have hterm : ∀ M ∈ Finset.Icc 1 N,
      (∑ n ∈ Finset.Ico 1 M,
          (1 / Real.sqrt (M : ℝ)) * (1 / Real.sqrt (n : ℝ))
            * ((M : ℝ) / ((M : ℝ) - (n : ℝ)))) ≤ 12 * L := by
    intro M hM
    obtain ⟨hM1, hMN⟩ := Finset.mem_Icc.mp hM
    have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
    have hsM : 0 < Real.sqrt (M : ℝ) := Real.sqrt_pos.mpr hMpos
    have hstep : ∀ n ∈ Finset.Ico 1 M,
        (1 / Real.sqrt (M : ℝ)) * (1 / Real.sqrt (n : ℝ)) * ((M : ℝ) / ((M : ℝ) - (n : ℝ)))
          = Real.sqrt (M : ℝ) * ((1 / Real.sqrt (n : ℝ)) / ((M : ℝ) - (n : ℝ))) := by
      intro n hn
      have hs : Real.sqrt (M : ℝ) * Real.sqrt (M : ℝ) = (M : ℝ) := Real.mul_self_sqrt hMpos.le
      have hden : ((M : ℝ) - (n : ℝ)) ≠ 0 := by
        have : (n : ℝ) < (M : ℝ) := by
          have := (Finset.mem_Ico.mp hn).2
          exact_mod_cast this
        linarith
      field_simp
      rw [Real.sq_sqrt hMpos.le]
    rw [Finset.sum_congr rfl hstep, ← Finset.mul_sum]
    have hinner := innerSumSqrtBound M hM1
    have hLM : Real.log ((M : ℝ) + 2) ≤ L := by
      rw [hLdef]
      apply Real.log_le_log (by positivity)
      have : (M : ℝ) ≤ (N : ℝ) := by exact_mod_cast hMN
      linarith
    calc Real.sqrt (M : ℝ) *
          (∑ n ∈ Finset.Ico 1 M, (1 / Real.sqrt (n : ℝ)) / ((M : ℝ) - (n : ℝ)))
        ≤ Real.sqrt (M : ℝ) * (12 * Real.log ((M : ℝ) + 2) / Real.sqrt (M : ℝ)) :=
          mul_le_mul_of_nonneg_left hinner (Real.sqrt_nonneg _)
      _ = 12 * Real.log ((M : ℝ) + 2) := by
          rw [mul_comm, div_mul_cancel₀]
          exact ne_of_gt hsM
      _ ≤ 12 * L := by linarith
  calc (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
        (1 / Real.sqrt (m : ℝ)) * (1 / Real.sqrt (n : ℝ))
          * max (m : ℝ) (n : ℝ) / |(m : ℝ) - (n : ℝ)|)
      = 2 * ∑ M ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Ico 1 M,
          (1 / Real.sqrt (M : ℝ)) * (1 / Real.sqrt (n : ℝ))
            * ((M : ℝ) / ((M : ℝ) - (n : ℝ))) :=
        symm_eq_two_tri (fun n : ℕ => 1 / Real.sqrt (n : ℝ)) N
    _ ≤ 2 * ∑ _M ∈ Finset.Icc 1 N, 12 * L := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact Finset.sum_le_sum hterm
    _ = 24 * ((N : ℝ) * L) := by
        rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel]
        simp only [nsmul_eq_mul]
        ring
    _ = 24 * (N : ℝ) * Real.log ((N : ℝ) + 2) := by rw [hLdef]; ring

/-! ### The critical-line coefficients of `M_K` -/

/-- **Pointwise expansion of the critical-line Möbius polynomial.**  Writing
`b_n = μ(n) n^{-1/2}`, one has `M_K(1/2 + it) = Σ_{n ≤ K} b_n n^{-it}`. -/
private lemma MK_crit_eq_dirPolySum (K : ℕ) (t : ℝ) :
    MK K ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)
      = ∑ n ∈ Finset.Icc 1 K,
          ((ArithmeticFunction.moebius n : ℂ) * (n : ℂ) ^ (-(1 / 2 : ℂ)))
            * (n : ℂ) ^ (-((t : ℂ) * Complex.I)) := by
  rw [MK]
  refine Finset.sum_congr rfl ?_
  intro n hn
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hn0 : (n : ℂ) ≠ 0 := by
    simp only [Ne, Nat.cast_eq_zero]
    omega
  have hsplit : -((1 / 2 : ℂ) + (t : ℂ) * Complex.I)
      = (-(1 / 2 : ℂ)) + (-((t : ℂ) * Complex.I)) := by ring
  rw [hsplit, Complex.cpow_add _ _ hn0]
  ring

/-- The critical-line coefficient is at most `n^{-1/2}` in modulus. -/
private lemma norm_moebius_mul_cpow_half_le (n : ℕ) (hn : 1 ≤ n) :
    ‖(ArithmeticFunction.moebius n : ℂ) * (n : ℂ) ^ (-(1 / 2 : ℂ))‖ ≤ 1 / Real.sqrt (n : ℝ) := by
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos (by omega : 0 < n)]
  have hre : ((-(1 / 2 : ℂ)).re) = -(1 / 2 : ℝ) := by rw [Complex.neg_re]; norm_num
  rw [hre]
  have hmu : ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast, ← Int.cast_abs]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)
  have hrpow : (n : ℝ) ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt (n : ℝ) := by
    rw [show (-(1 / 2 : ℝ)) = -(1 * (1 / 2)) by norm_num, Real.rpow_neg (Nat.cast_nonneg n),
      Real.rpow_mul (Nat.cast_nonneg n)]
    simp [Real.sqrt_eq_rpow]
  calc ‖(ArithmeticFunction.moebius n : ℂ)‖ * (n : ℝ) ^ (-(1 / 2 : ℝ))
      ≤ 1 * (n : ℝ) ^ (-(1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_right hmu (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    _ = 1 / Real.sqrt (n : ℝ) := by rw [one_mul, hrpow]

/-- **Diagonal (main term) bound.**  `Σ_{n ≤ K} ‖b_n‖² ≤ 2 log(K+2)`: since `‖b_n‖ ≤ n^{-1/2}`,
the sum is at most the harmonic sum `Σ_{n ≤ K} 1/n ≤ 1 + log K`. -/
private lemma mkCoefNormSqSum_le (K : ℕ) (hK : 1 ≤ K) :
    (∑ n ∈ Finset.Icc 1 K,
        ‖(ArithmeticFunction.moebius n : ℂ) * (n : ℂ) ^ (-(1 / 2 : ℂ))‖ ^ 2)
      ≤ 2 * Real.log ((K : ℝ) + 2) := by
  have hterm : ∀ n ∈ Finset.Icc 1 K,
      ‖(ArithmeticFunction.moebius n : ℂ) * (n : ℂ) ^ (-(1 / 2 : ℂ))‖ ^ 2 ≤ (n : ℝ)⁻¹ := by
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    calc ‖(ArithmeticFunction.moebius n : ℂ) * (n : ℂ) ^ (-(1 / 2 : ℂ))‖ ^ 2
        ≤ (1 / Real.sqrt (n : ℝ)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_moebius_mul_cpow_half_le n hn1) 2
      _ = (n : ℝ)⁻¹ := by rw [div_pow, one_pow, Real.sq_sqrt hnpos.le, one_div]
  have hsum : (∑ n ∈ Finset.Icc 1 K,
        ‖(ArithmeticFunction.moebius n : ℂ) * (n : ℂ) ^ (-(1 / 2 : ℂ))‖ ^ 2)
      ≤ ∑ n ∈ Finset.Icc 1 K, (n : ℝ)⁻¹ := Finset.sum_le_sum hterm
  have hharm : (∑ n ∈ Finset.Icc 1 K, (n : ℝ)⁻¹) ≤ 1 + Real.log (K : ℝ) := by
    have h := harmonic_le_one_add_log K
    rw [harmonic_eq_sum_Icc] at h
    simpa using h
  have hlog : 1 + Real.log (K : ℝ) ≤ 2 * Real.log ((K : ℝ) + 2) := by
    have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (by omega : 0 < K)
    have hL1 : 1 ≤ Real.log ((K : ℝ) + 2) := by
      rw [Real.le_log_iff_exp_le (by linarith : (0 : ℝ) < (K : ℝ) + 2)]
      calc Real.exp 1 ≤ 3 := le_of_lt Real.exp_one_lt_three
        _ ≤ (K : ℝ) + 2 := by
            have : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
            linarith
    have hlogK : Real.log (K : ℝ) ≤ Real.log ((K : ℝ) + 2) :=
      Real.log_le_log hKpos (by linarith)
    linarith
  linarith

/-- **Mean square of the truncated Möbius polynomial on the critical line.**
There is an absolute `C > 0` with
`∫_0^T ‖M_K(1/2 + it)‖² dt ≤ C (T + K log(K+2)) log(K+2)` for all `K, T ≥ 1`. -/
theorem MKIntervalMeanSquare : ∃ C : ℝ, 0 < C ∧ ∀ (K : ℕ) (T : ℝ), 1 ≤ K → 1 ≤ T →
    (∫ t in (0 : ℝ)..T, ‖Work.ZeroDensity.Ingham.MK K ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2)
      ≤ C * ((T + (K : ℝ) * Real.log ((K : ℝ) + 2)) * Real.log ((K : ℝ) + 2)) := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := dirPolyIntervalMeanValueBound
  obtain ⟨C₂, hC₂pos, hC₂⟩ := kernBound_local
  refine ⟨2 + C₁ * C₂, by positivity, ?_⟩
  intro K T hK hT
  have hT0 : (0 : ℝ) ≤ T := by linarith
  set L : ℝ := Real.log ((K : ℝ) + 2) with hLdef
  have hL1 : 1 ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le (by positivity : (0 : ℝ) < (K : ℝ) + 2)]
    calc Real.exp 1 ≤ 3 := le_of_lt Real.exp_one_lt_three
      _ ≤ (K : ℝ) + 2 := by
          have : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
          linarith
  set b : ℕ → ℂ := fun n => (ArithmeticFunction.moebius n : ℂ) * (n : ℂ) ^ (-(1 / 2 : ℂ)) with hbdef
  have hnormb : ∀ n : ℕ, 1 ≤ n → ‖b n‖ ≤ 1 / Real.sqrt (n : ℝ) :=
    fun n hn => norm_moebius_mul_cpow_half_le n hn
  have hIntEq : (∫ t in (0 : ℝ)..T, ‖MK K ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2)
      = ∫ t in (0 : ℝ)..T, ‖∑ n ∈ Finset.Icc 1 K, b n * (n : ℂ) ^ (-((t : ℂ) * Complex.I))‖ ^ 2 := by
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only
    rw [MK_crit_eq_dirPolySum K t]
  have hMVT := hC₁ b K 0 T hT0
  have hbnd : (∫ t in (0 : ℝ)..T, ‖∑ n ∈ Finset.Icc 1 K, b n * (n : ℂ) ^ (-((t : ℂ) * Complex.I))‖ ^ 2)
      ≤ T * (∑ n ∈ Finset.Icc 1 K, ‖b n‖ ^ 2)
        + C₁ * (∑ m ∈ Finset.Icc 1 K, ∑ n ∈ Finset.Icc 1 K,
            ‖b m‖ * ‖b n‖ * max (m : ℝ) (n : ℝ) / |(m : ℝ) - (n : ℝ)|) := by
    have h2 := (abs_le.mp hMVT).2
    simp only [sub_zero] at h2
    linarith
  have hS : (∑ n ∈ Finset.Icc 1 K, ‖b n‖ ^ 2) ≤ 2 * L := by
    rw [hLdef]
    exact mkCoefNormSqSum_le K hK
  have hKr1 : (∑ m ∈ Finset.Icc 1 K, ∑ n ∈ Finset.Icc 1 K,
        ‖b m‖ * ‖b n‖ * max (m : ℝ) (n : ℝ) / |(m : ℝ) - (n : ℝ)|)
      ≤ (∑ m ∈ Finset.Icc 1 K, ∑ n ∈ Finset.Icc 1 K,
        (1 / Real.sqrt (m : ℝ)) * (1 / Real.sqrt (n : ℝ))
          * max (m : ℝ) (n : ℝ) / |(m : ℝ) - (n : ℝ)|) := by
    apply Finset.sum_le_sum
    intro m hm
    apply Finset.sum_le_sum
    intro n hn
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hmb := hnormb m hm1
    have hnb := hnormb n hn1
    have hmaxnn : 0 ≤ max (m : ℝ) (n : ℝ) := le_trans (Nat.cast_nonneg n) (le_max_right _ _)
    have hstep : ‖b m‖ * ‖b n‖ * max (m : ℝ) (n : ℝ)
        ≤ (1 / Real.sqrt (m : ℝ)) * (1 / Real.sqrt (n : ℝ)) * max (m : ℝ) (n : ℝ) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul hmb hnb (norm_nonneg _) (by positivity)) hmaxnn
    exact div_le_div_of_nonneg_right hstep (abs_nonneg _)
  have hKr2 : (∑ m ∈ Finset.Icc 1 K, ∑ n ∈ Finset.Icc 1 K,
        (1 / Real.sqrt (m : ℝ)) * (1 / Real.sqrt (n : ℝ))
          * max (m : ℝ) (n : ℝ) / |(m : ℝ) - (n : ℝ)|) ≤ C₂ * (K : ℝ) * L := by
    rw [hLdef]
    exact hC₂ K hK
  have hKr : (∑ m ∈ Finset.Icc 1 K, ∑ n ∈ Finset.Icc 1 K,
        ‖b m‖ * ‖b n‖ * max (m : ℝ) (n : ℝ) / |(m : ℝ) - (n : ℝ)|) ≤ C₂ * (K : ℝ) * L :=
    le_trans hKr1 hKr2
  have hA : T * (∑ n ∈ Finset.Icc 1 K, ‖b n‖ ^ 2) ≤ T * (2 * L) :=
    mul_le_mul_of_nonneg_left hS hT0
  have hB : C₁ * (∑ m ∈ Finset.Icc 1 K, ∑ n ∈ Finset.Icc 1 K,
        ‖b m‖ * ‖b n‖ * max (m : ℝ) (n : ℝ) / |(m : ℝ) - (n : ℝ)|) ≤ C₁ * (C₂ * (K : ℝ) * L) :=
    mul_le_mul_of_nonneg_left hKr hC₁pos.le
  have hmain : (∫ t in (0 : ℝ)..T, ‖∑ n ∈ Finset.Icc 1 K, b n * (n : ℂ) ^ (-((t : ℂ) * Complex.I))‖ ^ 2)
      ≤ T * (2 * L) + C₁ * (C₂ * (K : ℝ) * L) := le_trans hbnd (add_le_add hA hB)
  have hfinalB : T * (2 * L) + C₁ * (C₂ * (K : ℝ) * L)
      ≤ (2 + C₁ * C₂) * ((T + (K : ℝ) * L) * L) := by
    have hc : 0 ≤ C₁ * C₂ := by positivity
    have hKL : 0 ≤ (K : ℝ) * L := by positivity
    have hKL2 : (K : ℝ) * L ≤ (K : ℝ) * L * L := by nlinarith [hKL, hL1]
    have h1 : 0 ≤ 2 * ((K : ℝ) * L * L) := by positivity
    have h2 : 0 ≤ C₁ * C₂ * (T * L) := by positivity
    have h3 : 0 ≤ C₁ * C₂ * ((K : ℝ) * L * (L - 1)) := by positivity
    have hdiff : (2 + C₁ * C₂) * ((T + (K : ℝ) * L) * L)
        - (T * (2 * L) + C₁ * (C₂ * (K : ℝ) * L))
        = 2 * ((K : ℝ) * L * L) + C₁ * C₂ * (T * L) + C₁ * C₂ * ((K : ℝ) * L * (L - 1)) := by
      ring
    linarith
  rw [hIntEq]
  exact le_trans hmain hfinalB

end Work.ZeroDensity.Ingham
