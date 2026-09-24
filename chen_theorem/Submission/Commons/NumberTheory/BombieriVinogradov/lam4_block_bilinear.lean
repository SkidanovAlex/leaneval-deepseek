import Mathlib
import Submission.Commons.NumberTheory.Goldbach.sum_vaughan_log_part

namespace Commons.NumberTheory.BombieriVinogradov

open scoped BigOperators

/-- The divisors of `n ≥ 1` satisfying `Q` (where `Q` implies `≤ U`) are exactly the
elements of `[1,U]` that divide `n` and satisfy `Q`. -/
private lemma sum_divisors_filter_eq_Icc (n U : ℕ) (hn : 1 ≤ n) {Q : ℕ → Prop} [DecidablePred Q]
    (hQ : ∀ m, Q m → m ≤ U) (f : ℕ → ℂ) :
    ∑ m ∈ n.divisors.filter Q, f m
      = ∑ m ∈ (Finset.Icc 1 U).filter (fun m => m ∣ n), (if Q m then f m else 0) := by
  have hset : n.divisors.filter Q = (Finset.Icc 1 U).filter (fun m => m ∣ n ∧ Q m) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hmdvd, hn0⟩, hQm⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hmdvd (by omega), hQ m hQm⟩, hmdvd, hQm⟩
    · rintro ⟨⟨hm1, hmU⟩, hmdvd, hQm⟩
      exact ⟨⟨hmdvd, by omega⟩, hQm⟩
  rw [hset, ← Finset.filter_filter]
  exact Finset.sum_filter Q f

/-- For `m > 0`, the `k` in `[1, x/M]` with `m*k ≤ y` are exactly `[1, y/m]`, provided
`y/m ≤ x/M`. -/
private lemma filter_Icc_mul_le {m x y M : ℕ} (hm : 0 < m) (hyx : y / m ≤ x / M) :
    (Finset.Icc 1 (x / M)).filter (fun k => m * k ≤ y) = Finset.Icc 1 (y / m) := by
  ext k
  rw [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hk1, _⟩, hky⟩
    exact ⟨hk1, (Nat.le_div_iff_mul_le hm).mpr (by simpa [mul_comm] using hky)⟩
  · rintro ⟨hk1, hky⟩
    exact ⟨⟨hk1, le_trans hky hyx⟩, by simpa [mul_comm] using (Nat.le_div_iff_mul_le hm).mp hky⟩

/-- For `M ≥ 1`, `y ≤ x` and `M < m`, one has `y/m ≤ x/M`. -/
private lemma div_div_le_div_div {M x y m : ℕ} (hM : 1 ≤ M) (hy : y ≤ x) (hm : M < m) :
    y / m ≤ x / M := by
  calc y / m ≤ x / m := Nat.div_le_div_right hy
    _ ≤ x / M := Nat.div_le_div_left (by omega) (by omega)

lemma lam4_block_bilinear (T M x y q : ℕ) (hM : 1 ≤ M) (hMT : T ≤ M) (hMx : M ≤ x) (hy : y ≤ x)
    (χ : DirichletCharacter ℂ q) :
    (∑ n ∈ Finset.Icc 1 y,
        (∑ m ∈ n.divisors.filter (fun m => M < m ∧ m ≤ 2 * M ∧ T < n / m),
            ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ) *
              (∑ d ∈ (n / m).divisors.filter (fun d => d ≤ T),
                ((ArithmeticFunction.moebius d : ℤ) : ℂ)))
        * χ (n : ZMod q))
      = ∑ m ∈ Finset.Icc 1 (2 * M), ∑ k ∈ Finset.Icc 1 (x / M),
          (if m * k ≤ y then (1 : ℂ) else 0)
            * (if T < m ∧ M < m ∧ m ≤ 2 * M then
                ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ) else 0)
            * (if T < k then
                (∑ d ∈ k.divisors.filter (fun d => d ≤ T),
                  ((ArithmeticFunction.moebius d : ℤ) : ℂ)) else 0)
            * χ ((m * k : ℕ) : ZMod q) := by
  let B : ℕ → ℂ := fun k =>
    ∑ d ∈ k.divisors.filter (fun d => d ≤ T), ((ArithmeticFunction.moebius d : ℤ) : ℂ)
  change (∑ n ∈ Finset.Icc 1 y,
        (∑ m ∈ n.divisors.filter (fun m => M < m ∧ m ≤ 2 * M ∧ T < n / m),
            ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ) * B (n / m))
        * χ (n : ZMod q))
      = ∑ m ∈ Finset.Icc 1 (2 * M), ∑ k ∈ Finset.Icc 1 (x / M),
          (if m * k ≤ y then (1 : ℂ) else 0)
            * (if T < m ∧ M < m ∧ m ≤ 2 * M then
                ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ) else 0)
            * (if T < k then B k else 0)
            * χ ((m * k : ℕ) : ZMod q)
  -- Step 1: rewrite the divisor sum inside each `n`
  have hL1 : (∑ n ∈ Finset.Icc 1 y,
        (∑ m ∈ n.divisors.filter (fun m => M < m ∧ m ≤ 2 * M ∧ T < n / m),
            ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ) * B (n / m))
        * χ (n : ZMod q))
      = ∑ n ∈ Finset.Icc 1 y, ∑ m ∈ (Finset.Icc 1 (2 * M)).filter (fun m => m ∣ n),
          (if M < m ∧ m ≤ 2 * M ∧ T < n / m then
              ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ) * B (n / m) else 0)
            * χ (n : ZMod q) := by
    refine Finset.sum_congr rfl (fun n hn => ?_)
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    rw [Finset.sum_mul]
    rw [sum_divisors_filter_eq_Icc n (2 * M) hn1
          (Q := fun m => M < m ∧ m ≤ 2 * M ∧ T < n / m)
          (hQ := fun m hm => hm.2.1)
          (f := fun m => ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ) * B (n / m) * χ (n : ZMod q))]
    refine Finset.sum_congr rfl (fun m hm => ?_)
    by_cases h : M < m ∧ m ≤ 2 * M ∧ T < n / m <;> simp [h]
  -- Step 2: swap the order of summation
  have hL2 : (∑ n ∈ Finset.Icc 1 y, ∑ m ∈ (Finset.Icc 1 (2 * M)).filter (fun m => m ∣ n),
          (if M < m ∧ m ≤ 2 * M ∧ T < n / m then
              ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ) * B (n / m) else 0)
            * χ (n : ZMod q))
      = ∑ m ∈ Finset.Icc 1 (2 * M), ∑ k ∈ Finset.Icc 1 (y / m),
          (if M < m ∧ m ≤ 2 * M ∧ T < (m * k) / m then
              ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ) * B ((m * k) / m) else 0)
            * χ ((m * k : ℕ) : ZMod q) :=
    Commons.NumberTheory.Goldbach.sum_Icc_filter_dvd_swap (M := y) (U := 2 * M)
      (g := fun n m => (if M < m ∧ m ≤ 2 * M ∧ T < n / m then
              ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ) * B (n / m) else 0)
            * χ (n : ZMod q))
  -- Step 3: simplify `(m*k)/m = k`
  have hL3 : (∑ m ∈ Finset.Icc 1 (2 * M), ∑ k ∈ Finset.Icc 1 (y / m),
          (if M < m ∧ m ≤ 2 * M ∧ T < (m * k) / m then
              ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ) * B ((m * k) / m) else 0)
            * χ ((m * k : ℕ) : ZMod q))
      = ∑ m ∈ Finset.Icc 1 (2 * M), ∑ k ∈ Finset.Icc 1 (y / m),
          (if M < m ∧ m ≤ 2 * M ∧ T < k then
              ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ) * B k else 0)
            * χ ((m * k : ℕ) : ZMod q) := by
    refine Finset.sum_congr rfl (fun m hm => ?_)
    have hm0 : 0 < m := by have := (Finset.mem_Icc.mp hm).1; omega
    refine Finset.sum_congr rfl (fun k hk => ?_)
    rw [Nat.mul_div_right k hm0]
  -- Step 4: the RHS equals the same reduced form
  have hR : (∑ m ∈ Finset.Icc 1 (2 * M), ∑ k ∈ Finset.Icc 1 (x / M),
          (if m * k ≤ y then (1 : ℂ) else 0)
            * (if T < m ∧ M < m ∧ m ≤ 2 * M then
                ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ) else 0)
            * (if T < k then B k else 0)
            * χ ((m * k : ℕ) : ZMod q))
      = ∑ m ∈ Finset.Icc 1 (2 * M), ∑ k ∈ Finset.Icc 1 (y / m),
          (if M < m ∧ m ≤ 2 * M ∧ T < k then
              ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ) * B k else 0)
            * χ ((m * k : ℕ) : ZMod q) := by
    refine Finset.sum_congr rfl (fun m hm => ?_)
    by_cases hMltm : M < m
    · -- case M < m
      obtain ⟨hm1, hm2⟩ := Finset.mem_Icc.mp hm
      have hm0 : 0 < m := by omega
      have hTm : T < m := lt_of_le_of_lt hMT hMltm
      have hyx : y / m ≤ x / M := div_div_le_div_div hM hy hMltm
      have hmiddle : (if T < m ∧ M < m ∧ m ≤ 2 * M then
              ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ) else 0)
          = ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ) := if_pos ⟨hTm, hMltm, hm2⟩
      have h1a : (∑ k ∈ Finset.Icc 1 (x / M),
            (if m * k ≤ y then (1 : ℂ) else 0)
              * (if T < m ∧ M < m ∧ m ≤ 2 * M then
                  ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ) else 0)
              * (if T < k then B k else 0)
              * χ ((m * k : ℕ) : ZMod q))
          = ∑ k ∈ Finset.Icc 1 (x / M),
              (if m * k ≤ y then
                  ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ) * (if T < k then B k else 0)
                    * χ ((m * k : ℕ) : ZMod q) else 0) := by
        refine Finset.sum_congr rfl (fun k hk => ?_)
        rw [hmiddle]
        by_cases h : m * k ≤ y <;> simp [h]
      have h1b : (∑ k ∈ Finset.Icc 1 (x / M),
              (if m * k ≤ y then
                  ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ) * (if T < k then B k else 0)
                    * χ ((m * k : ℕ) : ZMod q) else 0))
          = ∑ k ∈ Finset.Icc 1 (y / m),
              ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ) * (if T < k then B k else 0)
                * χ ((m * k : ℕ) : ZMod q) := by
        rw [← Finset.sum_filter, filter_Icc_mul_le hm0 hyx]
      have h2 : (∑ k ∈ Finset.Icc 1 (y / m),
              (if M < m ∧ m ≤ 2 * M ∧ T < k then
                  ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ) * B k else 0)
                * χ ((m * k : ℕ) : ZMod q))
          = ∑ k ∈ Finset.Icc 1 (y / m),
              ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ) * (if T < k then B k else 0)
                * χ ((m * k : ℕ) : ZMod q) := by
        refine Finset.sum_congr rfl (fun k hk => ?_)
        have hif : (if M < m ∧ m ≤ 2 * M ∧ T < k then
                  ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ) * B k else 0)
              = ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ) * (if T < k then B k else 0) := by
          by_cases h : T < k
          · rw [if_pos ⟨hMltm, hm2, h⟩, if_pos h]
          · rw [if_neg (fun hc => h hc.2.2), if_neg h, mul_zero]
        rw [hif]
      rw [h1a, h1b, h2]
    · -- case ¬ M < m : both inner sums vanish
      have hLz : (∑ k ∈ Finset.Icc 1 (x / M),
            (if m * k ≤ y then (1 : ℂ) else 0)
              * (if T < m ∧ M < m ∧ m ≤ 2 * M then
                  ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ) else 0)
              * (if T < k then B k else 0)
              * χ ((m * k : ℕ) : ZMod q)) = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        simp [hMltm]
      have hRz : (∑ k ∈ Finset.Icc 1 (y / m),
              (if M < m ∧ m ≤ 2 * M ∧ T < k then
                  ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ) * B k else 0)
                * χ ((m * k : ℕ) : ZMod q)) = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        simp [hMltm]
      rw [hLz, hRz]
  rw [hL1, hL2, hL3]
  exact hR.symm

end Commons.NumberTheory.BombieriVinogradov
