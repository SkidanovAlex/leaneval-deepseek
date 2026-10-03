import Mathlib
import Submission.Work.FIArea6Road.DivisorWindowDefs

namespace Work.FIArea6Road

open Finset
open scoped BigOperators

/-- `D2` is monotone. -/
private lemma D2_mono {p q : ℕ} (h : p ≤ q) : D2 p ≤ D2 q := by
  unfold D2
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc le_rfl h)
    (fun i _ _ => tauR_nonneg i)

/-- The difference of two partial sums of `τ` is the sum over the corresponding interval. -/
private lemma D2_sub_split (p q : ℕ) (h : p ≤ q) :
    D2 q - D2 p = ∑ k ∈ Finset.Icc (p + 1) q, tauR k := by
  have hunion : Finset.Icc 1 q = Finset.Icc 1 p ∪ Finset.Icc (p + 1) q := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_union]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases hk : k ≤ p
      · exact Or.inl ⟨h1, hk⟩
      · exact Or.inr ⟨by omega, h2⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨h1, le_trans h2 h⟩
      · exact ⟨by omega, h2⟩
  have hdisj : Disjoint (Finset.Icc 1 p) (Finset.Icc (p + 1) q) := by
    rw [Finset.disjoint_left]
    intro k hk1 hk2
    simp only [Finset.mem_Icc] at hk1 hk2
    omega
  have hD2q : D2 q = D2 p + ∑ k ∈ Finset.Icc (p + 1) q, tauR k := by
    unfold D2
    rw [hunion, Finset.sum_union hdisj]
  linarith

/-- For `a ≥ 1`, the difference `D2(M/a) - D2((N-1)/a)` counts the integers `b` with
`N ≤ a*b ≤ M`, weighted by `τ(b)`. -/
private lemma D2_window_diff (N M a : ℕ) (hNM : N ≤ M) (ha : 1 ≤ a) :
    (∑ b ∈ Finset.Icc 1 M, (if N ≤ a * b ∧ a * b ≤ M then tauR b else 0))
      = D2 (M / a) - D2 ((N - 1) / a) := by
  have ha0 : 0 < a := by omega
  have hle : (N - 1) / a ≤ M / a := Nat.div_le_div_right (by omega : N - 1 ≤ M)
  have hfilter : (Finset.Icc 1 M).filter (fun b => N ≤ a * b ∧ a * b ≤ M)
      = Finset.Icc ((N - 1) / a + 1) (M / a) := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hb1, hbM⟩, hNa, haM⟩
      refine ⟨?_, ?_⟩
      · have hlt : (N - 1) / a < b := by
          rw [Nat.div_lt_iff_lt_mul ha0, Nat.mul_comm b a]
          have hab : 0 < a * b := Nat.mul_pos ha0 (by omega)
          omega
        omega
      · rw [Nat.le_div_iff_mul_le ha0, Nat.mul_comm b a]
        omega
    · rintro ⟨hb1, hbM⟩
      have hlt : (N - 1) / a < b := by omega
      have hdiv : N - 1 < b * a := (Nat.div_lt_iff_lt_mul ha0).mp hlt
      have hmul : b * a ≤ M := (Nat.le_div_iff_mul_le ha0).mp hbM
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
      · exact le_trans (Nat.succ_le_succ (Nat.zero_le _)) hb1
      · have := Nat.div_le_self M a; omega
      · rw [Nat.mul_comm b a] at hdiv; omega
      · rw [Nat.mul_comm b a] at hmul; omega
  rw [D2_sub_split _ _ hle, ← Finset.sum_filter, hfilter]

/-- Swapping the order of the two factors inside the defining condition. -/
private lemma mul_cond_swap (N M a c : ℕ) :
    (N ≤ c * a ∧ c * a ≤ M) ↔ (N ≤ a * c ∧ a * c ≤ M) := by
  rw [Nat.mul_comm c a]

/-- The "swapped" form of `D2_window_diff`: the summation runs over the *first* factor. -/
private lemma window_diff_swapped (N M a : ℕ) (hNM : N ≤ M) (ha : 1 ≤ a) :
    (∑ c ∈ Finset.Icc 1 M, (if N ≤ c * a ∧ c * a ≤ M then tauR c else 0))
      = D2 (M / a) - D2 ((N - 1) / a) := by
  rw [← D2_window_diff N M a hNM ha]
  apply Finset.sum_congr rfl
  intro c _
  by_cases h : N ≤ c * a ∧ c * a ≤ M
  · rw [if_pos h, if_pos ((mul_cond_swap N M a c).mp h)]
  · rw [if_neg h, if_neg (fun hh => h ((mul_cond_swap N M a c).mpr hh))]

/-- `∑_{n ∈ [N,M]} d4 n` is the sum of `τ(a)τ(b)` over all ordered pairs `(a,b)` of positive
integers with `N ≤ a b ≤ M`, reindexed as a rectangular double sum over `[1,M]²`. -/
private lemma d4_window_double_sum (N M : ℕ) :
    (∑ n ∈ Finset.Icc N M, d4 n)
      = ∑ a ∈ Finset.Icc 1 M, ∑ b ∈ Finset.Icc 1 M,
          (if N ≤ a * b ∧ a * b ≤ M then tauR a * tauR b else 0) := by
  have hL : (∑ n ∈ Finset.Icc N M, d4 n)
      = ∑ n ∈ Finset.Icc N M, ∑ p ∈ n.divisorsAntidiagonal, tauR p.1 * tauR p.2 := by
    apply Finset.sum_congr rfl
    intro n _
    rw [d4, ← Nat.sum_divisorsAntidiagonal (fun a b => tauR a * tauR b)]
  rw [hL, Finset.sum_sigma']
  have hT : (∑ a ∈ Finset.Icc 1 M, ∑ b ∈ Finset.Icc 1 M,
        (if N ≤ a * b ∧ a * b ≤ M then tauR a * tauR b else 0))
      = ∑ p ∈ ((Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M)).filter
            (fun p => N ≤ p.1 * p.2 ∧ p.1 * p.2 ≤ M), tauR p.1 * tauR p.2 := by
    rw [Finset.sum_filter, Finset.sum_product]
  rw [hT]
  refine Finset.sum_bij (fun x _ => x.2) ?_ ?_ ?_ ?_
  · intro x hx
    have hs := Finset.mem_sigma.mp hx
    obtain ⟨hp1, hpne⟩ := Nat.mem_divisorsAntidiagonal.mp hs.2
    rw [Finset.mem_Icc] at hs
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
    have hpos1 : 1 ≤ x.2.1 := by
      rcases Nat.eq_zero_or_pos x.2.1 with h | h
      · rw [h, zero_mul] at hp1; exact absurd hp1.symm hpne
      · exact h
    have hpos2 : 1 ≤ x.2.2 := by
      rcases Nat.eq_zero_or_pos x.2.2 with h | h
      · rw [h, mul_zero] at hp1; exact absurd hp1.symm hpne
      · exact h
    refine ⟨⟨⟨hpos1, ?_⟩, ⟨hpos2, ?_⟩⟩, ?_, ?_⟩
    · nlinarith [hp1, hpos2, hs.2]
    · nlinarith [hp1, hpos1, hs.2]
    · nlinarith [hp1, hs.1]
    · nlinarith [hp1, hs.2]
  · intro x1 hx1 x2 hx2 heq
    have hs1 := Finset.mem_sigma.mp hx1
    have hs2 := Finset.mem_sigma.mp hx2
    have e1 : x1.2.1 * x1.2.2 = x1.1 := (Nat.mem_divisorsAntidiagonal.mp hs1.2).1
    have e2 : x2.2.1 * x2.2.2 = x2.1 := (Nat.mem_divisorsAntidiagonal.mp hs2.2).1
    have hnn : x1.1 = x2.1 := by rw [← e1, ← e2, heq]
    exact Sigma.ext hnn (heq_of_eq heq)
  · rintro ⟨a, b⟩ hb
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hb
    obtain ⟨⟨⟨ha1, haM⟩, ⟨hb1, _⟩⟩, hNab, habM⟩ := hb
    refine ⟨⟨a * b, (a, b)⟩, ?_, rfl⟩
    rw [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisorsAntidiagonal]
    exact ⟨⟨hNab, habM⟩, ⟨rfl, Nat.mul_ne_zero (by omega) (by omega)⟩⟩
  · rintro ⟨n, p⟩ _; rfl

/-- The "large divisors" `a > U` contribute at most the whole window sum over `b ≤ M/U`. -/
private lemma window_second_le (N M U : ℕ) (hNM : N ≤ M) (hU : 1 ≤ U) :
    (∑ a ∈ (Finset.Icc 1 M).filter (fun a => U < a),
        tauR a * (D2 (M / a) - D2 ((N - 1) / a)))
      ≤ ∑ b ∈ Finset.Icc 1 (M / U), tauR b * (D2 (M / b) - D2 ((N - 1) / b)) := by
  set K : Finset ℕ := (Finset.Icc 1 M).filter (fun a => U < a) with hK
  have hKmem : ∀ a ∈ K, 1 ≤ a ∧ U < a := by
    intro a ha
    rw [hK, Finset.mem_filter, Finset.mem_Icc] at ha
    exact ⟨ha.1.1, ha.2⟩
  have hstep1 : (∑ a ∈ K, tauR a * (D2 (M / a) - D2 ((N - 1) / a)))
      = ∑ c ∈ Finset.Icc 1 M, ∑ a ∈ K,
          (if N ≤ c * a ∧ c * a ≤ M then tauR a * tauR c else 0) := by
    have hpoint : ∀ a ∈ K, tauR a * (D2 (M / a) - D2 ((N - 1) / a))
        = ∑ c ∈ Finset.Icc 1 M,
            (if N ≤ c * a ∧ c * a ≤ M then tauR a * tauR c else 0) := by
      intro a ha
      rw [← window_diff_swapped N M a hNM (hKmem a ha).1, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c _
      rw [mul_ite, mul_zero]
    rw [Finset.sum_congr rfl hpoint, Finset.sum_comm]
  rw [hstep1]
  have hsub : Finset.Icc 1 (M / U) ⊆ Finset.Icc 1 M :=
    Finset.Icc_subset_Icc le_rfl (Nat.div_le_self M U)
  have hzero : ∀ c ∈ Finset.Icc 1 M, c ∉ Finset.Icc 1 (M / U) →
      (∑ a ∈ K, (if N ≤ c * a ∧ c * a ≤ M then tauR a * tauR c else 0)) = 0 := by
    intro c hc hc'
    apply Finset.sum_eq_zero
    intro a ha
    rw [if_neg]
    intro hcon
    have hc1 : 1 ≤ c := (Finset.mem_Icc.mp hc).1
    have haU : U + 1 ≤ a := by have := (hKmem a ha).2; omega
    have ha0 : 0 < a := by omega
    have hca : c ≤ M / a := (Nat.le_div_iff_mul_le ha0).mpr hcon.2
    have h1 : M / a ≤ M / (U + 1) := Nat.div_le_div_left haU (by omega)
    have h2 : M / (U + 1) ≤ M / U := Nat.div_le_div_left (by omega) (by omega)
    exact hc' (Finset.mem_Icc.mpr ⟨hc1, le_trans hca (le_trans h1 h2)⟩)
  calc ∑ c ∈ Finset.Icc 1 M, ∑ a ∈ K,
          (if N ≤ c * a ∧ c * a ≤ M then tauR a * tauR c else 0)
      = ∑ c ∈ Finset.Icc 1 (M / U), ∑ a ∈ K,
          (if N ≤ c * a ∧ c * a ≤ M then tauR a * tauR c else 0) :=
        (Finset.sum_subset hsub hzero).symm
    _ ≤ ∑ c ∈ Finset.Icc 1 (M / U), tauR c * (D2 (M / c) - D2 ((N - 1) / c)) := by
        apply Finset.sum_le_sum
        intro c hc
        have hc1 : 1 ≤ c := (Finset.mem_Icc.mp hc).1
        calc ∑ a ∈ K, (if N ≤ c * a ∧ c * a ≤ M then tauR a * tauR c else 0)
            ≤ ∑ a ∈ Finset.Icc 1 M,
                (if N ≤ c * a ∧ c * a ≤ M then tauR a * tauR c else 0) := by
              apply Finset.sum_le_sum_of_subset_of_nonneg
              · rw [hK]; exact Finset.filter_subset _ _
              · intro a _ _; split_ifs with h
                · exact mul_nonneg (tauR_nonneg a) (tauR_nonneg c)
                · exact le_refl 0
          _ = tauR c * (∑ a ∈ Finset.Icc 1 M,
                (if N ≤ c * a ∧ c * a ≤ M then tauR a else 0)) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro a _
              rw [mul_ite, mul_zero, mul_comm (tauR a) (tauR c)]
          _ = tauR c * (D2 (M / c) - D2 ((N - 1) / c)) := by
              rw [D2_window_diff N M c hNM hc1]

/-- The "small divisors" `a ≤ U` contribute at most the window sum over `e ≤ U`. -/
private lemma window_first_le (N M U : ℕ) (hNM : N ≤ M) (_hU : 1 ≤ U) :
    (∑ a ∈ (Finset.Icc 1 M).filter (fun a => ¬ U < a),
        tauR a * (D2 (M / a) - D2 ((N - 1) / a)))
      ≤ ∑ e ∈ Finset.Icc 1 U, tauR e * (D2 (M / e) - D2 ((N - 1) / e)) := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro a ha
    rw [Finset.mem_filter, Finset.mem_Icc] at ha
    rw [Finset.mem_Icc]
    exact ⟨ha.1.1, by omega⟩
  · intro a ha _
    rw [Finset.mem_Icc] at ha
    have hle : (N - 1) / a ≤ M / a := Nat.div_le_div_right (by omega : N - 1 ≤ M)
    exact mul_nonneg (tauR_nonneg a) (sub_nonneg.mpr (D2_mono hle))

/-- Main lemma. -/
theorem d4_window_decomp (N M U : ℕ) (hN : 1 ≤ N) (hNM : N ≤ M) (hU : 1 ≤ U) :
    (∑ n ∈ Finset.Icc N M, d4 n)
      ≤ (∑ e ∈ Finset.Icc 1 U, tauR e * (D2 (M / e) - D2 ((N - 1) / e)))
        + ∑ f ∈ Finset.Icc 1 (M / U), tauR f * (D2 (M / f) - D2 ((N - 1) / f)) := by
  rw [d4_window_double_sum N M]
  have hweak : (∑ a ∈ Finset.Icc 1 M, ∑ b ∈ Finset.Icc 1 M,
        (if N ≤ a * b ∧ a * b ≤ M then tauR a * tauR b else 0))
      = ∑ a ∈ Finset.Icc 1 M, tauR a * (D2 (M / a) - D2 ((N - 1) / a)) := by
    apply Finset.sum_congr rfl
    intro a ha
    have ha1 : 1 ≤ a := (Finset.mem_Icc.mp ha).1
    rw [← D2_window_diff N M a hNM ha1, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    rw [mul_ite, mul_zero]
  rw [hweak, ← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 M) (fun a => U < a)
        (fun a => tauR a * (D2 (M / a) - D2 ((N - 1) / a)))]
  have h1 := window_first_le N M U hNM hU
  have h2 := window_second_le N M U hNM hU
  linarith

end Work.FIArea6Road
