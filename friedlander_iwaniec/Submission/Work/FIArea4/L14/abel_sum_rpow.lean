import Mathlib

namespace Work.FIArea4.L14

open Finset

/-- Reindexing a sum over `Icc 1 N` as a sum over `range N`. -/
lemma sum_Icc_one_eq_sum_range (a : ℕ → ℝ) (N : ℕ) :
    ∑ q ∈ Finset.Icc 1 N, a q = ∑ i ∈ Finset.range N, a (i + 1) := by
  rw [← Finset.Ico_add_one_right_eq_Icc (1 : ℕ) N, Finset.sum_Ico_eq_sum_range]
  simp [Nat.add_comm]

/-- The elementary inequality `q * (q^(β-1) - (q+1)^(β-1)) ≤ (q+1)^(β-1)` for `β > 0`.

This is the algebra identity `q * (q+1)^(β-1) = (q+1)^β - (q+1)^(β-1)` together with
`q^β ≤ (q+1)^β`. -/
lemma pow_diff_mul_le (β : ℝ) (hβ0 : 0 < β) (q : ℕ) :
    (q : ℝ) * ((q : ℝ) ^ (β - 1) - ((q : ℝ) + 1) ^ (β - 1)) ≤ ((q : ℝ) + 1) ^ (β - 1) := by
  have hx : (0 : ℝ) < (q : ℝ) + 1 := by positivity
  have hid : (q : ℝ) * (((q : ℝ) + 1) ^ (β - 1)) =
      ((q : ℝ) + 1) ^ β - ((q : ℝ) + 1) ^ (β - 1) := by
    have h : ((q : ℝ) + 1) ^ β = ((q : ℝ) + 1) ^ (β - 1) * ((q : ℝ) + 1) := by
      conv_lhs => rw [show β = (β - 1) + 1 by ring]
      rw [Real.rpow_add hx, Real.rpow_one]
    rw [h]; ring
  have hid2 : (q : ℝ) * (q : ℝ) ^ (β - 1) = (q : ℝ) ^ β := by
    rcases Nat.eq_zero_or_pos q with hq | hq
    · subst hq; simp [Real.zero_rpow hβ0.ne']
    · have hq' : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
      have h : (q : ℝ) ^ β = (q : ℝ) ^ (β - 1) * (q : ℝ) := by
        conv_lhs => rw [show β = (β - 1) + 1 by ring]
        rw [Real.rpow_add hq', Real.rpow_one]
      rw [h]; ring
  have hle : (q : ℝ) ^ β ≤ ((q : ℝ) + 1) ^ β :=
    Real.rpow_le_rpow (by positivity) (by linarith) hβ0.le
  calc (q : ℝ) * ((q : ℝ) ^ (β - 1) - ((q : ℝ) + 1) ^ (β - 1))
      = (q : ℝ) * (q : ℝ) ^ (β - 1) - (q : ℝ) * ((q : ℝ) + 1) ^ (β - 1) := by ring
    _ = (q : ℝ) ^ β - (((q : ℝ) + 1) ^ β - ((q : ℝ) + 1) ^ (β - 1)) := by rw [hid2, hid]
    _ ≤ ((q : ℝ) + 1) ^ (β - 1) := by linarith

/-- Sum of the power weights, by comparison with an integral:
`∑_{i<n} (i+2)^(β-1) ≤ (n+1)^β / β` for `0 < β ≤ 1`. -/
lemma rpow_sum_shift_le (β : ℝ) (hβ0 : 0 < β) (hβ1 : β ≤ 1) (n : ℕ) :
    ∑ i ∈ Finset.range n, ((i + 2 : ℕ) : ℝ) ^ (β - 1) ≤ ((n + 1 : ℕ) : ℝ) ^ β / β := by
  have hanti : AntitoneOn (fun x : ℝ => x ^ (β - 1)) (Set.Icc 1 (1 + (n : ℝ))) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (by linarith [hx.1]) hxy (by linarith)
  have h := AntitoneOn.sum_le_integral (f := fun x : ℝ => x ^ (β - 1)) (x₀ := (1 : ℝ))
    (a := n) hanti
  have h1 : ∑ i ∈ Finset.range n, (1 + ((i + 1 : ℕ) : ℝ)) ^ (β - 1)
      = ∑ i ∈ Finset.range n, ((i + 2 : ℕ) : ℝ) ^ (β - 1) := by
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    push_cast
    ring
  have hint : ∫ x in (1 : ℝ)..(1 + (n : ℝ)), x ^ (β - 1) = ((1 + (n : ℝ)) ^ β - 1) / β := by
    rw [integral_rpow (a := (1 : ℝ)) (b := 1 + (n : ℝ)) (r := β - 1) (Or.inl (by linarith))]
    rw [show (β - 1) + 1 = β by ring, Real.one_rpow]
  have hfin : ((1 + (n : ℝ)) ^ β - 1) / β ≤ ((n + 1 : ℕ) : ℝ) ^ β / β := by
    have heq : (1 : ℝ) + ↑n = ↑(n + 1) := by push_cast; ring
    rw [heq, div_le_div_iff_of_pos_right hβ0]
    linarith
  calc ∑ i ∈ Finset.range n, ((i + 2 : ℕ) : ℝ) ^ (β - 1)
      = ∑ i ∈ Finset.range n, (1 + ((i + 1 : ℕ) : ℝ)) ^ (β - 1) := h1.symm
    _ ≤ ∫ x in (1 : ℝ)..(1 + (n : ℝ)), x ^ (β - 1) := h
    _ = ((1 + (n : ℝ)) ^ β - 1) / β := hint
    _ ≤ ((n + 1 : ℕ) : ℝ) ^ β / β := hfin

/-- Abel's summation identity in range form. -/
lemma abel_identity' (a w : ℕ → ℝ) (N : ℕ) (hN : 1 ≤ N) :
    ∑ i ∈ Finset.range N, w (i + 1) * a (i + 1)
      = w N * (∑ i ∈ Finset.range N, a (i + 1))
        + ∑ i ∈ Finset.range (N - 1),
            (w (i + 1) - w (i + 2)) * (∑ j ∈ Finset.range (i + 1), a (j + 1)) := by
  have h := Finset.sum_range_by_parts (fun i => w (i + 1)) (fun i => a (i + 1)) N
  simp only [smul_eq_mul] at h
  rw [h, show N - 1 + 1 = N by omega]
  have hT2' : (∑ i ∈ Finset.range (N - 1),
        (w (i + 2) - w (i + 1)) * (∑ j ∈ Finset.range (i + 1), a (j + 1)))
      = - ∑ i ∈ Finset.range (N - 1),
            (w (i + 1) - w (i + 2)) * (∑ j ∈ Finset.range (i + 1), a (j + 1)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hT2']; ring

theorem abel_sum_rpow (β : ℝ) (hβ : 0 < β) : ∃ C : ℝ, 0 < C ∧ ∀ (a : ℕ → ℝ) (M : ℝ) (N : ℕ),
    0 ≤ M → (∀ q, 0 ≤ a q) → (∀ Q, Q ≤ N → ∑ q ∈ Finset.Icc 1 Q, a q ≤ (Q : ℝ) * M) →
      ∑ q ∈ Finset.Icc 1 N, a q * (q : ℝ) ^ (β - 1) ≤ C * (N : ℝ) ^ β * M := by
  refine ⟨1 + β⁻¹, by positivity, ?_⟩
  intro a M N hM ha hbound
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · subst hN0
    rw [Finset.Icc_eq_empty_of_lt (by norm_num : (0 : ℕ) < 1)]
    simp only [Finset.sum_empty]
    positivity
  · have hN : 1 ≤ N := hNpos
    let w : ℕ → ℝ := fun k => (k : ℝ) ^ (β - 1)
    let A : ℕ → ℝ := fun n => ∑ j ∈ Finset.range n, a (j + 1)
    have hA_bound : ∀ n, n ≤ N → A n ≤ (n : ℝ) * M := by
      intro n hn
      show (∑ j ∈ Finset.range n, a (j + 1)) ≤ (n : ℝ) * M
      rw [← sum_Icc_one_eq_sum_range a n]
      exact hbound n hn
    have hLHS : ∑ q ∈ Finset.Icc 1 N, a q * (q : ℝ) ^ (β - 1)
        = ∑ i ∈ Finset.range N, w (i + 1) * a (i + 1) := by
      rw [sum_Icc_one_eq_sum_range (fun q => a q * (q : ℝ) ^ (β - 1)) N]
      apply Finset.sum_congr rfl
      intro i _
      show a (i + 1) * ((i + 1 : ℕ) : ℝ) ^ (β - 1) = w (i + 1) * a (i + 1)
      simp only [w]
      ring
    have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
    have hrpowN : (N : ℝ) ^ (β - 1) * (N : ℝ) = (N : ℝ) ^ β := by
      have h' : (N : ℝ) ^ β = (N : ℝ) ^ (β - 1) * (N : ℝ) := by
        conv_lhs => rw [show β = (β - 1) + 1 by ring]
        rw [Real.rpow_add hNr, Real.rpow_one]
      exact h'.symm
    rcases le_or_gt 1 β with hβge | hβlt
    · rw [hLHS]
      calc ∑ i ∈ Finset.range N, w (i + 1) * a (i + 1)
          ≤ ∑ i ∈ Finset.range N, (N : ℝ) ^ (β - 1) * a (i + 1) := by
              apply Finset.sum_le_sum
              intro i hi
              have hiN : i + 1 ≤ N := by
                have hilt : i < N := Finset.mem_range.mp hi
                omega
              have hwle : w (i + 1) ≤ (N : ℝ) ^ (β - 1) := by
                simp only [w]
                exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hiN) (by linarith)
              exact mul_le_mul_of_nonneg_right hwle (ha (i + 1))
        _ = (N : ℝ) ^ (β - 1) * A N := by
              show (∑ i ∈ Finset.range N, (N : ℝ) ^ (β - 1) * a (i + 1))
                  = (N : ℝ) ^ (β - 1) * (∑ j ∈ Finset.range N, a (j + 1))
              rw [Finset.mul_sum]
        _ ≤ (N : ℝ) ^ (β - 1) * ((N : ℝ) * M) := by
              apply mul_le_mul_of_nonneg_left (hA_bound N le_rfl)
              exact Real.rpow_nonneg (Nat.cast_nonneg N) _
        _ = (N : ℝ) ^ β * M := by rw [← mul_assoc, hrpowN]
        _ ≤ (1 + β⁻¹) * (N : ℝ) ^ β * M := by
              have h1 : (1 + β⁻¹) * (N : ℝ) ^ β * M
                  = (N : ℝ) ^ β * M + β⁻¹ * ((N : ℝ) ^ β * M) := by ring
              rw [h1]
              have h2 : 0 ≤ β⁻¹ * ((N : ℝ) ^ β * M) :=
                mul_nonneg (by positivity)
                  (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) β) hM)
              linarith
    · have hβ1 : β ≤ 1 := hβlt.le
      rw [hLHS, abel_identity' a w N hN]
      have hwN : w N * A N ≤ (N : ℝ) ^ β * M := by
        show (N : ℝ) ^ (β - 1) * A N ≤ (N : ℝ) ^ β * M
        calc (N : ℝ) ^ (β - 1) * A N ≤ (N : ℝ) ^ (β - 1) * ((N : ℝ) * M) := by
                apply mul_le_mul_of_nonneg_left (hA_bound N le_rfl)
                exact Real.rpow_nonneg (Nat.cast_nonneg N) _
          _ = (N : ℝ) ^ β * M := by rw [← mul_assoc, hrpowN]
      have hsum2 : ∑ i ∈ Finset.range (N - 1), (w (i + 1) - w (i + 2)) * A (i + 1)
          ≤ M * ((N : ℝ) ^ β / β) := by
        calc ∑ i ∈ Finset.range (N - 1), (w (i + 1) - w (i + 2)) * A (i + 1)
            ≤ ∑ i ∈ Finset.range (N - 1),
                (w (i + 1) - w (i + 2)) * ((i + 1 : ℕ) * M) := by
                apply Finset.sum_le_sum
                intro i hi
                have hiN : i + 1 ≤ N :=
                  Nat.succ_le_of_lt (lt_of_lt_of_le (Finset.mem_range.mp hi) (Nat.sub_le N 1))
                have hnn : 0 ≤ w (i + 1) - w (i + 2) := by
                  have hwle : w (i + 2) ≤ w (i + 1) := by
                    simp only [w]
                    exact Real.rpow_le_rpow_of_nonpos (by positivity)
                      (by push_cast; linarith) (by linarith)
                  linarith
                exact mul_le_mul_of_nonneg_left (hA_bound (i + 1) hiN) hnn
          _ = M * ∑ i ∈ Finset.range (N - 1), (w (i + 1) - w (i + 2)) * (i + 1 : ℕ) := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro i _
                ring
          _ ≤ M * ∑ i ∈ Finset.range (N - 1), ((i + 2 : ℕ) : ℝ) ^ (β - 1) := by
                apply mul_le_mul_of_nonneg_left _ hM
                apply Finset.sum_le_sum
                intro i _
                have hq := pow_diff_mul_le β hβ (i + 1)
                have hcast : ((i + 1 : ℕ) : ℝ) + 1 = ((i + 2 : ℕ) : ℝ) := by push_cast; ring
                rw [hcast] at hq
                simp only [w]
                rw [mul_comm]
                exact hq
          _ ≤ M * ((N : ℝ) ^ β / β) := by
                apply mul_le_mul_of_nonneg_left _ hM
                have h := rpow_sum_shift_le β hβ hβ1 (N - 1)
                rw [show N - 1 + 1 = N by omega] at h
                exact h
      calc w N * A N + ∑ i ∈ Finset.range (N - 1), (w (i + 1) - w (i + 2)) * A (i + 1)
          ≤ (N : ℝ) ^ β * M + M * ((N : ℝ) ^ β / β) := add_le_add hwN hsum2
        _ = (1 + β⁻¹) * (N : ℝ) ^ β * M := by rw [div_eq_mul_inv]; ring

end Work.FIArea4.L14
