import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mr_core

/-- Telescoping identity for a sum over `Icc N (M-1)`: the sum of consecutive differences
`f n - f (n+1)` collapses to `f N - f M`. -/
lemma sum_Icc_telescope (f : ℕ → ℝ) (N M : ℕ) (hN : 1 ≤ N) (hNM : N ≤ M) :
    ∑ n ∈ Finset.Icc N (M - 1), (f n - f (n + 1)) = f N - f M := by
  rcases eq_or_lt_of_le hNM with rfl | hlt
  · have hempty : Finset.Icc N (N - 1) = ∅ := by
      rw [Finset.Icc_eq_empty_iff]; omega
    rw [hempty, Finset.sum_empty, sub_self]
  · have hNM' : N ≤ M - 1 := by omega
    have h1 := Finset.sum_Icc_sub (m := N) (n := M - 1) hNM' f
    have hneg : ∑ i ∈ Finset.Icc N (M - 1), (f i - f (i + 1))
        = - ∑ i ∈ Finset.Icc N (M - 1), (f (i + 1) - f i) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _; ring
    rw [hneg, h1]
    have hM : M - 1 + 1 = M := by omega
    rw [hM]; ring

/-- Telescoping identity, forward orientation. -/
lemma sum_Icc_telescope_fwd (f : ℕ → ℝ) (N M : ℕ) (hN : 1 ≤ N) (hNM : N ≤ M) :
    ∑ n ∈ Finset.Icc N (M - 1), (f (n + 1) - f n) = f M - f N := by
  have h := sum_Icc_telescope f N M hN hNM
  have h2 : ∑ n ∈ Finset.Icc N (M - 1), (f (n + 1) - f n)
      = - ∑ n ∈ Finset.Icc N (M - 1), (f n - f (n + 1)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro n _; ring
  rw [h2, h]; ring

/-- Reindexing a sum over `Icc N (M-1)` by the shift `j ↦ j+1`. -/
lemma sum_Icc_shift (h : ℕ → ℝ) (N M : ℕ) (hN : 1 ≤ N) (hNM : N ≤ M) :
    ∑ j ∈ Finset.Icc N (M - 1), h (j + 1) = ∑ k ∈ Finset.Icc (N + 1) M, h k := by
  apply Finset.sum_bij (fun n _ => n + 1)
  · intro n hn; simp only [Finset.mem_Icc] at hn ⊢; omega
  · intro n1 _ n2 _ heq; omega
  · intro k hk
    simp only [Finset.mem_Icc] at hk
    exact ⟨k - 1, by simp only [Finset.mem_Icc]; omega, by omega⟩
  · intro n _; rfl

/-- Elementary real-variable inequality: for `x ≥ 3`,
`1 / (x * log x) ≤ log (log x) - log (log (x-1))`. -/
lemma loglog_recip_le_real (x : ℝ) (hx : 3 ≤ x) :
    1 / (x * Real.log x) ≤ Real.log (Real.log x) - Real.log (Real.log (x - 1)) := by
  have hx1 : (1:ℝ) < x := by linarith
  have hx0 : (0:ℝ) < x := by linarith
  have hxm0 : (0:ℝ) < x - 1 := by linarith
  have hlx : 0 < Real.log x := Real.log_pos hx1
  have hlxm : 0 < Real.log (x - 1) := Real.log_pos (by linarith : (1:ℝ) < x - 1)
  have hbd : Real.log x - Real.log (x - 1) = Real.log (x / (x - 1)) := by
    rw [Real.log_div (by linarith) (by linarith)]
  have h1x : 1 / x ≤ Real.log x - Real.log (x - 1) := by
    rw [hbd]
    have h := Real.one_sub_inv_le_log_of_pos (div_pos hx0 hxm0)
    have hsimp : 1 - (x / (x - 1))⁻¹ = 1 / x := by field_simp; ring
    linarith [h, hsimp]
  have hsub : Real.log (Real.log x) - Real.log (Real.log (x - 1))
      = Real.log (Real.log x / Real.log (x - 1)) := by
    rw [Real.log_div (ne_of_gt hlx) (ne_of_gt hlxm)]
  rw [hsub]
  have hratio : (Real.log x - Real.log (x - 1)) / Real.log x
      ≤ Real.log (Real.log x / Real.log (x - 1)) := by
    have hba : Real.log x / Real.log (x - 1)
        = 1 + (Real.log x - Real.log (x - 1)) / Real.log (x - 1) := by
      field_simp; ring
    rw [hba]
    have hu : 0 < 1 + (Real.log x - Real.log (x - 1)) / Real.log (x - 1) := by
      rw [← hba]; exact div_pos hlx hlxm
    have h := Real.one_sub_inv_le_log_of_pos hu
    have hsimp : 1 - (1 + (Real.log x - Real.log (x - 1)) / Real.log (x - 1))⁻¹
        = (Real.log x - Real.log (x - 1)) / Real.log x := by
      rw [← hba, inv_div]; field_simp
    linarith [h, hsimp]
  calc 1 / (x * Real.log x) = (1 / x) / Real.log x := by rw [div_div]
    _ ≤ (Real.log x - Real.log (x - 1)) / Real.log x :=
        div_le_div_of_nonneg_right h1x (le_of_lt hlx)
    _ ≤ Real.log (Real.log x / Real.log (x - 1)) := hratio

/-- Natural-number version of `loglog_recip_le_real`. -/
lemma loglog_recip_le_aux (k : ℕ) (hk : 3 ≤ k) :
    1 / ((k : ℝ) * Real.log (k : ℝ))
      ≤ Real.log (Real.log (k : ℝ)) - Real.log (Real.log ((k - 1 : ℕ) : ℝ)) := by
  have hx : (3:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
  have h := loglog_recip_le_real (k:ℝ) hx
  have hcast : ((k - 1 : ℕ) : ℝ) = (k:ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ k)]; norm_num
  rw [hcast]; exact h

/-- Sum/integral comparison bound: `∑_{k=N+1}^M 1/(k log k) ≤ log log M - log log N`. -/
lemma sum_inv_k_log_k_le_aux (N M : ℕ) (hN : 2 ≤ N) (hNM : N ≤ M) :
    ∑ k ∈ Finset.Icc (N + 1) M, 1 / ((k : ℝ) * Real.log (k : ℝ))
      ≤ Real.log (Real.log (M : ℝ)) - Real.log (Real.log (N : ℝ)) := by
  have hN1 : 1 ≤ N := by omega
  have hterm : ∀ k ∈ Finset.Icc (N + 1) M,
      1 / ((k : ℝ) * Real.log (k : ℝ))
        ≤ (Real.log (Real.log (k : ℝ)) - Real.log (Real.log ((k - 1 : ℕ) : ℝ))) := by
    intro k hk
    simp only [Finset.mem_Icc] at hk
    exact loglog_recip_le_aux k (by omega)
  calc ∑ k ∈ Finset.Icc (N + 1) M, 1 / ((k : ℝ) * Real.log (k : ℝ))
      ≤ ∑ k ∈ Finset.Icc (N + 1) M,
          (Real.log (Real.log (k : ℝ)) - Real.log (Real.log ((k - 1 : ℕ) : ℝ))) :=
        Finset.sum_le_sum hterm
    _ = ∑ j ∈ Finset.Icc N (M - 1),
          ((fun m : ℕ => Real.log (Real.log (m : ℝ))) (j + 1)
            - (fun m : ℕ => Real.log (Real.log (m : ℝ))) j) := by
        rw [← sum_Icc_shift (fun k : ℕ => Real.log (Real.log (k : ℝ)) - Real.log (Real.log ((k - 1 : ℕ) : ℝ))) N M hN1 hNM]
        apply Finset.sum_congr rfl
        intro j _
        simp
    _ = Real.log (Real.log (M : ℝ)) - Real.log (Real.log (N : ℝ)) := by
        rw [sum_Icc_telescope_fwd (fun m : ℕ => Real.log (Real.log (m : ℝ))) N M hN1 hNM]

/-- Splitting one summand of the weighted sum into a telescoping part and a remainder. -/
lemma term_eq (n : ℕ) (hn : 2 ≤ n) :
    (n:ℝ) * (1 / ((n:ℝ) * Real.log (n:ℝ)) - 1 / (((n:ℝ) + 1) * Real.log ((n:ℝ) + 1)))
      = (1 / Real.log (n:ℝ) - 1 / Real.log ((n:ℝ) + 1))
        + 1 / (((n:ℝ) + 1) * Real.log ((n:ℝ) + 1)) := by
  have hn0 : (n:ℝ) ≠ 0 := by positivity
  have hn1 : (n:ℝ) + 1 ≠ 0 := by positivity
  have hln : Real.log (n:ℝ) ≠ 0 := by
    have : (1:ℝ) < n := by exact_mod_cast (by omega : 1 < n)
    exact ne_of_gt (Real.log_pos this)
  have hln1 : Real.log ((n:ℝ) + 1) ≠ 0 := by
    have : (1:ℝ) < (n:ℝ) + 1 := by
      have : (2:ℝ) ≤ n := by exact_mod_cast hn
      linarith
    exact ne_of_gt (Real.log_pos this)
  field_simp
  ring

theorem invLog_weight_sum_le (N M : ℕ) (hN : 2 ≤ N) (hNM : N ≤ M) :
    (∑ n ∈ Finset.Icc N (M - 1),
        (n : ℝ) * (1 / ((n : ℝ) * Real.log (n : ℝ)) -
          1 / (((n : ℝ) + 1) * Real.log ((n : ℝ) + 1))))
      ≤ 1 / Real.log (N : ℝ) +
        (Real.log (Real.log (M : ℝ)) - Real.log (Real.log (N : ℝ))) := by
  have hN1 : 1 ≤ N := by omega
  have hsplit : (∑ n ∈ Finset.Icc N (M - 1),
        (n : ℝ) * (1 / ((n : ℝ) * Real.log (n : ℝ)) -
          1 / (((n : ℝ) + 1) * Real.log ((n : ℝ) + 1))))
      = (∑ n ∈ Finset.Icc N (M - 1),
          (1 / Real.log (n : ℝ) - 1 / Real.log ((n : ℝ) + 1)))
        + (∑ n ∈ Finset.Icc N (M - 1),
          1 / (((n : ℝ) + 1) * Real.log ((n : ℝ) + 1))) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    have hn2 : 2 ≤ n := by simp only [Finset.mem_Icc] at hn; omega
    exact term_eq n hn2
  rw [hsplit]
  have htel : (∑ n ∈ Finset.Icc N (M - 1),
          (1 / Real.log (n : ℝ) - 1 / Real.log ((n : ℝ) + 1)))
      = 1 / Real.log (N : ℝ) - 1 / Real.log (M : ℝ) := by
    have h := sum_Icc_telescope (fun m : ℕ => 1 / Real.log (m : ℝ)) N M hN1 hNM
    simpa only [Nat.cast_add, Nat.cast_one] using h
  rw [htel]
  have hshift : (∑ n ∈ Finset.Icc N (M - 1),
          1 / (((n : ℝ) + 1) * Real.log ((n : ℝ) + 1)))
      = ∑ k ∈ Finset.Icc (N + 1) M, 1 / ((k : ℝ) * Real.log (k : ℝ)) := by
    have h := sum_Icc_shift (fun k : ℕ => 1 / ((k:ℝ) * Real.log (k:ℝ))) N M hN1 hNM
    simpa only [Nat.cast_add, Nat.cast_one] using h
  rw [hshift]
  have hb := sum_inv_k_log_k_le_aux N M hN hNM
  have hpos : 0 ≤ 1 / Real.log (M : ℝ) := by
    have hM1 : (1:ℝ) < M := by exact_mod_cast (by omega : 1 < M)
    exact div_nonneg zero_le_one (le_of_lt (Real.log_pos hM1))
  linarith [hb, hpos]

end Work.BMF.mr_core
