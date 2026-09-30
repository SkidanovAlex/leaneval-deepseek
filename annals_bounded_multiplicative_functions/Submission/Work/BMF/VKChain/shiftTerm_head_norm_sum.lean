import Mathlib
import Submission.Work.BMF.HurwitzShift

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Norm bound for the head of the shift-difference series

This file proves `Work.BMF.VKChain.shiftTerm_head_norm_sum`: the head `∑_{m < K₀}` of the
shift-difference series `∑_m ((m+a)^{-s} - (m+1)^{-s})` at `s = σ + i t` is bounded by
`a^{-σ} + 2 ∑_{1 ≤ m ≤ K₀} m^{-σ}`, uniformly in `t` and for every `a > 0`, `σ > 0`.

The proof is elementary: the triangle inequality bounds each term by the sum of the moduli of
its two summands, `(m+a)^{-σ} + (m+1)^{-σ}`, and the two resulting sums are compared with the
Riemann-type sum `∑_{1 ≤ m ≤ K₀} m^{-σ}` by monotonicity of `x ↦ x^{-σ}` and a reindexing.
-/

namespace Work.BMF.VKChain

open scoped BigOperators

/-- Reindexing: `∑_{m < n} f (1 + m) = ∑_{1 ≤ m ≤ n} f m`. -/
private lemma sum_range_one_add (f : ℕ → ℝ) (n : ℕ) :
    (∑ m ∈ Finset.range n, f (1 + m)) = ∑ m ∈ Finset.Icc 1 n, f m := by
  have hIcc : Finset.Icc 1 n = Finset.Ico 1 (n + 1) := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [hIcc, Finset.sum_Ico_eq_sum_range]
  simp

/-- `x ↦ x^{-σ}` is decreasing on the positive reals, so the shifted sum `∑_{m<n} (m+a)^{-σ}`
is dominated by `a^{-σ}` plus the Riemann tail `∑_{1 ≤ m ≤ n} m^{-σ}`. -/
private lemma sum_rpow_shift_le (n : ℕ) (a σ : ℝ) (ha : 0 < a) (hσ0 : 0 < σ) :
    (∑ m ∈ Finset.range n, (((m : ℝ) + a)) ^ (-σ)) ≤
      a ^ (-σ) + ∑ m ∈ Finset.Icc 1 n, (m : ℝ) ^ (-σ) := by
  rcases n with _ | n
  · simp only [Finset.range_zero, Finset.sum_empty]
    have h0 : (0 : ℝ) ≤ a ^ (-σ) := (Real.rpow_pos_of_pos ha _).le
    have : (Finset.Icc 1 0 : Finset ℕ) = ∅ := by simp
    rw [this, Finset.sum_empty]
    simpa using h0
  · have hstep1 : (∑ m ∈ Finset.range n, ((((m + 1 : ℕ) : ℝ) + a)) ^ (-σ)) ≤
        ∑ m ∈ Finset.range n, (((m : ℝ) + 1)) ^ (-σ) := by
      apply Finset.sum_le_sum
      intro m _
      have hx : 0 < (m : ℝ) + 1 := by positivity
      have hxy : (m : ℝ) + 1 ≤ (((m + 1 : ℕ) : ℝ) + a) := by push_cast; linarith
      exact Real.rpow_le_rpow_of_nonpos hx hxy (by linarith)
    have hstep2 : (∑ m ∈ Finset.range n, (((m : ℝ) + 1)) ^ (-σ)) =
        ∑ m ∈ Finset.Icc 1 n, (m : ℝ) ^ (-σ) := by
      rw [← sum_range_one_add (fun j => (j : ℝ) ^ (-σ)) n]
      apply Finset.sum_congr rfl
      intro m _
      congr 1
      push_cast; ring
    have hstep3 : (∑ m ∈ Finset.Icc 1 n, (m : ℝ) ^ (-σ)) ≤
        ∑ m ∈ Finset.Icc 1 (n + 1), (m : ℝ) ^ (-σ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.Icc_subset_Icc_right (by omega)
      · intro i _ _
        exact Real.rpow_nonneg (Nat.cast_nonneg i) (-σ)
    calc ∑ m ∈ Finset.range (n + 1), ((m : ℝ) + a) ^ (-σ)
        = (∑ m ∈ Finset.range n, ((((m + 1 : ℕ) : ℝ) + a)) ^ (-σ)) + a ^ (-σ) := by
          rw [Finset.sum_range_succ']; simp
      _ ≤ (∑ m ∈ Finset.range n, (((m : ℝ) + 1)) ^ (-σ)) + a ^ (-σ) := add_le_add hstep1 le_rfl
      _ = (∑ m ∈ Finset.Icc 1 n, (m : ℝ) ^ (-σ)) + a ^ (-σ) := by rw [hstep2]
      _ ≤ (∑ m ∈ Finset.Icc 1 (n + 1), (m : ℝ) ^ (-σ)) + a ^ (-σ) := add_le_add hstep3 le_rfl
      _ = a ^ (-σ) + ∑ m ∈ Finset.Icc 1 (n + 1), (m : ℝ) ^ (-σ) := by ring

/-- Reindexing of the second sum: `∑_{m<K₀} (m+1)^{-σ} = ∑_{1 ≤ m ≤ K₀} m^{-σ}`. -/
private lemma sum_range_one_cast_eq (K₀ : ℕ) (σ : ℝ) :
    (∑ m ∈ Finset.range K₀, (((m : ℝ) + 1)) ^ (-σ)) =
      ∑ m ∈ Finset.Icc 1 K₀, (m : ℝ) ^ (-σ) := by
  rw [← sum_range_one_add (fun j => (j : ℝ) ^ (-σ)) K₀]
  apply Finset.sum_congr rfl
  intro m _
  congr 1
  push_cast; ring

/-- The head of the shift-difference series is bounded by `a^{-σ} + 2 ∑_{1 ≤ m ≤ K₀} m^{-σ}`,
uniformly in the imaginary part `t`. -/
theorem shiftTerm_head_norm_sum {K₀ : ℕ} {a σ t : ℝ} (ha : 0 < a) (hσ0 : 0 < σ) :
    ‖∑ m ∈ Finset.range K₀, Work.BMF.shiftTerm a m ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      a ^ (-σ) + 2 * ∑ m ∈ Finset.Icc 1 K₀, (m : ℝ) ^ (-σ) := by
  set s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hs_def
  have hsre : s.re = σ := by rw [hs_def]; simp
  -- Pointwise bound on the terms.
  have hterm : ∀ m : ℕ,
      ‖Work.BMF.shiftTerm a m s‖ ≤ ((m : ℝ) + a) ^ (-σ) + ((m : ℝ) + 1) ^ (-σ) := by
    intro m
    have h1 : 0 < (m : ℝ) + a := by positivity
    have h2 : 0 < (((m + 1 : ℕ) : ℝ)) := by positivity
    have e1 : ‖((((m : ℝ) + a : ℝ)) : ℂ) ^ (-s)‖ = ((m : ℝ) + a) ^ (-σ) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos h1, Complex.neg_re, hsre]
    have e2 : ‖(((((m + 1 : ℕ) : ℝ)) : ℂ) ^ (-s))‖ = ((m : ℝ) + 1) ^ (-σ) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos h2, Complex.neg_re, hsre]
      congr 1
      push_cast; ring
    unfold Work.BMF.shiftTerm
    calc ‖((((m : ℝ) + a : ℝ)) : ℂ) ^ (-s) - ((((m + 1 : ℕ) : ℝ)) : ℂ) ^ (-s)‖
        ≤ ‖((((m : ℝ) + a : ℝ)) : ℂ) ^ (-s)‖ + ‖(((((m + 1 : ℕ) : ℝ)) : ℂ) ^ (-s))‖ :=
          norm_sub_le _ _
      _ = ((m : ℝ) + a) ^ (-σ) + ((m : ℝ) + 1) ^ (-σ) := by rw [e1, e2]
  -- Sum up the pointwise bounds.
  have hsum_le : (∑ m ∈ Finset.range K₀, ‖Work.BMF.shiftTerm a m s‖) ≤
      a ^ (-σ) + 2 * ∑ m ∈ Finset.Icc 1 K₀, (m : ℝ) ^ (-σ) := by
    calc ∑ m ∈ Finset.range K₀, ‖Work.BMF.shiftTerm a m s‖
        ≤ ∑ m ∈ Finset.range K₀, (((m : ℝ) + a) ^ (-σ) + ((m : ℝ) + 1) ^ (-σ)) :=
          Finset.sum_le_sum (fun m _ => hterm m)
      _ = (∑ m ∈ Finset.range K₀, ((m : ℝ) + a) ^ (-σ)) +
            (∑ m ∈ Finset.range K₀, ((m : ℝ) + 1) ^ (-σ)) := Finset.sum_add_distrib
      _ ≤ (a ^ (-σ) + ∑ m ∈ Finset.Icc 1 K₀, (m : ℝ) ^ (-σ)) +
            (∑ m ∈ Finset.Icc 1 K₀, (m : ℝ) ^ (-σ)) := by
          apply add_le_add
          · exact sum_rpow_shift_le K₀ a σ ha hσ0
          · rw [sum_range_one_cast_eq]
      _ = a ^ (-σ) + 2 * ∑ m ∈ Finset.Icc 1 K₀, (m : ℝ) ^ (-σ) := by ring
  calc ‖∑ m ∈ Finset.range K₀, Work.BMF.shiftTerm a m s‖
      ≤ ∑ m ∈ Finset.range K₀, ‖Work.BMF.shiftTerm a m s‖ := norm_sum_le _ _
    _ ≤ a ^ (-σ) + 2 * ∑ m ∈ Finset.Icc 1 K₀, (m : ℝ) ^ (-σ) := hsum_le

end Work.BMF.VKChain
