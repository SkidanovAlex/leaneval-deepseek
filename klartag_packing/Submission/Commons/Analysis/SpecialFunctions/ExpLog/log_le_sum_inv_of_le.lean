import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Commons.Analysis.SpecialFunctions.ExpLog

/-- Telescoping sum over `Finset.Icc`: the sum of consecutive differences of a
function equals the difference of the endpoint values. -/
lemma sum_Icc_sub_eq (f : ℕ → ℝ) {K M : ℕ} (hKM : K ≤ M) :
    ∑ i ∈ Finset.Icc K M, (f (i + 1) - f i) = f (M + 1) - f K := by
  induction M, hKM using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [Finset.sum_Icc_succ_top (f := fun i => f (i + 1) - f i) (Nat.le_succ_of_le hn), ih]
    ring

/-- The harmonic tail sum dominates the logarithm of the ratio of the endpoints:
`log ((M+1)/K) ≤ ∑_{i=K}^{M} 1/i` for `1 ≤ K ≤ M`.  Proved by comparing each
`log ((i+1)/i)` with `1/i` and telescoping. -/
lemma log_div_le_sum_inv_Icc {K M : ℕ} (hK : 1 ≤ K) (hKM : K ≤ M) :
    Real.log (((M : ℝ) + 1) / (K : ℝ)) ≤ ∑ i ∈ Finset.Icc K M, 1 / (i : ℝ) := by
  have hcast : Real.log ((M : ℝ) + 1) - Real.log (K : ℝ)
      = ∑ i ∈ Finset.Icc K M, (Real.log ((i : ℝ) + 1) - Real.log (i : ℝ)) := by
    have h := sum_Icc_sub_eq (fun i => Real.log (i : ℝ)) hKM
    simp only [Nat.cast_add, Nat.cast_one] at h
    exact h.symm
  have hterm : ∀ i ∈ Finset.Icc K M,
      Real.log ((i : ℝ) + 1) - Real.log (i : ℝ) ≤ 1 / (i : ℝ) := by
    intro i hi
    have hi1 : 1 ≤ i := hK.trans (Finset.mem_Icc.mp hi).1
    have hipos : (0 : ℝ) < (i : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hi1)
    have hx : (0 : ℝ) < ((i : ℝ) + 1) / (i : ℝ) := by positivity
    calc Real.log ((i : ℝ) + 1) - Real.log (i : ℝ)
        = Real.log (((i : ℝ) + 1) / (i : ℝ)) :=
            (Real.log_div (by positivity) (by positivity)).symm
      _ ≤ ((i : ℝ) + 1) / (i : ℝ) - 1 := Real.log_le_sub_one_of_pos hx
      _ = 1 / (i : ℝ) := by field_simp; ring
  calc Real.log (((M : ℝ) + 1) / (K : ℝ))
      = Real.log ((M : ℝ) + 1) - Real.log (K : ℝ) := Real.log_div (by positivity) (by positivity)
    _ = ∑ i ∈ Finset.Icc K M, (Real.log ((i : ℝ) + 1) - Real.log (i : ℝ)) := hcast
    _ ≤ ∑ i ∈ Finset.Icc K M, 1 / (i : ℝ) := Finset.sum_le_sum hterm

/-- For reals `1 ≤ a ≤ R ≤ M`, the logarithm `log (R/a)` is bounded by the
truncated harmonic sum over those `i ∈ [1,M]` with `a ≤ i+1`. -/
theorem log_le_sum_inv_of_le (a R : ℝ) (M : ℕ) (ha : 1 ≤ a) (haR : a ≤ R) (hRM : R ≤ (M : ℝ)) :
    Real.log (R / a) ≤ ∑ i ∈ Finset.Icc 1 M, (if a ≤ (i : ℝ) + 1 then 1 / (i : ℝ) else 0) := by
  have ha0 : (0 : ℝ) ≤ a := by linarith
  set K : ℕ := max 1 ⌈a - 1⌉₊ with hK
  have hK1 : 1 ≤ K := le_max_left _ _
  have hKa : (K : ℝ) ≤ a := by
    rw [hK, Nat.cast_max, Nat.cast_one, max_le_iff]
    refine ⟨ha, ?_⟩
    have hlt := Nat.ceil_lt_add_one_of_gt_neg_one (R := ℝ) (show (-1 : ℝ) < a - 1 by linarith)
    linarith
  have hKM : K ≤ M := by
    have h : (K : ℝ) ≤ (M : ℝ) := le_trans hKa (le_trans haR hRM)
    exact_mod_cast h
  have hsum : ∑ i ∈ Finset.Icc 1 M, (if a ≤ (i : ℝ) + 1 then 1 / (i : ℝ) else 0)
      = ∑ i ∈ Finset.Icc K M, 1 / (i : ℝ) := by
    rw [← Finset.sum_filter]
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_Icc, hK, max_le_iff, Nat.ceil_le]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨h1, by linarith⟩, h2⟩
    · rintro ⟨⟨h1, h3⟩, h2⟩
      exact ⟨⟨h1, h2⟩, by linarith⟩
  rw [hsum]
  have hle : R / a ≤ ((M : ℝ) + 1) / (K : ℝ) := by
    calc R / a ≤ (M : ℝ) / a := div_le_div_of_nonneg_right hRM ha0
      _ ≤ ((M : ℝ) + 1) / a := div_le_div_of_nonneg_right (by linarith) ha0
      _ ≤ ((M : ℝ) + 1) / (K : ℝ) :=
          div_le_div_of_nonneg_left (by positivity)
            (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hK1)) hKa
  calc Real.log (R / a)
      ≤ Real.log (((M : ℝ) + 1) / (K : ℝ)) :=
          Real.log_le_log (div_pos (by linarith : (0:ℝ) < R) (by linarith : (0:ℝ) < a)) hle
    _ ≤ ∑ i ∈ Finset.Icc K M, 1 / (i : ℝ) := log_div_le_sum_inv_Icc hK1 hKM

end Commons.Analysis.SpecialFunctions.ExpLog