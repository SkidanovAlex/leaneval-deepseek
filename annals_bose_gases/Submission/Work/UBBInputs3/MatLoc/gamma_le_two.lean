import Mathlib.Algebra.Order.Star.Real
import Submission.Work.UBBInputs3.MatLoc.prof_norm
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.UBBInputs3.MatLoc.gamma_le_two`

The Lieb–Solovej deficit `γ_k = ½ Σ_s (prof(s+k) - prof(s))²` of the normalised triangle
profile satisfies the trivial (Cauchy–Schwarz) bound `γ_k ≤ 2` for every `p` and `k`.

The proof is the elementary estimate `(a-b)² ≤ 2a² + 2b²` applied termwise, together with
the two normalisations

* `Σ_{s∈[-p-|k|,p+|k|]} prof(s)² = 1`   (the profile is supported in `[-p,p]`),
* `Σ_{s∈[-p-|k|,p+|k|]} prof(s+k)² = 1` (likewise, after the translation `s ↦ s+k`).
-/

noncomputable section

open scoped BigOperators
open Finset

namespace Work.UBBInputs3.MatLoc

/-! ## Vanishing of the profile off its support -/

/-- The triangle profile vanishes where `|s| ≥ p + 1`. -/
lemma tri_eq_zero_of_abs_ge (p : ℕ) (s : ℤ) (h : (p : ℤ) + 1 ≤ |s|) :
    Work.UBBInputs3.tri p s = 0 := by
  unfold Work.UBBInputs3.tri
  rw [max_eq_left]
  have h' : (p : ℝ) + 1 ≤ |(s : ℝ)| := by
    have h1 : (((p : ℤ) + 1 : ℤ) : ℝ) ≤ ((|s| : ℤ) : ℝ) := Int.cast_le.mpr h
    simpa [Int.cast_abs] using h1
  linarith

/-- The normalised profile vanishes where `|s| ≥ p + 1`. -/
lemma prof_eq_zero_of_abs_ge (p : ℕ) (s : ℤ) (h : (p : ℤ) + 1 ≤ |s|) :
    Work.UBBInputs3.prof p s = 0 := by
  rw [Work.UBBInputs3.prof, tri_eq_zero_of_abs_ge p s h, zero_div]

/-- The normalised profile vanishes outside its support `[-p,p]`. -/
lemma prof_eq_zero_of_not_mem (p : ℕ) {s : ℤ}
    (h : s ∉ Finset.Icc (-(p : ℤ)) (p : ℤ)) : Work.UBBInputs3.prof p s = 0 := by
  refine prof_eq_zero_of_abs_ge p s ?_
  simp only [Finset.mem_Icc, not_and_or, not_le] at h
  rcases h with h | h
  · have hs : s < 0 := by omega
    rw [abs_of_neg hs]; omega
  · have hs : 0 ≤ s := by omega
    rw [abs_of_nonneg hs]; omega

/-! ## The two normalisations -/

/-- `Σ_{s∈[-p-|k|,p+|k|]} prof(s+k)² = 1`. -/
lemma sum_prof_sq_shift (p : ℕ) (k : ℤ) :
    ∑ s ∈ Finset.Icc (-(p : ℤ) - |k|) ((p : ℤ) + |k|),
        (Work.UBBInputs3.prof p (s + k)) ^ 2 = 1 := by
  have hshift :
      (∑ s ∈ Finset.Icc (-(p : ℤ) - |k|) ((p : ℤ) + |k|),
          (Work.UBBInputs3.prof p (s + k)) ^ 2)
        = ∑ t ∈ Finset.Icc (-(p : ℤ) - |k| + k) ((p : ℤ) + |k| + k),
            (Work.UBBInputs3.prof p t) ^ 2 := by
    have h := Work.UBBInputs3.sum_Icc_shift (fun t => (Work.UBBInputs3.prof p t) ^ 2)
      (-(p : ℤ) - |k| + k) ((p : ℤ) + |k| + k) k
    simpa only [add_sub_cancel_right] using h
  rw [hshift]
  have hlo : -(p : ℤ) - |k| + k ≤ -(p : ℤ) := by
    have := le_abs_self k; omega
  have hhi : (p : ℤ) ≤ (p : ℤ) + |k| + k := by
    have := neg_abs_le k; omega
  rw [Work.UBBInputs3.sum_Icc_congr_of_eq_zero_outside
        (fun t => (Work.UBBInputs3.prof p t) ^ 2) hlo hhi
        (fun t ht => by rw [prof_eq_zero_of_not_mem p ht]; ring)]
  exact prof_norm p

/-- `Σ_{s∈[-p-|k|,p+|k|]} prof(s)² = 1`. -/
lemma sum_prof_sq_self (p : ℕ) (k : ℤ) :
    ∑ s ∈ Finset.Icc (-(p : ℤ) - |k|) ((p : ℤ) + |k|),
        (Work.UBBInputs3.prof p s) ^ 2 = 1 := by
  have hlo : -(p : ℤ) - |k| ≤ -(p : ℤ) := by
    have := abs_nonneg k; omega
  have hhi : (p : ℤ) ≤ (p : ℤ) + |k| := by
    have := abs_nonneg k; omega
  rw [Work.UBBInputs3.sum_Icc_congr_of_eq_zero_outside
        (fun t => (Work.UBBInputs3.prof p t) ^ 2) hlo hhi
        (fun t ht => by rw [prof_eq_zero_of_not_mem p ht]; ring)]
  exact prof_norm p

/-! ## The bound `γ_k ≤ 2` -/

theorem gamma_le_two (p : ℕ) (k : ℤ) : Work.UBBInputs3.gamma p k ≤ 2 := by
  have h4 :
      ∑ s ∈ Finset.Icc (-(p : ℤ) - |k|) ((p : ℤ) + |k|),
        (Work.UBBInputs3.prof p (s + k) - Work.UBBInputs3.prof p s) ^ 2 ≤ 4 := by
    calc ∑ s ∈ Finset.Icc (-(p : ℤ) - |k|) ((p : ℤ) + |k|),
          (Work.UBBInputs3.prof p (s + k) - Work.UBBInputs3.prof p s) ^ 2
        ≤ ∑ s ∈ Finset.Icc (-(p : ℤ) - |k|) ((p : ℤ) + |k|),
            (2 * (Work.UBBInputs3.prof p (s + k)) ^ 2
              + 2 * (Work.UBBInputs3.prof p s) ^ 2) := by
          refine Finset.sum_le_sum fun s _ => ?_
          nlinarith [sq_nonneg (Work.UBBInputs3.prof p (s + k) + Work.UBBInputs3.prof p s)]
      _ = 2 * (∑ s ∈ Finset.Icc (-(p : ℤ) - |k|) ((p : ℤ) + |k|),
              (Work.UBBInputs3.prof p (s + k)) ^ 2)
            + 2 * (∑ s ∈ Finset.Icc (-(p : ℤ) - |k|) ((p : ℤ) + |k|),
              (Work.UBBInputs3.prof p s) ^ 2) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ = 4 := by
          rw [sum_prof_sq_shift p k, sum_prof_sq_self p k]
          norm_num
  unfold Work.UBBInputs3.gamma
  linarith

end Work.UBBInputs3.MatLoc
