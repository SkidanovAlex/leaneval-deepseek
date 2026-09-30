import Mathlib
import Submission.Work.BMF.VKGrowthDefs
import Submission.Work.BMF.ioc_abel_identity
import Submission.Work.BMF.sum_Icc_sub_telescope

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Tools for the Vinogradov–Korobov block analysis
-/

namespace Work.BMF

open Finset
open scoped BigOperators

noncomputable section

/-- Telescoping differences over `Ioc`. -/
lemma sum_Ioc_sub_telescope {G : Type*} [AddCommGroup G] (w : ℕ → G) {a b : ℕ} (h : a ≤ b) :
    ∑ n ∈ Finset.Ioc a b, (w n - w (n + 1)) = w (a + 1) - w (b + 1) := by
  have hset : Finset.Ioc a b = Finset.Icc (a + 1) b := by
    ext x
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  rw [hset]
  exact sum_Icc_sub_telescope w (a + 1) b (by omega)

/-- **Abel summation bound.**  If the partial sums of `e` over `(K, r]` are bounded by `B` and
`w` is nonnegative and decreasing, then `‖∑_{K<n≤R} w n * e n‖ ≤ w (K+1) * B`. -/
lemma norm_sum_Ioc_mul_le {K R : ℕ} {w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n)
    (hmono : ∀ n, w (n + 1) ≤ w n) {e : ℕ → ℂ} {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ r ∈ Finset.Ioc K R, ‖∑ n ∈ Finset.Ioc K r, e n‖ ≤ B) :
    ‖∑ n ∈ Finset.Ioc K R, (w n : ℂ) * e n‖ ≤ w (K + 1) * B := by
  by_cases hRK : K < R
  · set A : ℕ → ℂ := fun n => ∑ k ∈ Finset.Ioc K n, e k with hA
    have hA0 : A K = 0 := by simp [hA]
    have hstep : ∀ k, K ≤ k → A (k + 1) = A k + e (k + 1) := by
      intro k hk
      simp only [hA]
      rw [Finset.sum_Ioc_succ_top hk]
    have habel := ioc_abel_identity e (fun n => (w n : ℂ)) A K R hA0 hstep hRK
    have h1 : ‖(w R : ℂ) * A R‖ ≤ w R * B := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw R)]
      exact mul_le_mul_of_nonneg_left (hB R (by simp only [Finset.mem_Ioc]; omega)) (hw R)
    have h2 : ‖∑ n ∈ Finset.Ioc K (R - 1), ((w n : ℂ) - (w (n + 1) : ℂ)) * A n‖ ≤
        ∑ n ∈ Finset.Ioc K (R - 1), (w n - w (n + 1)) * B := by
      refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun n hn => ?_)
      have hnK : K < n := (Finset.mem_Ioc.mp hn).1
      have hnR : n < R := by
        have := (Finset.mem_Ioc.mp hn).2
        omega
      have hle : ‖A n‖ ≤ B := hB n (by simp only [Finset.mem_Ioc]; exact ⟨hnK, le_of_lt hnR⟩)
      have hwn : 0 ≤ w n - w (n + 1) := sub_nonneg.mpr (hmono n)
      have hcast : ((w n : ℂ) - (w (n + 1) : ℂ)) = ((w n - w (n + 1) : ℝ) : ℂ) := by
        push_cast; ring
      rw [norm_mul, hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hwn]
      exact mul_le_mul_of_nonneg_left hle hwn
    have hsum_tel : ∑ n ∈ Finset.Ioc K (R - 1), (w n - w (n + 1)) = w (K + 1) - w R := by
      have hKR : K ≤ R - 1 := Nat.le_sub_one_of_lt hRK
      have hR1 : 1 ≤ R := by omega
      have := sum_Ioc_sub_telescope w (a := K) (b := R - 1) hKR
      rw [this, Nat.sub_add_cancel hR1]
    calc ‖∑ n ∈ Finset.Ioc K R, (w n : ℂ) * e n‖
        = ‖(w R : ℂ) * A R + ∑ n ∈ Finset.Ioc K (R - 1), ((w n : ℂ) - (w (n + 1) : ℂ)) * A n‖ := by
          rw [habel]
      _ ≤ ‖(w R : ℂ) * A R‖ + ‖∑ n ∈ Finset.Ioc K (R - 1), ((w n : ℂ) - (w (n + 1) : ℂ)) * A n‖ :=
          norm_add_le _ _
      _ ≤ w R * B + ∑ n ∈ Finset.Ioc K (R - 1), (w n - w (n + 1)) * B := add_le_add h1 h2
      _ = w R * B + (w (K + 1) - w R) * B := by rw [← Finset.sum_mul, hsum_tel]
      _ = w (K + 1) * B := by ring
  · have hempty : Finset.Ioc K R = ∅ := by
      ext x
      simp only [Finset.mem_Ioc, Finset.notMem_empty, iff_false, not_and]
      intro h
      omega
    rw [hempty, Finset.sum_empty, norm_zero]
    exact mul_nonneg (hw _) hB0

end

end Work.BMF
