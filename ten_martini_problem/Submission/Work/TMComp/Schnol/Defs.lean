import Mathlib
import Submission.Work.TMContract.Components
import Submission.Work.TMC16Core.Basic.dirMat_mulVec_entry

/-!
# Component C15 (`P_Schnol`): shared definitions

Vocabulary for the finite-volume proof of weak Schnol (Avila–Jitomirskaya, *The Ten Martini
Problem*, §9 ¶1): the summable weight `wt n = (1+|n|)^{-2}` (giving the growth bound
`|u n| ≤ C (1+|n|)` of AJ (9.2)), the total mass `Wtot`, the zero extension `ext` of a vector
indexed by `Fin (2M+1)` to all of `ℤ` (index `i` ↔ site `i - M`), and the Dirichlet
truncation `winMat` of the almost Mathieu operator to the window `[-M, M]`.
-/

open scoped ENNReal
open LeanEval.Analysis.TenMartini

noncomputable section

namespace Work.TMComp.Schnol

/-! ## 1. The weight `wt n = (1 + |n|)^{-2}` -/

/-- The summable weight `wt n = (1 + |n|)⁻¹ ^ 2` of the pigeonhole step of Schnol's theorem. -/
def wt (n : ℤ) : ℝ := (1 + |(n : ℝ)|)⁻¹ ^ 2

/-- The total mass `Wtot = Σ_n wt n` (finite, and `≥ 1`). -/
def Wtot : ℝ := ∑' n : ℤ, wt n

theorem wt_pos (n : ℤ) : 0 < wt n := by
  rw [wt]; positivity

theorem wt_nonneg (n : ℤ) : 0 ≤ wt n := (wt_pos n).le

theorem wt_le_one (n : ℤ) : wt n ≤ 1 := by
  have h1 : (1 : ℝ) ≤ 1 + |(n : ℝ)| := by have := abs_nonneg (n : ℝ); linarith
  rw [wt]
  calc (1 + |(n : ℝ)|)⁻¹ ^ 2 ≤ (1 : ℝ) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (inv_le_one_of_one_le₀ h1) 2
    _ = 1 := by norm_num

theorem summable_wt_nat : Summable (fun n : ℕ => ((1 : ℝ) + n)⁻¹ ^ 2) := by
  have h : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
    (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
  have h2 : Summable (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ) ^ 2) :=
    (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ) ^ 2) 1).mpr h
  refine h2.congr (fun n => ?_)
  push_cast
  rw [one_div, inv_pow]
  ring_nf

theorem wt_natAbs_aux (n : ℕ) : ((1 : ℝ) + n)⁻¹ ^ 2 = ((n : ℝ) + 1)⁻¹ ^ 2 := by
  have h : (1 : ℝ) + n = (n : ℝ) + 1 := by ring
  rw [h]

theorem summable_wt : Summable wt := by
  refine Summable.of_nat_of_neg_add_one (f := wt) ?_ ?_
  · refine summable_wt_nat.congr (fun n => ?_)
    rw [wt]
    have h1 : |((n : ℤ) : ℝ)| = (n : ℝ) := by
      push_cast
      exact abs_of_nonneg (by positivity)
    rw [h1]
  · refine Summable.of_nonneg_of_le
      (f := fun n : ℕ => ((1 : ℝ) + n)⁻¹ ^ 2) (fun n => ?_) (fun n => ?_) summable_wt_nat
    · rw [wt]; positivity
    · rw [wt]
      have h1 : |((-(n + 1) : ℤ) : ℝ)| = (n : ℝ) + 1 := by
        push_cast
        rw [abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)]
      rw [h1]
      apply pow_le_pow_left₀ (by positivity)
      exact inv_anti₀ (by positivity) (by linarith)

theorem wt_zero_le_Wtot : wt 0 ≤ Wtot := by
  rw [Wtot]
  simpa using Summable.sum_le_tsum ({0} : Finset ℤ) (fun i _ => wt_nonneg i) summable_wt

theorem Wtot_pos : 0 < Wtot := lt_of_lt_of_le (wt_pos 0) wt_zero_le_Wtot

/-- The window sum of the weights is at most the total mass. -/
theorem sum_window_wt_le (M : ℕ) :
    ∑ m ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), wt m ≤ Wtot := by
  rw [Wtot]
  exact Summable.sum_le_tsum _ (fun i _ => wt_nonneg i) summable_wt

/-! ## 2. The zero extension of a window vector to `ℤ` -/

/-- Zero extension to `ℤ` of a vector indexed by `Fin (2*M+1)`: index `i` sits at site
`i - M`, and everything outside the window `[-M, M]` is `0`. -/
def ext (M : ℕ) (w : Fin (2 * M + 1) → ℂ) (m : ℤ) : ℂ :=
  if 0 ≤ m + (M : ℤ) then
    (if h2 : (m + (M : ℤ)).toNat < 2 * M + 1 then
      w ⟨(m + (M : ℤ)).toNat, h2⟩ else 0)
  else 0

theorem ext_eq (M : ℕ) (w : Fin (2 * M + 1) → ℂ) (i : Fin (2 * M + 1)) :
    ext M w ((i : ℤ) - (M : ℤ)) = w i := by
  have hmm : ((i : ℤ) - (M : ℤ)) + (M : ℤ) = (i : ℤ) := by ring
  have hge : 0 ≤ ((i : ℤ) - (M : ℤ)) + (M : ℤ) := by
    rw [hmm]; exact_mod_cast Nat.zero_le (i : ℕ)
  have hlt : (((i : ℤ) - (M : ℤ)) + (M : ℤ)).toNat < 2 * M + 1 := by
    rw [Int.toNat_lt hge, hmm]; exact_mod_cast i.isLt
  have hv : (((i : ℤ) - (M : ℤ)) + (M : ℤ)).toNat = (i : ℕ) := by
    rw [hmm, Int.toNat_natCast]
  rw [ext, if_pos hge, dif_pos hlt]
  exact congrArg w (Fin.ext hv)

theorem ext_eq_zero_of_lt (M : ℕ) (w : Fin (2 * M + 1) → ℂ) {m : ℤ} (h : m < -(M : ℤ)) :
    ext M w m = 0 := by
  have hneg : ¬ (0 ≤ m + (M : ℤ)) := by omega
  rw [ext, if_neg hneg]

theorem ext_eq_zero_of_gt (M : ℕ) (w : Fin (2 * M + 1) → ℂ) {m : ℤ} (h : (M : ℤ) < m) :
    ext M w m = 0 := by
  have hge : 0 ≤ m + (M : ℤ) := by omega
  have hnot : ¬ ((m + (M : ℤ)).toNat < 2 * M + 1) := by
    rw [Int.toNat_lt hge]; omega
  rw [ext, if_pos hge, dif_neg hnot]

/-- At site `(i:ℤ) - M + 1`: the neighbouring index, or `0` at the right boundary. -/
theorem ext_succ (M : ℕ) (w : Fin (2 * M + 1) → ℂ) (i : Fin (2 * M + 1)) :
    ext M w (((i : ℤ) - (M : ℤ)) + 1) =
      (if h : (i : ℕ) + 1 < 2 * M + 1 then w ⟨(i : ℕ) + 1, h⟩ else 0) := by
  by_cases h : (i : ℕ) + 1 < 2 * M + 1
  · rw [dif_pos h]
    have hkey : (((i : ℤ) - (M : ℤ)) + 1)
        = (((⟨(i : ℕ) + 1, h⟩ : Fin (2 * M + 1)) : ℤ) - (M : ℤ)) := by
      push_cast; ring
    rw [hkey]
    exact ext_eq M w _
  · rw [dif_neg h]
    have hi : (i : ℕ) = 2 * M := by omega
    have hkey : (((i : ℤ) - (M : ℤ)) + 1) = (M : ℤ) + 1 := by push_cast [hi]; ring
    rw [hkey]
    exact ext_eq_zero_of_gt M w (by omega)

/-- At site `(i:ℤ) - M - 1`: the neighbouring index, or `0` at the left boundary. -/
theorem ext_pred (M : ℕ) (w : Fin (2 * M + 1) → ℂ) (i : Fin (2 * M + 1)) :
    ext M w (((i : ℤ) - (M : ℤ)) - 1) =
      (if h : 0 < (i : ℕ) then w ⟨(i : ℕ) - 1, by omega⟩ else 0) := by
  by_cases h : 0 < (i : ℕ)
  · rw [dif_pos h]
    have hkey : (((i : ℤ) - (M : ℤ)) - 1)
        = (((⟨(i : ℕ) - 1, by omega⟩ : Fin (2 * M + 1)) : ℤ) - (M : ℤ)) := by
      push_cast; omega
    rw [hkey]
    exact ext_eq M w _
  · rw [dif_neg h]
    have hi : (i : ℕ) = 0 := by omega
    have hkey : (((i : ℤ) - (M : ℤ)) - 1) = -(M : ℤ) - 1 := by push_cast [hi]; ring
    rw [hkey]
    exact ext_eq_zero_of_lt M w (by omega)

/-! ## 3. The Dirichlet truncation to the window `[-M, M]` -/

/-- The Dirichlet truncation of the almost Mathieu operator to the window `[-M, M]` of
`2*M+1` sites: the symmetric tridiagonal matrix with diagonal `amoPot θ` and off-diagonal
`1`.  Its index `i` corresponds to site `i - M`. -/
def winMat (M : ℕ) (α lam θ : ℝ) : Matrix (Fin (2 * M + 1)) (Fin (2 * M + 1)) ℂ :=
  Work.TMC16Core.dirMat α lam (θ - (M : ℝ) * α) 0 (2 * M + 1)

/-- The restriction of `φ : ℓ²(ℤ)` to the window `[-M, M]`, as a vector in
`EuclideanSpace ℂ (Fin (2*M+1))`. -/
def winVec (M : ℕ) (φ : EllTwo) : EuclideanSpace ℂ (Fin (2 * M + 1)) :=
  WithLp.toLp 2 (fun i : Fin (2 * M + 1) => φ ((i : ℤ) - (M : ℤ)))

end Work.TMComp.Schnol
