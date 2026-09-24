import Mathlib
import Submission.Work.GM.S3.hhat_defs
import Submission.Commons.Analysis.Calculus.smooth_bump_support_Icc_deriv_bounds

/-!
# All iterated derivatives of `w²` are bounded

`w2C u = w(u)²` is `C^∞` and compactly supported (its support is contained in `[1,2]`),
so each of its iterated derivatives is a continuous function with compact support, hence
bounded.  The work is done by
`Commons.Analysis.Calculus.exists_bound_iteratedDeriv_of_hasCompactSupport_smooth`, applied
to the *real* function `u ↦ w(u)²`; the complex function `w2C` is the coercion of it, and
`iteratedDeriv_ofReal_comp` transfers derivatives across the coercion.
-/

namespace Work.GM.S3

open Submission.LargeValues

theorem w2C_iteratedDeriv_bound (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k ≤ j, ∀ x : ℝ, ‖iteratedDeriv k w2C x‖ ≤ C := by
  -- The real function whose coercion is `w2C`.
  let g : ℝ → ℝ := fun u => bumpW u ^ 2
  have hg_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g := bumpW_contDiff.pow 2
  have hg_cs : HasCompactSupport g := by
    refine HasCompactSupport.intro (K := Set.Icc (1 : ℝ) 2) isCompact_Icc (fun x hx => ?_)
    show bumpW x ^ 2 = 0
    rw [bumpW_eq_zero_of_notMem hx]
    norm_num
  -- Bounds for the individual iterated derivatives of `g`.
  have hb : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |iteratedDeriv k g x| ≤ C :=
    Commons.Analysis.Calculus.exists_bound_iteratedDeriv_of_hasCompactSupport_smooth
      hg_smooth hg_cs
  choose Ck hCk using hb
  refine ⟨∑ k ∈ Finset.range (j + 1), Ck k, Finset.sum_nonneg (fun k _ => (hCk k).1), ?_⟩
  intro k hk x
  have hmem : k ∈ Finset.range (j + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hk)
  have hle : Ck k ≤ ∑ i ∈ Finset.range (j + 1), Ck i :=
    Finset.single_le_sum (fun i _ => (hCk i).1) hmem
  -- `w2C` is the coercion of `g`, so its iterated derivatives are those of `g`.
  have hw2C : w2C = fun y : ℝ => ((g y : ℝ) : ℂ) := by
    funext y
    rw [w2C_eq]
  have hiter : iteratedDeriv k w2C = fun y : ℝ => ((iteratedDeriv k g y : ℝ) : ℂ) := by
    rw [hw2C]
    exact iteratedDeriv_ofReal_comp k g
  have hnorm : ‖iteratedDeriv k w2C x‖ = |iteratedDeriv k g x| := by
    rw [hiter]
    simp [Complex.norm_real, Real.norm_eq_abs]
  rw [hnorm]
  exact ((hCk k).2 x).trans hle

end Work.GM.S3
