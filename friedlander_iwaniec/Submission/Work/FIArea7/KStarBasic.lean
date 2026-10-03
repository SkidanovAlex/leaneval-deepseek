/-
# `Submission.Work.FIArea7.KStarBasic` — the fibre decomposition of `K*`

The trivial part of *FI* (22.4): `K∗(N)` is the sum of its fibres `KInnerStar` over the real part
(compare `Work.FIArea7.KLinear_eq_sum_KInner`), each fibre satisfies the trivial bound `≤ 2Rz+1`
(one term per `s`), and `K∗` vanishes when the box is empty.
-/
import Mathlib
import Submission.Work.FIArea7.KStarDefs
import Submission.Work.FIArea7.KSum_bound

set_option autoImplicit false

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The trivial fibre bound for `K∗`: at most one term per `s` in the box. -/
theorem KInnerStar_le_card (Rz : ℤ) (w : GaussianInt) (k : ℤ) (chi : GaussianInt → ℂ) (r : ℤ)
    (hchi : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) :
    ‖KInnerStar Rz w k chi r‖ ≤ ((((2 * Rz + 1).toNat : ℕ)) : ℝ) := by
  have h1 : ‖KInnerStar Rz w k chi r‖
      ≤ ∑ s ∈ Finset.Icc (-Rz) Rz,
          (if Work.FIPlan.IsPrimary (⟨r, s⟩ : GaussianInt) then (1 : ℝ) else 0) := by
    rw [KInnerStar]
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun s _ => ?_))
    by_cases hp : Work.FIPlan.IsPrimary (⟨r, s⟩ : GaussianInt)
    · by_cases hz : Work.FIPlan.GaussCoprime (⟨r, s⟩ : GaussianInt) w
      · rw [if_pos ⟨hp, hz⟩, if_pos hp, norm_mul]
        calc ‖grossenChar chi k (⟨r, s⟩ : GaussianInt)‖ * ‖JKSym (w * (⟨r, s⟩ : GaussianInt))‖
            ≤ 1 * 1 := mul_le_mul (norm_grossenChar_le_one chi k hchi _) (norm_JKSym_le_one _)
                (norm_nonneg _) (by norm_num)
          _ = 1 := by ring
      · rw [if_neg (fun h => hz h.2), if_pos hp, norm_zero]; norm_num
    · rw [if_neg (fun h => hp h.1), if_neg hp, norm_zero]
  refine h1.trans ?_
  calc ∑ s ∈ Finset.Icc (-Rz) Rz,
        (if Work.FIPlan.IsPrimary (⟨r, s⟩ : GaussianInt) then (1 : ℝ) else 0)
      ≤ ∑ _s ∈ Finset.Icc (-Rz) Rz, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro s _
        by_cases hz : Work.FIPlan.IsPrimary (⟨r, s⟩ : GaussianInt) <;> simp [hz]
    _ = ((Finset.Icc (-Rz) Rz).card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ = ((((2 * Rz + 1).toNat : ℕ)) : ℝ) := by
        congr 1
        rw [Int.card_Icc]
        congr 1
        ring

end

end Work.FIArea7
