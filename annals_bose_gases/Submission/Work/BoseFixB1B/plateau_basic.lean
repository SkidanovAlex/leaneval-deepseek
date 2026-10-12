import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Submission.Work.BoseFixB1B.cutoffDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1B

open scoped Topology ContDiff

set_option autoImplicit false

theorem plateau_basic {A δ : ℝ} (hδ : 0 < δ) :
    ContDiff ℝ (⊤ : ENat) (plateau A δ) ∧
      (∀ t : ℝ, 0 ≤ plateau A δ t ∧ plateau A δ t ≤ 1) ∧
      (∀ t : ℝ, A ≤ |t| → plateau A δ t = 0) ∧
      (∀ t : ℝ, |t| ≤ A - δ → plateau A δ t = 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- smoothness: a product of two smooth transitions composed with affine maps
    unfold plateau
    exact (Real.smoothTransition.contDiff (n := ⊤)).comp (by fun_prop) |>.mul
      ((Real.smoothTransition.contDiff (n := ⊤)).comp (by fun_prop))
  · -- the range is contained in `[0,1]`
    intro t
    unfold plateau
    refine ⟨mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _), ?_⟩
    calc Real.smoothTransition ((t + A) / δ) * Real.smoothTransition ((A - t) / δ)
        ≤ 1 * 1 := mul_le_mul (Real.smoothTransition.le_one _) (Real.smoothTransition.le_one _)
          (Real.smoothTransition.nonneg _) zero_le_one
      _ = 1 := by ring
  · -- vanishing at `|t| ≥ A`
    intro t ht
    unfold plateau
    rcases le_abs.mp ht with h | h
    · have : (A - t) / δ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (le_of_lt hδ)
      rw [Real.smoothTransition.zero_of_nonpos this, mul_zero]
    · have : (t + A) / δ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (le_of_lt hδ)
      rw [Real.smoothTransition.zero_of_nonpos this, zero_mul]
  · -- both factors are `1` on `|t| ≤ A - δ`
    intro t ht
    have ht1 : -(A - δ) ≤ t := (abs_le.mp ht).1
    have ht2 : t ≤ A - δ := (abs_le.mp ht).2
    unfold plateau
    have h1 : 1 ≤ (t + A) / δ := by rw [le_div_iff₀ hδ]; linarith
    have h2 : 1 ≤ (A - t) / δ := by rw [le_div_iff₀ hδ]; linarith
    rw [Real.smoothTransition.one_of_one_le h1, Real.smoothTransition.one_of_one_le h2, mul_one]

end Work.BoseFixB1B
