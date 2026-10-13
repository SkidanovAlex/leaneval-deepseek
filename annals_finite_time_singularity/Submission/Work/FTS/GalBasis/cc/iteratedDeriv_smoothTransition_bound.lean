import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.GalBasis.cc

/-- `Real.smoothTransition` is `C^∞`, hence each of its first five derivatives is continuous
and therefore bounded on the compact interval `[0,1]`.  Taking the sum of the five bounds (plus
one) gives a single positive constant dominating all of them. -/
theorem iteratedDeriv_smoothTransition_bound : ∃ B : ℝ, 0 < B ∧ ∀ m : ℕ, m ≤ 4 → ∀ u : ℝ,
    u ∈ Set.Icc 0 1 → |iteratedDeriv m Real.smoothTransition u| ≤ B := by
  have hb : ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Set.Icc (0:ℝ) 1,
      |iteratedDeriv m Real.smoothTransition x| ≤ C := by
    intro m
    have hcont : Continuous (iteratedDeriv m Real.smoothTransition) := by
      apply ContDiff.continuous_iteratedDeriv' m
      exact Real.smoothTransition.contDiff
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont.continuousOn
    exact ⟨max C 0, le_max_right _ _, fun x hx => by
      have h := hC x hx
      rw [Real.norm_eq_abs] at h
      exact le_trans h (le_max_left _ _)⟩
  choose C hC0 hC using hb
  refine ⟨(∑ m ∈ Finset.range 5, C m) + 1, ?_, ?_⟩
  · have h : 0 ≤ ∑ m ∈ Finset.range 5, C m := Finset.sum_nonneg (fun i _ => hC0 i)
    linarith
  · intro m hm u hu
    have hm5 : m ∈ Finset.range 5 := Finset.mem_range.2 (by omega)
    have hle : C m ≤ ∑ m ∈ Finset.range 5, C m :=
      Finset.single_le_sum (fun i _ => hC0 i) hm5
    calc |iteratedDeriv m Real.smoothTransition u| ≤ C m := hC m u hu
      _ ≤ ∑ m ∈ Finset.range 5, C m := hle
      _ ≤ ∑ m ∈ Finset.range 5, C m + 1 := le_add_of_nonneg_right zero_le_one

end Work.FTS.GalBasis.cc
