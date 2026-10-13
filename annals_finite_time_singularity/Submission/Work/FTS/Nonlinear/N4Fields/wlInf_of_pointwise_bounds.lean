import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.WlInf_terms
import Submission.Work.Spaces.HkAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.N4Fields

theorem wlInf_of_pointwise_bounds {α B : ℝ} {h : ℝ → ℝ → ℝ} (hB : 0 ≤ B)
    (hr : ∀ k : ℕ, k ≤ 4 → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |(z + 1) ^ k * Work.Spaces.pzIter k h z θ| ≤ B)
    (ht : ∀ j k : ℕ, 1 ≤ j → k + j ≤ 4 → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |(z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter j h) z θ
        * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))| ≤ B) :
    Work.Spaces.WlInfMem α 4 h ∧ Work.Spaces.WlInf α 4 h ≤ 30 * B := by
  constructor
  · -- membership: every supremum occurring in `WlInf` is bounded by `B`
    refine ⟨fun k _ => ⟨B, fun y hy => ?_⟩, fun j _ k _ hj hjk => ⟨B, fun y hy => ?_⟩⟩
    · rcases hy with ⟨z, hz, θ, hθ, rfl⟩
      exact hr k (by omega) z hz θ hθ
    · rcases hy with ⟨z, hz, θ, hθ, rfl⟩
      exact ht j k hj hjk z hz θ hθ
  · -- every one of the `15 ≤ 25` summands is bounded by `B`
    have hzsum : (∑ k ∈ Finset.range 5, Work.Spaces.supAbs (fun z θ =>
        (z + 1) ^ k * Work.Spaces.pzIter k h z θ))
        ≤ ∑ k ∈ Finset.range 5, B := by
      apply Finset.sum_le_sum
      intro k hk
      exact Work.Spaces.supAbs_le fun z hz θ hθ =>
        hr k (by have := Finset.mem_range.mp hk; omega) z hz θ hθ
    have hmsum : (∑ j ∈ Finset.range 5, ∑ k ∈ Finset.range 5,
        (if 1 ≤ j ∧ k + j ≤ 4 then Work.Spaces.supAbs (fun z θ =>
          (z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter j h) z θ
            * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) else 0))
        ≤ ∑ j ∈ Finset.range 5, ∑ k ∈ Finset.range 5, B := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro k _
      split_ifs with hc
      · exact Work.Spaces.supAbs_le fun z hz θ hθ => ht j k hc.1 hc.2 z hz θ hθ
      · exact hB
    have hB5 : (∑ _k ∈ Finset.range 5, B) = 5 * B := by
      simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hB25 : (∑ _j ∈ Finset.range 5, ∑ _k ∈ Finset.range 5, B) = 25 * B := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring
    calc Work.Spaces.WlInf α 4 h
        = (∑ k ∈ Finset.range 5, Work.Spaces.supAbs (fun z θ =>
              (z + 1) ^ k * Work.Spaces.pzIter k h z θ))
          + ∑ j ∈ Finset.range 5, ∑ k ∈ Finset.range 5,
              (if 1 ≤ j ∧ k + j ≤ 4 then Work.Spaces.supAbs (fun z θ =>
                (z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter j h) z θ
                  * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) else 0) := rfl
      _ ≤ (∑ _k ∈ Finset.range 5, B) + ∑ _j ∈ Finset.range 5, ∑ _k ∈ Finset.range 5, B :=
          add_le_add hzsum hmsum
      _ = 5 * B + 25 * B := by rw [hB25, hB5]
      _ = 30 * B := by ring

end Work.FTS.Nonlinear.N4Fields
