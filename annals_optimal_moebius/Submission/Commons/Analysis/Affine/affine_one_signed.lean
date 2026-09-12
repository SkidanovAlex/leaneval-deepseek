import Mathlib.Analysis.Normed.Order.Lattice

namespace Commons.Analysis.Affine

/-- If the affine function `u ↦ A + B * u` does not vanish on the open interval `(0, 1)`,
then it has constant sign there: it is either everywhere positive or everywhere negative. -/
lemma affine_one_signed {A B : ℝ}
    (h : ∀ u ∈ Set.Ioo (0 : ℝ) 1, A + B * u ≠ 0) :
    (∀ u ∈ Set.Ioo (0 : ℝ) 1, 0 < A + B * u) ∨
      (∀ u ∈ Set.Ioo (0 : ℝ) 1, A + B * u < 0) := by
  have hcont : ContinuousOn (fun u : ℝ => A + B * u) (Set.Ioo (0 : ℝ) 1) := by
    fun_prop
  -- No point of `(0,1)` is negative while another is positive: by the intermediate value
  -- theorem the segment joining them would have to hit a zero, contradicting `h`.
  have key : ∀ u ∈ Set.Ioo (0 : ℝ) 1, ∀ v ∈ Set.Ioo (0 : ℝ) 1,
      ¬ (A + B * u < 0 ∧ 0 < A + B * v) := by
    intro u hu v hv hsign
    have hsurj := ContinuousOn.surjOn_Icc hcont hu hv
    have h0 : (0 : ℝ) ∈ Set.Icc (A + B * u) (A + B * v) :=
      ⟨le_of_lt hsign.1, le_of_lt hsign.2⟩
    obtain ⟨w, hw, hw0⟩ := hsurj h0
    exact h w hw hw0
  by_cases hpos : ∃ u ∈ Set.Ioo (0 : ℝ) 1, 0 < A + B * u
  · left
    intro u hu
    by_contra hle
    push Not at hle
    have hlt : A + B * u < 0 := lt_of_le_of_ne hle (h u hu)
    obtain ⟨v, hv, hvpos⟩ := hpos
    exact key u hu v hv ⟨hlt, hvpos⟩
  · right
    intro u hu
    push Not at hpos
    have hle : A + B * u ≤ 0 := hpos u hu
    exact lt_of_le_of_ne hle (h u hu)

end Commons.Analysis.Affine