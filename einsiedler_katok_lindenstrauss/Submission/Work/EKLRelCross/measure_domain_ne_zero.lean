import Mathlib
import Submission.Work.EKLRelCross.LeafCtor

namespace Work.EKLRelCross

open MeasureTheory

/-- If `μ` gives positive mass to every neighbourhood of `x₀`, and `μ`-a.e. point has trivial
`U`-stabiliser, then any set `Z` containing an open neighbourhood `O ∋ x₀` intersected with the
`U`-free set — hence any superset `Z` of such a `G` — has positive `μ`-mass, in particular
`μ Z ≠ 0`.

Indeed the free set `F` has full `μ`-measure, so `μ (O ∩ F) = μ O > 0`, while
`O ∩ F ⊆ G ⊆ Z`; hence `μ Z ≥ μ (O ∩ F) > 0`. -/
theorem measure_domain_ne_zero {U : Subgroup Work.EKLContract.SL3}
    {μ : MeasureTheory.Measure Work.EKLContract.X3}
    {x₀ : Work.EKLContract.X3}
    (hfree : ∀ᵐ x ∂μ, ∀ u ∈ U, u • x = x → u = 1)
    (hpos : ∀ s : Set Work.EKLContract.X3, IsOpen s → x₀ ∈ s → 0 < μ s)
    {Z G O : Set Work.EKLContract.X3} (hO : IsOpen O) (hxO : x₀ ∈ O)
    (hOG : O ∩ {y : Work.EKLContract.X3 | ∀ u ∈ U, u • y = y → u = 1} ⊆ G)
    (hGZ : G ⊆ Z) :
    μ Z ≠ 0 := by
  -- The `U`-free set.
  set F : Set Work.EKLContract.X3 := {y | ∀ u ∈ U, u • y = y → u = 1} with hF
  -- It is conull.
  have hnull : μ Fᶜ = 0 := by
    have h := (MeasureTheory.ae_iff).1 hfree
    rw [hF]
    simpa only [Set.compl_ofPred] using h
  -- `O ∩ F ⊆ G ⊆ Z`.
  have hsub : O ∩ F ⊆ Z := fun y hy => hGZ (hOG hy)
  -- `μ O ≤ μ (O ∩ F)` since `O \ F` is null.
  have hle : μ O ≤ μ (O ∩ F) := by
    have hsub2 : O ⊆ (O ∩ F) ∪ Fᶜ := by
      intro y hy
      by_cases hyF : y ∈ F
      · exact Or.inl ⟨hy, hyF⟩
      · exact Or.inr hyF
    calc μ O ≤ μ ((O ∩ F) ∪ Fᶜ) := measure_mono hsub2
      _ ≤ μ (O ∩ F) + μ Fᶜ := measure_union_le _ _
      _ = μ (O ∩ F) := by rw [hnull, add_zero]
  -- Hence `0 < μ (O ∩ F)` and therefore `0 < μ Z`.
  have hposOF : 0 < μ (O ∩ F) := lt_of_lt_of_le (hpos O hO hxO) hle
  exact ne_of_gt (lt_of_lt_of_le hposOF (measure_mono hsub))

end Work.EKLRelCross
