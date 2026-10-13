import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Elliptic.power_hardy_bounds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Elliptic

/-- A `C¹` function on `[0, π/2]` vanishing at both endpoints satisfies a bound of the
form `|f θ| ≤ C * min θ (π/2 - θ)` with the same constant `C` bounding the derivative.
The constant is the maximum of `‖derivWithin f [0, π/2]‖`, which is finite because the
one-sided derivative is continuous on the compact interval. -/
theorem contDiffOn_one_bounds {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (Set.Icc 0 (Real.pi / 2))) (h0 : f 0 = 0)
    (hpi : f (Real.pi / 2) = 0) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ θ ∈ Set.Icc 0 (Real.pi / 2), |f θ| ≤ C * min θ (Real.pi / 2 - θ)) ∧
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), ‖deriv f θ‖ ≤ C) := by
  have hpos : (0 : ℝ) < Real.pi / 2 := by positivity
  have hUniq : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) (Real.pi / 2)) := uniqueDiffOn_Icc hpos
  have hcont : ContinuousOn (derivWithin f (Set.Icc (0 : ℝ) (Real.pi / 2)))
      (Set.Icc (0 : ℝ) (Real.pi / 2)) := hf.continuousOn_derivWithin hUniq le_rfl
  obtain ⟨x₀, hx₀, hmax⟩ :=
    isCompact_Icc.exists_isMaxOn ⟨0, ⟨le_rfl, hpos.le⟩⟩ hcont.norm
  let M : ℝ := ‖derivWithin f (Set.Icc (0 : ℝ) (Real.pi / 2)) x₀‖
  have hMnonneg : 0 ≤ M := norm_nonneg _
  have hderiv : ∀ x ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      HasDerivWithinAt f (derivWithin f (Set.Icc (0 : ℝ) (Real.pi / 2)) x)
        (Set.Icc (0 : ℝ) (Real.pi / 2)) x := by
    intro x hx
    exact ((hf.contDiffWithinAt hx).differentiableWithinAt one_ne_zero).hasDerivWithinAt
  have hsub : ∀ {a b : ℝ}, a ∈ Set.Icc (0 : ℝ) (Real.pi / 2) →
      b ∈ Set.Icc (0 : ℝ) (Real.pi / 2) →
      Set.Icc a b ⊆ Set.Icc (0 : ℝ) (Real.pi / 2) := by
    intro a b ha hb
    exact Set.Icc_subset_Icc ha.1 hb.2
  have key : ∀ a b : ℝ, a ∈ Set.Icc (0 : ℝ) (Real.pi / 2) →
      b ∈ Set.Icc (0 : ℝ) (Real.pi / 2) → ∀ θ ∈ Set.Icc a b,
      ‖f θ - f a‖ ≤ M * (θ - a) := by
    intro a b ha hb θ hθ
    have hsub' := hsub ha hb
    refine norm_image_sub_le_of_norm_deriv_le_segment'
      (f := f) (f' := fun x => derivWithin f (Set.Icc (0 : ℝ) (Real.pi / 2)) x)
      (a := a) (b := b) (C := M) ?_ ?_ θ hθ
    · intro x hx
      exact (hderiv x (hsub' hx)).mono hsub'
    · intro x hx
      exact hmax (hsub' (Set.Ico_subset_Icc_self hx))
  refine ⟨M, hMnonneg, ?_, ?_⟩
  · intro θ hθ
    rcases le_total θ (Real.pi / 2 - θ) with hle | hle
    · rw [min_eq_left hle]
      have h := key 0 θ ⟨le_rfl, hpos.le⟩ hθ θ ⟨hθ.1, le_rfl⟩
      simpa [h0] using h
    · rw [min_eq_right hle]
      have h := key θ (Real.pi / 2) hθ ⟨hpos.le, le_rfl⟩ (Real.pi / 2) ⟨hθ.2, le_rfl⟩
      simpa [hpi] using h
  · intro θ hθ
    have hnhds : Set.Icc (0 : ℝ) (Real.pi / 2) ∈ nhds θ := Icc_mem_nhds hθ.1 hθ.2
    rw [← derivWithin_of_mem_nhds hnhds]
    exact hmax ⟨hθ.1.le, hθ.2.le⟩

end Work.Elliptic
