import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Elliptic.DivSinDefs
import Submission.Work.Elliptic.htU_near_pi2

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Elliptic

/-- Endpoint bounds at `θ = 0` for a `C²` function on `[0, π/2]` vanishing at `0`.

The two "compatibility" hypotheses identify the two-sided derivatives on the open interval with
the within-derivatives on the closed interval `[0, π/2]`; these are exactly the quantities that the
uniform estimates in the main theorem are phrased with.  The proof is a mean-value estimate:
`derivWithin f [0,π/2]` is `C¹` on `[0,π/2]` (being the derivative of a `C²` function) and
`iteratedDerivWithin 2 f [0,π/2] = derivWithin (derivWithin f [0,π/2]) [0,π/2]` is its derivative;
both are continuous on the compact interval, hence bounded. -/
theorem htUEndpointBoundsZero (f : ℝ → ℝ) (hf : ContDiffOn ℝ 2 f (Set.Icc 0 (Real.pi / 2))) (h0 : f 0 = 0)
    (hcomp1 : ∀ x ∈ Set.Ioo 0 (Real.pi / 2), deriv f x = iteratedDerivWithin 1 f (Set.Icc 0 (Real.pi / 2)) x)
    (hcomp2 : ∀ x ∈ Set.Ioo 0 (Real.pi / 2),
      deriv (deriv f) x = iteratedDerivWithin 2 f (Set.Icc 0 (Real.pi / 2)) x) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ x ∈ Set.Ioo 0 (Real.pi / 4), |f x| ≤ C * x) ∧
      (∀ x ∈ Set.Ioo 0 (Real.pi / 4), |deriv f x - derivWithin f (Set.Icc 0 (Real.pi / 2)) 0| ≤ C * x) ∧
      (∀ x ∈ Set.Ioo 0 (Real.pi / 4), |deriv (deriv f) x| ≤ C) := by
  have hpos : (0 : ℝ) < Real.pi / 2 := by positivity
  have hpi4 : Real.pi / 4 < Real.pi / 2 := by linarith [Real.pi_pos]
  have hUniq : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) (Real.pi / 2)) := uniqueDiffOn_Icc hpos
  -- `derivWithin f [0,π/2]` is continuous on the compact interval, hence bounded by `M1`.
  have hcontD : ContinuousOn (derivWithin f (Set.Icc 0 (Real.pi / 2))) (Set.Icc 0 (Real.pi / 2)) :=
    hf.continuousOn_derivWithin hUniq (by norm_num)
  obtain ⟨x₁, hx₁, hmax1⟩ :=
    isCompact_Icc.exists_isMaxOn ⟨0, ⟨le_rfl, hpos.le⟩⟩ hcontD.norm
  let M1 : ℝ := ‖derivWithin f (Set.Icc 0 (Real.pi / 2)) x₁‖
  -- `derivWithin f [0,π/2]` is `C¹`, and its derivative `iteratedDerivWithin 2 f [0,π/2]` is
  -- continuous on the compact interval, hence bounded by `M2`.
  have hDc : ContDiffOn ℝ 1 (derivWithin f (Set.Icc 0 (Real.pi / 2))) (Set.Icc 0 (Real.pi / 2)) :=
    hf.derivWithin hUniq (by norm_num)
  have hcontE : ContinuousOn
      (derivWithin (derivWithin f (Set.Icc 0 (Real.pi / 2))) (Set.Icc 0 (Real.pi / 2)))
      (Set.Icc 0 (Real.pi / 2)) := hDc.continuousOn_derivWithin hUniq (by norm_num)
  obtain ⟨x₂, hx₂, hmax2⟩ :=
    isCompact_Icc.exists_isMaxOn ⟨0, ⟨le_rfl, hpos.le⟩⟩ hcontE.norm
  let M2 : ℝ :=
    ‖derivWithin (derivWithin f (Set.Icc 0 (Real.pi / 2))) (Set.Icc 0 (Real.pi / 2)) x₂‖
  let C : ℝ := max M1 M2
  have hC : 0 ≤ C :=
    le_trans (norm_nonneg (derivWithin f (Set.Icc 0 (Real.pi / 2)) x₁)) (le_max_left M1 M2)
  have hEeq : iteratedDerivWithin 2 f (Set.Icc 0 (Real.pi / 2)) =
      derivWithin (derivWithin f (Set.Icc 0 (Real.pi / 2))) (Set.Icc 0 (Real.pi / 2)) := by
    have h := iteratedDerivWithin_succ (n := 1) (f := f) (s := Set.Icc 0 (Real.pi / 2))
    rw [iteratedDerivWithin_one] at h
    exact h
  have key1 : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 4), |f x| ≤ C * x := by
    intro x hx
    have hxs : x ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨hx.1.le, (lt_trans hx.2 hpi4).le⟩
    have hsub : Set.Icc (0 : ℝ) x ⊆ Set.Icc (0 : ℝ) (Real.pi / 2) :=
      Set.Icc_subset_Icc le_rfl hxs.2
    have hfdiff : DifferentiableOn ℝ f (Set.Icc (0 : ℝ) (Real.pi / 2)) :=
      hf.differentiableOn (by norm_num)
    have hderiv : ∀ y ∈ Set.Icc (0 : ℝ) x,
        HasDerivWithinAt f (derivWithin f (Set.Icc 0 (Real.pi / 2)) y) (Set.Icc (0 : ℝ) x) y := by
      intro y hy
      exact ((hfdiff y (hsub hy)).hasDerivWithinAt).mono hsub
    have hbound : ∀ y ∈ Set.Ico (0 : ℝ) x,
        ‖derivWithin f (Set.Icc 0 (Real.pi / 2)) y‖ ≤ C := by
      intro y hy
      have hy_s : y ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := hsub (Set.Ico_subset_Icc_self hy)
      exact le_trans (hmax1 hy_s) (le_max_left M1 M2)
    have hmain := norm_image_sub_le_of_norm_deriv_le_segment'
      (f := f) (f' := fun y => derivWithin f (Set.Icc 0 (Real.pi / 2)) y)
      (a := 0) (b := x) (C := C) hderiv hbound x ⟨hx.1.le, le_rfl⟩
    rw [Real.norm_eq_abs, h0, sub_zero, sub_zero] at hmain
    exact hmain
  have key2 : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 4),
      |deriv f x - derivWithin f (Set.Icc 0 (Real.pi / 2)) 0| ≤ C * x := by
    intro x hx
    have hxpi2 : x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hx.1, lt_trans hx.2 hpi4⟩
    have hxs : x ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨hx.1.le, (lt_trans hx.2 hpi4).le⟩
    have hsub : Set.Icc (0 : ℝ) x ⊆ Set.Icc (0 : ℝ) (Real.pi / 2) :=
      Set.Icc_subset_Icc le_rfl hxs.2
    have hDdiff : DifferentiableOn ℝ (derivWithin f (Set.Icc (0 : ℝ) (Real.pi / 2)))
        (Set.Icc (0 : ℝ) (Real.pi / 2)) := hDc.differentiableOn (by norm_num)
    have hderiv : ∀ y ∈ Set.Icc (0 : ℝ) x,
        HasDerivWithinAt (derivWithin f (Set.Icc 0 (Real.pi / 2)))
          (derivWithin (derivWithin f (Set.Icc 0 (Real.pi / 2))) (Set.Icc 0 (Real.pi / 2)) y)
          (Set.Icc (0 : ℝ) x) y := by
      intro y hy
      exact ((hDdiff y (hsub hy)).hasDerivWithinAt).mono hsub
    have hbound : ∀ y ∈ Set.Ico (0 : ℝ) x,
        ‖derivWithin (derivWithin f (Set.Icc 0 (Real.pi / 2))) (Set.Icc 0 (Real.pi / 2)) y‖ ≤ C := by
      intro y hy
      have hy_s : y ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := hsub (Set.Ico_subset_Icc_self hy)
      exact le_trans (hmax2 hy_s) (le_max_right M1 M2)
    have hmain := norm_image_sub_le_of_norm_deriv_le_segment'
      (f := derivWithin f (Set.Icc 0 (Real.pi / 2)))
      (f' := fun y => derivWithin (derivWithin f (Set.Icc 0 (Real.pi / 2))) (Set.Icc 0 (Real.pi / 2)) y)
      (a := 0) (b := x) (C := C) hderiv hbound x ⟨hx.1.le, le_rfl⟩
    have hcomp1x : deriv f x = derivWithin f (Set.Icc 0 (Real.pi / 2)) x := by
      have h := hcomp1 x hxpi2
      rwa [iteratedDerivWithin_one] at h
    rw [Real.norm_eq_abs, sub_zero] at hmain
    rw [hcomp1x]
    exact hmain
  have key3 : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 4), |deriv (deriv f) x| ≤ C := by
    intro x hx
    have hxpi2 : x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hx.1, lt_trans hx.2 hpi4⟩
    have hxs : x ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨hx.1.le, (lt_trans hx.2 hpi4).le⟩
    have h2 := hcomp2 x hxpi2
    rw [h2, hEeq, ← Real.norm_eq_abs]
    exact le_trans (hmax2 hxs) (le_max_right M1 M2)
  exact ⟨C, hC, key1, key2, key3⟩

end Work.Elliptic
