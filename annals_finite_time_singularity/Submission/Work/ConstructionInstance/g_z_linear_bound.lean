import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.ConstructionInstance.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Set Filter
open scoped Topology

namespace Work.ConstructionInstance

/-- **Linear bound for the modulation `g` near `z = 0`.**

`g` is `C²` on the open rectangle `(-1,∞) × (-1, π/2+1)` and vanishes on the line `z = 0`
(`hquad0`).  Then `g` is dominated by a linear function of `z` on the whole strip
`z ∈ [0,1]`, `θ ∈ [0,π/2]`.

Proof.  On the compact box `Q = [0,1] × [0,π/2]`, which is contained in the open set on which
`g` is `C²`, the partial derivative `φ(z,θ) = ∂_z g(z,θ)` — realised as
`(fderiv ℝ (uncurry g) (z,θ)) (1,0)` — is continuous, hence bounded by some `B ≥ 0`.  For each
`θ`, the mean-value inequality applied to the slice `z ↦ g z θ` on `[0,z]` with `g 0 θ = 0`
gives `|g z θ| ≤ B z`. -/
theorem g_z_linear_bound {g : ℝ → ℝ → ℝ} (hquad0 : ∀ θ : ℝ, g 0 θ = 0)
    (hsm : ContDiffOn ℝ 2 (Function.uncurry g)
      (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (Real.pi / 2 + 1))) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ θ : ℝ, θ ∈ Work.Spaces.Iθ → ∀ z : ℝ, z ∈ Set.Icc (0:ℝ) 1 →
      |g z θ| ≤ K * z := by
  have hopen : IsOpen (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (Real.pi / 2 + 1) : Set (ℝ × ℝ)) :=
    isOpen_Ioi.prod isOpen_Ioo
  have hQU : (Set.Icc (0:ℝ) 1 ×ˢ Work.Spaces.Iθ)
      ⊆ (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (Real.pi / 2 + 1) : Set (ℝ × ℝ)) := by
    rintro p ⟨hz, hθ⟩
    rw [Work.Spaces.Iθ] at hθ
    exact ⟨by rw [Set.mem_Ioi]; linarith [hz.1],
      by constructor <;> linarith [hθ.1, hθ.2, Real.pi_pos]⟩
  have hQcompact : IsCompact (Set.Icc (0:ℝ) 1 ×ˢ Work.Spaces.Iθ) :=
    isCompact_Icc.prod (by rw [Work.Spaces.Iθ]; exact isCompact_Icc)
  have hderiv : ContinuousOn (fderiv ℝ (Function.uncurry g))
      (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (Real.pi / 2 + 1)) :=
    hsm.continuousOn_fderiv_of_isOpen hopen (by norm_num)
  have hφcont : ContinuousOn
      (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry g) p) (1, 0))
      (Set.Icc (0:ℝ) 1 ×ˢ Work.Spaces.Iθ) := by
    have hcc : ContinuousOn (fun _ : ℝ × ℝ => ((1:ℝ), (0:ℝ)))
        (Set.Icc (0:ℝ) 1 ×ˢ Work.Spaces.Iθ) := continuousOn_const
    exact (hderiv.mono hQU).clm_apply hcc
  obtain ⟨B, hB⟩ := hQcompact.exists_bound_of_continuousOn hφcont
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  intro θ hθ z hz
  have hderivAt : ∀ x ∈ Set.Icc (0:ℝ) z,
      HasDerivWithinAt (fun y => g y θ) ((fderiv ℝ (Function.uncurry g) (x, θ)) (1, 0))
        (Set.Icc (0:ℝ) z) x := by
    intro x hx
    have hx0 : (0:ℝ) ≤ x := hx.1
    have hx1 : x ≤ 1 := le_trans hx.2 hz.2
    have hxU : (x, θ) ∈ (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (Real.pi / 2 + 1) : Set (ℝ × ℝ)) :=
      hQU ⟨⟨hx0, hx1⟩, hθ⟩
    have hd : DifferentiableAt ℝ (Function.uncurry g) (x, θ) :=
      (hsm.differentiableOn (by norm_num)).differentiableAt (hopen.mem_nhds hxU)
    have hcomp : HasFDerivAt ((Function.uncurry g) ∘ (fun y : ℝ => (y, θ)))
        ((fderiv ℝ (Function.uncurry g) (x, θ)) ∘SL (ContinuousLinearMap.inl ℝ ℝ ℝ)) x :=
      hd.hasFDerivAt.comp x (hasFDerivAt_prodMk_left x θ)
    have h1 : HasDerivAt ((Function.uncurry g) ∘ (fun y : ℝ => (y, θ)))
        ((fderiv ℝ (Function.uncurry g) (x, θ)) (1, 0)) x := by
      simpa [ContinuousLinearMap.inl_apply] using hcomp.hasDerivAt
    exact h1.hasDerivWithinAt
  have hbound : ∀ x ∈ Set.Ico (0:ℝ) z,
      ‖(fderiv ℝ (Function.uncurry g) (x, θ)) (1, 0)‖ ≤ max B 0 := by
    intro x hx
    have hx0 : (0:ℝ) ≤ x := hx.1
    have hx1 : x ≤ 1 := le_trans (le_of_lt hx.2) hz.2
    have hmem : (x, θ) ∈ (Set.Icc (0:ℝ) 1 ×ˢ Work.Spaces.Iθ) := ⟨⟨hx0, hx1⟩, hθ⟩
    exact le_trans (hB _ hmem) (le_max_left _ _)
  have hMVT := norm_image_sub_le_of_norm_deriv_le_segment'
      (f := fun y => g y θ)
      (f' := fun x => (fderiv ℝ (Function.uncurry g) (x, θ)) (1, 0))
      (a := 0) (b := z) (C := max B 0) hderivAt hbound
  have hzmem : z ∈ Set.Icc (0:ℝ) z := ⟨hz.1, le_rfl⟩
  have hfin := hMVT z hzmem
  rw [hquad0 θ, sub_zero, sub_zero, Real.norm_eq_abs] at hfin
  exact hfin

end Work.ConstructionInstance
