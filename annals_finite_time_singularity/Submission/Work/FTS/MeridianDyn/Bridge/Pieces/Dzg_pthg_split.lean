import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.MeridianDyn.Defs
import Submission.Work.FTS.Galerkin.Defs
import Submission.Work.Construction.Basic
import Submission.Work.Stability.PthFstarAdd
import Submission.Work.Stability.PzFstarAdd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

namespace Work.FTS.MeridianDyn.Bridge.Pieces

/-- The joint interior-smoothness hypothesis of `Work.FTS.Galerkin.RegPkg.smooth` makes the
`z`-slice `z' ↦ g z' θ τ` differentiable at `z`, for `(z,θ)` in the open quadrant and
`τ > -1`. -/
theorem differentiableAt_slice_z_of_smooth {g : Work.FTS.Galerkin.Fam}
    (hs : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2) ×ˢ Set.Ioi (-1 : ℝ)))
    {z θ τ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) (hτ : -1 < τ) :
    DifferentiableAt ℝ (fun z' => g z' θ τ) z := by
  have hV : IsOpen (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2) ×ˢ Set.Ioi (-1 : ℝ) :
      Set (ℝ × ℝ × ℝ)) := isOpen_Ioi.prod (isOpen_Ioo.prod isOpen_Ioi)
  have hmem : (z, θ, τ) ∈ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2) ×ˢ
      Set.Ioi (-1 : ℝ) : Set (ℝ × ℝ × ℝ)) := ⟨hz, hθ, hτ⟩
  have hcd : ContDiffAt ℝ 1 (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2) (z, θ, τ) :=
    ((contDiffOn_infty.mp hs) 1).contDiffAt (hV.mem_nhds hmem)
  have hinner : DifferentiableAt ℝ (fun z' : ℝ => (z', θ, τ)) z := by fun_prop
  have hout := hcd.differentiableAt (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  have := hout.comp z hinner
  simpa [Function.comp_def] using this

/-- The joint interior-smoothness hypothesis of `Work.FTS.Galerkin.RegPkg.smooth` makes the
`θ`-slice `θ' ↦ g z θ' τ` differentiable at `θ`, for `(z,θ)` in the open quadrant and
`τ > -1`. -/
theorem differentiableAt_slice_theta_of_smooth {g : Work.FTS.Galerkin.Fam}
    (hs : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2) ×ˢ Set.Ioi (-1 : ℝ)))
    {z θ τ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) (hτ : -1 < τ) :
    DifferentiableAt ℝ (fun θ' => g z θ' τ) θ := by
  have hV : IsOpen (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2) ×ˢ Set.Ioi (-1 : ℝ) :
      Set (ℝ × ℝ × ℝ)) := isOpen_Ioi.prod (isOpen_Ioo.prod isOpen_Ioi)
  have hmem : (z, θ, τ) ∈ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2) ×ˢ
      Set.Ioi (-1 : ℝ) : Set (ℝ × ℝ × ℝ)) := ⟨hz, hθ, hτ⟩
  have hcd : ContDiffAt ℝ 1 (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2) (z, θ, τ) :=
    ((contDiffOn_infty.mp hs) 1).contDiffAt (hV.mem_nhds hmem)
  have hinner : DifferentiableAt ℝ (fun θ' : ℝ => (z, θ', τ)) θ := by fun_prop
  have hout := hcd.differentiableAt (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  have := hout.comp θ hinner
  simpa [Function.comp_def] using this

theorem Dzg_pthg_split {α : ℝ} {g : Work.FTS.MeridianDyn.Fam}
    (hreg : Work.FTS.Galerkin.RegPkg α g) :
    (∀ z θ τ : ℝ, (z, θ) ∈ Work.Construction.Qd → 0 < τ →
        Work.Spaces.Dz (Work.Construction.Ftau α g τ) z θ
          = Work.Spaces.Dz (Work.Construction.Fstar α) z θ
            + Work.Spaces.Dz (Work.FTS.Galerkin.slice g τ) z θ)
      ∧ (∀ z θ τ : ℝ, (z, θ) ∈ Work.Construction.Qd → 0 < τ →
        Work.Spaces.pth (Work.Construction.Ftau α g τ) z θ
          = Work.Spaces.pth (Work.Construction.Fstar α) z θ
            + Work.Spaces.pth (Work.FTS.Galerkin.slice g τ) z θ) := by
  constructor
  · intro z θ τ hQd hτ
    obtain ⟨hz, hθ⟩ := hQd
    have hz0 : 0 < z := hz
    have hθ0 : θ ∈ Set.Ioo (0 : ℝ) (π / 2) := hθ
    have hτ' : -1 < τ := by linarith
    have hF : DifferentiableAt ℝ (fun z' => Work.Construction.Fstar α z' θ) z :=
      Work.Stability.differentiableAt_Fstar_slice α θ z (by linarith)
    have hg : DifferentiableAt ℝ (fun z' => g z' θ τ) z :=
      differentiableAt_slice_z_of_smooth hreg.smooth hz0 hθ0 hτ'
    show z * deriv (fun z' => Work.Construction.Fstar α z' θ + g z' θ τ) z
        = z * deriv (fun z' => Work.Construction.Fstar α z' θ) z
          + z * deriv (fun z' => g z' θ τ) z
    rw [show (fun z' => Work.Construction.Fstar α z' θ + g z' θ τ)
          = (fun z' => Work.Construction.Fstar α z' θ) + (fun z' => g z' θ τ) from rfl,
        deriv_add hF hg]
    ring
  · intro z θ τ hQd hτ
    obtain ⟨hz, hθ⟩ := hQd
    have hz0 : 0 < z := hz
    have hθ0 : θ ∈ Set.Ioo (0 : ℝ) (π / 2) := hθ
    have hτ' : -1 < τ := by linarith
    have hF : DifferentiableAt ℝ (fun θ' => Work.Construction.Fstar α z θ') θ :=
      Work.Stability.differentiableAt_Fstar_slice_theta α z θ hθ0
    have hg : DifferentiableAt ℝ (fun θ' => g z θ' τ) θ :=
      differentiableAt_slice_theta_of_smooth hreg.smooth hz0 hθ0 hτ'
    show deriv (fun θ' => Work.Construction.Fstar α z θ' + g z θ' τ) θ
        = deriv (fun θ' => Work.Construction.Fstar α z θ') θ
          + deriv (fun θ' => g z θ' τ) θ
    rw [show (fun θ' => Work.Construction.Fstar α z θ' + g z θ' τ)
          = (fun θ' => Work.Construction.Fstar α z θ') + (fun θ' => g z θ' τ) from rfl,
        deriv_add hF hg]

end Work.FTS.MeridianDyn.Bridge.Pieces
