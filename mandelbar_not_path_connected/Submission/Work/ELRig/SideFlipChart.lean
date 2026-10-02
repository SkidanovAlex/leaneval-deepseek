import Mathlib
import Submission.Work.ELRig.CylLift
import Submission.Work.ELRig.CylSides
import Submission.Work.ELRig.Defs
import Submission.Work.ELRig.Sides
import Submission.Work.ELRig.rayPt_iterate
import Submission.Work.ELRig.exists_local_angle_at_lift
import Submission.Work.Top.mem_paramRay_extAngle
import Submission.Work.ELTop.Defs
import Submission.Work.ELTop.paramRay_subset_pairSide
import Submission.Work.ELTop.paramRay_subset_pairSideNear

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELRig

open Classical Filter Set
open scoped Topology

variable {c : ℂ} {d : Work.EL.RootParabolic c}
variable {fl : Work.EL.ParabolicFlower (Work.EL.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) d.z₁}
variable {L : Work.ELRig.RayCylLift d fl}
variable {P : Work.EL.CoPair d.hN}
variable {s₀ : ℝ}

/-- The **straightening chart** of the ray `R(α₁)` at the point `p = L.γ₁ s₀`: the Böttcher value
of `Ψ w`, normalised by its value at `p`.  The Böttcher image of the ray `R(α₁)` is the straight
positive real ray and `p` is sent to `1`; the two sides of the ray correspond to the upper and the
lower half-plane in this chart. -/
noncomputable def sideFlipChart (c : ℂ) (d : Work.EL.RootParabolic c)
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) d.z₁)
    (L : Work.ELRig.RayCylLift d fl) (s₀ : ℝ) : ℂ → ℂ :=
  fun w => Work.EL.dynPhi c d.φ (fl.Ψ w) /
    Work.Top.NakaneData.rayPoint Work.EL.alpha1 (L.τ s₀)

@[simp] theorem sideFlipChart_apply (w : ℂ) :
    sideFlipChart c d fl L s₀ w = Work.EL.dynPhi c d.φ (fl.Ψ w) /
      Work.Top.NakaneData.rayPoint Work.EL.alpha1 (L.τ s₀) := rfl

theorem rayPoint_alpha1_ne_zero : Work.Top.NakaneData.rayPoint Work.EL.alpha1 (L.τ s₀) ≠ 0 := by
  rw [Work.Top.NakaneData.rayPoint]
  have ht : ((L.τ s₀ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_trans zero_lt_one (L.hτ1 s₀)) : L.τ s₀ ≠ 0)
  exact mul_ne_zero ht (Complex.exp_ne_zero _)

/-- On the lift of the ray `α₁`, the chart is real and positive: it is the level ratio. -/
theorem sideFlipChart_eq_ofReal (s : ℝ) :
    sideFlipChart c d fl L s₀ (L.γ₁ s) = (L.τ s / L.τ s₀ : ℝ) := by
  rw [sideFlipChart_apply, L.hΨ₁ s, Work.Top.NakaneData.Phi_rayPt d.hN (L.hτ1 s)]
  rw [Work.Top.NakaneData.rayPoint, Work.Top.NakaneData.rayPoint]
  rw [mul_div_mul_right _ _ (Complex.exp_ne_zero _)]
  exact (Complex.ofReal_div (L.τ s) (L.τ s₀)).symm

theorem sideFlipChart_at_p : sideFlipChart c d fl L s₀ (L.γ₁ s₀) = 1 := by
  have h := sideFlipChart_eq_ofReal (c := c) (d := d) (fl := fl) (L := L) (s₀ := s₀) s₀
  rw [h, div_self (ne_of_gt (lt_trans zero_lt_one (L.hτ1 s₀)))]
  exact Complex.ofReal_one

/-- The dynamical Böttcher coordinate is continuous off the filled Julia set. -/
theorem continuousOn_dynPhi : ContinuousOn (Work.EL.dynPhi c d.φ) (Work.EL.K c)ᶜ := by
  rw [continuousOn_iff_continuous_domRestrict]
  have h : (Set.domRestrict (Work.EL.K c)ᶜ (Work.EL.dynPhi c d.φ))
      = fun z => ((d.hN.e z : Work.Top.exteriorDisc) : ℂ) := by
    funext z
    exact d.hN.he z
  rw [h]
  exact continuous_subtype_val.comp d.hN.e.continuous

/-- The chart is continuous at `p`. -/
theorem sideFlipChart_continuousAt :
    ContinuousAt (sideFlipChart c d fl L s₀) (L.γ₁ s₀) := by
  have hq : fl.Ψ (L.γ₁ s₀) ∉ Work.EL.K c := by
    rw [L.hΨ₁ s₀]; exact Work.EL.rayPt_notMem_K d.hN (L.hτ1 s₀)
  have h1 : ContinuousAt (Work.EL.dynPhi c d.φ) (fl.Ψ (L.γ₁ s₀)) :=
    (continuousOn_dynPhi (c := c) (d := d)).continuousAt
      ((Work.ParamRays.isClosed_filledJulia c).isOpen_compl.mem_nhds hq)
  exact (h1.comp fl.Ψ_diff.continuous.continuousAt).div_const _


/-- The chart is injective where `Ψ` is injective and lands outside `K c`. -/
theorem sideFlipChart_injOn :
    Set.InjOn (sideFlipChart c d fl L s₀)
      {w : ℂ | w.re < -L.R ∧ fl.Ψ w ∉ Work.EL.K c} := by
  intro a ha b hb hab
  have h : fl.Ψ a = fl.Ψ b := by
    have h2 : Work.EL.dynPhi c d.φ (fl.Ψ a) = Work.EL.dynPhi c d.φ (fl.Ψ b) := by
      have := congrArg (fun z => z * Work.Top.NakaneData.rayPoint Work.EL.alpha1 (L.τ s₀)) hab
      simpa only [sideFlipChart_apply, div_mul_cancel₀ _ rayPoint_alpha1_ne_zero] using this
    exact d.hN.injOn_Phi ha.2 hb.2 h2
  exact L.hinj ha.1 hb.1 h


/-- Some ball around `p = L.γ₁ s₀` on which `Ψ` is injective and lands outside `K c`, and which is
contained in the far-left half plane. -/
theorem exists_ball_sideFlip (hre : (L.γ₁ s₀).re < -L.R) :
    ∃ ρ > 0, Metric.ball (L.γ₁ s₀) ρ ⊆
      {w : ℂ | w.re < -L.R ∧ fl.Ψ w ∉ Work.EL.K c} := by
  have hq : fl.Ψ (L.γ₁ s₀) ∉ Work.EL.K c := by
    rw [L.hΨ₁ s₀]; exact Work.EL.rayPt_notMem_K d.hN (L.hτ1 s₀)
  have h1 : {w : ℂ | fl.Ψ w ∉ Work.EL.K c} ∈ nhds (L.γ₁ s₀) :=
    (fl.Ψ_diff.continuous.continuousAt).preimage_mem_nhds
      ((Work.ParamRays.isClosed_filledJulia c).isOpen_compl.mem_nhds hq)
  have h2 : {w : ℂ | w.re < -L.R} ∈ nhds (L.γ₁ s₀) :=
    (isOpen_lt Complex.continuous_re continuous_const).mem_nhds hre
  obtain ⟨ρ, hρ, hsub⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem h1 h2)
  exact ⟨ρ, hρ, fun w hw => ⟨(hsub hw).2, (hsub hw).1⟩⟩

end Work.ELRig
