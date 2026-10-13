import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_RegExport.RXR7.Joint.CLM
import Submission.Work.FTS_RegExport.RXR7.Joint.ProfBasic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Set Filter
open Work.FTS.Galerkin (Fn Fam slice)

namespace Work.FTS_RegExport.RXR7

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! ## §7  Interior differentiability of the profile

At a point of the slab with `τ > 0` the profile agrees locally with `F_* + g`; both parts are
differentiable there (`F_*` is smooth, `g` is jointly `C¹` by `RegPkgMin.c1`), and the coordinates
of the resulting `fderiv` are computed from `hEq` and the algebra `mixed 1 0 = z ∂_z`,
`mixed 0 1 = sin 2θ ∂_θ`. -/

theorem hasFDerivAt_profD_of_pos {α C₀ : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g : Fam} {S : ℝ}
    (hS : 0 < S) (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (hEq : ∀ z θ τ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 < τ → τ ≤ S →
      HasDerivAt (fun s => Prof α g z θ s) (-(K7 α Φs E g z θ τ)) τ) :
    ∀ p : ℝ × ℝ × ℝ, p ∈ R7Slab S → 0 < p.2.2 →
      HasFDerivAt (fun y : ℝ × ℝ × ℝ => Prof α g y.1 y.2.1 y.2.2) (ProfD α Φs E g p) p := by
  intro p hp hτ
  have hz : 0 < p.1 := hp.1
  have hθ0 : 0 < p.2.1 := hp.2.1.1
  have hθ1 : p.2.1 < Real.pi / 2 := hp.2.1.2
  have hτS : p.2.2 ≤ S := hp.2.2.2
  -- the eventual identity with `F_* + g` on the open slab
  have hev : (fun y : ℝ × ℝ × ℝ => Prof α g y.1 y.2.1 y.2.2) =ᶠ[𝓝 p]
      (fun y : ℝ × ℝ × ℝ =>
        Work.Construction.Fstar (Work.FTS.Regularity.pExp α) y.1 y.2.1 + g y.1 y.2.1 y.2.2) := by
    filter_upwards [(isOpen_Ioi.preimage continuous_fst).mem_nhds hz,
      (isOpen_Ioo.preimage (continuous_fst.comp continuous_snd)).mem_nhds ⟨hθ0, hθ1⟩,
      (isOpen_Ioi.preimage (continuous_snd.comp continuous_snd)).mem_nhds hτ]
      with y hy1 hy2 hy3
    exact Prof_eq hy1 hy2.1.le hy2.2.le hy3.le
  have h3 : deriv (fun τ => g p.1 p.2.1 τ) p.2.2 = -(K7 α Φs E g p.1 p.2.1 p.2.2) := by
    have h1 := hEq p.1 p.2.1 p.2.2 hz hθ0 hθ1 hτ hτS
    have hev2 : (fun s => Prof α g p.1 p.2.1 s) =ᶠ[𝓝 p.2.2]
        (fun s => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) p.1 p.2.1
          + g p.1 p.2.1 s) := by
      filter_upwards [(isOpen_Ioi).preimage continuous_id |>.mem_nhds hτ] with s hs
      exact Prof_eq hz hθ0.le hθ1.le hs.le
    have h2 := h1.congr_of_eventuallyEq hev2.symm
    have h4 := (hasDerivAt_const_add_iff
      (c := Work.Construction.Fstar (Work.FTS.Regularity.pExp α) p.1 p.2.1)).mp h2
    rw [h4.deriv]

  -- derivative of the `F_*` part
  have hFstar : HasFDerivAt
      (fun y : ℝ × ℝ × ℝ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) y.1 y.2.1)
      (tripleCLM
        (Work.Spaces.pz (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ)
          p.1 p.2.1)
        (Work.Spaces.pth (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ)
          p.1 p.2.1) 0) p := by
    have hcd : ContDiffAt ℝ 1 (fun y : ℝ × ℝ × ℝ =>
        Work.Construction.Fstar (Work.FTS.Regularity.pExp α) y.1 y.2.1) p := by
      have h1 : ContDiffAt ℝ 1 (fun q : ℝ × ℝ =>
          Work.Construction.Fstar (Work.FTS.Regularity.pExp α) q.1 q.2) (p.1, p.2.1) :=
        Fstar_contDiffAt hz hθ0 hθ1
      have h2 : ContDiffAt ℝ 1 (fun y : ℝ × ℝ × ℝ => (y.1, y.2.1)) p :=
        (p1.prod p2).contDiff.contDiffAt
      exact h1.comp p h2
    have hD := (hcd.differentiableAt one_ne_zero).hasFDerivAt
    have e1 : (fderiv ℝ (fun y : ℝ × ℝ × ℝ =>
          Work.Construction.Fstar (Work.FTS.Regularity.pExp α) y.1 y.2.1) p) (1, 0, 0)
        = Work.Spaces.pz (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ)
            p.1 p.2.1 := by
      rw [fderiv_apply_e1 hD]
      simp only [Work.Spaces.pz]
    have e2 : (fderiv ℝ (fun y : ℝ × ℝ × ℝ =>
          Work.Construction.Fstar (Work.FTS.Regularity.pExp α) y.1 y.2.1) p) (0, 1, 0)
        = Work.Spaces.pth (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ)
            p.1 p.2.1 := by
      rw [fderiv_apply_e2 hD]
      simp only [Work.Spaces.pth]
    have e3 : (fderiv ℝ (fun y : ℝ × ℝ × ℝ =>
          Work.Construction.Fstar (Work.FTS.Regularity.pExp α) y.1 y.2.1) p) (0, 0, 1) = 0 := by
      rw [fderiv_apply_e3 hD]
      simp
    rw [clm_ext_triple e1 e2 e3] at hD
    exact hD
  -- derivative of the `g` part
  have hg : HasFDerivAt (fun y : ℝ × ℝ × ℝ => g y.1 y.2.1 y.2.2)
      (tripleCLM (deriv (fun z => g z p.2.1 p.2.2) p.1)
        (deriv (fun θ => g p.1 θ p.2.2) p.2.1)
        (deriv (fun τ => g p.1 p.2.1 τ) p.2.2)) p := by
    have hopen : (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2) ×ˢ Set.Ioi (0 : ℝ))
        ∈ 𝓝 p := (isOpen_Ioi.prod (isOpen_Ioo.prod isOpen_Ioi)).mem_nhds
      ⟨hz, ⟨hθ0, hθ1⟩, hτ⟩
    have hcd : ContDiffAt ℝ 1 (fun y : ℝ × ℝ × ℝ => g y.1 y.2.1 y.2.2) p :=
      hOK.1.1.c1.contDiffAt hopen
    have hD := (hcd.differentiableAt one_ne_zero).hasFDerivAt
    have e1 : (fderiv ℝ (fun y : ℝ × ℝ × ℝ => g y.1 y.2.1 y.2.2) p) (1, 0, 0)
        = deriv (fun z => g z p.2.1 p.2.2) p.1 := by
      rw [fderiv_apply_e1 hD]
    have e2 : (fderiv ℝ (fun y : ℝ × ℝ × ℝ => g y.1 y.2.1 y.2.2) p) (0, 1, 0)
        = deriv (fun θ => g p.1 θ p.2.2) p.2.1 := by
      rw [fderiv_apply_e2 hD]
    have e3 : (fderiv ℝ (fun y : ℝ × ℝ × ℝ => g y.1 y.2.1 y.2.2) p) (0, 0, 1)
        = -(K7 α Φs E g p.1 p.2.1 p.2.2) := by
      rw [fderiv_apply_e3 hD, h3]
    rw [h3]
    rw [clm_ext_triple e1 e2 e3] at hD
    exact hD
  -- the sum
  have hsum := (hFstar.add hg).congr_of_eventuallyEq hev
  -- identify the two coordinate expressions
  have haz : Work.Spaces.mixed 1 0 (slice g p.2.2) p.1 p.2.1 / p.1
      = deriv (fun z => g z p.2.1 p.2.2) p.1 := by
    rw [mixed_one_zero]
    simp only [Work.Spaces.pz, slice]
    rw [mul_div_cancel_left₀ _ (ne_of_gt hz)]
  have hat : Work.Spaces.mixed 0 1 (slice g p.2.2) p.1 p.2.1 / Real.sin (2 * p.2.1)
      = deriv (fun θ => g p.1 θ p.2.2) p.2.1 := by
    rw [mixed_zero_one]
    simp only [Work.Spaces.pth, slice]
    rw [mul_div_cancel_left₀ _ (sin_two_ne_zero hθ0 hθ1)]
  have hD_eq : tripleCLM
        (Work.Spaces.pz (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ)
          p.1 p.2.1)
        (Work.Spaces.pth (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ)
          p.1 p.2.1) 0
      + tripleCLM (deriv (fun z => g z p.2.1 p.2.2) p.1)
          (deriv (fun θ => g p.1 θ p.2.2) p.2.1)
          (deriv (fun τ => g p.1 p.2.1 τ) p.2.2) = ProfD α Φs E g p := by
    rw [tripleCLM_add, ← haz, ← hat, h3]
    simp only [zero_add]
    rfl
  rw [hD_eq] at hsum
  exact hsum

end Work.FTS_RegExport.RXR7
