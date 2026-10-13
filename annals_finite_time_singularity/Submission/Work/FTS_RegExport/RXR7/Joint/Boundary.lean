import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS_RegExport.RXR7.Joint.CLM
import Submission.Work.FTS_RegExport.RXR7.Joint.ProfBasic
import Submission.Work.FTS_RegExport.RXR7.Support.r7FTC
import Submission.Work.FTS_RegExport.RXR7.Support.hasFDerivWithinAt_of_ftc

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

/-! ## §8  Boundary differentiability of the profile

At a point of the slab with `τ = 0` the `(z,θ)`-part of the derivative is the differential of the
`τ = 0` slice (which is `C⁴` on the open quadrant by `RegPkgMin.c4`), while the `τ`-part is
`-K7`, obtained by the fundamental theorem of calculus from `hEq` (`r7FTC`) plus continuity of
`K7` on the slab.  The assembly is the general lemma `hasFDerivWithinAt_of_ftc`. -/

theorem hasFDerivWithinAt_profD_of_eq_zero {α C₀ : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g : Fam}
    {S : ℝ} (hS : 0 < S) (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (hK7cont : ContinuousOn (fun p : ℝ × ℝ × ℝ => K7 α Φs E g p.1 p.2.1 p.2.2) (R7Slab S))
    (hEq : ∀ z θ τ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 < τ → τ ≤ S →
      HasDerivAt (fun s => Prof α g z θ s) (-(K7 α Φs E g z θ τ)) τ) :
    ∀ p : ℝ × ℝ × ℝ, p ∈ R7Slab S → p.2.2 = 0 →
      HasFDerivWithinAt (fun y : ℝ × ℝ × ℝ => Prof α g y.1 y.2.1 y.2.2)
        (ProfD α Φs E g p) (R7Slab S) p := by
  intro p hp hτ0
  have hz : 0 < p.1 := hp.1
  have hθ0 : 0 < p.2.1 := hp.2.1.1
  have hθ1 : p.2.1 < Real.pi / 2 := hp.2.1.2
  -- the `τ = 0` slice is `C⁴` (hence differentiable) on the open quadrant
  have hsmooth : ContDiffOn ℝ 4 (Function.uncurry (slice g 0)) Work.FTS.EllipticEst.Q0 :=
    hOK.1.1.c4 0 (le_refl 0)
  have hdiff0 : DifferentiableAt ℝ (fun q : ℝ × ℝ => g q.1 q.2 0) (p.1, p.2.1) := by
    have hmem : (p.1, p.2.1) ∈ Work.FTS.EllipticEst.Q0 := ⟨hz, hθ0, hθ1⟩
    exact ((hsmooth.contDiffAt ((isOpen_Ioi.prod isOpen_Ioo).mem_nhds hmem)).differentiableAt
      (by simp))
  have hev0 : (fun q : ℝ × ℝ => Prof α g q.1 q.2 0) =ᶠ[𝓝 (p.1, p.2.1)]
      (fun q : ℝ × ℝ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) q.1 q.2
        + g q.1 q.2 0) := by
    filter_upwards [(isOpen_Ioi.prod isOpen_Ioo).mem_nhds
      (show ((p.1, p.2.1) : ℝ × ℝ) ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2) from
        ⟨hz, hθ0, hθ1⟩)] with q hq
    exact Prof_eq hq.1 hq.2.1.le hq.2.2.le (le_refl 0)
  have hslice : HasFDerivAt (fun q : ℝ × ℝ => Prof α g q.1 q.2 0)
      (pairCLM
        (Work.Spaces.pz (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ)
            p.1 p.2.1
          + Work.Spaces.pz (fun z θ => g z θ 0) p.1 p.2.1)
        (Work.Spaces.pth (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ)
            p.1 p.2.1
          + Work.Spaces.pth (fun z θ => g z θ 0) p.1 p.2.1)) (p.1, p.2.1) := by
    have hFs : HasFDerivAt (fun q : ℝ × ℝ =>
        Work.Construction.Fstar (Work.FTS.Regularity.pExp α) q.1 q.2)
        (pairCLM
          (Work.Spaces.pz (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ)
            p.1 p.2.1)
          (Work.Spaces.pth (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ)
            p.1 p.2.1)) (p.1, p.2.1) := by
      have hD := (Fstar_differentiableAt (α := α) (q := (p.1, p.2.1)) hz hθ0 hθ1).hasFDerivAt
      have e1 : (fderiv ℝ (fun q : ℝ × ℝ =>
            Work.Construction.Fstar (Work.FTS.Regularity.pExp α) q.1 q.2) (p.1, p.2.1)) (1, 0)
          = Work.Spaces.pz (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ)
              p.1 p.2.1 := by
        rw [fderiv_apply_2d_1 hD]
        simp only [Work.Spaces.pz]
      have e2 : (fderiv ℝ (fun q : ℝ × ℝ =>
            Work.Construction.Fstar (Work.FTS.Regularity.pExp α) q.1 q.2) (p.1, p.2.1)) (0, 1)
          = Work.Spaces.pth (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ)
              p.1 p.2.1 := by
        rw [fderiv_apply_2d_2 hD]
        simp only [Work.Spaces.pth]
      rw [clm_ext_pair e1 e2] at hD
      exact hD
    have hGs : HasFDerivAt (fun q : ℝ × ℝ => g q.1 q.2 0)
        (pairCLM (Work.Spaces.pz (fun z θ => g z θ 0) p.1 p.2.1)
          (Work.Spaces.pth (fun z θ => g z θ 0) p.1 p.2.1)) (p.1, p.2.1) := by
      have hD := hdiff0.hasFDerivAt
      have e1 : (fderiv ℝ (fun q : ℝ × ℝ => g q.1 q.2 0) (p.1, p.2.1)) (1, 0)
          = Work.Spaces.pz (fun z θ => g z θ 0) p.1 p.2.1 := by
        rw [fderiv_apply_2d_1 hD]
        simp only [Work.Spaces.pz]
      have e2 : (fderiv ℝ (fun q : ℝ × ℝ => g q.1 q.2 0) (p.1, p.2.1)) (0, 1)
          = Work.Spaces.pth (fun z θ => g z θ 0) p.1 p.2.1 := by
        rw [fderiv_apply_2d_2 hD]
        simp only [Work.Spaces.pth]
      rw [clm_ext_pair e1 e2] at hD
      exact hD
    have hsum := hFs.add hGs
    rw [pairCLM_add] at hsum
    exact hsum.congr_of_eventuallyEq hev0
  -- the CLM of the boundary derivative is `pairCLM (FPz p) (FPt p)`
  have hL0 : pairCLM
        (Work.Spaces.pz (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ)
            p.1 p.2.1
          + Work.Spaces.pz (fun z θ => g z θ 0) p.1 p.2.1)
        (Work.Spaces.pth (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ)
            p.1 p.2.1
          + Work.Spaces.pth (fun z θ => g z θ 0) p.1 p.2.1)
      = pairCLM (FPz α g p) (FPt α g p) := by
    congr 1
    · rw [FPz, hτ0, mixed_one_zero, mul_div_cancel_left₀ _ (ne_of_gt hz)]
      rfl
    · rw [FPt, hτ0, mixed_zero_one, mul_div_cancel_left₀ _ (sin_two_ne_zero hθ0 hθ1)]
      rfl
  have hFD0 : HasFDerivAt (fun q : ℝ × ℝ => Prof α g q.1 q.2 0)
      (pairCLM (FPz α g p) (FPt α g p)) (p.1, p.2.1) := by
    rw [← hL0]; exact hslice
  -- the FTC identity for the profile
  have hftc : ∀ z' ∈ Set.Ioi (0 : ℝ), ∀ θ' ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      ∀ τ ∈ Set.Icc (0 : ℝ) S,
      Prof α g z' θ' τ - Prof α g z' θ' 0
        = ∫ s in (0 : ℝ)..τ, -(K7 α Φs E g z' θ' s) := by
    intro z' hz' θ' hθ' τ hτ
    rw [intervalIntegral.integral_neg]
    exact Work.FTS_RegExport.RXR7.Support.r7FTC hS hα hα13 hOK hK7cont hEq z' θ' τ
      hz' hθ'.1 hθ'.2 hτ.1 hτ.2
  have hmain := Work.FTS_RegExport.RXR7.Support.hasFDerivWithinAt_of_ftc
    (A := Set.Ioi (0 : ℝ)) (B := Set.Ioo (0 : ℝ) (Real.pi / 2)) (S := S) hS.le
    (h := fun z θ τ => Prof α g z θ τ) (h₀ := fun z θ => Prof α g z θ 0)
    (κ := fun z θ τ => -(K7 α Φs E g z θ τ)) hz ⟨hθ0, hθ1⟩ hFD0 hftc (hK7cont.neg)
  -- match the CLMs
  have hCLM : bdryCLM (pairCLM (FPz α g p) (FPt α g p)) (-(K7 α Φs E g p.1 p.2.1 0))
      = ProfD α Φs E g p := by
    rw [bdryCLM_pairCLM]
    unfold ProfD FR
    rw [hτ0]
  have hp_eq : ((p.1, p.2.1, 0) : ℝ × ℝ × ℝ) = p := by
    ext <;> simp [hτ0]
  rw [hp_eq] at hmain
  rw [← hCLM]
  simp only [bdryCLM]
  exact hmain

end Work.FTS_RegExport.RXR7
