import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.StarSlotPcs.DzdIterBound
import Submission.Work.FTS_MuLamOK.Rows.Rl2Open
import Submission.Work.FTS_RegExport.RXT.Ftau_bounds
import Submission.Work.FTS_RegExport.RXT.Slots.v2_velPert
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
import Submission.Work.FTS_RegExport.RXT.Sys.abs_L12dens_Fstar_add_le
import Submission.Work.FTS_RegExport.RXT.Sys.continuousAt_Qang_of_bounds
import Submission.Work.FTS_RegExport.RXT.Sys.hasDerivAt_mixed_z
import Submission.Work.FTS_RegExport.RXT.SysAux.explicit_piece_bounds
import Submission.Work.FTS_RegExport.RXT.SysAux.pertSlot_contDiffOn
import Submission.Work.FTS_RegExport.RXT.st1_stdata2
import Submission.Work.FTS_RegExport.RXT.velVanish2Aux
import Submission.Work.FTS_RegExport.RXT0.L12FtauTauLip
import Submission.Work.FTS_RegExport.RXT0.SJC.slotJetContinuousOn
import Submission.Work.FTS_RegExport.THL.Defs
import Submission.Work.R1G.DecayInZ_gA
import Submission.Work.Stability.mul_rpow_le
-- ===== merged: Submission.Work.FTS_RegExport.RXR7.Joint.Boundary =====
section

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
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXR7.Joint.Interior =====
section

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
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.FKJets =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `L12FKaux.FKJets` — the angular moments `Q = ∫_θ K(θ)·D_z^k F(τ)` and their `z`-derivatives

`FK F z = ∫_θ F z θ K(θ) dθ` is the `k = 0` member of the family

  `Q(k)(z) = ∫_θ K(θ) · D_z^k F(τ)(z,θ) dθ`,

and `D_z^{k+1}(L₁₂ F)(z) = -Q(k)(z)`.  The module provides

* `Qlim`, `Qapp` — the moments of the limit profile `F(τ) = F_* + slice g τ` and of the
  approximants `F(τ) = F_* + slice (gn n) τ`;
* `Qapp_hasDerivAt` — `∂_z Q(n,k) = Q(n,k+1)/z` (differentiation under the angular integral);
* `Qapp_tendsto` — `Q(n,k) → Q(k)` along the approximants (dominated convergence in `θ`);
* `Qapp_bound` — the uniform bound `|Q(n,k)| ≤ 3(π/2)C_B`.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXT.Sys.L12FKaux

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-- `K ≥ 0` on the angular interval. -/
theorem K_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Work.Spaces.K θ := by
  rw [Work.Spaces.K]
  have hs : 0 ≤ Real.sin θ := Real.sin_nonneg_of_mem_Icc
    ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  have hc : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  positivity

/-- The `k`-th angular moment of the limit profile `F(τ) = F_* + slice g τ`. -/
def Qlim (α : ℝ) (g : Fam) (τ : ℝ) (k : ℕ) : ℝ → ℝ :=
  fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ *
    (Work.Spaces.DzIter k (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ
      + Work.Spaces.DzIter k (slice g τ) z θ)

/-- The `k`-th angular moment of the approximant `F_* + slice (gn n) τ`. -/
def Qapp (α : ℝ) (gn : ℕ → Fam) (τ : ℝ) (n k : ℕ) : ℝ → ℝ :=
  fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ *
    Work.Spaces.DzIter k (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
      (gn n) τ) z θ

/-! ## §1 Differentiating in `z` -/

/-- `∂_z (D_z^k f) = D_z^{k+1} f / z`. -/
theorem pz_DzIter_eq {f : ℝ → ℝ → ℝ} (k : ℕ) {z θ : ℝ} (hz : z ≠ 0) :
    Work.Spaces.pz (Work.Spaces.DzIter k f) z θ
      = Work.Spaces.DzIter (k + 1) f z θ / z := by
  show Work.Spaces.pz (Work.Spaces.DzIter k f) z θ
    = (z * Work.Spaces.pz (Work.Spaces.DzIter k f) z θ) / z
  rw [mul_div_cancel_left₀ _ hz]

/-- **Differentiation under the angular integral**: `∂_z Q(n,k) = Q(n,k+1)/z` for `k ≤ 1`. -/
theorem Qapp_hasDerivAt {α : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    {gn : ℕ → Fam} {τ : ℝ} {CB : ℝ} (hCB : 0 ≤ CB)
    (h3 : ∀ n : ℕ, ContDiffOn ℝ 4 (Function.uncurry
      (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ))
      Work.FTS.EllipticEst.Q0)
    (hsl : ∀ (n : ℕ) (k : ℕ), k ≤ 3 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter k (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
        (gn n) τ) z θ| ≤ CB)
    (n : ℕ) {k : ℕ} (hk : k ≤ 2) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (Qapp α gn τ n k) (Qapp α gn τ n (k + 1) z / z) z := by
  have h2 : ContDiffOn ℝ 2 (Function.uncurry
      (Work.Spaces.DzIter k (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
        (gn n) τ))) Work.FTS.EllipticEst.Q0 :=
    Work.FTS.StrongEps.contDiffOn_uncurry_DzIter_shift Work.FTS.EllipticEst.isOpen_Q0 k 2
      ((h3 n).of_le (Nat.cast_le.mpr (by omega : 2 + k ≤ 4)))
  have hb0 : ∀ x ∈ Set.Ioo (z / 2) (2 * z), ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      |Work.Spaces.DzIter k (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
        (gn n) τ) x θ| ≤ CB := by
    intro x hx θ hθ
    exact hsl n k (by omega) x θ (by linarith [hx.1, hz]) hθ.1 hθ.2
  have hb : ∀ x ∈ Set.Ioo (z / 2) (2 * z), ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      |Work.Spaces.pz (Work.Spaces.DzIter k (Work.Construction.Ftau
        (Work.FTS.Regularity.pExp α) (gn n) τ)) x θ| ≤ 2 * CB / z := by
    intro x hx θ hθ
    have hx0 : 0 < x := by linarith [hx.1, hz]
    have hbnd := hsl n (k + 1) (by omega) x θ hx0 hθ.1 hθ.2
    have hval : Work.Spaces.DzIter (k + 1) (Work.Construction.Ftau
        (Work.FTS.Regularity.pExp α) (gn n) τ) x θ
        = x * deriv (fun z' => Work.Spaces.DzIter k (Work.Construction.Ftau
            (Work.FTS.Regularity.pExp α) (gn n) τ) z' θ) x := rfl
    rw [hval, abs_mul, abs_of_pos hx0] at hbnd
    rw [Work.Spaces.pz]
    have h1 : |deriv (fun z' => Work.Spaces.DzIter k (Work.Construction.Ftau
        (Work.FTS.Regularity.pExp α) (gn n) τ) z' θ) x| ≤ CB / x := by
      rw [le_div_iff₀ hx0]
      linarith [hbnd]
    have h2' : CB / x ≤ 2 * CB / z := by
      have hzx : z ≤ 2 * x := by linarith [hx.1]
      have h3' : 1 / x ≤ 2 / z := by
        rw [div_le_div_iff₀ hx0 hz]
        linarith
      calc CB / x = CB * (1 / x) := by ring
        _ ≤ CB * (2 / z) := mul_le_mul_of_nonneg_left h3' hCB
        _ = 2 * CB / z := by ring
    linarith [h1, h2']
  have hCmax : (0 : ℝ) ≤ max CB (2 * CB / z) := le_trans hCB (le_max_left _ _)
  have hb' : ∀ x ∈ Set.Ioo (z / 2) (2 * z), ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      |Work.Spaces.pz (Work.Spaces.DzIter k (Work.Construction.Ftau
        (Work.FTS.Regularity.pExp α) (gn n) τ)) x θ| ≤ max CB (2 * CB / z) :=
    fun x hx θ hθ => le_trans (hb x hx θ hθ) (le_max_right _ _)
  have hb0' : ∀ x ∈ Set.Ioo (z / 2) (2 * z), ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      |Work.Spaces.DzIter k (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
        (gn n) τ) x θ| ≤ max CB (2 * CB / z) :=
    fun x hx θ hθ => le_trans (hb0 x hx θ hθ) (le_max_left _ _)
  have key := hasDerivAt_integral_Itheta_K (f := Work.Spaces.DzIter k
    (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ))
    h2 hz hCmax hb' hb0'
  have hval : (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Work.Spaces.pz
      (Work.Spaces.DzIter k (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
        (gn n) τ)) z θ)
      = (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Work.Spaces.DzIter (k + 1)
          (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ) z θ) / z := by
    rw [← MeasureTheory.integral_div]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    show Work.Spaces.K θ * Work.Spaces.pz (Work.Spaces.DzIter k (Work.Construction.Ftau
        (Work.FTS.Regularity.pExp α) (gn n) τ)) z θ
      = Work.Spaces.K θ * Work.Spaces.DzIter (k + 1) (Work.Construction.Ftau
        (Work.FTS.Regularity.pExp α) (gn n) τ) z θ / z
    rw [pz_DzIter_eq k (ne_of_gt hz)]
    ring
  rw [hval] at key
  have hdef : Qapp α gn τ n k
      = fun x => ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Work.Spaces.DzIter k
          (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ) x θ := rfl
  rw [hdef]
  exact key

/-! ## §2 Convergence along the approximants -/

/-- **Dominated convergence in `θ`**: `Q(n,k) z → Q(k) z` for `k ≤ 2`. -/
theorem Qapp_tendsto {α : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    {gn : ℕ → Fam} {g : Fam} {τ : ℝ} {Cw CB : ℝ} (hCw : 0 ≤ Cw) (hCB : 0 ≤ CB)
    (h4 : ∀ n : ℕ, ContDiffOn ℝ 4 (Function.uncurry (slice (gn n) τ))
      Work.FTS.EllipticEst.Q0)
    (hbd : ∀ (n : ℕ) (k : ℕ), k ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter k (slice (gn n) τ) z θ| ≤ Cw * SW z)
    (h2 : ∀ n : ℕ, ContDiffOn ℝ 4 (Function.uncurry
      (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ))
      Work.FTS.EllipticEst.Q0)
    (hsl : ∀ (n : ℕ) (k : ℕ), k ≤ 3 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter k (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
        (gn n) τ) z θ| ≤ CB)
    (hjet : ∀ (k : ℕ), k ≤ 2 → ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Filter.Tendsto (fun n => Work.Spaces.DzIter k (slice (gn n) τ) z θ) Filter.atTop
        (𝓝 (Work.Spaces.DzIter k (slice g τ) z θ)))
    {k : ℕ} (hk : k ≤ 2) {z : ℝ} (hz : 0 < z) :
    Filter.Tendsto (fun n => Qapp α gn τ n k z) Filter.atTop (𝓝 (Qlim α g τ k z)) := by
  have hKc : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.K p.2)
      Work.FTS.EllipticEst.Q0 := by
    have hfun : (fun p : ℝ × ℝ => Work.Spaces.K p.2)
        = fun p : ℝ × ℝ => 3 * Real.sin p.2 * Real.cos p.2 ^ 2 := by
      funext p; rw [Work.Spaces.K]
    rw [hfun]
    exact ((continuous_const.mul (Real.continuous_sin.comp continuous_snd)).mul
      ((Real.continuous_cos.comp continuous_snd).pow 2)).continuousOn
  have hKcont : Continuous fun θ : ℝ => Work.Spaces.K θ * CB := by
    have hfun : Work.Spaces.K = fun θ : ℝ => 3 * Real.sin θ * Real.cos θ ^ 2 := by
      funext θ; rw [Work.Spaces.K]
    rw [hfun]
    exact ((continuous_const.mul Real.continuous_sin).mul
      (Real.continuous_cos.pow 2)).mul continuous_const
  have hFmeas : ∀ n : ℕ, AEStronglyMeasurable (fun θ : ℝ => Work.Spaces.K θ
      * Work.Spaces.DzIter k (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
        (gn n) τ) z θ) (volume.restrict Work.Spaces.Iθ) := by
    intro n
    have hD : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.DzIter k
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ) p.1 p.2)
        Work.FTS.EllipticEst.Q0 :=
      (Work.FTS.StrongEps.contDiffOn_uncurry_DzIter_shift Work.FTS.EllipticEst.isOpen_Q0 k 0
        (by simpa using (h2 n).of_le (Nat.cast_le.mpr (by omega : 0 + k ≤ 4)))).continuousOn
    have hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.K p.2
        * Work.Spaces.DzIter k (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (gn n) τ) p.1 p.2) Work.FTS.EllipticEst.Q0 := hKc.mul hD
    exact Work.FTS_RegExport.RXT.Slots.aesm_slice_Q0
      (g := fun x θ => Work.Spaces.K θ * Work.Spaces.DzIter k
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ) x θ) hcont hz
  have hint : Integrable (fun θ : ℝ => Work.Spaces.K θ * CB)
      (volume.restrict Work.Spaces.Iθ) := by
    refine MeasureTheory.Integrable.mono' (MeasureTheory.integrable_const (3 * CB))
      (hKcont.continuousOn.aestronglyMeasurable measurableSet_Icc) ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
    show ‖Work.Spaces.K θ * CB‖ ≤ 3 * CB
    have hK3 : Work.Spaces.K θ ≤ 3 := by
      have h := abs_K_le_three θ
      rwa [abs_of_nonneg (K_nonneg_Iθ hθ)] at h
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (K_nonneg_Iθ hθ), abs_of_nonneg hCB]
    exact mul_le_mul_of_nonneg_right hK3 hCB
  have hbound : ∀ n : ℕ, ∀ᵐ a ∂(volume.restrict Work.Spaces.Iθ),
      ‖Work.Spaces.K a * Work.Spaces.DzIter k (Work.Construction.Ftau
        (Work.FTS.Regularity.pExp α) (gn n) τ) z a‖ ≤ Work.Spaces.K a * CB := by
    intro n
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
    rcases eq_or_lt_of_le hθ.1 with h0 | h0
    · subst h0
      have hK0 : Work.Spaces.K 0 = 0 := by rw [Work.Spaces.K, Real.sin_zero]; ring
      simp only [hK0, zero_mul, norm_zero, le_refl]
    rcases eq_or_lt_of_le hθ.2 with h1 | h1
    · subst h1
      have hK1 : Work.Spaces.K (Real.pi / 2) = 0 := by
        rw [Work.Spaces.K, Real.cos_pi_div_two]; ring
      simp only [hK1, zero_mul, norm_zero, le_refl]
    show ‖Work.Spaces.K θ * Work.Spaces.DzIter k (Work.Construction.Ftau
      (Work.FTS.Regularity.pExp α) (gn n) τ) z θ‖ ≤ Work.Spaces.K θ * CB
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (K_nonneg_Iθ ⟨h0.le, h1.le⟩)]
    exact mul_le_mul_of_nonneg_left (hsl n k (by omega) z θ hz h0 h1)
      (K_nonneg_Iθ ⟨h0.le, h1.le⟩)
  have hlim : ∀ᵐ a ∂(volume.restrict Work.Spaces.Iθ), Filter.Tendsto
      (fun n => Work.Spaces.K a * Work.Spaces.DzIter k (Work.Construction.Ftau
        (Work.FTS.Regularity.pExp α) (gn n) τ) z a) Filter.atTop
      (𝓝 (Work.Spaces.K a * (Work.Spaces.DzIter k
          (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z a
        + Work.Spaces.DzIter k (slice g τ) z a))) := by
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
    rcases eq_or_lt_of_le hθ.1 with h0 | h0
    · subst h0
      have hK0 : Work.Spaces.K 0 = 0 := by rw [Work.Spaces.K, Real.sin_zero]; ring
      simp only [hK0, zero_mul]
      exact tendsto_const_nhds
    rcases eq_or_lt_of_le hθ.2 with h1 | h1
    · subst h1
      have hK1 : Work.Spaces.K (Real.pi / 2) = 0 := by
        rw [Work.Spaces.K, Real.cos_pi_div_two]; ring
      simp only [hK1, zero_mul]
      exact tendsto_const_nhds
    have hQ : (z, θ) ∈ Work.Construction.Qd := ⟨hz, h0, h1⟩
    have hadd : ∀ n : ℕ, Work.Spaces.DzIter k
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ) z θ
        = Work.Spaces.DzIter k (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ
          + Work.Spaces.DzIter k (slice (gn n) τ) z θ :=
      fun n => DzIter_Fstar_add (β := Work.FTS.Regularity.pExp α)
        (Work.FTS.Regularity.pExp_pos hα) (Work.FTS.Regularity.pExp_le_one hα13)
        (h4 n) hk z θ hz h0 h1
    have h1' : Filter.Tendsto (fun n => Work.Spaces.DzIter k
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ) z θ)
        Filter.atTop (𝓝 (Work.Spaces.DzIter k
          (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ
          + Work.Spaces.DzIter k (slice g τ) z θ)) := by
      refine ((tendsto_const_nhds.add (hjet k hk z θ hQ))).congr' ?_
      filter_upwards with n
      exact (hadd n).symm
    show Filter.Tendsto (fun n => Work.Spaces.K θ * Work.Spaces.DzIter k
      (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ) z θ) Filter.atTop
      (𝓝 (Work.Spaces.K θ * (Work.Spaces.DzIter k
          (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ
        + Work.Spaces.DzIter k (slice g τ) z θ)))
    exact tendsto_const_nhds.mul h1'
  have key := MeasureTheory.tendsto_integral_of_dominated_convergence
    (μ := volume.restrict Work.Spaces.Iθ)
    (F := fun n θ => Work.Spaces.K θ * Work.Spaces.DzIter k
      (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ) z θ)
    (f := fun θ => Work.Spaces.K θ * (Work.Spaces.DzIter k
        (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ
      + Work.Spaces.DzIter k (slice g τ) z θ))
    (bound := fun θ => Work.Spaces.K θ * CB) hFmeas hint hbound hlim
  simpa only [Qapp, Qlim] using key

/-! ## §3 The uniform bound on the moments -/

/-- **`|Q(n,k) z| ≤ 3(π/2)C_B`** for `k ≤ 2`. -/
theorem Qapp_bound {α : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    {gn : ℕ → Fam} {τ : ℝ} {CB : ℝ} (hCB : 0 ≤ CB)
    (h2 : ∀ n : ℕ, ContDiffOn ℝ 4 (Function.uncurry
      (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ))
      Work.FTS.EllipticEst.Q0)
    (hsl : ∀ (n : ℕ) (k : ℕ), k ≤ 3 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter k (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
        (gn n) τ) z θ| ≤ CB)
    (n : ℕ) {k : ℕ} (hk : k ≤ 3) {z : ℝ} (hz : 0 < z) :
    |Qapp α gn τ n k z| ≤ 3 * (Real.pi / 2) * CB := by
  have hmem : AEStronglyMeasurable (fun θ : ℝ => |Work.Spaces.K θ * Work.Spaces.DzIter k
      (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ) z θ|)
      (volume.restrict Work.Spaces.Iθ) := by
    have hKc : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.K p.2)
        Work.FTS.EllipticEst.Q0 := by
      have hfun : (fun p : ℝ × ℝ => Work.Spaces.K p.2)
          = fun p : ℝ × ℝ => 3 * Real.sin p.2 * Real.cos p.2 ^ 2 := by
        funext p; rw [Work.Spaces.K]
      rw [hfun]
      exact ((continuous_const.mul (Real.continuous_sin.comp continuous_snd)).mul
        ((Real.continuous_cos.comp continuous_snd).pow 2)).continuousOn
    have hD : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.DzIter k
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ) p.1 p.2)
        Work.FTS.EllipticEst.Q0 :=
      (Work.FTS.StrongEps.contDiffOn_uncurry_DzIter_shift Work.FTS.EllipticEst.isOpen_Q0 k 0
        (by simpa using (h2 n).of_le (Nat.cast_le.mpr (by omega : 0 + k ≤ 4)))).continuousOn
    refine Work.FTS_RegExport.RXT.Slots.aesm_slice_Q0
      (g := fun x θ => |Work.Spaces.K θ * Work.Spaces.DzIter k
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ) x θ|) ?_ hz
    have hfun : Function.uncurry (fun x θ => |Work.Spaces.K θ * Work.Spaces.DzIter k
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ) x θ|)
        = fun p : ℝ × ℝ => |Work.Spaces.K p.2
          * Work.Spaces.DzIter k (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
            (gn n) τ) p.1 p.2| := rfl
    rw [hfun]
    exact (hKc.mul hD).abs
  have hint : Integrable (fun θ : ℝ => |Work.Spaces.K θ * Work.Spaces.DzIter k
      (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ) z θ|)
      (volume.restrict Work.Spaces.Iθ) := by
    refine Integrable.mono' (integrable_const (3 * CB)) hmem ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
    try dsimp only
    rcases eq_or_lt_of_le hθ.1 with h0 | h0
    · subst h0
      have hK0 : Work.Spaces.K 0 = 0 := by rw [Work.Spaces.K, Real.sin_zero]; ring
      show ‖|Work.Spaces.K 0 * Work.Spaces.DzIter k (Work.Construction.Ftau
        (Work.FTS.Regularity.pExp α) (gn n) τ) z 0|‖ ≤ 3 * CB
      rw [hK0, zero_mul, abs_zero, norm_zero]
      linarith [hCB]
    rcases eq_or_lt_of_le hθ.2 with h1 | h1
    · subst h1
      have hK1 : Work.Spaces.K (Real.pi / 2) = 0 := by
        rw [Work.Spaces.K, Real.cos_pi_div_two]; ring
      show ‖|Work.Spaces.K (Real.pi / 2) * Work.Spaces.DzIter k (Work.Construction.Ftau
        (Work.FTS.Regularity.pExp α) (gn n) τ) z (Real.pi / 2)|‖ ≤ 3 * CB
      rw [hK1, zero_mul, abs_zero, norm_zero]
      linarith [hCB]
    show ‖|Work.Spaces.K θ * Work.Spaces.DzIter k (Work.Construction.Ftau
      (Work.FTS.Regularity.pExp α) (gn n) τ) z θ|‖ ≤ 3 * CB
    rw [Real.norm_eq_abs, abs_abs, abs_mul]
    exact mul_le_mul (abs_K_le_three θ) (hsl n k (by omega) z θ hz h0 h1) (abs_nonneg _)
      (by norm_num)
  have h1 : ‖Qapp α gn τ n k z‖
      ≤ ∫ θ in Work.Spaces.Iθ, ‖Work.Spaces.K θ * Work.Spaces.DzIter k
          (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ) z θ‖ := by
    rw [Qapp]
    exact MeasureTheory.norm_integral_le_integral_norm _
  have h2' : (∫ θ in Work.Spaces.Iθ, ‖Work.Spaces.K θ * Work.Spaces.DzIter k
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ) z θ‖)
      ≤ ∫ θ in Work.Spaces.Iθ, 3 * CB := by
    refine MeasureTheory.integral_mono_ae hint (MeasureTheory.integrable_const _) ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
    try dsimp only
    rcases eq_or_lt_of_le hθ.1 with h0 | h0
    · subst h0
      have hK0 : Work.Spaces.K 0 = 0 := by rw [Work.Spaces.K, Real.sin_zero]; ring
      rw [hK0, zero_mul, norm_zero]
      linarith [hCB]
    rcases eq_or_lt_of_le hθ.2 with h1 | h1
    · subst h1
      have hK1 : Work.Spaces.K (Real.pi / 2) = 0 := by
        rw [Work.Spaces.K, Real.cos_pi_div_two]; ring
      rw [hK1, zero_mul, norm_zero]
      linarith [hCB]
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (abs_K_le_three θ) (hsl n k (by omega) z θ hz h0 h1) (abs_nonneg _)
      (by norm_num)
  have h3 : (∫ θ in Work.Spaces.Iθ, 3 * CB) = 3 * (Real.pi / 2) * CB := by
    rw [Work.Elliptic.integral_Iθ_eq_interval, intervalIntegral.integral_const]
    simp only [sub_zero, smul_eq_mul]
    ring
  rw [Real.norm_eq_abs] at h1
  linarith [h1, h2', le_of_eq h3]

end Work.FTS_RegExport.RXT.Sys.L12FKaux
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT0.RXJets.starSlots =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT0.RXJets.starSlots` — the star slots are continuous on the slab

The three transport slots of the *star* residual `Φ̃_* = v2_PhiStar α Φs` — namely
`𝒱(Φ̃_*)`, `ℛ(Φ̃_*)` and `𝒰(Φ̃_*)/sin 2θ` — are `C^∞` on the open quadrant `Q0`, so all their
mixed jets of order `≤ 2` are jointly continuous there.  Since the slab
`slb S = (0,∞) × (0,π/2) × [0,S]` only carries an extra `τ`-coordinate (the functions do not
depend on `p.2.2`) and projects into `Q0`, the jets are jointly continuous on the slab.

The smoothness inputs are the `StarPkgo2`-witness smoothness `hStar.smooth : SmoothOpen Φs`
together with

* `Work.FTS.PhiStar.CoreAux.smoothOpen_PhiTs` for `Φ̃_*`,
* `Work.FTS.NonlinRows.Rl1.smoothOpen_Vop_open` / `…smoothOpen_Uop_open` and
  `Work.FTS.NonlinRows.smoothOpen_Rop` for the three operators,
* `Work.FTS.PhiStar.StarPkgo2Aux.smoothOpen_div_sin2` for the division by `sin 2θ`,

and the jet continuity from `Work.FTS.StrongEps.continuousOn_mixed_of_contDiffOn`.
-/

namespace Work.FTS_RegExport.RXT0.RXJets

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- **Slab lift.**  A mixed jet `D_z^kD_θ^l` of a function which is continuous on the open
quadrant is continuous on the slab `(0,∞) × (0,π/2) × [0,S]`: the slab maps into `Q0` under the
projection `p ↦ (p.1, p.2.1)`, and the `τ`-coordinate is not used. -/
theorem slabLift {f : ℝ → ℝ → ℝ} {S : ℝ} {k l : ℕ}
    (h : ContinuousOn (Function.uncurry (Work.Spaces.mixed k l f))
      Work.FTS.EllipticEst.Q0) :
    ContinuousOn (fun p : ℝ × ℝ × ℝ => Work.Spaces.mixed k l f p.1 p.2.1) (slb S) :=
  h.comp ((continuous_fst.prodMk (continuous_fst.comp continuous_snd)).continuousOn)
    (fun p hp => by
      obtain ⟨h1, h2, h3, -, -⟩ := mem_slb.mp hp
      exact Work.FTS.EllipticEst.mem_Q0.mpr ⟨h1, h2, h3⟩)

theorem starSlots {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hStar : Work.FTS.Final.StarPkgo2 (Work.FTS.Regularity.pExp α) Cs Φs)
    (S : ℝ) (k l : ℕ) (hkl : k + l ≤ 2) :
    ContinuousOn (fun p : ℝ × ℝ × ℝ => Work.Spaces.mixed k l
        (fun z θ => Work.Construction.Vop (Work.FTS_RegExport.RXT.v2_PhiStar α Φs) z θ)
        p.1 p.2.1) (Work.FTS_RegExport.RXT0.RXJets.slb S) ∧
      ContinuousOn (fun p : ℝ × ℝ × ℝ => Work.Spaces.mixed k l
        (fun z θ => Work.Construction.Rop (Work.FTS.Regularity.pExp α)
          (Work.FTS_RegExport.RXT.v2_PhiStar α Φs) z θ) p.1 p.2.1)
        (Work.FTS_RegExport.RXT0.RXJets.slb S) ∧
      ContinuousOn (fun p : ℝ × ℝ × ℝ => Work.Spaces.mixed k l
        (fun z θ => Work.Construction.Uop (Work.FTS.Regularity.pExp α)
          (Work.FTS_RegExport.RXT.v2_PhiStar α Φs) z θ / Real.sin (2 * θ)) p.1 p.2.1)
        (Work.FTS_RegExport.RXT0.RXJets.slb S) := by
  have hβ : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hβ1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  have hsm : Work.FTS.EllipticEst.SmoothOpen Φs := hStar.smooth
  -- the star residual is `C^∞` on the open quadrant
  have hPs : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.VocabO2.PhiTs (Work.FTS.Regularity.pExp α) Φs) :=
    (Work.FTS.PhiStar.CoreAux.smoothOpen_PhiTs (α := Work.FTS.Regularity.pExp α) (Φs := Φs)
      hβ hβ1 hsm).1
  -- the three slots are `C^∞` on the open quadrant
  have hV : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.Vop (Work.FTS.VocabO2.PhiTs (Work.FTS.Regularity.pExp α) Φs)) :=
    Work.FTS.NonlinRows.Rl1.smoothOpen_Vop_open hPs
  have hR : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.Rop (Work.FTS.Regularity.pExp α)
        (Work.FTS.VocabO2.PhiTs (Work.FTS.Regularity.pExp α) Φs)) :=
    Work.FTS.NonlinRows.smoothOpen_Rop hPs
  have hU : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Construction.Uop (Work.FTS.Regularity.pExp α)
        (Work.FTS.VocabO2.PhiTs (Work.FTS.Regularity.pExp α) Φs) z θ / Real.sin (2 * θ)) :=
    Work.FTS.PhiStar.StarPkgo2Aux.smoothOpen_div_sin2
      (Work.FTS.NonlinRows.Rl1.smoothOpen_Uop_open (α := Work.FTS.Regularity.pExp α) hPs)
  -- their mixed jets of order `≤ 2` are continuous on the open quadrant
  have hVc : ContinuousOn (Function.uncurry (Work.Spaces.mixed k l
      (Work.Construction.Vop (Work.FTS.VocabO2.PhiTs (Work.FTS.Regularity.pExp α) Φs))))
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS.StrongEps.continuousOn_mixed_of_contDiffOn (k := 3) (j := k) (i := l)
      (hV.forall 3) (by omega)
  have hRc : ContinuousOn (Function.uncurry (Work.Spaces.mixed k l
      (Work.Construction.Rop (Work.FTS.Regularity.pExp α)
        (Work.FTS.VocabO2.PhiTs (Work.FTS.Regularity.pExp α) Φs))))
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS.StrongEps.continuousOn_mixed_of_contDiffOn (k := 3) (j := k) (i := l)
      (hR.forall 3) (by omega)
  have hUc : ContinuousOn (Function.uncurry (Work.Spaces.mixed k l
      (fun z θ => Work.Construction.Uop (Work.FTS.Regularity.pExp α)
        (Work.FTS.VocabO2.PhiTs (Work.FTS.Regularity.pExp α) Φs) z θ / Real.sin (2 * θ))))
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS.StrongEps.continuousOn_mixed_of_contDiffOn (k := 3) (j := k) (i := l)
      (hU.forall 3) (by omega)
  exact ⟨slabLift hVc, slabLift hRc, slabLift hUc⟩

end Work.FTS_RegExport.RXT0.RXJets
end
-- ===== merged: Submission.Work.FTS_RegExport.RXVP3.Ftau_bounds_unif =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXVP3.Ftau_bounds_unif` — a fake-time-uniform bound for `F(τ)`

The profile of the strong route is `F(τ) = Ftau (pExp α) (GR α g) τ = F_* + g(τ)` on the open
quadrant, and `Work.FTS_RegExport.RXT.Ftau_bounds.Ftau_bounds` bounds its first three `D_z`-jets
on the open quadrant by `10*M + |K|` (`M` from `FstarJet7`, `K = 10/√(γ-1)·(C₀·(pExp α)²)`), a
constant which is in fact independent of `τ` — but the *statement* of `Ftau_bounds` puts the
existential `∃ C` after the current fake time `τ`, so it cannot be read as a uniform statement.

Here the `∃ C` is taken *before* the quantifier on `τ ≥ 0`.  Every ingredient is already
fake-time-free:

* the radial factor `F_*`: `Work.FTS_RegExport.RXT.ftau_contDiffOn_Fstar_Q0` for the `C²`-regularity on `Q0` and
  `Work.FTS_RegExport.RXT.ftau_DzIter_Fstar_le` with `M` from `FstarJet7` for the `D_z`-jets;
* the `g`-part: `Work.FTS_RegExport.RXT.Sys.ftau_DzIter_GR_le_uniform` (which needs only
  `LimApprox`, i.e. `hOK.2`, and a point `τ ∈ Icc 0 S` — used with `S := τ`), whose bound
  `10/√(γ-1)·(C₀·(pExp α)²)` is the horizon-free one produced by `mixed_uniform`;
* `D_z`-additivity on the sum: `Work.FTS_RegExport.RXT.ftau_DzIter_one_add` / `Work.FTS_RegExport.RXT.ftau_DzIter_two_add`, using that
  `DynOK'` supplies the `C⁴`-regularity of the slices of `g` at *every* `τ ≥ 0`
  (`RegPkgMin.c4`, i.e. `hOK.1.1.c4 τ hτ`).

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_RegExport.RXVP3

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.RegExportIface.RXT (GR)

set_option autoImplicit false

/-- **Uniform bounds for the profile `F(τ) = F_* + g(τ)` and its `D_z`-derivatives.**  On the
open quadrant `F(z,θ) = F_*(z,θ) + g(z,θ,τ)`; the `F_*`-part is bounded by `FstarJet7`
(together with the elementary `|α Γ/c| ≤ 10`), and the `g`-part by `mixed_uniform` at the
horizon `max τ 1`, whose constant is independent of the horizon.  Hence the same constant
`10*M + |K|` works for every `τ ≥ 0`. -/
theorem Ftau_bounds_unif {α C₀ : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam}
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, 0 ≤ τ → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) τ z θ| ≤ C ∧
      |Work.Spaces.Dz (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) τ) z θ| ≤ C ∧
      |Work.Spaces.DzIter 2 (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) τ) z θ| ≤ C := by
  obtain ⟨M, hMpos, hM⟩ := Work.FTS.StrongPersist.H6Pair6Aux.FstarJet7
  set K : ℝ := 10 / Real.sqrt (Work.Spaces.gam (Work.FTS.Regularity.pExp α) - 1)
      * (C₀ * (Work.FTS.Regularity.pExp α) ^ 2) with hK
  refine ⟨10 * M + |K|, ?_, ?_⟩
  · have h10M : 0 ≤ 10 * M := by linarith
    linarith [abs_nonneg K]
  · intro τ hτ z θ hz h1 h2
    have hp0 : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
    have hp1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
    have hA : Work.FTS.FinalV2.LimApprox (Work.FTS.Regularity.pExp α) C₀ Φs E g := hOK.2
    have hFc : ContDiffOn ℝ 2
        (Function.uncurry (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)))
        Work.FTS.EllipticEst.Q0 :=
      Work.FTS_RegExport.RXT.ftau_contDiffOn_Fstar_Q0 hp0 hp1
    have hGc : ContDiffOn ℝ 2
        (Function.uncurry (slice (GR α g) τ)) Work.FTS.EllipticEst.Q0 :=
      ((hOK.1.1.c4 τ hτ).of_le (by norm_num)).congr
        (fun p hp => Work.FTS_RegExport.RXT.ftau_slice_GR_eq hτ hp.1 hp.2.1.le hp.2.2.le)
    have hF1 : ContDiffOn ℝ 1
        (Function.uncurry (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)))
        Work.FTS.EllipticEst.Q0 := hFc.of_le (by norm_num)
    have hG1 : ContDiffOn ℝ 1
        (Function.uncurry (slice (GR α g) τ)) Work.FTS.EllipticEst.Q0 := hGc.of_le (by norm_num)
    have sp0 : Work.Spaces.DzIter 0
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (GR α g) τ) z θ
        = Work.Spaces.DzIter 0 (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ
          + Work.Spaces.DzIter 0 (slice (GR α g) τ) z θ := rfl
    have sp1 : Work.Spaces.DzIter 1
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (GR α g) τ) z θ
        = Work.Spaces.DzIter 1 (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ
          + Work.Spaces.DzIter 1 (slice (GR α g) τ) z θ := by
      change Work.Spaces.DzIter 1 (fun z θ =>
          Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ + slice (GR α g) τ z θ) z θ
        = Work.Spaces.DzIter 1 (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ
          + Work.Spaces.DzIter 1 (slice (GR α g) τ) z θ
      exact Work.FTS_RegExport.RXT.ftau_DzIter_one_add hF1 hG1 z θ hz h1 h2
    have sp2 : Work.Spaces.DzIter 2
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (GR α g) τ) z θ
        = Work.Spaces.DzIter 2 (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ
          + Work.Spaces.DzIter 2 (slice (GR α g) τ) z θ := by
      change Work.Spaces.DzIter 2 (fun z θ =>
          Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ + slice (GR α g) τ z θ) z θ
        = Work.Spaces.DzIter 2 (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ
          + Work.Spaces.DzIter 2 (slice (GR α g) τ) z θ
      exact Work.FTS_RegExport.RXT.ftau_DzIter_two_add hFc hGc z θ hz h1 h2
    have hF00 : |Work.Spaces.DzIter 0
        (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ| ≤ 10 * M :=
      Work.FTS_RegExport.RXT.ftau_DzIter_Fstar_le hα hα13 hM 0 (by norm_num) z θ hz h1 h2
    have hF11 : |Work.Spaces.DzIter 1
        (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ| ≤ 10 * M :=
      Work.FTS_RegExport.RXT.ftau_DzIter_Fstar_le hα hα13 hM 1 (by norm_num) z θ hz h1 h2
    have hF22 : |Work.Spaces.DzIter 2
        (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ| ≤ 10 * M :=
      Work.FTS_RegExport.RXT.ftau_DzIter_Fstar_le hα hα13 hM 2 (by norm_num) z θ hz h1 h2
    have hG00 : |Work.Spaces.DzIter 0 (slice (GR α g) τ) z θ| ≤ K := by
      rw [hK]
      exact Work.FTS_RegExport.RXT.Sys.ftau_DzIter_GR_le_uniform hα hα13 hA τ
        ⟨hτ, le_rfl⟩ 0 (by norm_num) z θ hz h1 h2
    have hG11 : |Work.Spaces.DzIter 1 (slice (GR α g) τ) z θ| ≤ K := by
      rw [hK]
      exact Work.FTS_RegExport.RXT.Sys.ftau_DzIter_GR_le_uniform hα hα13 hA τ
        ⟨hτ, le_rfl⟩ 1 (by norm_num) z θ hz h1 h2
    have hG22 : |Work.Spaces.DzIter 2 (slice (GR α g) τ) z θ| ≤ K := by
      rw [hK]
      exact Work.FTS_RegExport.RXT.Sys.ftau_DzIter_GR_le_uniform hα hα13 hA τ
        ⟨hτ, le_rfl⟩ 2 (by norm_num) z θ hz h1 h2
    refine ⟨?_, ?_, ?_⟩
    · calc |Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (GR α g) τ z θ|
          = |Work.Spaces.DzIter 0
              (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (GR α g) τ) z θ| := rfl
        _ = |Work.Spaces.DzIter 0 (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ
              + Work.Spaces.DzIter 0 (slice (GR α g) τ) z θ| := by rw [sp0]
        _ ≤ |Work.Spaces.DzIter 0 (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ|
              + |Work.Spaces.DzIter 0 (slice (GR α g) τ) z θ| := abs_add_le _ _
        _ ≤ 10 * M + K := add_le_add hF00 hG00
        _ ≤ 10 * M + |K| := by linarith [le_abs_self K]
    · change |Work.Spaces.DzIter 1
          (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (GR α g) τ) z θ|
          ≤ 10 * M + |K|
      calc |Work.Spaces.DzIter 1
            (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (GR α g) τ) z θ|
          = |Work.Spaces.DzIter 1 (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ
              + Work.Spaces.DzIter 1 (slice (GR α g) τ) z θ| := by rw [sp1]
        _ ≤ |Work.Spaces.DzIter 1 (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ|
              + |Work.Spaces.DzIter 1 (slice (GR α g) τ) z θ| := abs_add_le _ _
        _ ≤ 10 * M + K := add_le_add hF11 hG11
        _ ≤ 10 * M + |K| := by linarith [le_abs_self K]
    · calc |Work.Spaces.DzIter 2
            (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (GR α g) τ) z θ|
          = |Work.Spaces.DzIter 2 (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ
              + Work.Spaces.DzIter 2 (slice (GR α g) τ) z θ| := by rw [sp2]
        _ ≤ |Work.Spaces.DzIter 2 (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ|
              + |Work.Spaces.DzIter 2 (slice (GR α g) τ) z θ| := abs_add_le _ _
        _ ≤ 10 * M + K := add_le_add hF22 hG22
        _ ≤ 10 * M + |K| := by linarith [le_abs_self K]

end Work.FTS_RegExport.RXVP3
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXVP3.L12dens_mass_unif =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXVP3

set_option autoImplicit false

open MeasureTheory Set

/-- **Mass (L¹) bound for the `L₁₂`-density of the profile `F(τ) = F_* + g(τ)`.**

The profile is `F(τ) = Ftau (pExp α) (GR α g) τ = fun z θ => Fstar (pExp α) z θ
+ slice (GR α g) τ z θ` (definitionally).  The two hypotheses are exactly the two pieces of
information the bound needs:

* `hu` bounds the slice `slice (GR α g) τ` by the weight `Cw·z^{3/2}/(1+z)²`, which is the
  input of `RXT.Sys.abs_L12dens_Fstar_add_le`: the angular part of the density is bounded
  by `3(π/2)(20/(1+s)² + Cw·s^{1/2}/(1+s)²)`;
* `hcont` is joint continuity of `F(τ)` on the open quadrant, which makes the angular moment
  continuous on `(0,∞)` (`RXT.Sys.continuousAt_Qang_of_bounds`), hence supplies the a.e.
  strong measurability needed for `MeasureTheory.Integrable.mono'`.

The majorant is integrable with integral `≤ 120 + 18·Cw` (`RXT.Sys.majorant_Ioi_integrable`),
and the statement of that lemma is *literal* — no `∃ C`, no `τ`, no horizon — which is why the
final constant here is exactly `120 + 18·Cw`. -/
theorem L12dens_mass_unif {α Cw : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) (hCw : 0 ≤ Cw)
    {g : Work.FTS.Galerkin.Fam}
    (hu : ∀ τ : ℝ, 0 ≤ τ → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.FTS.Galerkin.slice (Work.FTS.RegExportIface.RXT.GR α g) τ z θ|
        ≤ Cw * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2))
    (hcont : ∀ τ : ℝ, 0 ≤ τ → ContinuousOn (Function.uncurry
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) τ)) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    ∀ τ : ℝ, 0 ≤ τ →
      MeasureTheory.IntegrableOn (Work.Construction.L12dens (Work.Construction.Ftau
          (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) τ)) (Set.Ioi 0) ∧
      (∫ s in Set.Ioi 0, |Work.Construction.L12dens (Work.Construction.Ftau
          (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) τ) s|)
        ≤ 120 + 18 * Cw := by
  have hp0 : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hp1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  have hα1 : α ≤ 1 := le_trans hα13 (by norm_num)
  obtain ⟨hmaj_int, hmaj_val⟩ := Work.FTS_RegExport.RXT.Sys.majorant_Ioi_integrable hCw
  intro τ hτ
  set F : ℝ → ℝ → ℝ := Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
      (Work.FTS.RegExportIface.RXT.GR α g) τ with hFdef
  have hFsplit : F = fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ
      + Work.FTS.Galerkin.slice (Work.FTS.RegExportIface.RXT.GR α g) τ z θ := rfl
  -- ## §1 the pointwise bound of the `L₁₂`-density of `F(τ)` by the elementary majorant
  have hpt : ∀ s : ℝ, 0 < s →
      |Work.Construction.L12dens F s|
        ≤ 3 * (Real.pi / 2)
            * (20 / (1 + s) ^ 2 + Cw * (s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2)) := by
    intro s hs
    have h := Work.FTS_RegExport.RXT.Sys.abs_L12dens_Fstar_add_le
      (α := Work.FTS.Regularity.pExp α) hp0 hp1 hCw
      (u := Work.FTS.Galerkin.slice (Work.FTS.RegExportIface.RXT.GR α g) τ) (hu τ hτ) hs
    rw [hFsplit]
    exact h
  -- ## §2 continuity of the angular moment, hence of the density, on `(0,∞)`
  have hFc : ContinuousOn (Function.uncurry F)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    rw [hFsplit]
    exact hcont τ hτ
  have hQcont : ContinuousOn (fun s => ∫ θ in Work.Spaces.Iθ,
      Work.Elliptic.Ktheta θ * F s θ) (Set.Ioi 0) := by
    intro s₀ hs₀
    refine (Work.FTS_RegExport.RXT.Sys.continuousAt_Qang_of_bounds (f := F) hs₀
      hFc (A := 20 + Cw * (2 * s₀) ^ ((3 : ℝ) / 2)) ?_).continuousWithinAt
    intro z θ hz hθ0 hθ1
    have hz0 : 0 < z :=
      lt_of_lt_of_le (by linarith [show (0 : ℝ) < s₀ from hs₀] : (0 : ℝ) < s₀ / 2) hz.1.le
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ0.le, hθ1.le⟩
    have h1 : |Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ|
        ≤ 10 * |Work.FM.Fstar z| :=
      Work.FTS_RegExport.RXT.Sys.abs_Fstar_le_ten hp0 hp1 hθI
    have h2 : |Work.FM.Fstar z| ≤ 2 := Work.FTS_RegExport.RXT.Sys.abs_FM_Fstar_le_two hz0.le
    have h3 : |Work.FTS.Galerkin.slice (Work.FTS.RegExportIface.RXT.GR α g) τ z θ|
        ≤ Cw * (2 * s₀) ^ ((3 : ℝ) / 2) :=
      le_trans (hu τ hτ z θ hz0 hθ0 hθ1)
        (mul_le_mul_of_nonneg_left
          (Work.FTS_RegExport.RXT.Sys.weight_le_rpow hz0 hz.2.le) hCw)
    rw [hFsplit]
    calc |Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ
          + Work.FTS.Galerkin.slice (Work.FTS.RegExportIface.RXT.GR α g) τ z θ|
        ≤ |Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ|
          + |Work.FTS.Galerkin.slice (Work.FTS.RegExportIface.RXT.GR α g) τ z θ| :=
          abs_add_le _ _
      _ ≤ 10 * |Work.FM.Fstar z| + Cw * (2 * s₀) ^ ((3 : ℝ) / 2) := add_le_add h1 h3
      _ ≤ 10 * 2 + Cw * (2 * s₀) ^ ((3 : ℝ) / 2) := by
          have h10 : 10 * |Work.FM.Fstar z| ≤ 10 * 2 :=
            mul_le_mul_of_nonneg_left h2 (by norm_num)
          linarith
      _ = 20 + Cw * (2 * s₀) ^ ((3 : ℝ) / 2) := by ring
  have hdens_eq : ∀ s : ℝ, Work.Construction.L12dens F s
      = (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ * F s θ) / s :=
    fun s => Work.FTS_RegExport.RXT.Sys.L12dens_eq_thetaIntegral F s
  have hdenc : ContinuousOn (Work.Construction.L12dens F) (Set.Ioi 0) :=
    (hQcont.div continuousOn_id (fun s hs => ne_of_gt hs)).congr (fun s _ => hdens_eq s)
  -- ## §3 integrability of the density and the mass bound
  refine ⟨?_, ?_⟩
  · refine MeasureTheory.Integrable.mono' hmaj_int
      (hdenc.aestronglyMeasurable measurableSet_Ioi) ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with s hs
    rw [Real.norm_eq_abs]
    exact hpt s hs
  · calc (∫ s in Set.Ioi 0, |Work.Construction.L12dens F s|)
        ≤ ∫ s in Set.Ioi 0, 3 * (Real.pi / 2)
            * (20 / (1 + s) ^ 2 + Cw * (s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2)) :=
          MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall (fun s => abs_nonneg _))
            hmaj_int (by
              filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with s hs
              exact hpt s hs)
      _ ≤ 120 + 18 * Cw := hmaj_val

end Work.FTS_RegExport.RXVP3
end
-- ===== merged: Submission.Work.FTS_RegExport.RXVP3.velPert_unif =====
section

set_option synthInstance.maxHeartbeats 400000 -- v435-synth

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.FTS_RegExport.RXVP3

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- **`v2_velPert` with a `τ`-uniform constant** (the perturbation half of
`RXVP3.velVanish2_unif`).

This is `Work.FTS_RegExport.RXT.Slots.v2_velPert`
(`Submission/Work/FTS_RegExport/RXT/Slots/v2_velPert.lean`, proved, `sorry`-free) with the
horizon removed: instead of `∀ S > 0, ∃ M, ∀ τ ∈ Icc 0 S`, one single `M` works for every
`τ ≥ 0`.  The proof is a verbatim re-run, with the horizon chosen *inside* the `∀ τ`:

IMPORT `Submission.Work.FTS_RegExport.RXT.Slots.v2_velPert` (its helper lemmas
`velPert_FK_eq`, `velPert_continuousOn_K`, `velPert_contDiffOn_Theta`, `velPert_mixed_sub_three`,
`velPert_hkMem_bound`, `velPert_limit_bound` are already public in namespace
`Work.FTS_RegExport.RXT`, so do NOT re-prove them) and copy the body of the final theorem
`v2_velPert`, editing ONLY the quantifier plumbing, as follows.  Put the file in namespace
`Work.FTS_RegExport.RXVP3`, `set_option autoImplicit false`, `set_option maxHeartbeats 1600000`,
and keep every hypothesis exactly as below (including the unused `hSol`, which `v2_velPert`'s
proof never touches) so that the rest of the proof copies unchanged.  Since the statement lives
in `Work.FTS_RegExport.RXVP3`, open or fully qualify the `Work.FTS_RegExport.RXT` helpers.

The witness of `v2_velPert` is `C4 * (max Ce 0 * (max C₀ 0 * (pExp α)^2))`, where
`obtain ⟨C4, hC40, hC4⟩ := velPert_hkMem_bound (pExp α)(...)` — it does **not** contain `S`.
So replace

  `intro S hS`
  `obtain ⟨gn, B, L, hApprox, _hLip, hJet, _hμ⟩ := hOK.2 S hS`
  `... refine ⟨C4 * (...), ?_⟩`
  `intro τ hτ z θ hz hθ hθ2 Q hQ j i hji`

by

  `refine ⟨C4 * (max Ce 0 * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2)), ?_⟩`
  `intro τ hτ z θ hz hθ hθ2 Q hQ j i hji`
  `have hS : 0 < max τ 1 := lt_of_lt_of_le zero_lt_one (le_max_right τ 1)`
  `have hτS : τ ∈ Set.Icc (0:ℝ) (max τ 1) := ⟨hτ, le_max_left τ 1⟩`
  `obtain ⟨gn, B, L, hApprox, _hLip, hJet, _hμ⟩ := hOK.2 (max τ 1) hS`

and then (this is the *only* other change) route every horizon-local use through `hτS`:
`hApprox n τ hτ` ↦ `hApprox n τ hτS` (also inside `hReg`), `hJet τ hτ j i hji z' θ' hzθ` ↦
`hJet τ hτS j i hji z' θ' hzθ`, and every `hτ.1` (the `0 ≤ τ` component of the interval
membership, e.g. in `hOK.1.1.c4 τ hτ.1`, `hOK.1.2 τ hτ.1`, `contDiffOn_slice_PhiR_Q0 ... τ
hτ.1`, `Ftau_bounds ... τ hτ.1`, `contDiffOn_Ftau_Q0 ... τ hτ.1`) ↦ `hτ`.  The closing calls
`hMP τ hτ z θ hz hθ hθ2 ...` already take `hτ : 0 ≤ τ` and are copied verbatim.  Nothing else
changes; in particular the `ℋ⁴ → L^∞` trade-off `velPert_hkMem_bound`, the uniform `ℋ⁴`-bounds
on the approximants (`hReg`), the jet-convergence stack
(`v2_L12DzIterTendsto`, `v2_thetaJetsTendsto`, `v2_SlotJetsTendsto`, `v2_paramC2`,
`contDiffOn_three_L12`), and the three `velPert_limit_bound` calls are copied line for line — all
their constants are already `τ`-free (`max Ce 0`, `max C₀ 0`, `C4`, `CA1`). -/
theorem velPert_unif {α Ce C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC (Work.FTS.Regularity.pExp α) u →
      Work.FTS.Final.EllPkgGo (Work.FTS.Regularity.pExp α) Ce u (E u) ∧
        Work.FTS.ClassC.EllPkgK (Work.FTS.Regularity.pExp α) 6 Ce u (E u))
    (hEL3 : Work.FTS.FinalV2.EllLimOK3 (Work.FTS.Regularity.pExp α) E)
    {g : Work.FTS.Galerkin.Fam} (hSol : Work.FTS.FinalV2.Sol (Work.FTS.Regularity.pExp α) Φs E g)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g) :
    ∃ M : ℝ, ∀ τ : ℝ, 0 ≤ τ → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      ∀ Q ∈ ({(Work.Construction.Rop (Work.FTS.Regularity.pExp α)
            (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
              (Work.FTS.Galerkin.slice g τ) (E (Work.FTS.Galerkin.slice g τ)))),
          Work.Construction.Vop
            (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
              (Work.FTS.Galerkin.slice g τ) (E (Work.FTS.Galerkin.slice g τ))),
          fun z θ => Work.Construction.Uop (Work.FTS.Regularity.pExp α)
            (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
              (Work.FTS.Galerkin.slice g τ) (E (Work.FTS.Galerkin.slice g τ))) z θ
            / Real.sin (2 * θ)} : Set (ℝ → ℝ → ℝ)),
        ∀ j i : ℕ, j + i ≤ 2 → |Work.Spaces.mixed j i Q z θ| ≤ M * min z 1 := by
  have hαG : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hαG1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  -- the `ℋ⁴ → L^∞` trade-offs
  obtain ⟨CA1, hCA10, hA1⟩ := Work.FTS_RegExport.RXA1w.abs_mixed_le_HkNorm_C4_w_proved hαG hαG1
  obtain ⟨C4, hC40, hC4⟩ := Work.FTS_RegExport.RXT.velPert_hkMem_bound hαG hαG1
  refine ⟨C4 * (max Ce 0 * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2)), ?_⟩
  intro τ hτ z θ hz hθ hθ2 Q hQ j i hji
  have hS : 0 < max τ 1 := lt_of_lt_of_le zero_lt_one (le_max_right τ 1)
  have hτS : τ ∈ Set.Icc (0:ℝ) (max τ 1) := ⟨hτ, le_max_left τ 1⟩
  -- the class-`C` approximants of `LimApprox`
  obtain ⟨gn, B, L, hApprox, _hLip, hJet, _hμ⟩ := hOK.2 (max τ 1) hS
  -- ## regularity of the class-`C` approximants
  have hReg : ∀ n : ℕ, ContDiffOn ℝ 4 (Function.uncurry (slice (gn n) τ))
        Work.FTS.EllipticEst.Q0 ∧ Work.Spaces.HkMem (Work.FTS.Regularity.pExp α) 4
          (slice (gn n) τ) ∧
      Work.FTS.Nonlin.BdryTraces (Work.FTS.Regularity.pExp α) 4 (slice (gn n) τ) ∧
      Work.Spaces.HkNorm (Work.FTS.Regularity.pExp α) 4 (slice (gn n) τ)
        ≤ max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2 := by
    intro n
    obtain ⟨hCn, hXn, _⟩ := hApprox n τ hτS
    have h2 : C₀ * (Work.FTS.Regularity.pExp α) ^ 2
        ≤ max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2 :=
      mul_le_mul_of_nonneg_right (le_max_left C₀ 0) (sq_nonneg (Work.FTS.Regularity.pExp α))
    exact ⟨hCn.reg.of_le (by norm_num),
      Work.FTS.IPGen.HkMem_mono_le hCn.reg 4 (by norm_num) hCn.mem,
      hCn.bdry_le_six (by norm_num), le_trans hXn h2⟩
  -- ## the limit slice and its data
  have hF4 : ContDiffOn ℝ 4 (Function.uncurry (slice g τ)) Work.FTS.EllipticEst.Q0 :=
    hOK.1.1.c4 τ hτ
  have hFmem : Work.Spaces.HkMem (Work.FTS.Regularity.pExp α) 4 (slice g τ) :=
    hOK.1.1.mem4 τ hτ
  have hFnorm : Work.Spaces.HkNorm (Work.FTS.Regularity.pExp α) 4 (slice g τ)
      ≤ max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2 := by
    have h2 : C₀ * (Work.FTS.Regularity.pExp α) ^ 2
        ≤ max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2 :=
      mul_le_mul_of_nonneg_right (le_max_left C₀ 0) (sq_nonneg (Work.FTS.Regularity.pExp α))
    exact le_trans (hOK.1.2 τ hτ) h2
  -- the `E`-jets of the limit slice
  obtain ⟨_hBsl, hE3lim, hEconv⟩ := hEL3 (fun n => slice (gn n) τ) (slice g τ) B
    (fun n => (hApprox n τ hτS).1) (fun n => (hApprox n τ hτS).2.2) hF4
    (fun j i hji z' θ' hzθ => hJet τ hτS j i hji z' θ' hzθ)
  -- ## `𝔽K` and `L₁₂` of the limit slice
  have hFKlim : ContDiffOn ℝ 2 (Work.Construction.FK (slice g τ)) (Set.Ioi 0) := by
    have hF2 : ContDiffOn ℝ 2 (Function.uncurry (slice g τ))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := hF4.of_le (by norm_num)
    have hbase : ∀ (b : ℕ), b ≤ 2 → ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 →
        |Work.Spaces.mixed b 0 (slice g τ) z' θ'| ≤ C4 * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2) := by
      intro b hb z' θ' hz' hθ' hθ'2
      have h1 := hC4 (slice g τ) (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2) hF4 hFmem hFnorm b 0 (by omega) z' θ'
        hz' hθ' hθ'2
      have h2 : C4 * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2) * min z' 1 ≤ C4 * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2) * 1 :=
        mul_le_mul_of_nonneg_left (min_le_right _ _)
          (mul_nonneg hC40 (mul_nonneg (le_max_right C₀ 0) (sq_nonneg (Work.FTS.Regularity.pExp α))))
      linarith [h1, h2]
    have hb : ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 →
        |slice g τ z' θ'| ≤ C4 * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2) ∧
        |Work.Spaces.Dz (slice g τ) z' θ'| ≤ C4 * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2) ∧
        |Work.Spaces.DzIter 2 (slice g τ) z' θ'| ≤ C4 * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2) :=
      fun z' θ' hz' hθ' hθ'2 =>
        ⟨by simpa using hbase 0 (by norm_num) z' θ' hz' hθ' hθ'2,
         by simpa using hbase 1 (by norm_num) z' θ' hz' hθ' hθ'2,
         by simpa using hbase 2 (by norm_num) z' θ' hz' hθ' hθ'2⟩
    exact Work.FTS_RegExport.RXT.Slots.v2_paramC2 (φ := Work.Spaces.K)
      (C := C4 * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2))
      Work.FTS_RegExport.RXT.velPert_continuousOn_K hF2 hb
  have hL12lim : ContDiffOn ℝ 3 (Work.Construction.L12 (slice g τ)) (Set.Ioi 0) :=
    Work.FTS_RegExport.RXT.contDiffOn_three_L12 hFKlim
  have hΘ3lim : ContDiffOn ℝ 3
      (Function.uncurry (Work.Construction.Theta (Work.FTS.Regularity.pExp α) (slice g τ)))
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS_RegExport.RXT.velPert_contDiffOn_Theta (α := Work.FTS.Regularity.pExp α) hL12lim
  have hElim3 : ContDiffOn ℝ 3 (Function.uncurry (fun z θ => E (slice g τ) z θ))
      Work.FTS.EllipticEst.Q0 := hE3lim
  -- ## `𝔽K`-jets of the approximants and the `Θ`-jets
  have hL12jets : ∀ j : ℕ, j ≤ 3 → ∀ z' : ℝ, 0 < z' →
      Filter.Tendsto (fun n : ℕ => Work.Spaces.DzIter j
          (fun z _ => Work.Construction.L12 (slice (gn n) τ) z) z' 0) Filter.atTop
        (nhds (Work.Spaces.DzIter j
          (fun z _ => Work.Construction.L12 (slice g τ) z) z' 0)) := by
    intro j hj z' hz'
    refine Work.FTS_RegExport.RXT.Slots.v2_L12DzIterTendsto (C0 := CA1 * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2))
      (F := fun n => slice (gn n) τ) (G := slice g τ) (by positivity) ?_ hF4 ?_ ?_ j hj z' hz'
    · intro n; exact (hReg n).1
    · intro n b a hba z'' θ'' hz'' hθ'' hθ''2
      have h1 := hA1 (slice (gn n) τ) (hReg n).1 (hReg n).2.1 (hReg n).2.2.1 b a hba
        z'' θ'' hz'' hθ'' hθ''2
      have h2 : Work.Spaces.HkNorm (Work.FTS.Regularity.pExp α) 4 (slice (gn n) τ)
          ≤ max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2 := (hReg n).2.2.2
      have hA0 : 0 ≤ CA1 * (z'' ^ ((3 : ℝ) / 2) / (1 + z'') ^ 2) :=
        mul_nonneg hCA10 (div_nonneg (Real.rpow_nonneg hz''.le _) (by positivity))
      calc |Work.Spaces.mixed b a (slice (gn n) τ) z'' θ''|
          ≤ CA1 * (z'' ^ ((3 : ℝ) / 2) / (1 + z'') ^ 2)
              * Work.Spaces.HkNorm (Work.FTS.Regularity.pExp α) 4 (slice (gn n) τ) := h1
        _ ≤ CA1 * (z'' ^ ((3 : ℝ) / 2) / (1 + z'') ^ 2) * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2) :=
            mul_le_mul_of_nonneg_left h2 hA0
        _ = CA1 * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2) * (z'' ^ ((3 : ℝ) / 2) / (1 + z'') ^ 2) := by ring
    · intro b a hab z'' θ'' hz'' hθ'' hθ''2
      exact hJet τ hτS b a (by omega) z'' θ'' ⟨hz'', hθ'', hθ''2⟩
  have hΘconv : ∀ j i : ℕ, j + i ≤ 3 → ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 →
      Filter.Tendsto (fun n : ℕ => Work.Spaces.mixed j i
          (Work.Construction.Theta (Work.FTS.Regularity.pExp α) (slice (gn n) τ)) z' θ')
        Filter.atTop
        (nhds (Work.Spaces.mixed j i
          (Work.Construction.Theta (Work.FTS.Regularity.pExp α) (slice g τ)) z' θ')) :=
    Work.FTS_RegExport.RXT.Slots.v2_thetaJetsTendsto (α := Work.FTS.Regularity.pExp α)
      (F := fun n => slice (gn n) τ) (G := slice g τ) hL12jets
  -- ## `C³`-regularity of the residuals
  have hΦ3 : ∀ n : ℕ, ContDiffOn ℝ 3
      (Function.uncurry (fun z θ => E (slice (gn n) τ) z θ)) Work.FTS.EllipticEst.Q0 := by
    intro n
    exact ((hEll _ (hApprox n τ hτS).1).1.smooth).of_le (by norm_num)
  have hΘ3 : ∀ n : ℕ, ContDiffOn ℝ 3 (Function.uncurry
      (Work.Construction.Theta (Work.FTS.Regularity.pExp α) (slice (gn n) τ)))
      Work.FTS.EllipticEst.Q0 := by
    intro n
    refine Work.FTS_RegExport.RXT.velPert_contDiffOn_Theta (α := Work.FTS.Regularity.pExp α) ?_
    refine Work.FTS_RegExport.RXT.contDiffOn_three_L12 ?_
    have h1 : ContDiffOn ℝ 2 (fun z => 3 * Work.Elliptic.Fstar (slice (gn n) τ) z)
        (Set.Ioi 0) := contDiffOn_const.mul ((hApprox n τ hτS).1.fsm 2)
    refine h1.congr fun z' _ => ?_
    rw [Work.FTS_RegExport.RXT.velPert_FK_eq]
  have hΞ3 : ∀ n : ℕ, ContDiffOn ℝ 3 (Function.uncurry (fun z θ =>
      Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice (gn n) τ)
        (E (slice (gn n) τ)) z θ)) Work.FTS.EllipticEst.Q0 := by
    intro n
    refine ((hΦ3 n).sub (hΘ3 n)).congr fun p _ => ?_
    rcases p with ⟨z', θ'⟩
    simp only [Function.uncurry, Pi.sub_apply, Work.Construction.PhiTil]
  have hΞ3lim : ContDiffOn ℝ 3 (Function.uncurry (fun z θ =>
      Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice g τ)
        (E (slice g τ)) z θ)) Work.FTS.EllipticEst.Q0 := by
    refine ((hElim3.sub hΘ3lim)).congr fun p _ => ?_
    rcases p with ⟨z', θ'⟩
    simp only [Function.uncurry, Pi.sub_apply, Work.Construction.PhiTil]
  -- ## the jets of the residuals converge
  have hΞconv : ∀ b a : ℕ, a + b ≤ 3 → ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 →
      Filter.Tendsto (fun n : ℕ => Work.Spaces.mixed b a (fun z θ =>
          Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice (gn n) τ)
            (E (slice (gn n) τ)) z θ) z' θ') Filter.atTop
        (nhds (Work.Spaces.mixed b a (fun z θ =>
          Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice g τ)
            (E (slice g τ)) z θ) z' θ')) := by
    intro b a hba z' θ' hz' hθ' hθ'2
    have hfun : (fun n : ℕ => Work.Spaces.mixed b a (fun z θ =>
          Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice (gn n) τ)
            (E (slice (gn n) τ)) z θ) z' θ')
        = fun n : ℕ => Work.Spaces.mixed b a (fun z θ => E (slice (gn n) τ) z θ) z' θ'
            - Work.Spaces.mixed b a (fun z θ =>
                Work.Construction.Theta (Work.FTS.Regularity.pExp α) (slice (gn n) τ) z θ)
                z' θ' := by
      funext n
      exact Work.FTS_RegExport.RXT.velPert_mixed_sub_three (b := b) (a := a) hba (hΦ3 n) (hΘ3 n) hz' hθ' hθ'2
    have hlim : Work.Spaces.mixed b a (fun z θ =>
          Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice g τ)
            (E (slice g τ)) z θ) z' θ'
        = Work.Spaces.mixed b a (fun z θ => E (slice g τ) z θ) z' θ'
            - Work.Spaces.mixed b a (fun z θ =>
                Work.Construction.Theta (Work.FTS.Regularity.pExp α) (slice g τ) z θ)
                z' θ' :=
      Work.FTS_RegExport.RXT.velPert_mixed_sub_three (b := b) (a := a) hba hElim3 hΘ3lim hz' hθ' hθ'2
    rw [hfun, hlim]
    exact (hEconv b a (by omega) z' θ' ⟨hz', hθ', hθ'2⟩).sub
      (hΘconv b a (by omega) z' θ' hz' hθ' hθ'2)
  -- ## the slot jets converge
  have hslotconv := Work.FTS_RegExport.RXT.Slots.v2_SlotJetsTendsto (α := Work.FTS.Regularity.pExp α)
    (Ξ := fun n => fun z θ => Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
      (slice (gn n) τ) (E (slice (gn n) τ)) z θ)
    (Ξlim := fun z θ => Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
      (slice g τ) (E (slice g τ)) z θ) hΞ3 hΞ3lim hΞconv
  -- ## the final liminf, slotwise
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hQ
  rcases hQ with rfl | rfl | rfl
  · -- the `ℛ`-slot
    refine Work.FTS_RegExport.RXT.velPert_limit_bound (M := C4 * (max Ce 0 * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2)))
      (A := fun n => fun z θ => Work.Construction.Rop (Work.FTS.Regularity.pExp α)
        (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice (gn n) τ)
          (E (slice (gn n) τ))) z θ) ?_ ?_ j i hji z θ hz hθ hθ2
    · intro n j' i' hji' z' θ' hz' hθ' hθ'2
      obtain ⟨hCn, _⟩ := hApprox n τ hτS
      obtain ⟨hGo, _⟩ := hEll _ hCn
      have hXn0 : 0 ≤ Work.FTS.Nonlin.Xn (Work.FTS.Regularity.pExp α) (slice (gn n) τ) :=
        Work.Spaces.HkNorm_nonneg _ _ _
      have hkey : Work.Spaces.HkNorm (Work.FTS.Regularity.pExp α) 4
          (Work.Construction.Rop (Work.FTS.Regularity.pExp α)
            (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice (gn n) τ)
              (E (slice (gn n) τ))))
          ≤ max Ce 0 * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2) := by
        refine le_trans hGo.R.2 ?_
        calc Ce * Work.FTS.Nonlin.Xn (Work.FTS.Regularity.pExp α) (slice (gn n) τ)
            ≤ max Ce 0 * Work.FTS.Nonlin.Xn (Work.FTS.Regularity.pExp α) (slice (gn n) τ) :=
              mul_le_mul_of_nonneg_right (le_max_left Ce 0) hXn0
          _ ≤ max Ce 0 * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2) :=
              mul_le_mul_of_nonneg_left (hReg n).2.2.2 (le_max_right Ce 0)
      exact hC4 _ _ (hGo.R.1.1.of_le (by norm_num)) hGo.R.1.2 hkey j' i' hji'
        z' θ' hz' hθ' hθ'2
    · intro b a hba z' θ' hz' hθ' hθ'2
      exact (hslotconv b a hba z' θ' hz' hθ' hθ'2).1
  · -- the `𝒱`-slot
    refine Work.FTS_RegExport.RXT.velPert_limit_bound (M := C4 * (max Ce 0 * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2)))
      (A := fun n => fun z θ => Work.Construction.Vop
        (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice (gn n) τ)
          (E (slice (gn n) τ))) z θ) ?_ ?_ j i hji z θ hz hθ hθ2
    · intro n j' i' hji' z' θ' hz' hθ' hθ'2
      obtain ⟨hCn, _⟩ := hApprox n τ hτS
      obtain ⟨hGo, _⟩ := hEll _ hCn
      have hXn0 : 0 ≤ Work.FTS.Nonlin.Xn (Work.FTS.Regularity.pExp α) (slice (gn n) τ) :=
        Work.Spaces.HkNorm_nonneg _ _ _
      have hkey : Work.Spaces.HkNorm (Work.FTS.Regularity.pExp α) 4
          (Work.Construction.Vop
            (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice (gn n) τ)
              (E (slice (gn n) τ))))
          ≤ max Ce 0 * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2) := by
        refine le_trans hGo.V.2 ?_
        calc Ce * Work.FTS.Nonlin.Xn (Work.FTS.Regularity.pExp α) (slice (gn n) τ)
            ≤ max Ce 0 * Work.FTS.Nonlin.Xn (Work.FTS.Regularity.pExp α) (slice (gn n) τ) :=
              mul_le_mul_of_nonneg_right (le_max_left Ce 0) hXn0
          _ ≤ max Ce 0 * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2) :=
              mul_le_mul_of_nonneg_left (hReg n).2.2.2 (le_max_right Ce 0)
      exact hC4 _ _ (hGo.V.1.1.of_le (by norm_num)) hGo.V.1.2 hkey j' i' hji'
        z' θ' hz' hθ' hθ'2
    · intro b a hba z' θ' hz' hθ' hθ'2
      exact (hslotconv b a hba z' θ' hz' hθ' hθ'2).2.1
  · -- the `𝒰/sin 2θ`-slot
    refine Work.FTS_RegExport.RXT.velPert_limit_bound (M := C4 * (max Ce 0 * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2)))
      (A := fun n => fun z θ => Work.Construction.Uop (Work.FTS.Regularity.pExp α)
        (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice (gn n) τ)
          (E (slice (gn n) τ))) z θ / Real.sin (2 * θ)) ?_ ?_ j i hji z θ hz hθ hθ2
    · intro n j' i' hji' z' θ' hz' hθ' hθ'2
      obtain ⟨hCn, _⟩ := hApprox n τ hτS
      obtain ⟨hGo, _⟩ := hEll _ hCn
      have hXn0 : 0 ≤ Work.FTS.Nonlin.Xn (Work.FTS.Regularity.pExp α) (slice (gn n) τ) :=
        Work.Spaces.HkNorm_nonneg _ _ _
      have hkey : Work.Spaces.HkNorm (Work.FTS.Regularity.pExp α) 4
          (fun z θ => Work.Construction.Uop (Work.FTS.Regularity.pExp α)
            (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice (gn n) τ)
              (E (slice (gn n) τ))) z θ / Real.sin (2 * θ))
          ≤ max Ce 0 * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2) := by
        refine le_trans hGo.U.2 ?_
        calc Ce * Work.FTS.Nonlin.Xn (Work.FTS.Regularity.pExp α) (slice (gn n) τ)
            ≤ max Ce 0 * Work.FTS.Nonlin.Xn (Work.FTS.Regularity.pExp α) (slice (gn n) τ) :=
              mul_le_mul_of_nonneg_right (le_max_left Ce 0) hXn0
          _ ≤ max Ce 0 * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2) :=
              mul_le_mul_of_nonneg_left (hReg n).2.2.2 (le_max_right Ce 0)
      exact hC4 _ _ (hGo.U.1.1.of_le (by norm_num)) hGo.U.1.2 hkey j' i' hji'
        z' θ' hz' hθ' hθ'2
    · intro b a hba z' θ' hz' hθ' hθ'2
      exact (hslotconv b a hba z' θ' hz' hθ' hθ'2).2.2

end Work.FTS_RegExport.RXVP3
end
end
