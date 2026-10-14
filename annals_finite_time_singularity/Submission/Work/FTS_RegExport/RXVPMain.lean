import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.NNReal.Defs
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Filter.Defs
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS.LocData6.zfarR_jet_le6_of_jets
import Submission.Work.FTS.LocDataExt.Zfar5
import Submission.Work.FTS.MeridianDyn.All
import Submission.Work.FTS.RegExportIface.RXT.Leaves
import Submission.Work.FTS_FinalLeaves.profDerivData_min_proved
import Submission.Work.FTS_RegExport.RXB.l12_aux
import Submission.Work.FTS_RegExport.VPOpen
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_alt_majorant
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_theta
import Submission.Work.Spaces.bt_prod_integrable
-- ===== merged: Submission.Work.FTS_RegExport.RXT.Sys.gdot_eq_profile =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology NNReal
open Set Filter MeasureTheory

namespace Work.FTS_RegExport.RXT.Sys

open Work.FTS.Galerkin (Fn Fam)
open Work.FTS.RegExportIface (Vθ7)
open Work.FTS.RegExportIface.RXT (VR cR GR ΦR μR)
open Work.FTS.RegPkgGal (extG)
open Work.FTS.Regularity (pExp profFull)
open Work.FTS.FinalV2 (gS tauExt LimApprox DynOK' EllLimOK3 Sol)
open Work.FTS.Nonlin (PsiCan)
open Work.FTS_RegExport.RXR5 (AgreeOnQ)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- On the quadrant, `extG (GR α g)` is `g` itself. -/
private theorem gdot_extG_GR_eq (α : ℝ) {g : Fam} {z θ τ : ℝ}
    (hz : 0 < z) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ Real.pi / 2) (hτ : 0 ≤ τ) :
    extG (GR α g) z θ τ = g z θ τ := by
  show extG (gS α (tauExt g)) z θ τ = g z θ τ
  rw [Work.FTS.FinalV2.extG_gS_of_mem α (tauExt g) hθ0 hθ1,
    Work.FTS.RegPkgGal.extG_of_pos hz hτ, Work.FTS.FinalV2.tauExt_of_nonneg g hτ]

/-- The slice of the sanitised family agrees with the slice of `g` on the quadrant. -/
private theorem gdot_AgreeOnQ_slice_GR (α : ℝ) (g : Fam) (τ : ℝ) (hτ : 0 ≤ τ) :
    AgreeOnQ (Work.FTS.Galerkin.slice (GR α g) τ) (Work.FTS.Galerkin.slice g τ) := by
  intro z θ hz hθ hθlt
  simp only [Work.FTS.Galerkin.slice]
  rw [← Work.FTS.RegPkgGal.extG_of_pos (g := GR α g) hz hτ]
  exact gdot_extG_GR_eq α hz hθ.le hθlt.le hτ

/-- The slice of `ΦR α Φs E g` agrees with the slice of `PsiCan Φs E g` on the quadrant. -/
private theorem gdot_AgreeOnQ_slice_PhiR (α : ℝ) {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g : Fam}
    {τ : ℝ} (hτ : 0 ≤ τ) :
    AgreeOnQ (Work.FTS.Galerkin.slice (ΦR α Φs E g) τ)
      (Work.FTS.Galerkin.slice (PsiCan Φs E g) τ) := by
  intro z θ hz hθ hθlt
  show Work.FTS.Galerkin.slice (ΦR α Φs E g) τ z θ
      = Work.FTS.Galerkin.slice (PsiCan Φs E g) τ z θ
  have h1 : Work.FTS.Galerkin.slice (ΦR α Φs E g) τ z θ
      = PsiCan Φs E (tauExt g) z θ τ :=
    Work.FTS.RegExportIface.psiR_of_mem (α := α) (Φs := Φs) (E := E)
      (G := tauExt g) hz hθ hθlt
  rw [h1]
  show Φs z θ + E (Work.FTS.Galerkin.slice (tauExt g) τ) z θ
      = Φs z θ + E (Work.FTS.Galerkin.slice g τ) z θ
  rw [Work.FTS.FinalV2.slice_tauExt g hτ]

/-- The full-profile slice of the sanitised family agrees with `Ftau (pExp α) g τ`. -/
private theorem gdot_AgreeOnQ_profFull (α : ℝ) {g : Fam} {τ : ℝ} (hτ : 0 ≤ τ) :
    AgreeOnQ (fun z θ => profFull α (extG (GR α g)) z θ τ)
      (Work.Construction.Ftau (pExp α) g τ) := by
  intro z θ hz hθ hθlt
  show profFull α (extG (GR α g)) z θ τ = Work.Construction.Ftau (pExp α) g τ z θ
  rw [Work.FTS.Regularity.profFull_apply]
  show Work.Construction.Fstar (pExp α) z θ + extG (GR α g) z θ τ
      = Work.Construction.Fstar (pExp α) z θ + g z θ τ
  rw [gdot_extG_GR_eq α hz hθ.le hθlt.le hτ]

/-- The sanitised full profile agrees with `Ftau (pExp α) g τ` on the quadrant. -/
private theorem gdot_AgreeOnQ_Ftau (α : ℝ) {g : Fam} {τ : ℝ} (hτ : 0 ≤ τ) :
    AgreeOnQ (Work.Construction.Ftau (pExp α) (GR α g) τ)
      (Work.Construction.Ftau (pExp α) g τ) :=
  Work.FTS_RegExport.RXR5.Ftau_congr_of_agreeOnQ (α := pExp α)
    (g := GR α g) (g' := g) (τ := τ) (gdot_AgreeOnQ_slice_GR α g τ hτ)

/-- The two `PhiTil`s agree on the quadrant. -/
private theorem gdot_AgreeOnQ_PhiTil (α : ℝ) {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g : Fam}
    {τ : ℝ} (hτ : 0 ≤ τ) :
    AgreeOnQ
      (Work.Construction.PhiTil (pExp α) (Work.Construction.Ftau (pExp α) g τ)
        (Work.FTS.Galerkin.slice (PsiCan Φs E g) τ))
      (Work.FTS.RegExportIface.phiTil (pExp α) (GR α g) (ΦR α Φs E g) τ) := by
  intro z θ hz hθ hθlt
  have h1 : Work.Construction.Ftau (pExp α) (GR α g) τ z θ
      = Work.Construction.Ftau (pExp α) g τ z θ :=
    gdot_AgreeOnQ_Ftau (g := g) α hτ z θ hz hθ hθlt
  have hL12 : Work.Construction.L12 (Work.Construction.Ftau (pExp α) (GR α g) τ) z
      = Work.Construction.L12 (Work.Construction.Ftau (pExp α) g τ) z :=
    Work.FTS_RegExport.RXR5.L12_congr_of_agreeOnQ
      (h := gdot_AgreeOnQ_Ftau (g := g) α hτ) (z := z) hz.le
  have h2 : Work.FTS.Galerkin.slice (ΦR α Φs E g) τ z θ
      = Work.FTS.Galerkin.slice (PsiCan Φs E g) τ z θ :=
    gdot_AgreeOnQ_slice_PhiR (α := α) (Φs := Φs) (E := E) (g := g) hτ z θ hz hθ hθlt
  show Work.Construction.PhiTil (pExp α) (Work.Construction.Ftau (pExp α) g τ)
        (Work.FTS.Galerkin.slice (PsiCan Φs E g) τ) z θ
      = Work.FTS.RegExportIface.phiTil (pExp α) (GR α g) (ΦR α Φs E g) τ z θ
  simp only [Work.Construction.PhiTil, Work.FTS.RegExportIface.phiTil,
    Work.Construction.Theta, h2, hL12]

/-- **The transport expression of the target equals its unfolded form at `(g, PsiCan Φs E g)`.** -/
private theorem gdot_transport_congr (α : ℝ) {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g : Fam}
    {z θ τ : ℝ} (hz : 0 < z) (hθ : 0 < θ) (hθlt : θ < Real.pi / 2) (hτ : 0 < τ) :
    ((1 - Work.FTS.Galerkin.muDyn (pExp α) (PsiCan Φs E g) g τ)
          + Work.Construction.L12 (Work.Construction.Ftau (pExp α) g τ) z
            * Work.Construction.c2m θ
          + 2 * pExp α * Work.Construction.Vop (Work.Construction.PhiTil (pExp α)
              (Work.Construction.Ftau (pExp α) g τ)
              (Work.FTS.Galerkin.slice (PsiCan Φs E g) τ)) z θ)
        * Work.Spaces.Dz (Work.Construction.Ftau (pExp α) g τ) z θ
      + (2 * Work.Construction.Uop (pExp α)
          (Work.FTS.Galerkin.slice (PsiCan Φs E g) τ) z θ)
        * Work.Spaces.pth (Work.Construction.Ftau (pExp α) g τ) z θ
      + ((1 + Work.FTS.Galerkin.muDyn (pExp α) (PsiCan Φs E g) g τ)
          - Work.Construction.L12 (Work.Construction.Ftau (pExp α) g τ) z / (pExp α)
          + Real.sin θ ^ 2 * Work.Construction.FK (Work.Construction.Ftau (pExp α) g τ) z
          - 2 * Work.Construction.Rop (pExp α) (Work.Construction.PhiTil (pExp α)
              (Work.Construction.Ftau (pExp α) g τ)
              (Work.FTS.Galerkin.slice (PsiCan Φs E g) τ)) z θ)
        * Work.Construction.Ftau (pExp α) g τ z θ
    = VR α Φs E g z θ τ
        * Work.Spaces.Dz (fun z θ => profFull α (extG (GR α g)) z θ τ) z θ
      + Vθ7 (pExp α) (ΦR α Φs E g) z θ τ
        * Work.Spaces.pth (fun z θ => profFull α (extG (GR α g)) z θ τ) z θ
      + cR α Φs E g z θ τ * profFull α (extG (GR α g)) z θ τ := by
  have hτle : 0 ≤ τ := hτ.le
  have hF := gdot_AgreeOnQ_Ftau (g := g) α hτle
  have hΦ := gdot_AgreeOnQ_slice_PhiR (α := α) (Φs := Φs) (E := E) (g := g) hτle
  have hFF := gdot_AgreeOnQ_profFull (g := g) α hτle
  have hΦt := gdot_AgreeOnQ_PhiTil (α := α) (Φs := Φs) (E := E) (g := g) hτle
  have hL12 : Work.Construction.L12 (Work.Construction.Ftau (pExp α) (GR α g) τ) z
      = Work.Construction.L12 (Work.Construction.Ftau (pExp α) g τ) z :=
    Work.FTS_RegExport.RXR5.L12_congr_of_agreeOnQ (h := hF) (z := z) hz.le
  have hFK : Work.Construction.FK (Work.Construction.Ftau (pExp α) (GR α g) τ) z
      = Work.Construction.FK (Work.Construction.Ftau (pExp α) g τ) z :=
    Work.FTS_RegExport.RXR5.FK_congr_of_agreeOnQ (h := hF) (z := z) hz
  have hVop : Work.Construction.Vop (Work.Construction.PhiTil (pExp α)
        (Work.Construction.Ftau (pExp α) g τ)
        (Work.FTS.Galerkin.slice (PsiCan Φs E g) τ)) z θ
      = Work.Construction.Vop (Work.FTS.RegExportIface.phiTil (pExp α) (GR α g)
          (ΦR α Φs E g) τ) z θ :=
    Work.FTS_RegExport.RXR5.Vop_congr_of_agreeOnQ (h := hΦt) hz hθ hθlt
  have hRop : Work.Construction.Rop (pExp α) (Work.Construction.PhiTil (pExp α)
        (Work.Construction.Ftau (pExp α) g τ)
        (Work.FTS.Galerkin.slice (PsiCan Φs E g) τ)) z θ
      = Work.Construction.Rop (pExp α) (Work.FTS.RegExportIface.phiTil (pExp α) (GR α g)
          (ΦR α Φs E g) τ) z θ :=
    Work.FTS_RegExport.RXR5.Rop_congr_of_agreeOnQ (h := hΦt) hz hθ hθlt
  have hUop : Work.Construction.Uop (pExp α) (Work.FTS.Galerkin.slice (PsiCan Φs E g) τ) z θ
      = Work.Construction.Uop (pExp α) (Work.FTS.Galerkin.slice (ΦR α Φs E g) τ) z θ :=
    Work.FTS_RegExport.RXR5.Uop_congr_of_agreeOnQ (h := hΦ.symm) hz hθ hθlt
  have hDz : Work.Spaces.Dz (fun z θ => profFull α (extG (GR α g)) z θ τ) z θ
      = Work.Spaces.Dz (Work.Construction.Ftau (pExp α) g τ) z θ :=
    Work.FTS_RegExport.RXR5.Dz_congr_of_agreeOnQ (h := hFF) hz hθ hθlt
  have hpth : Work.Spaces.pth (fun z θ => profFull α (extG (GR α g)) z θ τ) z θ
      = Work.Spaces.pth (Work.Construction.Ftau (pExp α) g τ) z θ :=
    Work.FTS_RegExport.RXR5.pth_congr_of_agreeOnQ (h := hFF) hz hθ hθlt
  have hval : profFull α (extG (GR α g)) z θ τ
      = Work.Construction.Ftau (pExp α) g τ z θ := hFF z θ hz hθ hθlt
  have hmu : Work.FTS.Final.maxMu (pExp α) (PsiCan Φs E g) g τ
      = Work.FTS.Galerkin.muDyn (pExp α) (PsiCan Φs E g) g τ := by
    simp only [Work.FTS.Final.maxMu]
    rw [max_eq_left hτle]
  simp only [Work.FTS.RegExportIface.RXT.VR, Work.FTS.RegExportIface.RXT.cR,
    Work.FTS.RegExportIface.RXT.GR, Work.FTS.RegExportIface.RXT.ΦR,
    Work.FTS.RegExportIface.RXT.μR, Work.FTS.RegExportIface.Vz7,
    Work.FTS.RegExportIface.Vθ7, Work.FTS.RegExportIface.cs7,
    Work.FTS.RegExportIface.phiTil, hmu, hL12, hFK, hVop, hRop, hUop, hDz, hpth, hval]

theorem gdot_eq_profile {S α Ce C₀ Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hS : 0 < S) (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC (Work.FTS.Regularity.pExp α) u →
      Work.FTS.Final.EllPkgGo (Work.FTS.Regularity.pExp α) Ce u (E u) ∧
        Work.FTS.ClassC.EllPkgK (Work.FTS.Regularity.pExp α) 6 Ce u (E u))
    (hEL3 : Work.FTS.FinalV2.EllLimOK3 (Work.FTS.Regularity.pExp α) E)
    (hStar : Work.FTS.Final.StarPkgo2 (Work.FTS.Regularity.pExp α) Cs Φs)
    (hSol : Work.FTS.FinalV2.Sol (Work.FTS.Regularity.pExp α) Φs E g)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (hμ : Work.FTS.RegExportIface.ClockBd α Φs E g) :
    ∀ z θ τ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 < τ → τ ≤ S →
      HasDerivAt (fun s => Work.FTS.Regularity.profFull α
          (Work.FTS.RegPkgGal.extG (Work.FTS.RegExportIface.RXT.GR α g)) z θ s)
        (-(Work.FTS.RegExportIface.RXT.VR α Φs E g z θ τ
            * Work.Spaces.Dz (fun z θ => Work.FTS.Regularity.profFull α
                (Work.FTS.RegPkgGal.extG (Work.FTS.RegExportIface.RXT.GR α g)) z θ τ) z θ
          + Work.FTS.RegExportIface.Vθ7 (Work.FTS.Regularity.pExp α)
              (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) z θ τ
            * Work.Spaces.pth (fun z θ => Work.FTS.Regularity.profFull α
                (Work.FTS.RegPkgGal.extG (Work.FTS.RegExportIface.RXT.GR α g)) z θ τ) z θ
          + Work.FTS.RegExportIface.RXT.cR α Φs E g z θ τ
            * Work.FTS.Regularity.profFull α
                (Work.FTS.RegPkgGal.extG (Work.FTS.RegExportIface.RXT.GR α g)) z θ τ)) τ := by
  intro z θ τ hz hθ hθlt hτ hτS
  have hp0 : 0 < pExp α := Work.FTS.Regularity.pExp_pos hα
  have hp1 : pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  have hQd : (z, θ) ∈ Work.Construction.Qd := ⟨hz, hθ, hθlt⟩
  -- the stream-function regularity and the derivation data
  have hΦ : ∀ τ' : ℝ, 0 < τ' → ContDiffOn ℝ 2
      (fun q : ℝ × ℝ => PsiCan Φs E g q.1 q.2 τ') Work.Construction.Qd :=
    fun τ' hτ' => (Work.FTS_FinalLeaves.psiCan_C3_proved hEL3 hStar hOK τ' hτ'.le).of_le
      (by norm_num)
  have hD : Work.FTS.MeridianDyn.ProfDerivData (pExp α) (PsiCan Φs E g) g :=
    Work.FTS_FinalLeaves.profDerivData_min_proved hOK.1.1 hΦ
  -- the clock stays away from `-1`
  have hne : ∀ τ' : ℝ, 0 ≤ τ' → 1 + Work.FTS.Galerkin.muDyn (pExp α)
      (PsiCan Φs E g) g τ' ≠ 0 := by
    intro τ' hτ' h0
    have h1 := hμ.1 τ' hτ'
    have h2 : Work.FTS.Galerkin.muDyn (pExp α) (PsiCan Φs E g) g τ' = -1 := by linarith
    rw [h2] at h1
    norm_num at h1
  have hDyn : Work.FTS.MeridianDyn.DynEqF (pExp α)
      (Work.FTS.Galerkin.muDyn (pExp α) (PsiCan Φs E g) g)
      (Work.FTS.MeridianDyn.profFam (pExp α) g) (PsiCan Φs E g) :=
    Work.FTS.MeridianDyn.DynEqF_of_isDynEqOn hp0 hp1 hD hSol.2 hne
  -- the pointwise equation, in transport form
  have hcos : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθlt⟩)
  have h1ab : Work.FTS.Galerkin.slice (PsiCan Φs E g) τ z θ
      = Work.Construction.PhiTil (pExp α) (Work.Construction.Ftau (pExp α) g τ)
          (Work.FTS.Galerkin.slice (PsiCan Φs E g) τ) z θ
        + Work.Construction.Theta (pExp α) (Work.Construction.Ftau (pExp α) g τ) z θ := by
    simp only [Work.Construction.PhiTil]; ring
  have halg := Work.FTS.MeridianDyn.Bridge.dynEqF_transport_form (α := pExp α)
    (μ := Work.FTS.Galerkin.muDyn (pExp α) (PsiCan Φs E g) g τ)
    (F := Work.Construction.Ftau (pExp α) g τ)
    (Φ := Work.FTS.Galerkin.slice (PsiCan Φs E g) τ)
    hp0 z θ hcos h1ab
    (hD.h2 z θ τ hQd hτ) (hD.h3 z θ τ hQd hτ) (hD.h5 z θ τ hQd hτ)
  -- the equation as an identity of the derivative
  have hdyn0 := hDyn z θ τ hQd hτ
  have hdyn : deriv (fun s => Work.Construction.Fstar (pExp α) z θ + g z θ s) τ
      + (1 + Work.FTS.Galerkin.muDyn (pExp α) (PsiCan Φs E g) g τ)
          * Work.Construction.Ftau (pExp α) g τ z θ
      + (1 - Work.FTS.Galerkin.muDyn (pExp α) (PsiCan Φs E g) g τ)
          * Work.Spaces.Dz (Work.Construction.Ftau (pExp α) g τ) z θ
      + Work.Construction.UVR (pExp α) (Work.Construction.Ftau (pExp α) g τ)
          (Work.FTS.Galerkin.slice (PsiCan Φs E g) τ) z θ = 0 := by
    have h1 : Work.FTS.MeridianDyn.slice (Work.FTS.MeridianDyn.profFam (pExp α) g) τ
        = Work.Construction.Ftau (pExp α) g τ := rfl
    have h2 : Work.FTS.MeridianDyn.slice (PsiCan Φs E g) τ
        = Work.FTS.Galerkin.slice (PsiCan Φs E g) τ := rfl
    have h3 : Work.FTS.MeridianDyn.profFam (pExp α) g z θ τ
        = Work.Construction.Ftau (pExp α) g τ z θ := rfl
    have h4 : (fun s => Work.FTS.MeridianDyn.profFam (pExp α) g z θ s)
        = fun s => Work.Construction.Fstar (pExp α) z θ + g z θ s := by
      funext s; rfl
    rw [h1, h2, h3, h4] at hdyn0
    exact hdyn0
  have hderiv1 : deriv (fun s => Work.Construction.Fstar (pExp α) z θ + g z θ s) τ
      = -((1 + Work.FTS.Galerkin.muDyn (pExp α) (PsiCan Φs E g) g τ)
          * Work.Construction.Ftau (pExp α) g τ z θ
        + (1 - Work.FTS.Galerkin.muDyn (pExp α) (PsiCan Φs E g) g τ)
          * Work.Spaces.Dz (Work.Construction.Ftau (pExp α) g τ) z θ
        + Work.Construction.UVR (pExp α) (Work.Construction.Ftau (pExp α) g τ)
          (Work.FTS.Galerkin.slice (PsiCan Φs E g) τ) z θ) := by
    linarith [hdyn]
  have hderiv0 : deriv (fun s => Work.Construction.Fstar (pExp α) z θ + g z θ s) τ
      = -(((1 - Work.FTS.Galerkin.muDyn (pExp α) (PsiCan Φs E g) g τ)
            + Work.Construction.L12 (Work.Construction.Ftau (pExp α) g τ) z
              * Work.Construction.c2m θ
            + 2 * pExp α * Work.Construction.Vop (Work.Construction.PhiTil (pExp α)
                (Work.Construction.Ftau (pExp α) g τ)
                (Work.FTS.Galerkin.slice (PsiCan Φs E g) τ)) z θ)
          * Work.Spaces.Dz (Work.Construction.Ftau (pExp α) g τ) z θ
        + (2 * Work.Construction.Uop (pExp α)
            (Work.FTS.Galerkin.slice (PsiCan Φs E g) τ) z θ)
          * Work.Spaces.pth (Work.Construction.Ftau (pExp α) g τ) z θ
        + ((1 + Work.FTS.Galerkin.muDyn (pExp α) (PsiCan Φs E g) g τ)
            - Work.Construction.L12 (Work.Construction.Ftau (pExp α) g τ) z / (pExp α)
            + Real.sin θ ^ 2 * Work.Construction.FK (Work.Construction.Ftau (pExp α) g τ) z
            - 2 * Work.Construction.Rop (pExp α) (Work.Construction.PhiTil (pExp α)
                (Work.Construction.Ftau (pExp α) g τ)
                (Work.FTS.Galerkin.slice (PsiCan Φs E g) τ)) z θ)
          * Work.Construction.Ftau (pExp α) g τ z θ) := by
    rw [hderiv1, halg]
  have hderivG : deriv (fun s => g z θ s) τ
      = deriv (fun s => Work.Construction.Fstar (pExp α) z θ + g z θ s) τ := by
    rw [deriv_const_add]
  have hHasG : HasDerivAt (fun s => g z θ s)
      (Work.FTS.Galerkin.dynLin (pExp α) g τ z θ
        + Work.FTS.Galerkin.dynRHS (pExp α) (PsiCan Φs E g) g τ z θ) τ :=
    (hSol.2 z θ τ hτ.le hQd).hasDerivAt (Ici_mem_nhds hτ)
  have hHas2 : HasDerivAt (fun s => g z θ s)
      (-(((1 - Work.FTS.Galerkin.muDyn (pExp α) (PsiCan Φs E g) g τ)
            + Work.Construction.L12 (Work.Construction.Ftau (pExp α) g τ) z
              * Work.Construction.c2m θ
            + 2 * pExp α * Work.Construction.Vop (Work.Construction.PhiTil (pExp α)
                (Work.Construction.Ftau (pExp α) g τ)
                (Work.FTS.Galerkin.slice (PsiCan Φs E g) τ)) z θ)
          * Work.Spaces.Dz (Work.Construction.Ftau (pExp α) g τ) z θ
        + (2 * Work.Construction.Uop (pExp α)
            (Work.FTS.Galerkin.slice (PsiCan Φs E g) τ) z θ)
          * Work.Spaces.pth (Work.Construction.Ftau (pExp α) g τ) z θ
        + ((1 + Work.FTS.Galerkin.muDyn (pExp α) (PsiCan Φs E g) g τ)
            - Work.Construction.L12 (Work.Construction.Ftau (pExp α) g τ) z / (pExp α)
            + Real.sin θ ^ 2 * Work.Construction.FK (Work.Construction.Ftau (pExp α) g τ) z
            - 2 * Work.Construction.Rop (pExp α) (Work.Construction.PhiTil (pExp α)
                (Work.Construction.Ftau (pExp α) g τ)
                (Work.FTS.Galerkin.slice (PsiCan Φs E g) τ)) z θ)
          * Work.Construction.Ftau (pExp α) g τ z θ)) τ := by
    rw [← hderiv0, ← hderivG, hHasG.deriv]
    exact hHasG
  -- transport the derivative to `profFull α (extG (GR α g))`
  have hevent : (fun s => profFull α (extG (GR α g)) z θ s)
      =ᶠ[𝓝 τ] (fun s => Work.Construction.Fstar (pExp α) z θ + g z θ s) := by
    filter_upwards [isOpen_Ioi.mem_nhds hτ] with s hs
    show Work.Construction.Fstar (pExp α) z θ + extG (GR α g) z θ s
        = Work.Construction.Fstar (pExp α) z θ + g z θ s
    rw [gdot_extG_GR_eq (g := g) α hz hθ.le hθlt.le hs.le]
  have hHas3 : HasDerivAt (fun s => Work.Construction.Fstar (pExp α) z θ
      + g z θ s)
      (-(((1 - Work.FTS.Galerkin.muDyn (pExp α) (PsiCan Φs E g) g τ)
            + Work.Construction.L12 (Work.Construction.Ftau (pExp α) g τ) z
              * Work.Construction.c2m θ
            + 2 * pExp α * Work.Construction.Vop (Work.Construction.PhiTil (pExp α)
                (Work.Construction.Ftau (pExp α) g τ)
                (Work.FTS.Galerkin.slice (PsiCan Φs E g) τ)) z θ)
          * Work.Spaces.Dz (Work.Construction.Ftau (pExp α) g τ) z θ
        + (2 * Work.Construction.Uop (pExp α)
            (Work.FTS.Galerkin.slice (PsiCan Φs E g) τ) z θ)
          * Work.Spaces.pth (Work.Construction.Ftau (pExp α) g τ) z θ
        + ((1 + Work.FTS.Galerkin.muDyn (pExp α) (PsiCan Φs E g) g τ)
            - Work.Construction.L12 (Work.Construction.Ftau (pExp α) g τ) z / (pExp α)
            + Real.sin θ ^ 2 * Work.Construction.FK (Work.Construction.Ftau (pExp α) g τ) z
            - 2 * Work.Construction.Rop (pExp α) (Work.Construction.PhiTil (pExp α)
                (Work.Construction.Ftau (pExp α) g τ)
                (Work.FTS.Galerkin.slice (PsiCan Φs E g) τ)) z θ)
          * Work.Construction.Ftau (pExp α) g τ z θ)) τ :=
    (hasDerivAt_const_add_iff (Work.Construction.Fstar (pExp α) z θ)).mpr hHas2
  have hHas4 : HasDerivAt (fun s => profFull α (extG (GR α g)) z θ s)
      (-(((1 - Work.FTS.Galerkin.muDyn (pExp α) (PsiCan Φs E g) g τ)
            + Work.Construction.L12 (Work.Construction.Ftau (pExp α) g τ) z
              * Work.Construction.c2m θ
            + 2 * pExp α * Work.Construction.Vop (Work.Construction.PhiTil (pExp α)
                (Work.Construction.Ftau (pExp α) g τ)
                (Work.FTS.Galerkin.slice (PsiCan Φs E g) τ)) z θ)
          * Work.Spaces.Dz (Work.Construction.Ftau (pExp α) g τ) z θ
        + (2 * Work.Construction.Uop (pExp α)
            (Work.FTS.Galerkin.slice (PsiCan Φs E g) τ) z θ)
          * Work.Spaces.pth (Work.Construction.Ftau (pExp α) g τ) z θ
        + ((1 + Work.FTS.Galerkin.muDyn (pExp α) (PsiCan Φs E g) g τ)
            - Work.Construction.L12 (Work.Construction.Ftau (pExp α) g τ) z / (pExp α)
            + Real.sin θ ^ 2 * Work.Construction.FK (Work.Construction.Ftau (pExp α) g τ) z
            - 2 * Work.Construction.Rop (pExp α) (Work.Construction.PhiTil (pExp α)
                (Work.Construction.Ftau (pExp α) g τ)
                (Work.FTS.Galerkin.slice (PsiCan Φs E g) τ)) z θ)
          * Work.Construction.Ftau (pExp α) g τ z θ)) τ :=
    (Filter.EventuallyEq.hasDerivAt_iff hevent).mpr hHas3
  rw [← gdot_transport_congr (α := α) (Φs := Φs) (E := E) (g := g) hz hθ hθlt hτ]
  exact hHas4

end Work.FTS_RegExport.RXT.Sys
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.datum_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.datum_bound` — the localised datum is `O(ω)` with all six derivatives

The localised datum of the route is separable in the self-similar variables,
`locG6 α L β = locR α L β (z)·Γ(θ)`, and the weight is `ω α z θ = z²·Γ(θ)/(1+z)²` with the *same*
angular factor once the profile exponent `pExp α = 3α` is inserted, so the statement is the
product of

* the angular jet bound `|D_θ^i Γ| ≤ 10⁵·Γ` (`LocData6.DthIter_Gam_abs_le6`, the same `Γ` on both
  sides), and
* the radial pointwise bound `|D_z^j locR| ≤ A·z²/(1+z)²` (from `FTS_LocDatum3a.hB_locR8`, the
  pointwise radial majorant of the localised datum),

through the separability identity `LocDataExt.mixed_sepGam`.
-/

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.FTS_RegExport.RXT

/-- The angular factor `Γ(θ) = (sin θ cos²θ)^α` of the weight `ω` is the `Gam`-factor at the
profile exponent `pExp α = 3α`. -/
lemma Gam_pExp_eq_Gamma (α θ : ℝ) :
    Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ = Work.FTS.Regularity.Gamma α θ := by
  rw [Work.Spaces.Gam, Work.FTS.Regularity.Gamma, Work.ConstructionInstance.Gamma,
    Work.FTS.Regularity.pExp]
  norm_num

/-- **The radial factor of the localised datum is `O(z²/(1+z)²)` with all its `D_z`-jets, up to
order `8`.**  This is the pointwise form of the squared weighted majorant
`FTS_LocDatum3a.hB_locR8` (`(D_z^j locR·w z)² ≤ R/(1+z)²`, `w z = (1+z)²/z²`), which unwinds to
`|D_z^j locR| ≤ √R·z²/(1+z)³ ≤ √R·z²/(1+z)²`.  (The proof is self-contained: if the delegated
`Work.FTS_RegExport.RXT.radial_jet_omega` is available, this is the same statement.) -/
lemma radial_jet_omega_local {α L β : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) (hL : 1 ≤ L) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ j : ℕ, j ≤ 8 → ∀ z θ : ℝ, 0 < z →
      |Work.Spaces.DzIter j
        (fun z _ => Work.FTS.LocDataExt.locR (Work.FTS.Regularity.pExp α) L β z) z θ|
        ≤ A * (z ^ 2 / (1 + z) ^ 2) := by
  have hp : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hp1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  obtain ⟨R, hR0, hR⟩ :=
    Work.FTS_LocDatum3a.hB_locR8 (Work.FTS.Regularity.pExp α) L β hp hp1 hL
  refine ⟨Real.sqrt R, Real.sqrt_nonneg R, fun j hj z θ hz => ?_⟩
  have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz
  have hsq := hR j hj z hzI θ
  have hsq' : (|Work.Spaces.DzIter j
        (fun z _ => Work.FTS.LocDataExt.locR (Work.FTS.Regularity.pExp α) L β z) z θ|
        * Work.Spaces.w z) ^ 2 ≤ R / (1 + z) ^ 2 := by
    have he : (|Work.Spaces.DzIter j
          (fun z _ => Work.FTS.LocDataExt.locR (Work.FTS.Regularity.pExp α) L β z) z θ|
          * Work.Spaces.w z) ^ 2
        = (Work.Spaces.DzIter j
          (fun z _ => Work.FTS.LocDataExt.locR (Work.FTS.Regularity.pExp α) L β z) z θ
          * Work.Spaces.w z) ^ 2 := by
      rw [mul_pow, mul_pow, sq_abs]
    rw [he]; exact hsq
  have hle : |Work.Spaces.DzIter j
        (fun z _ => Work.FTS.LocDataExt.locR (Work.FTS.Regularity.pExp α) L β z) z θ|
        * Work.Spaces.w z ≤ Real.sqrt R / (1 + z) := by
    have hle0 : (0 : ℝ) ≤ |Work.Spaces.DzIter j
        (fun z _ => Work.FTS.LocDataExt.locR (Work.FTS.Regularity.pExp α) L β z) z θ|
        * Work.Spaces.w z := by rw [Work.Spaces.w]; positivity
    have h1 : |Work.Spaces.DzIter j
          (fun z _ => Work.FTS.LocDataExt.locR (Work.FTS.Regularity.pExp α) L β z) z θ|
          * Work.Spaces.w z ≤ Real.sqrt (R / (1 + z) ^ 2) :=
      (Real.le_sqrt hle0 (by positivity)).mpr hsq'
    have h2 : Real.sqrt (R / (1 + z) ^ 2) = Real.sqrt R / (1 + z) := by
      have he : R / (1 + z) ^ 2 = (Real.sqrt R / (1 + z)) ^ 2 := by
        rw [div_pow, Real.sq_sqrt hR0]
      rw [he, Real.sqrt_sq (by positivity)]
    rwa [h2] at h1
  rw [Work.Spaces.w] at hle
  have hmul := mul_le_mul_of_nonneg_right hle (show (0 : ℝ) ≤ z ^ 2 / (1 + z) ^ 2 by positivity)
  have hsimp : |Work.Spaces.DzIter j
        (fun z _ => Work.FTS.LocDataExt.locR (Work.FTS.Regularity.pExp α) L β z) z θ|
        * ((1 + z) ^ 2 / z ^ 2) * (z ^ 2 / (1 + z) ^ 2)
      = |Work.Spaces.DzIter j
        (fun z _ => Work.FTS.LocDataExt.locR (Work.FTS.Regularity.pExp α) L β z) z θ| := by
    field_simp
  rw [hsimp] at hmul
  refine hmul.trans ?_
  have h1 : Real.sqrt R / (1 + z) ≤ Real.sqrt R := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < 1 + z)]
    calc Real.sqrt R = Real.sqrt R * 1 := by ring
      _ ≤ Real.sqrt R * (1 + z) :=
          mul_le_mul_of_nonneg_left (by linarith) (Real.sqrt_nonneg R)
  exact mul_le_mul_of_nonneg_right h1 (by positivity)

/-- The six components `(j, i)` of `idx` have `j ≤ 2` and `i ≤ 2`. -/
private lemma idx_le_two (k : Fin 6) :
    (Work.FTS.RegExportIface.RXT.idx k).1 ≤ 2 ∧ (Work.FTS.RegExportIface.RXT.idx k).2 ≤ 2 := by
  fin_cases k <;> simp [Work.FTS.RegExportIface.RXT.idx]

theorem datum_bound {α : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) {L β : ℝ} (hL : 1 ≤ L) :
    ∃ K₀ : ℝ, 0 ≤ K₀ ∧ ∀ k : Fin 6, ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed (Work.FTS.RegExportIface.RXT.idx k).1
        (Work.FTS.RegExportIface.RXT.idx k).2
        (Work.FTS.LocData6.locG6 (Work.FTS.Regularity.pExp α) L β) z θ|
        ≤ K₀ * Work.FTS.RegExportIface.ω α z θ := by
  obtain ⟨A, hA0, hA⟩ := radial_jet_omega_local hα hα13 hL
  refine ⟨100000 * A, mul_nonneg (by norm_num) hA0, fun k z θ hz hθ0 hθ1 => ?_⟩
  have hp : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hp1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, le_of_lt hθ1⟩
  have hji := idx_le_two k
  have hrad := hA (Work.FTS.RegExportIface.RXT.idx k).1 (by omega) z θ hz
  have hang := Work.FTS.LocData6.DthIter_Gam_abs_le6 (Work.FTS.RegExportIface.RXT.idx k).2
    (by omega) (Work.FTS.Regularity.pExp α) hp hp1 hθI
  have hfac : Work.FTS.LocData6.locG6 (Work.FTS.Regularity.pExp α) L β
      = fun z θ => Work.FTS.LocDataExt.locR (Work.FTS.Regularity.pExp α) L β z
          * Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ := by
    rw [Work.FTS.LocData6.locG6_eq, Work.FTS.LocDataExt.locG_eq_locR_Gam]
  rw [hfac, Work.FTS.LocDataExt.mixed_sepGam, abs_mul]
  refine (mul_le_mul hrad hang (abs_nonneg _) (mul_nonneg hA0 (by positivity))).trans ?_
  have heq : (A * (z ^ 2 / (1 + z) ^ 2)) * (100000 * Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ)
      = (100000 * A) * Work.FTS.RegExportIface.ω α z θ := by
    rw [Gam_pExp_eq_Gamma, Work.FTS.RegExportIface.ω]
    ring
  exact le_of_eq heq

end Work.FTS_RegExport.RXT
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.jc3_asm =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_RegExport.RXT

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- The elementary estimate `K · (2 · (ε/(4(K+1)))) < ε/2` for `K ≥ 0`, `ε > 0`. -/
lemma mul_two_div_lt {K ε : ℝ} (hK : 0 ≤ K) (hε : 0 < ε) :
    K * (2 * (ε / (4 * (K + 1)))) < ε / 2 := by
  rw [lt_div_iff₀ (by norm_num : (0:ℝ) < 2)]
  have h1 : (0:ℝ) < 4 * (K + 1) := by linarith
  field_simp
  nlinarith

theorem jc3_of_pieces {α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam}
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (T : ℝ) (hT : 0 < T)
    (hSpace : ∀ {a b c d : ℝ}, 0 < a → a ≤ b → 0 < c → c ≤ d → d < Real.pi / 2 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ τ ∈ Set.Icc (0:ℝ) T, ∀ j i : ℕ, j + i ≤ 3 →
        (∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d, ∀ z' ∈ Set.Icc a b,
          |Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g τ) z θ
            - Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g τ) z' θ| ≤ C * |z - z'|) ∧
        (∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d, ∀ θ' ∈ Set.Icc c d,
          |Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g τ) z θ
            - Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g τ) z θ'| ≤ C * |θ - θ'|))
    (hTau : ∃ L : ℝ, 0 ≤ L ∧ ∀ τ ∈ Set.Icc (0:ℝ) T, ∀ τ' ∈ Set.Icc (0:ℝ) T,
      ∀ b a : ℕ, a + b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.mixed b a (Work.FTS.Galerkin.slice g τ) z θ
          - Work.Spaces.mixed b a (Work.FTS.Galerkin.slice g τ') z θ| ≤ L * |τ - τ'|)
    (hLandau : ∀ {V W : ℝ → ℝ → ℝ} {x₀ δc L K : ℝ}, 0 < δc → 0 ≤ L → 0 ≤ K →
      (∀ τ τ' : ℝ, 0 ≤ τ → 0 ≤ τ' → ∀ x ∈ Set.Icc x₀ (x₀ + δc),
        |V x τ - V x τ'| ≤ L * |τ - τ'|) →
      (∀ τ : ℝ, 0 ≤ τ → ContinuousOn (fun x => W x τ) (Set.Icc x₀ (x₀ + δc))) →
      (∀ τ : ℝ, 0 ≤ τ → ∀ x ∈ Set.Icc x₀ (x₀ + δc),
        |W x τ - W x₀ τ| ≤ K * |x - x₀|) →
      (∀ τ : ℝ, 0 ≤ τ → ∀ x ∈ Set.Icc x₀ (x₀ + δc),
        HasDerivAt (fun x' => V x' τ) (W x τ) x) →
      ∀ τ τ' : ℝ, 0 ≤ τ → 0 ≤ τ' → |τ - τ'| ≤ δc ^ 2 →
        |W x₀ τ - W x₀ τ'| ≤ (2 * L + K) * Real.sqrt |τ - τ'|) :
    ∀ j i : ℕ, j + i ≤ 3 →
      ContinuousOn (fun p : ℝ × ℝ × ℝ =>
        Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g p.2.2) p.1 p.2.1)
        (Set.Ioi (0:ℝ) ×ˢ Set.Ioo (0:ℝ) (Real.pi / 2) ×ˢ Set.Icc (0:ℝ) T) := by
  intro j i hji
  rintro ⟨z, θ, τ⟩ hp
  change ContinuousWithinAt (fun q : ℝ × ℝ × ℝ =>
      Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g q.2.2) q.1 q.2.1)
    (Set.Ioi (0:ℝ) ×ˢ Set.Ioo (0:ℝ) (Real.pi / 2) ×ˢ Set.Icc (0:ℝ) T) (z, θ, τ)
  rw [Set.mem_prod] at hp
  obtain ⟨hz, hp⟩ := hp
  rw [Set.mem_prod] at hp
  obtain ⟨hθmem, hτmem⟩ := hp
  have hzpos : 0 < z := hz
  have hθ0 : 0 < θ := hθmem.1
  have hθπ : θ < Real.pi / 2 := hθmem.2
  -- the box around `(z,θ)`
  set dθ : ℝ := min (θ / 2) ((Real.pi / 2 - θ) / 2) with hdθdef
  have hdθpos : 0 < dθ := by
    rw [hdθdef]; exact lt_min (by linarith) (by linarith)
  have hdθle : dθ ≤ (Real.pi / 2 - θ) / 2 := by rw [hdθdef]; exact min_le_right _ _
  have hdθle' : dθ ≤ θ / 2 := by rw [hdθdef]; exact min_le_left _ _
  have hθlopos : 0 < θ - dθ := by linarith
  have hθhilt : θ + dθ < Real.pi / 2 := by linarith
  obtain ⟨Cs, hCsnn, hCslip⟩ := hSpace (a := z / 2) (b := 3 * z / 2) (c := θ - dθ)
    (d := θ + dθ) (by linarith) (by linarith) hθlopos (by linarith) hθhilt
  obtain ⟨Lτ, hLτnn, hLτ⟩ := hTau
  have hθmem' : θ ∈ Set.Icc (θ - dθ) (θ + dθ) := ⟨by linarith, by linarith⟩
  have hzmem' : z ∈ Set.Icc (z / 2) (3 * z / 2) := ⟨by linarith, by linarith⟩
  -- the time-continuity of the jet at the point
  have hτcont : ContinuousWithinAt
      (fun σ : ℝ => Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g σ) z θ)
      (Set.Icc (0:ℝ) T) τ :=
    tau_cont_mixed hT hzpos hθ0 hθπ hdθpos hdθle hLτnn hCsnn hji
      (fun σ hσ => hOK.1.1.c4 σ hσ.1) hLτ
      (fun σ hσ j' i' hj'i' => (hCslip σ hσ j' i' hj'i').1)
      (fun σ hσ j' i' hj'i' => (hCslip σ hσ j' i' hj'i').2)
      hLandau hτmem
  -- the ε-δ assembly
  refine Metric.continuousWithinAt_iff.mpr ?_
  intro ε hε
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := Metric.continuousWithinAt_iff.mp hτcont (ε / 2) (by linarith)
  set δx : ℝ := min (min δ₁ (ε / (4 * (Cs + 1)))) (min (z / 2) (dθ / 2)) with hδxdef
  have hδxpos : 0 < δx := by
    rw [hδxdef]
    refine lt_min (lt_min hδ₁pos (by positivity)) (lt_min (by linarith) (by linarith))
  refine ⟨δx, hδxpos, ?_⟩
  intro q hq hdist
  obtain ⟨z', θ', τ'⟩ := q
  change dist (Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g τ') z' θ')
    (Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g τ) z θ) < ε
  rw [Set.mem_prod] at hq
  obtain ⟨hz', hq⟩ := hq
  rw [Set.mem_prod] at hq
  obtain ⟨hθ'mem, hτ'mem⟩ := hq
  have hz'pos : 0 < z' := hz'
  rw [Prod.dist_eq, Prod.dist_eq, Real.dist_eq, Real.dist_eq, Real.dist_eq] at hdist
  have hδxle1 : δx ≤ z / 2 := by
    rw [hδxdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hδxle2 : δx ≤ dθ / 2 := by
    rw [hδxdef]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hδxle3 : δx ≤ δ₁ := by
    rw [hδxdef]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hδxle4 : δx ≤ ε / (4 * (Cs + 1)) := by
    rw [hδxdef]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hdz : |z' - z| < δx := lt_of_le_of_lt (le_max_left _ _) hdist
  have hdθ' : |θ' - θ| < δx :=
    lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hdist
  have hdτ' : |τ' - τ| < δx :=
    lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hdist
  have hz'in : z' ∈ Set.Icc (z / 2) (3 * z / 2) := by
    have h := abs_lt.mp (lt_of_lt_of_le hdz hδxle1)
    exact ⟨by linarith [h.2], by linarith [h.1]⟩
  have hθ'in : θ' ∈ Set.Icc (θ - dθ) (θ + dθ) := by
    have h := abs_lt.mp (lt_of_lt_of_le hdθ' hδxle2)
    exact ⟨by linarith [h.2, hdθpos], by linarith [h.1]⟩
  have hslip := hCslip τ' hτ'mem j i hji
  have h1 : |Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g τ') z' θ'
        - Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g τ') z θ|
      ≤ Cs * |z' - z| + Cs * |θ' - θ| := by
    calc |Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g τ') z' θ'
          - Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g τ') z θ|
        ≤ |Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g τ') z' θ'
            - Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g τ') z θ'|
          + |Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g τ') z θ'
            - Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g τ') z θ| := abs_sub_le _ _ _
      _ ≤ Cs * |z' - z| + Cs * |θ' - θ| :=
          add_le_add (hslip.1 z' hz'in θ' hθ'in z hzmem')
            (hslip.2 z hzmem' θ' hθ'in θ hθmem')
  have h2 : |Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g τ') z θ
      - Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g τ) z θ| < ε / 2 := by
    have h := hδ₁ hτ'mem (by rw [Real.dist_eq]; exact lt_of_lt_of_le hdτ' hδxle3)
    rwa [Real.dist_eq] at h
  have h3 : Cs * |z' - z| + Cs * |θ' - θ| < ε / 2 := by
    have h4 : |z' - z| + |θ' - θ| ≤ 2 * (ε / (4 * (Cs + 1))) :=
      le_of_lt (by linarith [add_lt_add hdz hdθ', hδxle4])
    have h5 : Cs * (|z' - z| + |θ' - θ|) ≤ Cs * (2 * (ε / (4 * (Cs + 1)))) :=
      mul_le_mul_of_nonneg_left h4 hCsnn
    have h6 : Cs * (2 * (ε / (4 * (Cs + 1)))) < ε / 2 := mul_two_div_lt hCsnn hε
    calc Cs * |z' - z| + Cs * |θ' - θ| = Cs * (|z' - z| + |θ' - θ|) := by ring
      _ ≤ Cs * (2 * (ε / (4 * (Cs + 1)))) := h5
      _ < ε / 2 := h6
  calc dist (Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g τ') z' θ')
        (Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g τ) z θ)
      = |Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g τ') z' θ'
          - Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g τ) z θ| := Real.dist_eq _ _
    _ ≤ |Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g τ') z' θ'
            - Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g τ') z θ|
          + |Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g τ') z θ
            - Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g τ) z θ| := abs_sub_le _ _ _
    _ < ε := by linarith [h1, h2, h3]

end Work.FTS_RegExport.RXT
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXVPMain =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXVPMain` — the `VelPkg` assembly

`Work.FTS_RegExport.VelPkg_of_open` is the one-line glue between the area's `VelPkgOpen`
(the repaired eight-field package: open-`θ` `bnd`/`vz0`/`cont`, no `axis`) and the frozen
`RegExportIface.VelPkg` (the same fields plus the `thHol` Hölder clause).  It exists so that the
final `velPkg_proved` is `VelPkg_of_open (RXVP3.velPkgOpen_of_vopLower …) (thHol …)`.
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter

namespace Work.FTS_RegExport

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.RegExportIface

set_option autoImplicit false

/-- **`VelPkgOpen` + `thHol` = the frozen `VelPkg`.** -/
theorem VelPkg_of_open {αG : ℝ} {μ : ℝ → ℝ} {G Φ : Fam} {S : ℝ}
    (h : Work.FTS_RegExport.VelPkgOpen αG μ G Φ S)
    (hth : ∃ β : ℝ, 0 < β ∧ β ≤ 1 ∧ ThHol (Vz7 αG μ G Φ) S β ∧ ThHol (cs7 αG μ G Φ) S β) :
    VelPkg αG μ G Φ S where
  bnd := h.bnd
  vz0 := h.vz0
  vth_ends := h.vth_ends
  c2 := h.c2
  dbnd := h.dbnd
  cont := h.cont
  thHol := hth
  vanish0 := h.vanish0
  vanishK := h.vanishK

end Work.FTS_RegExport
end
end
