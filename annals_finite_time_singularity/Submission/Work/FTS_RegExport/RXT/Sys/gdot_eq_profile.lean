import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.RegExportIface.RXT.Leaves
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS.MeridianDyn.All
import Submission.Work.FTS_FinalLeaves.profDerivData_min_proved
import Submission.Work.FTS_FinalLeaves.psiCan_C3_proved
import Submission.Work.FTS_RegExport.RXR5.Basic
import Submission.Work.FTS.MeridianDyn.Bridge.dynEqF_transport_form

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
