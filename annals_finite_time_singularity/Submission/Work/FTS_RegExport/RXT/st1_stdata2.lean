import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS.MeridianDyn.All
import Submission.Work.FTS.Nonlinear.n4norm_exists
import Submission.Work.FTS.RegExportIface.RXT.Leaves
import Submission.Work.FTS.StrongEps.EComparison.SlotsZeroSliceInt
import Submission.Work.FTS.StrongGlobal.Defs
import Submission.Work.FTS.StrongPersist.DthFstar_W6
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_FinalLeaves.profDerivData_min_proved
import Submission.Work.FTS_RegExport.C4.Dth_mixed_eq_C4
import Submission.Work.FTS_RegExport.RXT.Sys.miiAux
import Submission.Work.FTS_RegExport.RXT.jc3_aux
import Submission.Work.FTS_RegExport.RXVPMain
import Submission.Work.FTS_RegExport.THL.Defs
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_alt_majorant
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.H2W.PsiSlices.weakPos2_dilate
import Submission.Work.Spaces.bt_prod_integrable
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Stability.mul_rpow_le
-- ===== merged: Submission.Work.FTS_RegExport.RXR7.Support.r7FTC =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXR7.Support

open Set Filter MeasureTheory

theorem r7FTC {α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam} {S : ℝ}
    (hS : 0 < S) (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (hK7cont : ContinuousOn (fun p : ℝ × ℝ × ℝ =>
      Work.FTS_RegExport.RXR7.K7 α Φs E g p.1 p.2.1 p.2.2) (Work.FTS_RegExport.RXR7.R7Slab S))
    (hEq : ∀ z θ τ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 < τ → τ ≤ S →
      HasDerivAt (fun s => Work.FTS_RegExport.RXR7.Prof α g z θ s)
        (-(Work.FTS_RegExport.RXR7.K7 α Φs E g z θ τ)) τ) :
    ∀ z θ τ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 ≤ τ → τ ≤ S →
      Work.FTS_RegExport.RXR7.Prof α g z θ τ - Work.FTS_RegExport.RXR7.Prof α g z θ 0
        = -∫ s in (0:ℝ)..τ, Work.FTS_RegExport.RXR7.K7 α Φs E g z θ s := by
  intro z θ τ hz hθ hθπ hτ0 hτS
  rcases eq_or_lt_of_le hτ0 with hτeq | hτpos
  · -- the case `τ = 0`: the integral over a point and the difference both vanish
    subst hτeq
    simp
  · -- the case `τ > 0`: the fundamental theorem of calculus on `[0,τ]`
    have hzθ : (z, θ) ∈ Work.Construction.Qd := ⟨hz, hθ, hθπ⟩
    -- on `Icc 0 τ` the profile is `F_* z θ + g z θ s` (the sanitiser and the right-Taylor
    -- extension are inert at `z > 0`, `0 ≤ θ ≤ π/2`, `s ≥ 0`)
    have hEqOn : Set.EqOn (fun s => Work.FTS_RegExport.RXR7.Prof α g z θ s)
        (fun s => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ + g z θ s)
        (Set.Icc 0 τ) := by
      intro s hs
      have hs0 : 0 ≤ s := hs.1
      show Work.FTS.Regularity.profFull α
          (Work.FTS.RegPkgGal.extG (Work.FTS_RegExport.RXR7.GR α g)) z θ s = _
      rw [Work.FTS.Regularity.profFull_apply]
      congr 1
      rw [Work.FTS.RegPkgGal.extG_of_pos hz hs0]
      show Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) z θ s = g z θ s
      simp only [Work.FTS.FinalV2.gS, hz, hθ.le, hθπ.le, and_self, ↓reduceIte]
      exact Work.FTS.FinalV2.tauExt_of_nonneg g hs0
    -- continuity of the `τ`-slice, including the endpoint `τ = 0` (`RegPkgMin.cont`)
    have hcontg : ContinuousOn (fun s : ℝ => g z θ s) (Set.Icc 0 τ) :=
      (hOK.1.1.cont z θ hzθ).mono Set.Icc_subset_Ici_self
    have hcont2 : ContinuousOn (fun s : ℝ =>
        Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ + g z θ s) (Set.Icc 0 τ) :=
      continuousOn_const.add hcontg
    have hcont : ContinuousOn (fun s : ℝ => Work.FTS_RegExport.RXR7.Prof α g z θ s)
        (Set.Icc 0 τ) :=
      hcont2.congr hEqOn
    -- the pointwise derivative, straight from `hEq`
    have hderiv : ∀ s ∈ Set.Ioo (0:ℝ) τ,
        HasDerivAt (fun s => Work.FTS_RegExport.RXR7.Prof α g z θ s)
          (-(Work.FTS_RegExport.RXR7.K7 α Φs E g z θ s)) s := by
      intro s hs
      exact hEq z θ s hz hθ hθπ hs.1 (le_trans hs.2.le hτS)
    -- the `τ`-slice of `K7` is continuous on `[0,τ]`, hence interval integrable
    have hmaps : Set.MapsTo (fun s : ℝ => ((z, θ, s) : ℝ × ℝ × ℝ)) (Set.Icc 0 τ)
        (Work.FTS_RegExport.RXR7.R7Slab S) := by
      intro s hs
      refine ⟨hz, ⟨⟨hθ, hθπ⟩, hs.1, le_trans hs.2 hτS⟩⟩
    have hfuneq : ((fun p : ℝ × ℝ × ℝ => Work.FTS_RegExport.RXR7.K7 α Φs E g p.1 p.2.1 p.2.2)
        ∘ fun x : ℝ => (z, θ, id x))
        = (fun s : ℝ => Work.FTS_RegExport.RXR7.K7 α Φs E g z θ s) := by
      funext s; simp
    have hint : IntervalIntegrable (fun s => Work.FTS_RegExport.RXR7.K7 α Φs E g z θ s)
        MeasureTheory.volume 0 τ := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le hτpos.le]
      have hK7c := hK7cont.comp
        ((continuous_const.prodMk (continuous_const.prodMk continuous_id)).continuousOn) hmaps
      rwa [hfuneq] at hK7c
    have hFTC :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hτpos.le hcont hderiv hint.neg
    rw [intervalIntegral.integral_neg] at hFTC
    exact hFTC.symm

end Work.FTS_RegExport.RXR7.Support
end
-- ===== merged: Submission.Work.FTS_RegExport.RXR7.r7HEq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology NNReal
open Set Filter MeasureTheory

namespace Work.FTS_RegExport.RXR7

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.RegExportIface (Vθ7)
open Work.FTS.RegPkgGal (extG)
open Work.FTS.Regularity (pExp profFull)
open Work.FTS.FinalV2 (gS tauExt DynOK' Sol)
open Work.FTS.Nonlin (PsiCan)
open Work.FTS_RegExport.RXR5 (AgreeOnQ)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- On the quadrant, `extG (GR α g)` is `g` itself. -/
private theorem r7_extG_GR_eq (α : ℝ) {g : Fam} {z θ τ : ℝ}
    (hz : 0 < z) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ Real.pi / 2) (hτ : 0 ≤ τ) :
    extG (GR α g) z θ τ = g z θ τ := by
  show extG (gS α (tauExt g)) z θ τ = g z θ τ
  rw [Work.FTS.FinalV2.extG_gS_of_mem α (tauExt g) hθ0 hθ1,
    Work.FTS.RegPkgGal.extG_of_pos hz hτ, Work.FTS.FinalV2.tauExt_of_nonneg g hτ]

/-- The slice of the sanitised family agrees with the slice of `g` on the quadrant. -/
private theorem r7_AgreeOnQ_slice_GR (α : ℝ) (g : Fam) (τ : ℝ) (hτ : 0 ≤ τ) :
    AgreeOnQ (slice (GR α g) τ) (slice g τ) := by
  intro z θ hz hθ hθlt
  simp only [Work.FTS.Galerkin.slice]
  rw [← Work.FTS.RegPkgGal.extG_of_pos (g := GR α g) hz hτ]
  exact r7_extG_GR_eq α hz hθ.le hθlt.le hτ

/-- The slice of `ΦR α Φs E g` agrees with the slice of `PsiCan Φs E g` on the quadrant. -/
private theorem r7_AgreeOnQ_slice_PhiR (α : ℝ) {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g : Fam}
    {τ : ℝ} (hτ : 0 ≤ τ) :
    AgreeOnQ (slice (ΦR α Φs E g) τ) (slice (PsiCan Φs E g) τ) := by
  intro z θ hz hθ hθlt
  show slice (ΦR α Φs E g) τ z θ = slice (PsiCan Φs E g) τ z θ
  have h1 : slice (ΦR α Φs E g) τ z θ = PsiCan Φs E (tauExt g) z θ τ :=
    Work.FTS.RegExportIface.psiR_of_mem (α := α) (Φs := Φs) (E := E)
      (G := tauExt g) hz hθ hθlt
  rw [h1]
  show Φs z θ + E (slice (tauExt g) τ) z θ
      = Φs z θ + E (slice g τ) z θ
  rw [Work.FTS.FinalV2.slice_tauExt g hτ]

/-- The full-profile slice of the sanitised family agrees with `Ftau (pExp α) g τ`. -/
private theorem r7_AgreeOnQ_profFull (α : ℝ) {g : Fam} {τ : ℝ} (hτ : 0 ≤ τ) :
    AgreeOnQ (fun z θ => profFull α (extG (GR α g)) z θ τ)
      (Work.Construction.Ftau (pExp α) g τ) := by
  intro z θ hz hθ hθlt
  show profFull α (extG (GR α g)) z θ τ = Work.Construction.Ftau (pExp α) g τ z θ
  rw [Work.FTS.Regularity.profFull_apply]
  show Work.Construction.Fstar (pExp α) z θ + extG (GR α g) z θ τ
      = Work.Construction.Fstar (pExp α) z θ + g z θ τ
  rw [r7_extG_GR_eq α hz hθ.le hθlt.le hτ]

/-- The sanitised full profile agrees with `Ftau (pExp α) g τ` on the quadrant. -/
private theorem r7_AgreeOnQ_Ftau (α : ℝ) {g : Fam} {τ : ℝ} (hτ : 0 ≤ τ) :
    AgreeOnQ (Work.Construction.Ftau (pExp α) (GR α g) τ)
      (Work.Construction.Ftau (pExp α) g τ) :=
  Work.FTS_RegExport.RXR5.Ftau_congr_of_agreeOnQ (α := pExp α)
    (g := GR α g) (g' := g) (τ := τ) (r7_AgreeOnQ_slice_GR α g τ hτ)

/-- The two `PhiTil`s agree on the quadrant. -/
private theorem r7_AgreeOnQ_PhiTil (α : ℝ) {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g : Fam}
    {τ : ℝ} (hτ : 0 ≤ τ) :
    AgreeOnQ
      (Work.Construction.PhiTil (pExp α) (Work.Construction.Ftau (pExp α) g τ)
        (slice (PsiCan Φs E g) τ))
      (Work.FTS.RegExportIface.phiTil (pExp α) (GR α g) (ΦR α Φs E g) τ) := by
  intro z θ hz hθ hθlt
  have h1 : Work.Construction.Ftau (pExp α) (GR α g) τ z θ
      = Work.Construction.Ftau (pExp α) g τ z θ :=
    r7_AgreeOnQ_Ftau α hτ z θ hz hθ hθlt
  have hL12 : Work.Construction.L12 (Work.Construction.Ftau (pExp α) (GR α g) τ) z
      = Work.Construction.L12 (Work.Construction.Ftau (pExp α) g τ) z :=
    Work.FTS_RegExport.RXR5.L12_congr_of_agreeOnQ
      (h := r7_AgreeOnQ_Ftau (g := g) α hτ) (z := z) hz.le
  have h2 : slice (ΦR α Φs E g) τ z θ = slice (PsiCan Φs E g) τ z θ :=
    r7_AgreeOnQ_slice_PhiR (α := α) (Φs := Φs) (E := E) (g := g) hτ z θ hz hθ hθlt
  show Work.Construction.PhiTil (pExp α) (Work.Construction.Ftau (pExp α) g τ)
        (slice (PsiCan Φs E g) τ) z θ
      = Work.FTS.RegExportIface.phiTil (pExp α) (GR α g) (ΦR α Φs E g) τ z θ
  simp only [Work.Construction.PhiTil, Work.FTS.RegExportIface.phiTil,
    Work.Construction.Theta, h2, hL12]

/-- **The transport expression of the target equals its unfolded form at `(g, PsiCan Φs E g)`.** -/
private theorem r7_transport_congr (α : ℝ) {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g : Fam}
    {z θ τ : ℝ} (hz : 0 < z) (hθ : 0 < θ) (hθlt : θ < Real.pi / 2) (hτ : 0 < τ) :
    ((1 - Work.FTS.Galerkin.muDyn (pExp α) (PsiCan Φs E g) g τ)
          + Work.Construction.L12 (Work.Construction.Ftau (pExp α) g τ) z
            * Work.Construction.c2m θ
          + 2 * pExp α * Work.Construction.Vop (Work.Construction.PhiTil (pExp α)
              (Work.Construction.Ftau (pExp α) g τ)
              (slice (PsiCan Φs E g) τ)) z θ)
        * Work.Spaces.Dz (Work.Construction.Ftau (pExp α) g τ) z θ
      + (2 * Work.Construction.Uop (pExp α)
          (slice (PsiCan Φs E g) τ) z θ)
        * Work.Spaces.pth (Work.Construction.Ftau (pExp α) g τ) z θ
      + ((1 + Work.FTS.Galerkin.muDyn (pExp α) (PsiCan Φs E g) g τ)
          - Work.Construction.L12 (Work.Construction.Ftau (pExp α) g τ) z / (pExp α)
          + Real.sin θ ^ 2 * Work.Construction.FK (Work.Construction.Ftau (pExp α) g τ) z
          - 2 * Work.Construction.Rop (pExp α) (Work.Construction.PhiTil (pExp α)
              (Work.Construction.Ftau (pExp α) g τ)
              (slice (PsiCan Φs E g) τ)) z θ)
        * Work.Construction.Ftau (pExp α) g τ z θ
    = Vz7R α Φs E g z θ τ
        * Work.Spaces.Dz (fun z θ => Prof α g z θ τ) z θ
      + Vθ7R α Φs E g z θ τ
        * Work.Spaces.pth (fun z θ => Prof α g z θ τ) z θ
      + cs7R α Φs E g z θ τ * Prof α g z θ τ := by
  have hτle : 0 ≤ τ := hτ.le
  have hF := r7_AgreeOnQ_Ftau (g := g) α hτle
  have hΦ := r7_AgreeOnQ_slice_PhiR (α := α) (Φs := Φs) (E := E) (g := g) hτle
  have hFF := r7_AgreeOnQ_profFull (g := g) α hτle
  have hΦt := r7_AgreeOnQ_PhiTil (α := α) (Φs := Φs) (E := E) (g := g) hτle
  have hL12 : Work.Construction.L12 (Work.Construction.Ftau (pExp α) (GR α g) τ) z
      = Work.Construction.L12 (Work.Construction.Ftau (pExp α) g τ) z :=
    Work.FTS_RegExport.RXR5.L12_congr_of_agreeOnQ (h := hF) (z := z) hz.le
  have hFK : Work.Construction.FK (Work.Construction.Ftau (pExp α) (GR α g) τ) z
      = Work.Construction.FK (Work.Construction.Ftau (pExp α) g τ) z :=
    Work.FTS_RegExport.RXR5.FK_congr_of_agreeOnQ (h := hF) (z := z) hz
  have hVop : Work.Construction.Vop (Work.Construction.PhiTil (pExp α)
        (Work.Construction.Ftau (pExp α) g τ)
        (slice (PsiCan Φs E g) τ)) z θ
      = Work.Construction.Vop (Work.FTS.RegExportIface.phiTil (pExp α) (GR α g)
          (ΦR α Φs E g) τ) z θ :=
    Work.FTS_RegExport.RXR5.Vop_congr_of_agreeOnQ (h := hΦt) hz hθ hθlt
  have hRop : Work.Construction.Rop (pExp α) (Work.Construction.PhiTil (pExp α)
        (Work.Construction.Ftau (pExp α) g τ)
        (slice (PsiCan Φs E g) τ)) z θ
      = Work.Construction.Rop (pExp α) (Work.FTS.RegExportIface.phiTil (pExp α) (GR α g)
          (ΦR α Φs E g) τ) z θ :=
    Work.FTS_RegExport.RXR5.Rop_congr_of_agreeOnQ (h := hΦt) hz hθ hθlt
  have hUop : Work.Construction.Uop (pExp α) (slice (PsiCan Φs E g) τ) z θ
      = Work.Construction.Uop (pExp α) (slice (ΦR α Φs E g) τ) z θ :=
    Work.FTS_RegExport.RXR5.Uop_congr_of_agreeOnQ (h := hΦ.symm) hz hθ hθlt
  have hDz : Work.Spaces.Dz (fun z θ => Prof α g z θ τ) z θ
      = Work.Spaces.Dz (Work.Construction.Ftau (pExp α) g τ) z θ :=
    Work.FTS_RegExport.RXR5.Dz_congr_of_agreeOnQ (h := hFF) hz hθ hθlt
  have hpth : Work.Spaces.pth (fun z θ => Prof α g z θ τ) z θ
      = Work.Spaces.pth (Work.Construction.Ftau (pExp α) g τ) z θ :=
    Work.FTS_RegExport.RXR5.pth_congr_of_agreeOnQ (h := hFF) hz hθ hθlt
  have hval : Prof α g z θ τ = Work.Construction.Ftau (pExp α) g τ z θ :=
    hFF z θ hz hθ hθlt
  have hmu : Work.FTS.Final.maxMu (pExp α) (PsiCan Φs E g) g τ
      = Work.FTS.Galerkin.muDyn (pExp α) (PsiCan Φs E g) g τ := by
    simp only [Work.FTS.Final.maxMu]
    rw [max_eq_left hτle]
  simp only [Vz7R, Vθ7R, cs7R, GR, ΦR, μR, Prof,
    Work.FTS.RegExportIface.Vz7, Work.FTS.RegExportIface.Vθ7,
    Work.FTS.RegExportIface.cs7, Work.FTS.RegExportIface.phiTil,
    hmu, hL12, hFK, hVop, hRop, hUop, hDz, hpth, hval]

/-- The `c2` clause of `VelPkg` at the sanitised family gives `C²` of the canonical stream function
on the quadrant. -/
private theorem r7_psiCan_c2 {α : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g : Fam}
    (hVP : ∀ S > 0, Work.FTS.RegExportIface.VelPkg (pExp α)
      (μR α Φs E g) (GR α g) (ΦR α Φs E g) S) :
    ∀ τ' : ℝ, 0 < τ' →
      ContDiffOn ℝ 2 (fun q : ℝ × ℝ => PsiCan Φs E g q.1 q.2 τ') Work.Construction.Qd := by
  intro τ' hτ'
  have hSpos : 0 < τ' + 1 := by linarith
  have hτ'mem : τ' ∈ Set.Icc (0 : ℝ) (τ' + 1) := ⟨hτ'.le, by linarith⟩
  have hc2 : ContDiffOn ℝ 2
      (Function.uncurry (slice (ΦR α Φs E g) τ')) Work.FTS.EllipticEst.Q0 :=
    (hVP (τ' + 1) hSpos).c2 τ' hτ'mem
  rw [show Work.FTS.EllipticEst.Q0 = Work.Construction.Qd from rfl] at hc2
  refine hc2.congr ?_
  intro q hq
  obtain ⟨hz, hθ, hθlt⟩ := hq
  show PsiCan Φs E g q.1 q.2 τ'
      = Function.uncurry (slice (ΦR α Φs E g) τ') q
  rw [show Function.uncurry (slice (ΦR α Φs E g) τ') q
      = Work.FTS.RegExportIface.psiR α Φs E (tauExt g) q.1 q.2 τ' from rfl]
  rw [Work.FTS.RegExportIface.psiR_of_mem (α := α) (Φs := Φs) (E := E)
    (G := tauExt g) hz hθ hθlt]
  show Φs q.1 q.2 + E (slice g τ') q.1 q.2
      = Φs q.1 q.2 + E (slice (tauExt g) τ') q.1 q.2
  rw [Work.FTS.FinalV2.slice_tauExt g hτ'.le]

/-- **RX-R7, the `hEq` field** (the transport form of the profile equation at the closed-form
coefficients).  `K7 α Φs E g = Vz7ᵣ·D_z(Prof) + Vθ7ᵣ·∂_θ(Prof) + cs7ᵣ·Prof` with
`Vz7ᵣ/Vθ7ᵣ/cs7ᵣ = Vz7/Vθ7/cs7` at `(μR α Φs E g, GR α g, ΦR α Φs E g)`, and `Prof α g` the full
profile `profFull α (extG (GR α g))`; the claim is that on the open quadrant and for `0 < τ ≤ S`
the fake-time derivative of the profile is `-(K7 α Φs E g z θ τ)`.

**This is byte-for-byte the conclusion of the already-proved `Work.FTS_RegExport.RXT.Sys.gdot_eq_profile`**,
whose hypothesis list differs only in that it carries `hEll : ∀ u, ClassC (pExp α) u → EllPkgGo ∧
EllPkgK 6`, `hEL3 : EllLimOK3 (pExp α) E` and `hStar : StarPkgo2 (pExp α) Cs Φs` instead of
`hVP`.  In that proof those three hypotheses are used *only* to supply a single local fact,
`hΦ : ∀ τ' : ℝ, 0 < τ' → ContDiffOn ℝ 2 (fun q : ℝ × ℝ => PsiCan Φs E g q.1 q.2 τ') Qd`
(via `FTS_FinalLeaves.psiCan_C3_proved`; note `Qd = Ioi 0 ×ˢ Ioo 0 (π/2)`), which is fed to
`FTS_FinalLeaves.profDerivData_min_proved hOK.1.1 hΦ`.  **`hVP` supplies exactly that fact**:
`(hVP S' hS').c2` for any `S' > max S τ'` gives `ContDiffOn ℝ 2 (uncurry (slice (ΦR α Φs E g) τ')) Q0`
and `ΦR α Φs E g` agrees with `PsiCan Φs E g` on the quadrant at `τ' ≥ 0`
(`psiR_of_mem`, `slice_tauExt`, `PsiCan = Φs + E (slice ·)`).

So the intended proof is: **copy the proof of `RXT.Sys.gdot_eq_profile` verbatim and replace that
one supply of `hΦ`** (everything else — `DynEqF_of_isDynEqOn` with `hne` from `hμ`,
`MeridianDyn.Bridge.dynEqF_transport_form`, the congruence of `VR/cR/GR/ΦR/μR` with the
unfolded forms via `RXR5.AgreeOnQ`, and the final `HasDerivAt` transport along
`extG_gS_of_mem` — is reused unchanged). -/
theorem r7HEq {α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam} {S : ℝ}
    (hS : 0 < S) (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hSol : Work.FTS.FinalV2.Sol (Work.FTS.Regularity.pExp α) Φs E g)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (hμ : Work.FTS.RegExportIface.ClockBd α Φs E g)
    (hVP : ∀ S > 0, Work.FTS.RegExportIface.VelPkg (Work.FTS.Regularity.pExp α)
      (Work.FTS_RegExport.RXR7.μR α Φs E g) (Work.FTS_RegExport.RXR7.GR α g)
      (Work.FTS_RegExport.RXR7.ΦR α Φs E g) S) :
    ∀ z θ τ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 < τ → τ ≤ S →
      HasDerivAt (fun s => Work.FTS_RegExport.RXR7.Prof α g z θ s)
        (-(Work.FTS_RegExport.RXR7.K7 α Φs E g z θ τ)) τ := by
  intro z θ τ hz hθ hθlt hτ hτS
  have hp0 : 0 < pExp α := Work.FTS.Regularity.pExp_pos hα
  have hp1 : pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  have hQd : (z, θ) ∈ Work.Construction.Qd := ⟨hz, hθ, hθlt⟩
  -- the stream-function regularity, supplied here by `hVP` (in `RXT.Sys.gdot_eq_profile` it came
  -- from `hEll ∧ hEL3 ∧ hStar` via `psiCan_C3_proved`)
  have hΦ : ∀ τ' : ℝ, 0 < τ' → ContDiffOn ℝ 2
      (fun q : ℝ × ℝ => PsiCan Φs E g q.1 q.2 τ') Work.Construction.Qd :=
    r7_psiCan_c2 (α := α) (Φs := Φs) (E := E) (g := g) hVP
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
  have h1ab : slice (PsiCan Φs E g) τ z θ
      = Work.Construction.PhiTil (pExp α) (Work.Construction.Ftau (pExp α) g τ)
          (slice (PsiCan Φs E g) τ) z θ
        + Work.Construction.Theta (pExp α) (Work.Construction.Ftau (pExp α) g τ) z θ := by
    simp only [Work.Construction.PhiTil]; ring
  have halg := Work.FTS.MeridianDyn.Bridge.dynEqF_transport_form (α := pExp α)
    (μ := Work.FTS.Galerkin.muDyn (pExp α) (PsiCan Φs E g) g τ)
    (F := Work.Construction.Ftau (pExp α) g τ)
    (Φ := slice (PsiCan Φs E g) τ)
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
          (slice (PsiCan Φs E g) τ) z θ = 0 := by
    have h1 : Work.FTS.MeridianDyn.slice (Work.FTS.MeridianDyn.profFam (pExp α) g) τ
        = Work.Construction.Ftau (pExp α) g τ := rfl
    have h2 : Work.FTS.MeridianDyn.slice (PsiCan Φs E g) τ
        = slice (PsiCan Φs E g) τ := rfl
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
          (slice (PsiCan Φs E g) τ) z θ) := by
    linarith [hdyn]
  have hderiv0 : deriv (fun s => Work.Construction.Fstar (pExp α) z θ + g z θ s) τ
      = -(((1 - Work.FTS.Galerkin.muDyn (pExp α) (PsiCan Φs E g) g τ)
            + Work.Construction.L12 (Work.Construction.Ftau (pExp α) g τ) z
              * Work.Construction.c2m θ
            + 2 * pExp α * Work.Construction.Vop (Work.Construction.PhiTil (pExp α)
                (Work.Construction.Ftau (pExp α) g τ)
                (slice (PsiCan Φs E g) τ)) z θ)
          * Work.Spaces.Dz (Work.Construction.Ftau (pExp α) g τ) z θ
        + (2 * Work.Construction.Uop (pExp α)
            (slice (PsiCan Φs E g) τ) z θ)
          * Work.Spaces.pth (Work.Construction.Ftau (pExp α) g τ) z θ
        + ((1 + Work.FTS.Galerkin.muDyn (pExp α) (PsiCan Φs E g) g τ)
            - Work.Construction.L12 (Work.Construction.Ftau (pExp α) g τ) z / (pExp α)
            + Real.sin θ ^ 2 * Work.Construction.FK (Work.Construction.Ftau (pExp α) g τ) z
            - 2 * Work.Construction.Rop (pExp α) (Work.Construction.PhiTil (pExp α)
                (Work.Construction.Ftau (pExp α) g τ)
                (slice (PsiCan Φs E g) τ)) z θ)
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
                (slice (PsiCan Φs E g) τ)) z θ)
          * Work.Spaces.Dz (Work.Construction.Ftau (pExp α) g τ) z θ
        + (2 * Work.Construction.Uop (pExp α)
            (slice (PsiCan Φs E g) τ) z θ)
          * Work.Spaces.pth (Work.Construction.Ftau (pExp α) g τ) z θ
        + ((1 + Work.FTS.Galerkin.muDyn (pExp α) (PsiCan Φs E g) g τ)
            - Work.Construction.L12 (Work.Construction.Ftau (pExp α) g τ) z / (pExp α)
            + Real.sin θ ^ 2 * Work.Construction.FK (Work.Construction.Ftau (pExp α) g τ) z
            - 2 * Work.Construction.Rop (pExp α) (Work.Construction.PhiTil (pExp α)
                (Work.Construction.Ftau (pExp α) g τ)
                (slice (PsiCan Φs E g) τ)) z θ)
          * Work.Construction.Ftau (pExp α) g τ z θ)) τ := by
    rw [← hderiv0, ← hderivG, hHasG.deriv]
    exact hHasG
  -- transport the derivative to `profFull α (extG (GR α g))`
  have hevent : (fun s => Prof α g z θ s)
      =ᶠ[𝓝 τ] (fun s => Work.Construction.Fstar (pExp α) z θ + g z θ s) := by
    filter_upwards [isOpen_Ioi.mem_nhds hτ] with s hs
    show Work.Construction.Fstar (pExp α) z θ + extG (GR α g) z θ s
        = Work.Construction.Fstar (pExp α) z θ + g z θ s
    rw [r7_extG_GR_eq (g := g) α hz hθ.le hθlt.le hs.le]
  have hHas3 : HasDerivAt (fun s => Work.Construction.Fstar (pExp α) z θ
      + g z θ s)
      (-(((1 - Work.FTS.Galerkin.muDyn (pExp α) (PsiCan Φs E g) g τ)
            + Work.Construction.L12 (Work.Construction.Ftau (pExp α) g τ) z
              * Work.Construction.c2m θ
            + 2 * pExp α * Work.Construction.Vop (Work.Construction.PhiTil (pExp α)
                (Work.Construction.Ftau (pExp α) g τ)
                (slice (PsiCan Φs E g) τ)) z θ)
          * Work.Spaces.Dz (Work.Construction.Ftau (pExp α) g τ) z θ
        + (2 * Work.Construction.Uop (pExp α)
            (slice (PsiCan Φs E g) τ) z θ)
          * Work.Spaces.pth (Work.Construction.Ftau (pExp α) g τ) z θ
        + ((1 + Work.FTS.Galerkin.muDyn (pExp α) (PsiCan Φs E g) g τ)
            - Work.Construction.L12 (Work.Construction.Ftau (pExp α) g τ) z / (pExp α)
            + Real.sin θ ^ 2 * Work.Construction.FK (Work.Construction.Ftau (pExp α) g τ) z
            - 2 * Work.Construction.Rop (pExp α) (Work.Construction.PhiTil (pExp α)
                (Work.Construction.Ftau (pExp α) g τ)
                (slice (PsiCan Φs E g) τ)) z θ)
          * Work.Construction.Ftau (pExp α) g τ z θ)) τ :=
    (hasDerivAt_const_add_iff (Work.Construction.Fstar (pExp α) z θ)).mpr hHas2
  have hHas4 : HasDerivAt (fun s => Prof α g z θ s)
      (-(((1 - Work.FTS.Galerkin.muDyn (pExp α) (PsiCan Φs E g) g τ)
            + Work.Construction.L12 (Work.Construction.Ftau (pExp α) g τ) z
              * Work.Construction.c2m θ
            + 2 * pExp α * Work.Construction.Vop (Work.Construction.PhiTil (pExp α)
                (Work.Construction.Ftau (pExp α) g τ)
                (slice (PsiCan Φs E g) τ)) z θ)
          * Work.Spaces.Dz (Work.Construction.Ftau (pExp α) g τ) z θ
        + (2 * Work.Construction.Uop (pExp α)
            (slice (PsiCan Φs E g) τ) z θ)
          * Work.Spaces.pth (Work.Construction.Ftau (pExp α) g τ) z θ
        + ((1 + Work.FTS.Galerkin.muDyn (pExp α) (PsiCan Φs E g) g τ)
            - Work.Construction.L12 (Work.Construction.Ftau (pExp α) g τ) z / (pExp α)
            + Real.sin θ ^ 2 * Work.Construction.FK (Work.Construction.Ftau (pExp α) g τ) z
            - 2 * Work.Construction.Rop (pExp α) (Work.Construction.PhiTil (pExp α)
                (Work.Construction.Ftau (pExp α) g τ)
                (slice (PsiCan Φs E g) τ)) z θ)
          * Work.Construction.Ftau (pExp α) g τ z θ)) τ :=
    (Filter.EventuallyEq.hasDerivAt_iff hevent).mpr hHas3
  change HasDerivAt (fun s => Prof α g z θ s)
      (-(Vz7R α Φs E g z θ τ * Work.Spaces.Dz (fun z θ => Prof α g z θ τ) z θ
        + Vθ7R α Φs E g z θ τ * Work.Spaces.pth (fun z θ => Prof α g z θ τ) z θ
        + cs7R α Φs E g z θ τ * Prof α g z θ τ)) τ
  rw [← r7_transport_congr (α := α) (Φs := Φs) (E := E) (g := g) hz hθ hθlt hτ]
  exact hHas4

end Work.FTS_RegExport.RXR7
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.Sys.datum_jets =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `datum_jets` — the localised datum is `O(ω)` with all jets `j ≤ 8`, `i ≤ 6`

Same argument as `Work.FTS_RegExport.RXT.datum_bound` (which handles the six index pairs
`RXT.idx k`), but for the *full* index rectangle `j ≤ 8`, `i ≤ 6` needed by the strong-solution
route.  The two ingredients are

* the radial pointwise bound `|D_z^j locR| ≤ A·z²/(1+z)²` for `j ≤ 8`
  (`Work.FTS_RegExport.RXT.radial_jet_omega_local`), and
* the angular jet bound `|D_θ^i Γ| ≤ 10⁵·Γ` for `i ≤ 6`
  (`Work.FTS.LocData6.DthIter_Gam_abs_le6`),

combined through the separability identity `Work.FTS.LocDataExt.mixed_sepGam` and the
identification `Gam (pExp α) = Gamma α` of the two angular factors.
-/

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.FTS_RegExport.RXT.Sys

/-- **The localised datum `locG6 (pExp α) L β` is `O(ω)` with all mixed jets `j ≤ 8`, `i ≤ 6`**,
`ω α z θ = z²·Γ(θ)/(1+z)²` being the self-similar weight.  The datum is separable,
`locG6 = locR(z)·Γ(θ)`, so the statement is the product of the radial jet bound (order ≤ 8) and
the angular jet bound (order ≤ 6). -/
theorem datum_jets {α L β : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) (hL : 1 ≤ L) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ j i : ℕ, j ≤ 8 → i ≤ 6 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed j i (Work.FTS.LocData6.locG6 (Work.FTS.Regularity.pExp α) L β) z θ|
        ≤ K * Work.FTS.RegExportIface.ω α z θ := by
  obtain ⟨A, hA0, hA⟩ := Work.FTS_RegExport.RXT.radial_jet_omega_local hα hα13 hL
  refine ⟨100000 * A, mul_nonneg (by norm_num) hA0, fun j i hj hi z θ hz hθ0 hθ1 => ?_⟩
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, le_of_lt hθ1⟩
  have hrad := hA j hj z θ hz
  have hang := Work.FTS.LocData6.DthIter_Gam_abs_le6 i hi (Work.FTS.Regularity.pExp α)
    (Work.FTS.Regularity.pExp_pos hα) (Work.FTS.Regularity.pExp_le_one hα13) hθI
  have hfac : Work.FTS.LocData6.locG6 (Work.FTS.Regularity.pExp α) L β
      = fun z θ => Work.FTS.LocDataExt.locR (Work.FTS.Regularity.pExp α) L β z
          * Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ := by
    rw [Work.FTS.LocData6.locG6_eq, Work.FTS.LocDataExt.locG_eq_locR_Gam]
  rw [hfac, Work.FTS.LocDataExt.mixed_sepGam, abs_mul]
  refine (mul_le_mul hrad hang (abs_nonneg _) (mul_nonneg hA0 (by positivity))).trans ?_
  have heq : (A * (z ^ 2 / (1 + z) ^ 2))
        * (100000 * Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ)
      = (100000 * A) * Work.FTS.RegExportIface.ω α z θ := by
    rw [Work.FTS_RegExport.RXT.Gam_pExp_eq_Gamma, Work.FTS.RegExportIface.ω]
    ring
  exact le_of_eq heq

end Work.FTS_RegExport.RXT.Sys
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.Sys.intervalIntegrable_mixed_gdot =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.FTS_RegExport.RXT.Sys

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Two elementary tools -/

/-- **The slots of total order `≤ 1` of a `C²` function on the open quadrant are `C¹`.**  This is
the only place where the `C²`-regularity of `GdotLoc` is used beyond differentiability of `G`: the
`z`- and `θ`-slices of `mixed j i` (`j + i ≤ 1`) are differentiable at every point of `Q0`.
(For `j = i = 0` it is `ContDiffOn.of_le`; for the two first-order slots it is the finite-order
`D`-calculus of `Work.FTS.StrongEps`.) -/
private theorem contDiffOn_one_of_total_le_one {H : ℝ → ℝ → ℝ}
    (hH : ContDiffOn ℝ 2 (Function.uncurry H) Work.FTS.EllipticEst.Q0) {j i : ℕ} (hji : j + i ≤ 1) :
    ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.mixed j i H)) Work.FTS.EllipticEst.Q0 := by
  obtain rfl | rfl : j = 0 ∨ j = 1 := by omega
  · obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
    · simpa [Work.Spaces.mixed] using hH.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
    · simpa [Work.Spaces.mixed] using Work.FTS.StrongEps.contDiffOn_uncurry_Dth_fin
        Work.FTS.EllipticEst.isOpen_Q0 (n := 1) hH
  · obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
    · simpa [Work.Spaces.mixed] using Work.FTS.StrongEps.contDiffOn_uncurry_Dz_fin
        Work.FTS.EllipticEst.isOpen_Q0 (n := 1) hH
    · omega

/-- `HasDerivAt` turns the right-hand difference quotients along `ε₀/(n+1)` into a limit. -/
private theorem tendsto_slope_seq {f : ℝ → ℝ} {x L ε₀ : ℝ} (hε : 0 < ε₀)
    (h : HasDerivAt f L x) :
    Tendsto (fun n : ℕ => (f (x + ε₀ / (n + 1)) - f x) / (ε₀ / (n + 1))) atTop (𝓝 L) := by
  have hδ0 : Tendsto (fun n : ℕ => ε₀ / (n + 1)) atTop (𝓝 (0 : ℝ)) := by
    have h1 : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa [div_eq_mul_inv, mul_comm] using h1.const_mul ε₀
  have hpos : ∀ n : ℕ, ε₀ / (n + 1) ≠ 0 := fun n => by positivity
  have hx : Tendsto (fun n : ℕ => x + ε₀ / (n + 1)) atTop (𝓝[≠] x) :=
    tendsto_nhdsWithin_iff.mpr ⟨by simpa using hδ0.const_add x,
      Filter.Eventually.of_forall fun n => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        intro hh
        exact hpos n (by linarith)⟩
  refine (h.tendsto_slope.comp hx).congr' ?_
  filter_upwards with n
  simp only [Function.comp_apply, slope, smul_eq_mul, div_eq_mul_inv, vsub_eq_sub]
  ring

/-! ## The two induction steps -/

/-- **The `z`-step.**  If the values `σ ↦ mixed j i (H σ) a b` are measurable (`j + i ≤ 1`), then
so are the values of `mixed (j+1) i`: on `σ ∈ (0,S]` the latter is `a` times the `z`-difference
quotient of the former, and outside that set both sides vanish. -/
private theorem measurable_zstep {S : ℝ} {H : ℝ → ℝ → ℝ → ℝ} {j i : ℕ} (hji : j + i ≤ 1)
    (hCd : ∀ σ ∈ Set.Ioc (0 : ℝ) S,
      ContDiffOn ℝ 2 (Function.uncurry (H σ)) Work.FTS.EllipticEst.Q0)
    (ih : ∀ a b : ℝ, (a, b) ∈ Work.FTS.EllipticEst.Q0 →
      Measurable (fun σ : ℝ => if σ ∈ Set.Ioc (0 : ℝ) S then
        Work.Spaces.mixed j i (H σ) a b else 0)) :
    ∀ a b : ℝ, (a, b) ∈ Work.FTS.EllipticEst.Q0 →
      Measurable (fun σ : ℝ => if σ ∈ Set.Ioc (0 : ℝ) S then
        Work.Spaces.mixed (j + 1) i (H σ) a b else 0) := by
  intro a b hab
  obtain ⟨ha, hb0, hb1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hab
  have hδpos : ∀ n : ℕ, 0 < a / ((n : ℝ) + 1) := fun n => by positivity
  have hmem : ∀ n : ℕ, (a + a / ((n : ℝ) + 1), b) ∈ Work.FTS.EllipticEst.Q0 := fun n =>
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨by linarith [hδpos n], hb0, hb1⟩
  have hdiff : ∀ σ ∈ Set.Ioc (0 : ℝ) S, HasDerivAt (fun z' => Work.Spaces.mixed j i (H σ) z' b)
      (Work.Spaces.pz (Work.Spaces.mixed j i (H σ)) a b) a := by
    intro σ hσ
    have hB : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.mixed j i (H σ)))
        Work.FTS.EllipticEst.Q0 := contDiffOn_one_of_total_le_one (hCd σ hσ) hji
    have hD : DifferentiableAt ℝ (Function.uncurry (Work.Spaces.mixed j i (H σ))) (a, b) :=
      (hB.differentiableOn (by norm_num)).differentiableAt
        (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hab)
    simpa [Work.Spaces.pz] using (Work.Spaces.differentiableAt_curry_left hD).hasDerivAt
  have hmeas : ∀ n : ℕ, Measurable (fun σ : ℝ => if σ ∈ Set.Ioc (0 : ℝ) S then
      a * ((Work.Spaces.mixed j i (H σ) (a + a / ((n : ℝ) + 1)) b
        - Work.Spaces.mixed j i (H σ) a b) / (a / ((n : ℝ) + 1))) else 0) := by
    intro n
    have h1 := ih (a + a / ((n : ℝ) + 1)) b (hmem n)
    have h2 := ih a b hab
    have heq : (fun σ : ℝ => if σ ∈ Set.Ioc (0 : ℝ) S then
        a * ((Work.Spaces.mixed j i (H σ) (a + a / ((n : ℝ) + 1)) b
          - Work.Spaces.mixed j i (H σ) a b) / (a / ((n : ℝ) + 1))) else 0)
        = fun σ : ℝ => a * (((if σ ∈ Set.Ioc (0 : ℝ) S then
            Work.Spaces.mixed j i (H σ) (a + a / ((n : ℝ) + 1)) b else 0)
          - (if σ ∈ Set.Ioc (0 : ℝ) S then Work.Spaces.mixed j i (H σ) a b else 0))
            / (a / ((n : ℝ) + 1))) := by
      funext σ
      by_cases hσ : σ ∈ Set.Ioc (0 : ℝ) S <;> simp [hσ]
    rw [heq]
    exact ((h1.sub h2).div_const (a / ((n : ℝ) + 1))).const_mul a
  refine measurable_of_tendsto_metrizable hmeas ?_
  rw [tendsto_pi_nhds]
  intro σ
  by_cases hσ : σ ∈ Set.Ioc (0 : ℝ) S
  · rw [ite_eq_left hσ]
    have hlim := tendsto_slope_seq ha (hdiff σ hσ)
    have hval : Work.Spaces.mixed (j + 1) i (H σ) a b
        = a * Work.Spaces.pz (Work.Spaces.mixed j i (H σ)) a b := rfl
    rw [hval]
    refine (hlim.const_mul a).congr' ?_
    filter_upwards with n
    rw [ite_eq_left hσ]
  · rw [ite_eq_right hσ]
    have hzero : (fun n : ℕ => if σ ∈ Set.Ioc (0 : ℝ) S then
        a * ((Work.Spaces.mixed j i (H σ) (a + a / ((n : ℝ) + 1)) b
          - Work.Spaces.mixed j i (H σ) a b) / (a / ((n : ℝ) + 1))) else 0)
        = fun _ : ℕ => (0 : ℝ) := by
      funext n
      exact ite_eq_right hσ
    rw [hzero]
    exact tendsto_const_nhds

/-- **The `θ`-step, with `D_z` outermost** (`j = 0`, `i ≤ 1`): the analogue of `measurable_zstep`
in the angular direction, with the coefficient `sin (2θ)` and the shift `(π/2-θ)/(2(n+1))`, which
keeps the sample points inside the open quadrant.  Only this case of the `θ`-step is used, so no
commutation of `D_z` with `D_θ` is required. -/
private theorem measurable_thetastep_zero {S : ℝ} {H : ℝ → ℝ → ℝ → ℝ} {i : ℕ} (hi : i ≤ 1)
    (hCd : ∀ σ ∈ Set.Ioc (0 : ℝ) S,
      ContDiffOn ℝ 2 (Function.uncurry (H σ)) Work.FTS.EllipticEst.Q0)
    (ih : ∀ a b : ℝ, (a, b) ∈ Work.FTS.EllipticEst.Q0 →
      Measurable (fun σ : ℝ => if σ ∈ Set.Ioc (0 : ℝ) S then
        Work.Spaces.mixed 0 i (H σ) a b else 0)) :
    ∀ a b : ℝ, (a, b) ∈ Work.FTS.EllipticEst.Q0 →
      Measurable (fun σ : ℝ => if σ ∈ Set.Ioc (0 : ℝ) S then
        Work.Spaces.mixed 0 (i + 1) (H σ) a b else 0) := by
  intro a b hab
  obtain ⟨ha, hb0, hb1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hab
  have hε : 0 < (Real.pi / 2 - b) / 2 := by linarith
  have hδmem : ∀ n : ℕ, (a, b + ((Real.pi / 2 - b) / 2) / ((n : ℝ) + 1))
      ∈ Work.FTS.EllipticEst.Q0 := by
    intro n
    have hden : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have hδpos : 0 < ((Real.pi / 2 - b) / 2) / ((n : ℝ) + 1) := div_pos hε (by linarith)
    have hle : ((Real.pi / 2 - b) / 2) / ((n : ℝ) + 1) ≤ (Real.pi / 2 - b) / 2 :=
      div_le_self (by linarith) hden
    exact Work.FTS.EllipticEst.mem_Q0.mpr ⟨ha, by linarith, by linarith⟩
  have hdiff : ∀ σ ∈ Set.Ioc (0 : ℝ) S,
      HasDerivAt (fun θ' => Work.Spaces.mixed 0 i (H σ) a θ')
        (Work.Spaces.pth (Work.Spaces.mixed 0 i (H σ)) a b) b := by
    intro σ hσ
    have hB : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.mixed 0 i (H σ)))
        Work.FTS.EllipticEst.Q0 := contDiffOn_one_of_total_le_one (hCd σ hσ) (by omega)
    have hD : DifferentiableAt ℝ (Function.uncurry (Work.Spaces.mixed 0 i (H σ))) (a, b) :=
      (hB.differentiableOn (by norm_num)).differentiableAt
        (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hab)
    simpa [Work.Spaces.pth] using (Work.Spaces.differentiableAt_curry_right hD).hasDerivAt
  have hmeas : ∀ n : ℕ, Measurable (fun σ : ℝ => if σ ∈ Set.Ioc (0 : ℝ) S then
      Real.sin (2 * b) * ((Work.Spaces.mixed 0 i (H σ) a
        (b + ((Real.pi / 2 - b) / 2) / ((n : ℝ) + 1))
        - Work.Spaces.mixed 0 i (H σ) a b) / (((Real.pi / 2 - b) / 2) / ((n : ℝ) + 1))) else 0) := by
    intro n
    have h1 := ih a (b + ((Real.pi / 2 - b) / 2) / ((n : ℝ) + 1)) (hδmem n)
    have h2 := ih a b hab
    have heq : (fun σ : ℝ => if σ ∈ Set.Ioc (0 : ℝ) S then
        Real.sin (2 * b) * ((Work.Spaces.mixed 0 i (H σ) a
          (b + ((Real.pi / 2 - b) / 2) / ((n : ℝ) + 1))
          - Work.Spaces.mixed 0 i (H σ) a b) / (((Real.pi / 2 - b) / 2) / ((n : ℝ) + 1))) else 0)
        = fun σ : ℝ => Real.sin (2 * b) * (((if σ ∈ Set.Ioc (0 : ℝ) S then
            Work.Spaces.mixed 0 i (H σ) a (b + ((Real.pi / 2 - b) / 2) / ((n : ℝ) + 1)) else 0)
          - (if σ ∈ Set.Ioc (0 : ℝ) S then Work.Spaces.mixed 0 i (H σ) a b else 0))
            / (((Real.pi / 2 - b) / 2) / ((n : ℝ) + 1))) := by
      funext σ
      by_cases hσ : σ ∈ Set.Ioc (0 : ℝ) S <;> simp [hσ]
    rw [heq]
    exact ((h1.sub h2).div_const (((Real.pi / 2 - b) / 2) / ((n : ℝ) + 1))).const_mul
      (Real.sin (2 * b))
  refine measurable_of_tendsto_metrizable hmeas ?_
  rw [tendsto_pi_nhds]
  intro σ
  by_cases hσ : σ ∈ Set.Ioc (0 : ℝ) S
  · rw [ite_eq_left hσ]
    have hlim := tendsto_slope_seq hε (hdiff σ hσ)
    have hval : Work.Spaces.mixed 0 (i + 1) (H σ) a b
        = Real.sin (2 * b) * Work.Spaces.pth (Work.Spaces.mixed 0 i (H σ)) a b := rfl
    rw [hval]
    refine (hlim.const_mul (Real.sin (2 * b))).congr' ?_
    filter_upwards with n
    rw [ite_eq_left hσ]
  · rw [ite_eq_right hσ]
    have hzero : (fun n : ℕ => if σ ∈ Set.Ioc (0 : ℝ) S then
        Real.sin (2 * b) * ((Work.Spaces.mixed 0 i (H σ) a
          (b + ((Real.pi / 2 - b) / 2) / ((n : ℝ) + 1))
          - Work.Spaces.mixed 0 i (H σ) a b) / (((Real.pi / 2 - b) / 2) / ((n : ℝ) + 1)))
          else 0) = fun _ : ℕ => (0 : ℝ) := by
      funext n
      exact ite_eq_right hσ
    rw [hzero]
    exact tendsto_const_nhds

/-! ## The measurability of the six components -/

/-- **Measurability in `σ` of the mixed jets of `∂_τ g`.**  If every slice `gdot g σ`
(`σ ∈ (0,S]`) is `C²` on the open quadrant, then for every point `(a,b)` of the open quadrant and
every `(j,i)` with `j + i ≤ 2`, the map `σ ↦ mixed j i (gdot g σ) a b` is measurable on `(0,S]`.

The induction is over the total order, and each step keeps `D_z` outermost (see
`measurable_zstep` / `measurable_thetastep_zero`); the induction hypothesis is stated for *all*
points of the open quadrant, since the difference quotients are taken at neighbouring points. -/
private theorem measurable_mixed_gdot_quadrant {S : ℝ} {g : Work.FTS.Galerkin.Fam}
    (hCd : ∀ σ ∈ Set.Ioc (0 : ℝ) S,
      ContDiffOn ℝ 2 (Function.uncurry (Work.FTS.Galerkin.gdot g σ)) Work.FTS.EllipticEst.Q0) :
    ∀ j i : ℕ, j + i ≤ 2 → ∀ a b : ℝ, (a, b) ∈ Work.FTS.EllipticEst.Q0 →
      Measurable (fun σ : ℝ => if σ ∈ Set.Ioc (0 : ℝ) S then
        Work.Spaces.mixed j i (Work.FTS.Galerkin.gdot g σ) a b else 0) := by
  have key : ∀ n j i : ℕ, j + i = n → j + i ≤ 2 →
      ∀ a b : ℝ, (a, b) ∈ Work.FTS.EllipticEst.Q0 →
        Measurable (fun σ : ℝ => if σ ∈ Set.Ioc (0 : ℝ) S then
          Work.Spaces.mixed j i (Work.FTS.Galerkin.gdot g σ) a b else 0) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ihn =>
      intro j i hsum h2 a b hab
      rcases Nat.eq_zero_or_pos j with hj | hj
      · subst hj
        rcases Nat.eq_zero_or_pos i with hi | hi
        · subst hi
          have heq : (fun σ : ℝ => if σ ∈ Set.Ioc (0 : ℝ) S then
                Work.Spaces.mixed 0 0 (Work.FTS.Galerkin.gdot g σ) a b else 0)
              = fun σ : ℝ => if σ ∈ Set.Ioc (0 : ℝ) S then deriv (fun s => g a b s) σ else 0 := by
            funext σ
            by_cases hσ : σ ∈ Set.Ioc (0 : ℝ) S <;> simp [hσ, Work.FTS.Galerkin.gdot]
          rw [heq]
          exact Measurable.ite measurableSet_Ioc (measurable_deriv _) measurable_const
        · obtain ⟨i', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
          exact measurable_thetastep_zero (by omega) hCd
            (ihn i' (by omega) 0 i' (Nat.zero_add i') (by omega)) a b hab
      · obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
        exact measurable_zstep (by omega) hCd
          (ihn (j' + i) (by omega) j' i rfl (by omega)) a b hab
  intro j i hji
  exact key (j + i) j i rfl hji

/-! ## Integrability on the horizon -/

/-! The bound on the jets is `abs_mixed_gdot_le_of_GdotLoc` (from the compact-box bounds of
`GdotLoc`), the a.e. strong measurability is `aestronglyMeasurable_restrict_of_ae_eq` applied to
the measurable `if`-function of `measurable_mixed_gdot_quadrant`, and the integrability on the
finite interval is `integrableOn_Ioc_of_abs_bound`. -/

/-! ## The statement -/

theorem intervalIntegrable_mixed_gdot {S α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hS : 0 < S) (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hSol : Work.FTS.FinalV2.Sol (Work.FTS.Regularity.pExp α) Φs E g)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (hG : Work.FTS.RegExportIface.RXT.GdotLoc S g) :
    ∀ k : Fin 6, ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      IntervalIntegrable (fun σ => Work.Spaces.mixed (Work.FTS.RegExportIface.RXT.idx k).1
        (Work.FTS.RegExportIface.RXT.idx k).2 (Work.FTS.Galerkin.gdot g σ) z θ)
        MeasureTheory.volume 0 S := by
  intro k z θ hz hθ0 hθ1
  have hji : (Work.FTS.RegExportIface.RXT.idx k).1 + (Work.FTS.RegExportIface.RXT.idx k).2 ≤ 2 := by
    fin_cases k <;> simp [Work.FTS.RegExportIface.RXT.idx]
  have hmem : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ0, hθ1⟩
  have hit : Measurable (fun σ : ℝ => if σ ∈ Set.Ioc (0 : ℝ) S then
      Work.Spaces.mixed (Work.FTS.RegExportIface.RXT.idx k).1
        (Work.FTS.RegExportIface.RXT.idx k).2 (Work.FTS.Galerkin.gdot g σ) z θ else 0) :=
    measurable_mixed_gdot_quadrant (S := S) hG.1 _ _ hji z θ hmem
  have haesm : AEStronglyMeasurable
      (fun σ : ℝ => Work.Spaces.mixed (Work.FTS.RegExportIface.RXT.idx k).1
        (Work.FTS.RegExportIface.RXT.idx k).2 (Work.FTS.Galerkin.gdot g σ) z θ)
      (volume.restrict (Set.Ioc (0 : ℝ) S)) :=
    aestronglyMeasurable_restrict_of_ae_eq measurableSet_Ioc hit
      (fun σ hσ => by rw [ite_eq_left hσ])
  obtain ⟨C, hC0, hC⟩ := abs_mixed_gdot_le_of_GdotLoc (S := S) hG hji hz hθ0 hθ1
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hS.le).mpr
    (integrableOn_Ioc_of_abs_bound hC0 haesm hC)

end Work.FTS_RegExport.RXT.Sys
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.Sys.miiSteps =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.Sys.mixed_integral_identity` — S5a of the RX-St1 leaf plan

The integrated identity for the six components `w_k = D_z^{j}D_θ^{i}(slice g τ)`, `(j,i) = idx k`:

  `w_k(τ₂) − w_k(τ₁) = ∫_{τ₁}^{τ₂} (D^β ∂_τ g)(σ) dσ`.

The proof is by induction on the total order `j + i ≤ 2`.  The slot `(0,0)` is the fundamental
theorem of calculus in `τ` (the dynamic equation gives the pointwise derivative
`∂_τg(σ) = deriv (fun s => g z θ s) σ`, `RegPkgMin.cont` the continuity, and `GdotLoc` the
integrability).  Each step `(j,i) → (j+1,i)` (resp. `(0,i) → (0,i+1)`) differentiates the identity
for `(j,i)` in the variable `z` (resp. `θ`) along the difference-quotient sequence `z/(n+1)`
(resp. `((π/2−θ)/2)/(n+1)`) and passes to the limit with the dominated convergence theorem; the
domination is the uniform sup bound of `GdotLoc` combined with the mean value theorem.  Only
`D_z`-outermost and `D_θ`-outermost steps occur, so no commutation of `D_z` with `D_θ` is needed.
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter MeasureTheory

namespace Work.FTS_RegExport.RXT.Sys

open Work.FTS.Galerkin (Fn Fam slice gdot)
open Work.FTS.RegExportIface.RXT (idx GdotLoc)
open Work.FTS.Regularity (pExp)

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The base case -/

/-- **The base case `(0,0)`**: the fundamental theorem of calculus in `τ`. -/
theorem mii_P_00 {S : ℝ} {g : Fam}
    (hcont : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → ContinuousOn (fun τ => g z θ τ) (Set.Ici 0))
    (hderiv : ∀ z θ σ, 0 < σ → (z, θ) ∈ Work.Construction.Qd →
      HasDerivAt (fun s => g z θ s) (gdot g σ z θ) σ)
    (hR : mii_R S g 0 0) : mii_P S g 0 0 := by
  intro z θ hz hθ hθ' τ₁ τ₂ h0 h12 h2S
  have hQd : (z, θ) ∈ Work.Construction.Qd := ⟨hz, hθ, hθ'⟩
  have hder : ∀ σ ∈ Set.Ioo τ₁ τ₂, HasDerivAt (fun s : ℝ => g z θ s) (gdot g σ z θ) σ :=
    fun σ hσ => hderiv z θ σ (by linarith [hσ.1, h0]) hQd
  have hcont' : ContinuousOn (fun s : ℝ => g z θ s) (Set.Icc τ₁ τ₂) :=
    (hcont z θ hQd).mono fun s hs => h0.trans hs.1
  have hint : IntervalIntegrable (fun σ : ℝ => gdot g σ z θ) volume τ₁ τ₂ :=
    hR z θ hz hθ hθ' τ₁ τ₂ h0 h12 h2S
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le h12 hcont' hder hint
  simp only [Work.Spaces.mixed, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_zero,
    Work.FTS.Galerkin.slice_apply]
  rw [hFTC]

/-! ## The step in `z` -/

/-- **The step `(j,i) → (j+1,i)`**: differentiation in `z` of the identity for `(j,i)`, along the
difference-quotient sequence `z/(n+1)`. -/
theorem mii_step_z {S : ℝ} {g : Fam} (hG : GdotLoc S g)
    (hc4 : ∀ τ, 0 ≤ τ → ContDiffOn ℝ 4 (Function.uncurry (slice g τ)) Work.FTS.EllipticEst.Q0)
    {j i : ℕ} (hji : j + i ≤ 1) (hP : mii_P S g j i) (hR : mii_R S g j i) :
    mii_P S g (j + 1) i := by
  intro z θ hz hθ hθ' τ₁ τ₂ h0 h12 h2S
  obtain ⟨C, hC0, hC⟩ := mii_abs_pz_mixed_gdot_le hG (j := j) (i := i) hji hz hθ hθ'
  have hmeas : ∀ y θ', 0 < y → 0 < θ' → θ' < Real.pi / 2 →
      AEStronglyMeasurable (fun σ => Work.Spaces.mixed j i (gdot g σ) y θ')
        (volume.restrict (Set.Ioc τ₁ τ₂)) :=
    mii_aesm_mixed_gdot_low hG h0 h2S j i hji
  -- the limit of the left-hand sides
  have hA : ∀ τ ∈ Set.Icc (0 : ℝ) S,
      Tendsto (fun n : ℕ => z * ((Work.Spaces.mixed j i (slice g τ) (z + z / ((n : ℝ) + 1)) θ
          - Work.Spaces.mixed j i (slice g τ) z θ) / (z / ((n : ℝ) + 1)))) atTop
        (𝓝 (Work.Spaces.mixed (j + 1) i (slice g τ) z θ)) := by
    intro τ hτ
    have hd : HasDerivAt (fun y : ℝ => Work.Spaces.mixed j i (slice g τ) y θ)
        (Work.Spaces.pz (Work.Spaces.mixed j i (slice g τ)) z θ) z :=
      mii_hasDerivAt_mixed_slice_z (n := 4) (hc4 τ hτ.1) (by omega) hz ⟨hθ, hθ'⟩
    have h1 := (mii_tendsto_slope_seq hz hd).const_mul z
    simpa only [mii_mixed_succ_apply] using h1
  -- the dominated convergence theorem
  have hHmeas : ∀ n : ℕ, AEStronglyMeasurable
      (fun σ : ℝ => z * ((Work.Spaces.mixed j i (gdot g σ) (z + z / ((n : ℝ) + 1)) θ
          - Work.Spaces.mixed j i (gdot g σ) z θ) / (z / ((n : ℝ) + 1))))
      (volume.restrict (Set.Ioc τ₁ τ₂)) := by
    intro n
    have h1 := hmeas (z + z / ((n : ℝ) + 1)) θ (by positivity) hθ hθ'
    have h2 := hmeas z θ hz hθ hθ'
    have h3 : AEStronglyMeasurable
        (fun σ : ℝ => (z / ((n : ℝ) + 1))⁻¹
          * (Work.Spaces.mixed j i (gdot g σ) (z + z / ((n : ℝ) + 1)) θ
            - Work.Spaces.mixed j i (gdot g σ) z θ)) (volume.restrict (Set.Ioc τ₁ τ₂)) :=
      (h1.sub h2).const_mul _
    refine (h3.const_mul z).congr (Filter.Eventually.of_forall fun σ => ?_)
    simp only [div_eq_mul_inv]
    ring
  have hHbound : ∀ n : ℕ, ∀ᵐ σ ∂(volume.restrict (Set.Ioc τ₁ τ₂)),
      ‖z * ((Work.Spaces.mixed j i (gdot g σ) (z + z / ((n : ℝ) + 1)) θ
          - Work.Spaces.mixed j i (gdot g σ) z θ) / (z / ((n : ℝ) + 1)))‖ ≤ z * C := by
    intro n
    rw [ae_restrict_iff' measurableSet_Ioc]
    refine Filter.Eventually.of_forall fun σ hσ => ?_
    have hσmem : σ ∈ Set.Ioc (0 : ℝ) S := ⟨lt_of_le_of_lt h0 hσ.1, le_trans hσ.2 h2S⟩
    have ht : 0 < z / ((n : ℝ) + 1) := by positivity
    have htle : z / ((n : ℝ) + 1) ≤ z := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    have hcont : ContinuousOn (fun y : ℝ => Work.Spaces.mixed j i (gdot g σ) y θ)
        (Set.Icc z (z + z / ((n : ℝ) + 1))) :=
      mii_continuousOn_mixed_slice_z (n := 2) (hG.1 σ hσmem) (by omega) ⟨hθ, hθ'⟩ hz
    have hdiff : ∀ y ∈ Set.Ioo z (z + z / ((n : ℝ) + 1)),
        HasDerivAt (fun y' : ℝ => Work.Spaces.mixed j i (gdot g σ) y' θ)
          (deriv (fun y' : ℝ => Work.Spaces.mixed j i (gdot g σ) y' θ) y) y := by
      intro y hy
      exact (mii_hasDerivAt_mixed_slice_z (n := 2) (hG.1 σ hσmem) (by omega)
        (by linarith [hy.1]) ⟨hθ, hθ'⟩).differentiableAt.hasDerivAt
    have hb : ∀ y ∈ Set.Icc z (z + z / ((n : ℝ) + 1)),
        |deriv (fun y' : ℝ => Work.Spaces.mixed j i (gdot g σ) y' θ) y| ≤ C := by
      intro y hy
      have hy2 : y ≤ 2 * z := by linarith [hy.2, htle]
      have h1 : deriv (fun y' : ℝ => Work.Spaces.mixed j i (gdot g σ) y' θ) y
          = Work.Spaces.pz (Work.Spaces.mixed j i (gdot g σ)) y θ := rfl
      rw [h1]
      exact hC σ hσmem y ⟨by linarith [hy.1], hy2⟩
    have hMVT := mii_abs_sub_le_of_abs_deriv_le (a := z) (b := z + z / ((n : ℝ) + 1))
      (by linarith [ht]) hcont hdiff hb
    have hMVT' : |Work.Spaces.mixed j i (gdot g σ) (z + z / ((n : ℝ) + 1)) θ
        - Work.Spaces.mixed j i (gdot g σ) z θ| ≤ C * (z / ((n : ℝ) + 1)) := by
      have h := hMVT
      rwa [show z + z / ((n : ℝ) + 1) - z = z / ((n : ℝ) + 1) by ring] at h
    calc ‖z * ((Work.Spaces.mixed j i (gdot g σ) (z + z / ((n : ℝ) + 1)) θ
          - Work.Spaces.mixed j i (gdot g σ) z θ) / (z / ((n : ℝ) + 1)))‖
        = z * (|Work.Spaces.mixed j i (gdot g σ) (z + z / ((n : ℝ) + 1)) θ
            - Work.Spaces.mixed j i (gdot g σ) z θ| / (z / ((n : ℝ) + 1))) := by
          rw [Real.norm_eq_abs, abs_mul, abs_of_pos hz, abs_div, abs_of_pos ht]
      _ ≤ z * (C * (z / ((n : ℝ) + 1)) / (z / ((n : ℝ) + 1))) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hMVT' (le_of_lt ht)) (le_of_lt hz)
      _ = z * C := by field_simp
  have hHlim : ∀ᵐ σ ∂(volume.restrict (Set.Ioc τ₁ τ₂)),
      Tendsto (fun n : ℕ => z * ((Work.Spaces.mixed j i (gdot g σ) (z + z / ((n : ℝ) + 1)) θ
          - Work.Spaces.mixed j i (gdot g σ) z θ) / (z / ((n : ℝ) + 1)))) atTop
        (𝓝 (Work.Spaces.mixed (j + 1) i (gdot g σ) z θ)) := by
    rw [ae_restrict_iff' measurableSet_Ioc]
    refine Filter.Eventually.of_forall fun σ hσ => ?_
    have hσmem : σ ∈ Set.Ioc (0 : ℝ) S := ⟨lt_of_le_of_lt h0 hσ.1, le_trans hσ.2 h2S⟩
    have hd : HasDerivAt (fun y : ℝ => Work.Spaces.mixed j i (gdot g σ) y θ)
        (Work.Spaces.pz (Work.Spaces.mixed j i (gdot g σ)) z θ) z :=
      mii_hasDerivAt_mixed_slice_z (n := 2) (hG.1 σ hσmem) (by omega) hz ⟨hθ, hθ'⟩
    have h1 := (mii_tendsto_slope_seq hz hd).const_mul z
    simpa only [mii_mixed_succ_apply] using h1
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioc τ₁ τ₂)) :=
    isFiniteMeasure_restrict.mpr measure_Ioc_lt_top.ne
  have hDCT := tendsto_integral_of_dominated_convergence
    (μ := volume.restrict (Set.Ioc τ₁ τ₂))
    (F := fun n σ => z * ((Work.Spaces.mixed j i (gdot g σ) (z + z / ((n : ℝ) + 1)) θ
        - Work.Spaces.mixed j i (gdot g σ) z θ) / (z / ((n : ℝ) + 1))))
    (f := fun σ => Work.Spaces.mixed (j + 1) i (gdot g σ) z θ)
    (fun _ : ℝ => z * C) hHmeas (integrable_const _) hHbound hHlim
  -- the value of each integral
  have hCval : ∀ n : ℕ, (∫ σ in τ₁..τ₂, z * ((Work.Spaces.mixed j i (gdot g σ)
        (z + z / ((n : ℝ) + 1)) θ - Work.Spaces.mixed j i (gdot g σ) z θ) / (z / ((n : ℝ) + 1))))
      = z * ((Work.Spaces.mixed j i (slice g τ₂) (z + z / ((n : ℝ) + 1)) θ
          - Work.Spaces.mixed j i (slice g τ₂) z θ) / (z / ((n : ℝ) + 1)))
        - z * ((Work.Spaces.mixed j i (slice g τ₁) (z + z / ((n : ℝ) + 1)) θ
          - Work.Spaces.mixed j i (slice g τ₁) z θ) / (z / ((n : ℝ) + 1))) := by
    intro n
    have h1 : (∫ σ in τ₁..τ₂, Work.Spaces.mixed j i (gdot g σ) (z + z / ((n : ℝ) + 1)) θ)
        = Work.Spaces.mixed j i (slice g τ₂) (z + z / ((n : ℝ) + 1)) θ
          - Work.Spaces.mixed j i (slice g τ₁) (z + z / ((n : ℝ) + 1)) θ :=
      (hP (z + z / ((n : ℝ) + 1)) θ (by positivity) hθ hθ' τ₁ τ₂ h0 h12 h2S).symm
    have h2 : (∫ σ in τ₁..τ₂, Work.Spaces.mixed j i (gdot g σ) z θ)
        = Work.Spaces.mixed j i (slice g τ₂) z θ - Work.Spaces.mixed j i (slice g τ₁) z θ :=
      (hP z θ hz hθ hθ' τ₁ τ₂ h0 h12 h2S).symm
    have hi1 : IntervalIntegrable
        (fun σ => Work.Spaces.mixed j i (gdot g σ) (z + z / ((n : ℝ) + 1)) θ) volume τ₁ τ₂ :=
      hR (z + z / ((n : ℝ) + 1)) θ (by positivity) hθ hθ' τ₁ τ₂ h0 h12 h2S
    have hi2 : IntervalIntegrable (fun σ => Work.Spaces.mixed j i (gdot g σ) z θ) volume τ₁ τ₂ :=
      hR z θ hz hθ hθ' τ₁ τ₂ h0 h12 h2S
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_div,
      intervalIntegral.integral_sub hi1 hi2, h1, h2]
    ring
  -- assemble
  have hlimSub : Tendsto (fun n : ℕ => z * ((Work.Spaces.mixed j i (slice g τ₂)
        (z + z / ((n : ℝ) + 1)) θ - Work.Spaces.mixed j i (slice g τ₂) z θ) / (z / ((n : ℝ) + 1)))
      - z * ((Work.Spaces.mixed j i (slice g τ₁) (z + z / ((n : ℝ) + 1)) θ
        - Work.Spaces.mixed j i (slice g τ₁) z θ) / (z / ((n : ℝ) + 1)))) atTop
      (𝓝 (Work.Spaces.mixed (j + 1) i (slice g τ₂) z θ
        - Work.Spaces.mixed (j + 1) i (slice g τ₁) z θ)) :=
    (hA τ₂ ⟨h0.trans h12, h2S⟩).sub (hA τ₁ ⟨h0, le_trans h12 h2S⟩)
  have hlimInt : Tendsto (fun n : ℕ => z * ((Work.Spaces.mixed j i (slice g τ₂)
        (z + z / ((n : ℝ) + 1)) θ - Work.Spaces.mixed j i (slice g τ₂) z θ) / (z / ((n : ℝ) + 1)))
      - z * ((Work.Spaces.mixed j i (slice g τ₁) (z + z / ((n : ℝ) + 1)) θ
        - Work.Spaces.mixed j i (slice g τ₁) z θ) / (z / ((n : ℝ) + 1)))) atTop
      (𝓝 (∫ σ in τ₁..τ₂, Work.Spaces.mixed (j + 1) i (gdot g σ) z θ)) := by
    have hDCT' := hDCT
    rw [show (∫ σ, Work.Spaces.mixed (j + 1) i (gdot g σ) z θ
          ∂(volume.restrict (Set.Ioc τ₁ τ₂)))
        = ∫ σ in τ₁..τ₂, Work.Spaces.mixed (j + 1) i (gdot g σ) z θ from
      (intervalIntegral.integral_of_le h12).symm] at hDCT'
    refine hDCT'.congr' (Filter.Eventually.of_forall fun n => ?_)
    rw [← intervalIntegral.integral_of_le h12]
    exact hCval n
  exact tendsto_nhds_unique hlimSub hlimInt

/-! ## The step in `θ` -/

/-- **The step `(0,i) → (0,i+1)`**: differentiation in `θ` of the identity for `(0,i)`, along the
difference-quotient sequence `((π/2−θ)/2)/(n+1)`. -/
theorem mii_step_theta {S : ℝ} {g : Fam} (hG : GdotLoc S g)
    (hc4 : ∀ τ, 0 ≤ τ → ContDiffOn ℝ 4 (Function.uncurry (slice g τ)) Work.FTS.EllipticEst.Q0)
    {i : ℕ} (hi : i ≤ 1) (hP : mii_P S g 0 i) (hR : mii_R S g 0 i) :
    mii_P S g 0 (i + 1) := by
  intro z θ hz hθ hθ' τ₁ τ₂ h0 h12 h2S
  obtain ⟨C, hC0, hC⟩ := mii_abs_pth_mixed_gdot_le hG (j := 0) (i := i) (by omega) hz hθ hθ'
  have hmeas : ∀ y θ', 0 < y → 0 < θ' → θ' < Real.pi / 2 →
      AEStronglyMeasurable (fun σ => Work.Spaces.mixed 0 i (gdot g σ) y θ')
        (volume.restrict (Set.Ioc τ₁ τ₂)) :=
    mii_aesm_mixed_gdot_low hG h0 h2S 0 i (by omega)
  -- the limit of the left-hand sides
  have hA : ∀ τ ∈ Set.Icc (0 : ℝ) S,
      Tendsto (fun n : ℕ => Real.sin (2 * θ)
        * ((Work.Spaces.mixed 0 i (slice g τ) z (θ + ((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1))
          - Work.Spaces.mixed 0 i (slice g τ) z θ) / (((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1))))
        atTop (𝓝 (Work.Spaces.mixed 0 (i + 1) (slice g τ) z θ)) := by
    intro τ hτ
    have hd : HasDerivAt (fun y : ℝ => Work.Spaces.mixed 0 i (slice g τ) z y)
        (Work.Spaces.pth (Work.Spaces.mixed 0 i (slice g τ)) z θ) θ :=
      mii_hasDerivAt_mixed_slice_theta (n := 4) (hc4 τ hτ.1) (by omega) hz ⟨hθ, hθ'⟩
    have h1 := (mii_tendsto_slope_seq (show (0 : ℝ) < (Real.pi / 2 - θ) / 2 by linarith) hd)
      |>.const_mul (Real.sin (2 * θ))
    simpa only [mii_mixed_zero_succ_apply] using h1
  -- the dominated convergence theorem
  have hHmeas : ∀ n : ℕ, AEStronglyMeasurable
      (fun σ : ℝ => Real.sin (2 * θ)
        * ((Work.Spaces.mixed 0 i (gdot g σ) z (θ + ((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1))
          - Work.Spaces.mixed 0 i (gdot g σ) z θ) / (((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1))))
      (volume.restrict (Set.Ioc τ₁ τ₂)) := by
    intro n
    have h1 := hmeas z (θ + ((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1)) hz (by
      have : 0 < ((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1) := by positivity
      linarith) (by
      have h2 : ((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1) ≤ (Real.pi / 2 - θ) / 2 := by
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
        nlinarith [Nat.cast_nonneg (α := ℝ) n]
      linarith)
    have h2 := hmeas z θ hz hθ hθ'
    have h3 : AEStronglyMeasurable
        (fun σ : ℝ => (((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1))⁻¹
          * (Work.Spaces.mixed 0 i (gdot g σ) z (θ + ((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1))
            - Work.Spaces.mixed 0 i (gdot g σ) z θ)) (volume.restrict (Set.Ioc τ₁ τ₂)) :=
      (h1.sub h2).const_mul _
    refine (h3.const_mul (Real.sin (2 * θ))).congr (Filter.Eventually.of_forall fun σ => ?_)
    simp only [div_eq_mul_inv]
    ring
  have hHbound : ∀ n : ℕ, ∀ᵐ σ ∂(volume.restrict (Set.Ioc τ₁ τ₂)),
      ‖Real.sin (2 * θ)
        * ((Work.Spaces.mixed 0 i (gdot g σ) z (θ + ((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1))
          - Work.Spaces.mixed 0 i (gdot g σ) z θ) / (((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1)))‖
        ≤ |Real.sin (2 * θ)| * C := by
    intro n
    rw [ae_restrict_iff' measurableSet_Ioc]
    refine Filter.Eventually.of_forall fun σ hσ => ?_
    have hσmem : σ ∈ Set.Ioc (0 : ℝ) S := ⟨lt_of_le_of_lt h0 hσ.1, le_trans hσ.2 h2S⟩
    have ht : 0 < ((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1) := by positivity
    have htle : ((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1) ≤ (Real.pi / 2 - θ) / 2 := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    have hcont : ContinuousOn (fun y : ℝ => Work.Spaces.mixed 0 i (gdot g σ) z y)
        (Set.Icc θ (θ + ((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1))) :=
      mii_continuousOn_mixed_slice_theta (n := 2) (hG.1 σ hσmem) (by omega) hz hθ
        (by linarith [htle])
    have hdiff : ∀ y ∈ Set.Ioo θ (θ + ((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1)),
        HasDerivAt (fun y' : ℝ => Work.Spaces.mixed 0 i (gdot g σ) z y')
          (deriv (fun y' : ℝ => Work.Spaces.mixed 0 i (gdot g σ) z y') y) y := by
      intro y hy
      exact (mii_hasDerivAt_mixed_slice_theta (n := 2) (hG.1 σ hσmem) (by omega) hz
        ⟨by linarith [hy.1], by linarith [hy.2, htle]⟩).differentiableAt.hasDerivAt
    have hb : ∀ y ∈ Set.Icc θ (θ + ((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1)),
        |deriv (fun y' : ℝ => Work.Spaces.mixed 0 i (gdot g σ) z y') y| ≤ C := by
      intro y hy
      have h1 : deriv (fun y' : ℝ => Work.Spaces.mixed 0 i (gdot g σ) z y') y
          = Work.Spaces.pth (Work.Spaces.mixed 0 i (gdot g σ)) z y := rfl
      rw [h1]
      exact hC σ hσmem y ⟨by linarith [hy.1], by linarith [hy.2, htle]⟩
    have hMVT := mii_abs_sub_le_of_abs_deriv_le (a := θ)
      (b := θ + ((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1)) (by linarith [ht]) hcont hdiff hb
    have hMVT' : |Work.Spaces.mixed 0 i (gdot g σ) z (θ + ((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1))
        - Work.Spaces.mixed 0 i (gdot g σ) z θ| ≤ C * (((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1)) := by
      have h := hMVT
      rwa [show θ + ((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1) - θ
        = ((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1) by ring] at h
    calc ‖Real.sin (2 * θ)
          * ((Work.Spaces.mixed 0 i (gdot g σ) z (θ + ((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1))
            - Work.Spaces.mixed 0 i (gdot g σ) z θ) / (((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1)))‖
        = |Real.sin (2 * θ)| * (|Work.Spaces.mixed 0 i (gdot g σ) z (θ + ((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1))
            - Work.Spaces.mixed 0 i (gdot g σ) z θ| / (((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1))) := by
          rw [Real.norm_eq_abs, abs_mul, abs_div, abs_of_pos ht]
      _ ≤ |Real.sin (2 * θ)| * (C * (((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1))
            / (((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1))) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hMVT' (le_of_lt ht)) (abs_nonneg _)
      _ = |Real.sin (2 * θ)| * C := by
          rw [mul_div_assoc, div_self (ne_of_gt ht), mul_one]
  have hHlim : ∀ᵐ σ ∂(volume.restrict (Set.Ioc τ₁ τ₂)),
      Tendsto (fun n : ℕ => Real.sin (2 * θ)
        * ((Work.Spaces.mixed 0 i (gdot g σ) z (θ + ((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1))
          - Work.Spaces.mixed 0 i (gdot g σ) z θ) / (((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1))))
        atTop (𝓝 (Work.Spaces.mixed 0 (i + 1) (gdot g σ) z θ)) := by
    rw [ae_restrict_iff' measurableSet_Ioc]
    refine Filter.Eventually.of_forall fun σ hσ => ?_
    have hσmem : σ ∈ Set.Ioc (0 : ℝ) S := ⟨lt_of_le_of_lt h0 hσ.1, le_trans hσ.2 h2S⟩
    have hd : HasDerivAt (fun y : ℝ => Work.Spaces.mixed 0 i (gdot g σ) z y)
        (Work.Spaces.pth (Work.Spaces.mixed 0 i (gdot g σ)) z θ) θ :=
      mii_hasDerivAt_mixed_slice_theta (n := 2) (hG.1 σ hσmem) (by omega) hz ⟨hθ, hθ'⟩
    have h1 := (mii_tendsto_slope_seq (show (0 : ℝ) < (Real.pi / 2 - θ) / 2 by linarith) hd)
      |>.const_mul (Real.sin (2 * θ))
    simpa only [mii_mixed_zero_succ_apply] using h1
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioc τ₁ τ₂)) :=
    isFiniteMeasure_restrict.mpr measure_Ioc_lt_top.ne
  have hDCT := tendsto_integral_of_dominated_convergence
    (μ := volume.restrict (Set.Ioc τ₁ τ₂))
    (F := fun n σ => Real.sin (2 * θ)
        * ((Work.Spaces.mixed 0 i (gdot g σ) z (θ + ((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1))
          - Work.Spaces.mixed 0 i (gdot g σ) z θ) / (((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1))))
    (f := fun σ => Work.Spaces.mixed 0 (i + 1) (gdot g σ) z θ)
    (fun _ : ℝ => |Real.sin (2 * θ)| * C) hHmeas
    ((integrable_const _).const_mul _) hHbound hHlim
  -- the value of each integral
  have hCval : ∀ n : ℕ, (∫ σ in τ₁..τ₂, Real.sin (2 * θ)
        * ((Work.Spaces.mixed 0 i (gdot g σ) z (θ + ((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1))
          - Work.Spaces.mixed 0 i (gdot g σ) z θ) / (((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1))))
      = Real.sin (2 * θ)
          * ((Work.Spaces.mixed 0 i (slice g τ₂) z (θ + ((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1))
            - Work.Spaces.mixed 0 i (slice g τ₂) z θ) / (((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1)))
        - Real.sin (2 * θ)
          * ((Work.Spaces.mixed 0 i (slice g τ₁) z (θ + ((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1))
            - Work.Spaces.mixed 0 i (slice g τ₁) z θ) / (((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1))) := by
    intro n
    have h1 : (∫ σ in τ₁..τ₂, Work.Spaces.mixed 0 i (gdot g σ) z
          (θ + ((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1)))
        = Work.Spaces.mixed 0 i (slice g τ₂) z (θ + ((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1))
          - Work.Spaces.mixed 0 i (slice g τ₁) z (θ + ((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1)) :=
      (hP z (θ + ((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1)) hz (by
          have : 0 < ((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1) := by positivity
          linarith)
        (by
          have h2 : ((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1) ≤ (Real.pi / 2 - θ) / 2 := by
            rw [div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
            nlinarith [Nat.cast_nonneg (α := ℝ) n]
          linarith)
        τ₁ τ₂ h0 h12 h2S).symm
    have h2 : (∫ σ in τ₁..τ₂, Work.Spaces.mixed 0 i (gdot g σ) z θ)
        = Work.Spaces.mixed 0 i (slice g τ₂) z θ - Work.Spaces.mixed 0 i (slice g τ₁) z θ :=
      (hP z θ hz hθ hθ' τ₁ τ₂ h0 h12 h2S).symm
    have hi1 : IntervalIntegrable
        (fun σ => Work.Spaces.mixed 0 i (gdot g σ) z
          (θ + ((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1))) volume τ₁ τ₂ :=
      hR z (θ + ((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1)) hz (by
          have : 0 < ((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1) := by positivity
          linarith)
        (by
          have h2 : ((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1) ≤ (Real.pi / 2 - θ) / 2 := by
            rw [div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
            nlinarith [Nat.cast_nonneg (α := ℝ) n]
          linarith)
        τ₁ τ₂ h0 h12 h2S
    have hi2 : IntervalIntegrable (fun σ => Work.Spaces.mixed 0 i (gdot g σ) z θ) volume τ₁ τ₂ :=
      hR z θ hz hθ hθ' τ₁ τ₂ h0 h12 h2S
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_div,
      intervalIntegral.integral_sub hi1 hi2, h1, h2]
    ring
  -- assemble
  have hlimSub : Tendsto (fun n : ℕ => Real.sin (2 * θ)
        * ((Work.Spaces.mixed 0 i (slice g τ₂) z (θ + ((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1))
          - Work.Spaces.mixed 0 i (slice g τ₂) z θ) / (((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1)))
      - Real.sin (2 * θ)
        * ((Work.Spaces.mixed 0 i (slice g τ₁) z (θ + ((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1))
          - Work.Spaces.mixed 0 i (slice g τ₁) z θ) / (((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1))))
      atTop (𝓝 (Work.Spaces.mixed 0 (i + 1) (slice g τ₂) z θ
        - Work.Spaces.mixed 0 (i + 1) (slice g τ₁) z θ)) :=
    (hA τ₂ ⟨h0.trans h12, h2S⟩).sub (hA τ₁ ⟨h0, le_trans h12 h2S⟩)
  have hlimInt : Tendsto (fun n : ℕ => Real.sin (2 * θ)
        * ((Work.Spaces.mixed 0 i (slice g τ₂) z (θ + ((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1))
          - Work.Spaces.mixed 0 i (slice g τ₂) z θ) / (((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1)))
      - Real.sin (2 * θ)
        * ((Work.Spaces.mixed 0 i (slice g τ₁) z (θ + ((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1))
          - Work.Spaces.mixed 0 i (slice g τ₁) z θ) / (((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1))))
      atTop (𝓝 (∫ σ in τ₁..τ₂, Work.Spaces.mixed 0 (i + 1) (gdot g σ) z θ)) := by
    have hDCT' := hDCT
    rw [show (∫ σ, Work.Spaces.mixed 0 (i + 1) (gdot g σ) z θ
          ∂(volume.restrict (Set.Ioc τ₁ τ₂)))
        = ∫ σ in τ₁..τ₂, Work.Spaces.mixed 0 (i + 1) (gdot g σ) z θ from
      (intervalIntegral.integral_of_le h12).symm] at hDCT'
    refine hDCT'.congr' (Filter.Eventually.of_forall fun n => ?_)
    rw [← intervalIntegral.integral_of_le h12]
    exact hCval n
  exact tendsto_nhds_unique hlimSub hlimInt

end Work.FTS_RegExport.RXT.Sys
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.slice_space_lip =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.slice_space_lip`

**S2 of the RegExport plan**: the space-time Lipschitz bound for the jets of the strong solution.

For a family `g` satisfying `DynOK' (pExp α) C₀ Φs E g` and any box `[a,b] × [c,d]` of the open
quadrant (`0 < a ≤ b`, `0 < c ≤ d < π/2`), every mixed jet
`D_z^j D_θ^i (slice g τ)` of order `j + i ≤ 3` is, uniformly on `[0,T]` and on the box, Lipschitz
in both `z` and `θ` (with a *single* constant).

Route (the same one as `RXT.loc_sup4`): `DynOK'` gives the class-`C` approximants `gn` of the
solution with a uniform `ℋ⁶`-bound `Xn6 α (slice (gn n) τ) ≤ B` and `C⁴`-jet convergence on the
open quadrant, and `DynOK` gives the `C⁴`-regularity of the solution itself.  Each approximant
slice is `SmoothOpen`, hence:

* the derivative of `D_z^jD_θ^i f` in `z` is `D_z^{j+1}D_θ^i f / z` (definitional);
* the derivative in `θ` is `D_z^jD_θ^{i+1} f / sin(2θ)` (`Dth_mixed_eq_C4` of
  `RegExport/C4/Dth_mixed_eq_C4.lean`);
* both are bounded on the box by `classC_mixed_sup_le_four`, giving the mean-value bounds
  `K/a` (in `z`) and `K/σ` (in `θ`), where `K = C₁/√(γ-1)·B` and `σ = (4/π)·min c (π/2-d)`.

Passing to the limit in `n` (the `C⁴`-jet convergence of `LimApprox`) gives the same bounds for
`g` itself.  The single constant is `K/a + K/σ`.
-/

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_RegExport.RXT

/-! ## Two mean-value/Lipschitz engines -/

/-- If `φ` is differentiable on the closed interval `[lo,hi]` and its derivative is bounded by
`C` there, then `φ` is `C`-Lipschitz on that interval.  (The `ℝ → ℝ` form of
`Convex.norm_image_sub_le_of_norm_deriv_le`.) -/
private lemma abs_sub_le_of_deriv_le {φ : ℝ → ℝ} {C lo hi : ℝ}
    (hdiff : ∀ x ∈ Set.Icc lo hi, DifferentiableAt ℝ φ x)
    (hbd : ∀ x ∈ Set.Icc lo hi, |deriv φ x| ≤ C) :
    ∀ x ∈ Set.Icc lo hi, ∀ y ∈ Set.Icc lo hi, |φ x - φ y| ≤ C * |x - y| := by
  intro x hx y hy
  have h : ‖φ y - φ x‖ ≤ C * ‖y - x‖ :=
    Convex.norm_image_sub_le_of_norm_deriv_le hdiff
      (fun x hx => by rw [Real.norm_eq_abs]; exact hbd x hx) (convex_Icc lo hi) hx hy
  have h2 : |φ x - φ y| = ‖φ y - φ x‖ := by rw [Real.norm_eq_abs, abs_sub_comm]
  have h3 : |x - y| = ‖y - x‖ := by rw [Real.norm_eq_abs, abs_sub_comm]
  rw [h2, h3]
  exact h

/-- **The `z`-Lipschitz bound for the mixed slots.**  If `f` is smooth on the open quadrant and
every mixed slot of order `≤ 4` is bounded by `K` on the box `[a,b] × [c,d]`, then every mixed
slot `D_z^j D_θ^i f` with `j + i ≤ 3` is `K/a`-Lipschitz in `z` on the box. -/
private lemma mixed_lipschitz_z {f : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen f)
    {a b c d K : ℝ} (ha : 0 < a) (hc : 0 < c) (hd : d < π / 2) (hKnn : 0 ≤ K)
    (hK : ∀ p q : ℕ, p + q ≤ 4 → ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d,
      |Work.Spaces.mixed p q f z θ| ≤ K)
    {j i : ℕ} (hji : j + i ≤ 3) :
    ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d, ∀ z' ∈ Set.Icc a b,
      |Work.Spaces.mixed j i f z θ - Work.Spaces.mixed j i f z' θ| ≤ (K / a) * |z - z'| := by
  intro z hz θ hθ z' hz'
  have hθIoo : θ ∈ Set.Ioo 0 (π / 2) := ⟨lt_of_lt_of_le hc hθ.1, lt_of_le_of_lt hθ.2 hd⟩
  have hslice : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun x : ℝ => Work.Spaces.mixed j i f x θ) (Set.Ioi 0) :=
    (hF.mixed j i).curry_z hθIoo
  have hdiff : ∀ x ∈ Set.Icc a b,
      DifferentiableAt ℝ (fun x : ℝ => Work.Spaces.mixed j i f x θ) x := by
    intro x hx
    exact (hslice.differentiableOn (by simp)).differentiableAt
      (isOpen_Ioi.mem_nhds (lt_of_lt_of_le ha hx.1))
  have hbd : ∀ x ∈ Set.Icc a b,
      |deriv (fun x : ℝ => Work.Spaces.mixed j i f x θ) x| ≤ K / a := by
    intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le ha hx.1
    have hkey : x * Work.Spaces.pz (Work.Spaces.mixed j i f) x θ
        = Work.Spaces.mixed (j + 1) i f x θ := rfl
    have hdiv : Work.Spaces.pz (Work.Spaces.mixed j i f) x θ
        = Work.Spaces.mixed (j + 1) i f x θ / x := by
      rw [eq_div_iff (ne_of_gt hxpos), mul_comm]
      exact hkey
    have hderiv : deriv (fun x : ℝ => Work.Spaces.mixed j i f x θ) x
        = Work.Spaces.mixed (j + 1) i f x θ / x := by
      rw [show deriv (fun x : ℝ => Work.Spaces.mixed j i f x θ) x
            = Work.Spaces.pz (Work.Spaces.mixed j i f) x θ from rfl, hdiv]
    calc |deriv (fun x : ℝ => Work.Spaces.mixed j i f x θ) x|
        = |Work.Spaces.mixed (j + 1) i f x θ| / x := by
          rw [hderiv, abs_div, abs_of_pos hxpos]
      _ ≤ K / x := div_le_div_of_nonneg_right (hK (j + 1) i (by omega) x hx θ hθ) hxpos.le
      _ ≤ K / a := div_le_div_of_nonneg_left hKnn ha hx.1
  exact abs_sub_le_of_deriv_le hdiff hbd z hz z' hz'

/-- **The `θ`-Lipschitz bound for the mixed slots.**  If `f` is smooth on the open quadrant, every
mixed slot of order `≤ 4` is bounded by `K` on the box, and `σ > 0` bounds `sin(2θ)` from below on
`[c,d]`, then every mixed slot `D_z^j D_θ^i f` with `j + i ≤ 3` is `K/σ`-Lipschitz in `θ` on the
box. -/
private lemma mixed_lipschitz_theta {f : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen f)
    {a b c d K σ : ℝ} (ha : 0 < a) (hc : 0 < c) (hd : d < π / 2) (hKnn : 0 ≤ K)
    (hσpos : 0 < σ) (hσ : ∀ θ ∈ Set.Icc c d, σ ≤ Real.sin (2 * θ))
    (hK : ∀ p q : ℕ, p + q ≤ 4 → ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d,
      |Work.Spaces.mixed p q f z θ| ≤ K)
    {j i : ℕ} (hji : j + i ≤ 3) :
    ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d, ∀ θ' ∈ Set.Icc c d,
      |Work.Spaces.mixed j i f z θ - Work.Spaces.mixed j i f z θ'| ≤ (K / σ) * |θ - θ'| := by
  intro z hz θ hθ θ' hθ'
  have hzpos : 0 < z := lt_of_lt_of_le ha hz.1
  have hslice : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun x : ℝ => Work.Spaces.mixed j i f z x) (Set.Ioo 0 (π / 2)) :=
    (hF.mixed j i).curry_θ hzpos
  have hdiff : ∀ x ∈ Set.Icc c d,
      DifferentiableAt ℝ (fun x : ℝ => Work.Spaces.mixed j i f z x) x := by
    intro x hx
    exact (hslice.differentiableOn (by simp)).differentiableAt
      (isOpen_Ioo.mem_nhds ⟨lt_of_lt_of_le hc hx.1, lt_of_le_of_lt hx.2 hd⟩)
  have hbd : ∀ x ∈ Set.Icc c d,
      |deriv (fun x : ℝ => Work.Spaces.mixed j i f z x) x| ≤ K / σ := by
    intro x hx
    have hxIoo : x ∈ Set.Ioo 0 (π / 2) := ⟨lt_of_lt_of_le hc hx.1, lt_of_le_of_lt hx.2 hd⟩
    have hsin : 0 < Real.sin (2 * x) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hxIoo.1]) (by linarith [hxIoo.2, Real.pi_pos])
    have hDth := Work.FTS_RegExport.C4.Dth_mixed_eq_C4 (hF.forall 4) j i (by omega) hzpos hxIoo
    have hkey : Real.sin (2 * x) * Work.Spaces.pth (Work.Spaces.mixed j i f) z x
        = Work.Spaces.mixed j (i + 1) f z x := by
      simpa only [Work.Spaces.Dth] using hDth
    have hdiv : Work.Spaces.pth (Work.Spaces.mixed j i f) z x
        = Work.Spaces.mixed j (i + 1) f z x / Real.sin (2 * x) := by
      rw [eq_div_iff (ne_of_gt hsin), mul_comm]
      exact hkey
    have hderiv : deriv (fun x : ℝ => Work.Spaces.mixed j i f z x) x
        = Work.Spaces.mixed j (i + 1) f z x / Real.sin (2 * x) := by
      rw [show deriv (fun x : ℝ => Work.Spaces.mixed j i f z x) x
            = Work.Spaces.pth (Work.Spaces.mixed j i f) z x from rfl, hdiv]
    calc |deriv (fun x : ℝ => Work.Spaces.mixed j i f z x) x|
        = |Work.Spaces.mixed j (i + 1) f z x| / Real.sin (2 * x) := by
          rw [hderiv, abs_div, abs_of_pos hsin]
      _ ≤ K / Real.sin (2 * x) :=
          div_le_div_of_nonneg_right (hK j (i + 1) (by omega) z hz x hx) hsin.le
      _ ≤ K / σ := div_le_div_of_nonneg_left hKnn hσpos (hσ x hx)
  exact abs_sub_le_of_deriv_le hdiff hbd θ hθ θ' hθ'

/-! ## The target -/

theorem slice_space_lip {α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3) {g : Work.FTS.Galerkin.Fam}
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (T : ℝ) (hT : 0 < T) {a b c d : ℝ} (ha : 0 < a) (hab : a ≤ b) (hc : 0 < c) (hcd : c ≤ d)
    (hd : d < Real.pi / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ ∈ Set.Icc (0:ℝ) T, ∀ j i : ℕ, j + i ≤ 3 →
      (∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d, ∀ z' ∈ Set.Icc a b,
        |Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g τ) z θ
          - Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g τ) z' θ| ≤ C * |z - z'|) ∧
      (∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d, ∀ θ' ∈ Set.Icc c d,
        |Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g τ) z θ
          - Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g τ) z θ'| ≤ C * |θ - θ'|) := by
  -- the exponent `β = pExp α = 3α` is a positive exponent `≤ 1`
  have hβ : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hβ1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  -- the class-`C` interior `L^∞`–`ℋ⁶` trade-off
  obtain ⟨C₁, hC₁pos, hC₁⟩ := Work.FTS.StrongEps.classC_mixed_sup_le_four
  -- the approximating class-C families, the uniform `ℋ⁶`-bound `B`, and the jet convergence
  obtain ⟨gn, B, _L, h1, _h2, h3, _h4⟩ := hOK.2 (T + 1) (by linarith)
  have hBnn : 0 ≤ B := by
    have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (T + 1) := ⟨le_rfl, by linarith⟩
    have hx : 0 ≤ Work.FTS.StrongGlobal.Xn6 (Work.FTS.Regularity.pExp α)
        (Work.FTS.Galerkin.slice (gn 0) 0) := Work.Spaces.HkNorm_nonneg _ 6 _
    linarith [(h1 0 0 h0).2.2]
  -- the universal constant of the sup bounds
  set K : ℝ := C₁ / Real.sqrt (Work.Spaces.gam (Work.FTS.Regularity.pExp α) - 1) * B with hKdef
  have hKnn : 0 ≤ K := by
    rw [hKdef]
    exact mul_nonneg (div_nonneg hC₁pos.le (Real.sqrt_nonneg _)) hBnn
  -- the angular lower bound on `[c,d]`
  set σ : ℝ := (4 / π) * min c (π / 2 - d) with hσdef
  have hσpos : 0 < σ := by
    rw [hσdef]
    have h1' : 0 < min c (π / 2 - d) := lt_min hc (by linarith)
    positivity
  have hσle : ∀ θ ∈ Set.Icc c d, σ ≤ Real.sin (2 * θ) := by
    intro θ hθ
    have hθIθ : θ ∈ Work.Spaces.Iθ := ⟨by linarith [hθ.1, hc], by linarith [hθ.2, hd]⟩
    have hmin : min c (π / 2 - d) ≤ min θ (π / 2 - θ) :=
      le_min (le_trans (min_le_left _ _) hθ.1) (le_trans (min_le_right _ _) (by linarith [hθ.2]))
    have h4π : (0 : ℝ) ≤ 4 / π := div_nonneg (by norm_num) Real.pi_pos.le
    have h1' : (4 / π) * min θ (π / 2 - θ) ≤ Real.sin (2 * θ) := by
      have hms := mul_le_mul_of_nonneg_left (Work.FTS.H2.min_le_sin θ hθIθ) h4π
      have h4 : (4 / π) * ((π / 4) * Real.sin (2 * θ)) = Real.sin (2 * θ) := by
        rw [← mul_assoc, show (4 : ℝ) / π * (π / 4) = 1 by field_simp, one_mul]
      linarith [hms, h4]
    calc σ = (4 / π) * min c (π / 2 - d) := hσdef
      _ ≤ (4 / π) * min θ (π / 2 - θ) := mul_le_mul_of_nonneg_left hmin h4π
      _ ≤ Real.sin (2 * θ) := h1'
  refine ⟨K / a + K / σ, add_nonneg (div_nonneg hKnn ha.le) (div_nonneg hKnn hσpos.le), ?_⟩
  intro τ hτ j i hji
  have hτT : τ ∈ Set.Icc (0 : ℝ) (T + 1) := ⟨hτ.1, by linarith [hτ.2]⟩
  -- the uniform sup bound on the mixed slots of order `≤ 4`, for every approximant
  have hKn : ∀ n : ℕ, ∀ p q : ℕ, p + q ≤ 4 → ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc c d,
      |Work.Spaces.mixed p q (Work.FTS.Galerkin.slice (gn n) τ) x y| ≤ K := by
    intro n p q hpq x hx y hy
    have hCn : Work.FTS.ClassC.ClassC (Work.FTS.Regularity.pExp α)
        (Work.FTS.Galerkin.slice (gn n) τ) := (h1 n τ hτT).1
    have hn6 : Work.FTS.StrongGlobal.Xn6 (Work.FTS.Regularity.pExp α)
        (Work.FTS.Galerkin.slice (gn n) τ) ≤ B := (h1 n τ hτT).2.2
    have hxy : (x, y) ∈ Work.Construction.Qd :=
      ⟨lt_of_lt_of_le ha hx.1, lt_of_lt_of_le hc hy.1, lt_of_le_of_lt hy.2 hd⟩
    have hb := hC₁ (Work.FTS.Regularity.pExp α) ⟨hβ, hβ1⟩ hCn p q (by omega) hxy
    calc |Work.Spaces.mixed p q (Work.FTS.Galerkin.slice (gn n) τ) x y|
        ≤ C₁ / Real.sqrt (Work.Spaces.gam (Work.FTS.Regularity.pExp α) - 1)
            * Work.FTS.StrongGlobal.Xn6 (Work.FTS.Regularity.pExp α)
              (Work.FTS.Galerkin.slice (gn n) τ) := hb
      _ ≤ C₁ / Real.sqrt (Work.Spaces.gam (Work.FTS.Regularity.pExp α) - 1) * B :=
          mul_le_mul_of_nonneg_left hn6 (div_nonneg hC₁pos.le (Real.sqrt_nonneg _))
      _ = K := hKdef.symm
  -- the box lies in the open quadrant
  have hbox : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc c d, (x, y) ∈ Work.Construction.Qd :=
    fun x hx y hy => ⟨lt_of_lt_of_le ha hx.1, lt_of_lt_of_le hc hy.1, lt_of_le_of_lt hy.2 hd⟩
  constructor
  · -- Lipschitz in `z`
    intro z hz θ hθ z' hz'
    have hbnd : ∀ n : ℕ,
        |Work.Spaces.mixed j i (Work.FTS.Galerkin.slice (gn n) τ) z θ
          - Work.Spaces.mixed j i (Work.FTS.Galerkin.slice (gn n) τ) z' θ| ≤ (K / a) * |z - z'| :=
      fun n => mixed_lipschitz_z ((h1 n τ hτT).1).reg ha hc hd hKnn (hKn n) hji z hz θ hθ z' hz'
    have htend := ((h3 τ hτT j i (by omega) z θ (hbox z hz θ hθ)).sub
      (h3 τ hτT j i (by omega) z' θ (hbox z' hz' θ hθ))).abs
    have hlim := le_of_tendsto htend (Filter.Eventually.of_forall hbnd)
    calc |Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g τ) z θ
          - Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g τ) z' θ|
        ≤ (K / a) * |z - z'| := hlim
      _ ≤ (K / a + K / σ) * |z - z'| := by
          refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
          exact le_add_of_nonneg_right (div_nonneg hKnn hσpos.le)
  · -- Lipschitz in `θ`
    intro z hz θ hθ θ' hθ'
    have hbnd : ∀ n : ℕ,
        |Work.Spaces.mixed j i (Work.FTS.Galerkin.slice (gn n) τ) z θ
          - Work.Spaces.mixed j i (Work.FTS.Galerkin.slice (gn n) τ) z θ'| ≤ (K / σ) * |θ - θ'| :=
      fun n => mixed_lipschitz_theta ((h1 n τ hτT).1).reg ha hc hd hKnn hσpos hσle (hKn n) hji
        z hz θ hθ θ' hθ'
    have htend := ((h3 τ hτT j i (by omega) z θ (hbox z hz θ hθ)).sub
      (h3 τ hτT j i (by omega) z θ' (hbox z hz θ' hθ'))).abs
    have hlim := le_of_tendsto htend (Filter.Eventually.of_forall hbnd)
    calc |Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g τ) z θ
          - Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g τ) z θ'|
        ≤ (K / σ) * |θ - θ'| := hlim
      _ ≤ (K / a + K / σ) * |θ - θ'| := by
          refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
          exact le_add_of_nonneg_left (div_nonneg hKnn ha.le)

end Work.FTS_RegExport.RXT
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.st1_stdata2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology NNReal
open Set Filter

namespace Work.FTS_RegExport.RXT

/-- The second `z`-derivative at the origin. -/
theorem st1_quad2 {α : ℝ} (hα : 0 < α) {g : Work.FTS.Galerkin.Fam} {S K : ℝ}
    (hmin : Work.FTS.StrongGlobal.RegPkgMin (Work.FTS.Regularity.pExp α) g) (hS : 0 < S)
    (hK0 : 0 ≤ K)
    (hw : ∀ k : Fin 6, ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed (Work.FTS.RegExportIface.RXT.idx k).1
        (Work.FTS.RegExportIface.RXT.idx k).2
        (Work.FTS.Galerkin.slice g τ) z θ| ≤ K * Work.FTS.RegExportIface.ω α z θ) :
    ∃ Q₂ : ℝ, 0 ≤ Q₂ ∧ ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ θ ∈ Work.Spaces.Iθ,
      ∀ z : ℝ, 0 < z → z ≤ 2 →
        |Work.Spaces.pz (Work.Spaces.pz (Work.FTS.Regularity.gSlice (GG α g) τ)) z θ| ≤ Q₂ := by
  have hv : ∀ τ : ℝ, 0 ≤ τ → ∀ z : ℝ, 0 ≤ z → g z 0 τ = 0 ∧ g z (π / 2) τ = 0 :=
    fun τ hτ z hz => hmin.vanish τ hτ z hz
  refine ⟨2 * |K|, by positivity, ?_⟩
  intro τ hτ θ hθ z hz hz2
  rcases eq_or_lt_of_le hθ.1 with hθ0 | hθpos
  · -- `θ = 0`: the slice of `g̃` vanishes identically at this angle
    subst hθ0
    have h1 : Work.Spaces.pz
        (Work.Spaces.pz (Work.FTS.Regularity.gSlice (GG α g) τ)) z 0 = 0 := by
      show deriv (fun z' => Work.Spaces.pz (Work.FTS.Regularity.gSlice (GG α g) τ) z' 0) z = 0
      have hev : (fun z' : ℝ => Work.Spaces.pz (Work.FTS.Regularity.gSlice (GG α g) τ) z' 0)
          =ᶠ[𝓝 z] (fun _ => (0:ℝ)) := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
        exact pz_GG_eq_zero_left α hτ.1 hz' hv
      rw [hev.deriv_eq, deriv_const]
    rw [h1, abs_zero]
    positivity
  · rcases eq_or_lt_of_le hθ.2 with hθπ | hθlt
    · -- `θ = π/2`
      subst hθπ
      have h1 : Work.Spaces.pz
          (Work.Spaces.pz (Work.FTS.Regularity.gSlice (GG α g) τ)) z (π / 2) = 0 := by
        show deriv (fun z' =>
            Work.Spaces.pz (Work.FTS.Regularity.gSlice (GG α g) τ) z' (π / 2)) z = 0
        have hev : (fun z' : ℝ =>
              Work.Spaces.pz (Work.FTS.Regularity.gSlice (GG α g) τ) z' (π / 2))
            =ᶠ[𝓝 z] (fun _ => (0:ℝ)) := by
          filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
          exact pz_GG_eq_zero_right α hτ.1 hz' hv
        rw [hev.deriv_eq, deriv_const]
      rw [h1, abs_zero]
      positivity
    · -- interior
      rw [pz_pz_GG_eq α hτ.1 hz hθ]
      have h1 := hw (1 : Fin 6) τ hτ z θ hz hθpos hθlt
      norm_num [Work.FTS.RegExportIface.RXT.idx] at h1
      have h2 := hw (3 : Fin 6) τ hτ z θ hz hθpos hθlt
      norm_num [Work.FTS.RegExportIface.RXT.idx] at h2
      have hΓ1 : Work.FTS.Regularity.Gamma α θ ≤ 1 :=
        Work.ConstructionInstance.Gamma_le_one hα.le hθ
      have hΓ0 : 0 ≤ Work.FTS.Regularity.Gamma α θ :=
        Work.ConstructionInstance.Gamma_nonneg hθ
      -- `C²` at the interior point, and the `D_z²`-expansion
      have hnb : Work.FTS.EllipticEst.Q0 ∈ 𝓝 (z, θ) :=
        (isOpen_Ioi.prod isOpen_Ioo).mem_nhds ⟨hz, hθpos, hθlt⟩
      have hct : ContDiffAt ℝ 2 (Function.uncurry (Work.FTS.Galerkin.slice g τ)) (z, θ) :=
        ((hmin.c4 τ hτ.1).contDiffAt hnb).of_le (by norm_num)
      have hexp : Work.Spaces.DzIter 2 (Work.FTS.Galerkin.slice g τ) z θ
          = z * Work.Spaces.pz (Work.FTS.Galerkin.slice g τ) z θ
            + z ^ 2 * Work.Spaces.pz (Work.Spaces.pz (Work.FTS.Galerkin.slice g τ)) z θ :=
        dziter_two_fb hct
      have hbz : |Work.Spaces.DzIter 2 (Work.FTS.Galerkin.slice g τ) z θ|
          ≤ K * (z ^ 2 * Work.FTS.Regularity.Gamma α θ) :=
        le_trans h2 (mul_le_mul_of_nonneg_left
          (omega_le_zsq_mul_Gamma α z θ hz.le hθ) hK0)
      have hbz1 : |z * Work.Spaces.pz (Work.FTS.Galerkin.slice g τ) z θ|
          ≤ K * (z ^ 2 * Work.FTS.Regularity.Gamma α θ) := by
        have h2' : |Work.Spaces.mixed 1 0 (Work.FTS.Galerkin.slice g τ) z θ|
            ≤ K * (z ^ 2 * Work.FTS.Regularity.Gamma α θ) :=
          le_trans h1 (mul_le_mul_of_nonneg_left
            (omega_le_zsq_mul_Gamma α z θ hz.le hθ) hK0)
        simpa only [show Work.Spaces.mixed 1 0 (Work.FTS.Galerkin.slice g τ)
              = fun z θ => z * Work.Spaces.pz (Work.FTS.Galerkin.slice g τ) z θ from rfl]
          using h2'
      have hb : z ^ 2 * |Work.Spaces.pz
            (Work.Spaces.pz (Work.FTS.Galerkin.slice g τ)) z θ| ≤ (2 * |K|) * z ^ 2 := by
        have h0 : z ^ 2 * |Work.Spaces.pz
              (Work.Spaces.pz (Work.FTS.Galerkin.slice g τ)) z θ|
            = |z ^ 2 * Work.Spaces.pz
                (Work.Spaces.pz (Work.FTS.Galerkin.slice g τ)) z θ| := by
          rw [abs_mul, abs_of_nonneg (sq_nonneg z)]
        rw [h0]
        have hsplit : z ^ 2 * Work.Spaces.pz
              (Work.Spaces.pz (Work.FTS.Galerkin.slice g τ)) z θ
            = Work.Spaces.DzIter 2 (Work.FTS.Galerkin.slice g τ) z θ
              - z * Work.Spaces.pz (Work.FTS.Galerkin.slice g τ) z θ := by
          rw [hexp]; ring
        rw [hsplit]
        calc |Work.Spaces.DzIter 2 (Work.FTS.Galerkin.slice g τ) z θ
              - z * Work.Spaces.pz (Work.FTS.Galerkin.slice g τ) z θ|
            ≤ |Work.Spaces.DzIter 2 (Work.FTS.Galerkin.slice g τ) z θ|
              + |z * Work.Spaces.pz (Work.FTS.Galerkin.slice g τ) z θ| := by
                simpa only [sub_eq_add_neg, abs_neg] using
                  abs_add_le (Work.Spaces.DzIter 2 (Work.FTS.Galerkin.slice g τ) z θ)
                    (-(z * Work.Spaces.pz (Work.FTS.Galerkin.slice g τ) z θ))
          _ ≤ K * (z ^ 2 * Work.FTS.Regularity.Gamma α θ)
              + K * (z ^ 2 * Work.FTS.Regularity.Gamma α θ) := add_le_add hbz hbz1
          _ = (2 * K) * (z ^ 2 * Work.FTS.Regularity.Gamma α θ) := by ring
          _ ≤ (2 * K) * z ^ 2 :=
              mul_le_mul_of_nonneg_left (by nlinarith [hΓ1, hΓ0, sq_nonneg z])
                (by linarith)
          _ ≤ (2 * |K|) * z ^ 2 :=
              mul_le_mul_of_nonneg_right (by linarith [le_abs_self K]) (sq_nonneg z)
      have hfin : |Work.Spaces.pz (Work.Spaces.pz (Work.FTS.Galerkin.slice g τ)) z θ|
          ≤ 2 * |K| := by
        have h1 : |Work.Spaces.pz (Work.Spaces.pz (Work.FTS.Galerkin.slice g τ)) z θ| * z ^ 2
            ≤ (2 * |K|) * z ^ 2 := by
          simpa only [mul_comm (z ^ 2)] using hb
        have h2 : |Work.Spaces.pz (Work.Spaces.pz (Work.FTS.Galerkin.slice g τ)) z θ|
            ≤ (2 * |K|) * z ^ 2 / z ^ 2 := (le_div_iff₀ (pow_pos hz 2)).mpr h1
        rwa [mul_div_assoc, div_self (ne_of_gt (pow_pos hz 2)), mul_one] at h2
      exact hfin

end Work.FTS_RegExport.RXT
end
end
