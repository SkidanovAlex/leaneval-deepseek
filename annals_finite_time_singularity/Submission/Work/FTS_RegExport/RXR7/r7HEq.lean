import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_RegExport.RXR7.Defs
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS.MeridianDyn.All
import Submission.Work.FTS_FinalLeaves.profDerivData_min_proved
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
