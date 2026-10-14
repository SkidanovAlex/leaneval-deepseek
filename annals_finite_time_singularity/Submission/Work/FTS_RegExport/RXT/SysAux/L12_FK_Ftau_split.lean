import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS.FinalV2.Sanitize
import Submission.Work.FTS.GalFields.Tail.FK_Fstar_add
import Submission.Work.FTS.RegExportIface.RXT.Leaves
import Submission.Work.FTS.StrongEps.SupPort.HardyThetaOpen
import Submission.Work.FTS.TransportS.t3SlotGuarded
import Submission.Work.FTS_RegExport.RXB.l12_aux
import Submission.Work.FTS_RegExport.RXT.C2Radial
import Submission.Work.FTS_RegExport.RXT.Slots.v2_L12DzIterTendsto
import Submission.Work.FTS_RegExport.THL.Defs
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_alt_majorant
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT.SysAux

open scoped Real Topology
open MeasureTheory Set Filter

/-- **The `F_* + g̃`-split of the profile transforms.**  For the profile
`F(σ) = Ftau (pExp α) (GR α g) σ = Fstar (pExp α) + slice (gS α (tauExt g)) σ` of the modulation,
the transformed quantities split as `L₁₂(F) = L₁₂(F_*) + L₁₂(g̃)` with `L₁₂(F_*)(z) = 2β/(1+z)`
and `𝔽K(F) = 𝔽K(F_*) + 𝔽K(g̃)` with `𝔽K(F_*)(z) = β·2z/(1+z)²`. -/
theorem L12_FK_Ftau_split {α C₀ S : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) (hS : 0 < S)
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam}
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (hw : ∃ C : ℝ, ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ b a : ℕ, a + b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ →
      θ < Real.pi / 2 → |Work.Spaces.mixed b a (Work.FTS.Galerkin.slice g τ) z θ|
        ≤ C * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2)) :
    ∀ σ ∈ Set.Icc (0:ℝ) S, ∀ z : ℝ, 0 < z →
      (Work.Construction.L12 (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
            (Work.FTS.RegExportIface.RXT.GR α g) σ) z
          = 2 * Work.FTS.Regularity.pExp α / (1 + z)
            + Work.Construction.L12 (Work.FTS.Galerkin.slice
                (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)) σ) z) ∧
      (Work.Construction.FK (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
            (Work.FTS.RegExportIface.RXT.GR α g) σ) z
          = Work.FTS.Regularity.pExp α * (2 * z / (1 + z) ^ 2)
            + Work.Construction.FK (Work.FTS.Galerkin.slice
                (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)) σ) z) := by
  -- `F(σ) = Ftau (pExp α) (GR α g) σ = Fstar (pExp α) + slice (GR α g) σ`, and `GR α g` is the
  -- sanitiser `gS α (tauExt g)`, which agrees with `g` itself on the open quadrant for `σ ≥ 0`.
  -- Everything therefore follows from the `F_* + u`-additivity of the two integral transforms,
  -- the explicit values at `F_*` and the quadrant-congruence of `L₁₂` and `𝔽K`.
  intro σ hσ z hz
  have hαG : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hαG1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  have hσ0 : 0 ≤ σ := hσ.1
  -- the regularity package of the strong route: `C⁴` on the open quadrant and `ℋ⁴` at every `τ ≥ 0`
  have hreg := hOK.1.1
  -- `GR α g` agrees with `g` on the open quadrant (points of `Qd` are interior in `θ`)
  have hagGR : Work.FTS_RegExport.RXR5.AgreeOnQ
      (Work.FTS.Galerkin.slice (Work.FTS.RegExportIface.RXT.GR α g) σ)
      (Work.FTS.Galerkin.slice g σ) := by
    have h1 := Work.FTS_RegExport.RXR5.SG_slice_agreeOnQ α g σ
    rw [Work.FTS.FinalV2.slice_tauExt g hσ0] at h1
    exact h1
  -- hence the two full profiles agree on the quadrant
  have hFag : Work.FTS_RegExport.RXR5.AgreeOnQ
      (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
        (Work.FTS.RegExportIface.RXT.GR α g) σ)
      (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g σ) := by
    intro z' θ hz' hθ hθlt
    have h := hagGR z' θ hz' hθ hθlt
    simp only [Work.FTS.Galerkin.slice] at h ⊢
    simp only [Work.Construction.Ftau]
    rw [h]
  -- `L₁₂`-split
  have h12a := Work.FTS_RegExport.RXR5.L12_congr_of_agreeOnQ hFag hz.le
  have h12b : Work.Construction.L12 (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g σ) z
      = Work.Construction.L12 (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z
        + Work.Construction.L12 (Work.FTS.Galerkin.slice g σ) z :=
    Work.FTS_RegExport.RXT.L12_Fstar_add_c4 hαG hαG1
      (hreg.c4 σ hσ0) (hreg.mem4 σ hσ0) hz.le
  have h12c := Work.Construction.L12_Fstar_eq hαG hαG1 hz.le
  have h12d := Work.FTS_RegExport.RXR5.L12_congr_of_agreeOnQ hagGR.symm hz.le
  -- the angular slice of `g(σ)` is `L¹` against `K`: `∫_θ K θ u z θ / z` is integrable and
  -- `z > 0`, so multiplying back by `z` gives the certificate `FK_Fstar_add` asks for
  have hint : ∀ z' ∈ Set.Ioi (0:ℝ),
      IntegrableOn (fun θ => Work.FTS.Galerkin.slice g σ z' θ * Work.Spaces.K θ) Work.Spaces.Iθ := by
    intro z' hz'
    have h := Work.FTS.MeridianDyn.Bridge.Pieces.sliceK_integrableOn_of_continuousOn
      (hreg.c4 σ hσ0).continuousOn (hreg.mem4 σ hσ0) z' hz'
    have h2 : IntegrableOn (fun θ => (Work.Spaces.K θ * Work.FTS.Galerkin.slice g σ z' θ / z') * z')
        Work.Spaces.Iθ := h.mul_const z'
    refine h2.congr_fun ?_ measurableSet_Icc
    intro θ _
    show Work.Spaces.K θ * Work.FTS.Galerkin.slice g σ z' θ / z' * z'
      = Work.FTS.Galerkin.slice g σ z' θ * Work.Spaces.K θ
    rw [div_mul_cancel₀ _ (ne_of_gt hz')]
    ring
  -- `𝔽K`-split
  have hFKa := Work.FTS_RegExport.RXR5.FK_congr_of_agreeOnQ hFag hz
  have hFKb := Work.FTS.GalFields.Tail.FK_Fstar_add (α := Work.FTS.Regularity.pExp α)
    (u := Work.FTS.Galerkin.slice g σ) hint hz
  have hFKc := Work.FTS.Nonlinear.FstarPkg.FK_Fstar (α := Work.FTS.Regularity.pExp α) hαG hαG1 (z := z)
  have hFKd := Work.FTS_RegExport.RXR5.FK_congr_of_agreeOnQ hagGR.symm hz
  refine ⟨?_, ?_⟩
  · rw [h12a, h12b, h12c, h12d]
  · rw [hFKa]
    rw [show Work.Construction.FK (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g σ) z
      = Work.Construction.FK (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ
          + Work.FTS.Galerkin.slice g σ z θ) z from rfl]
    rw [hFKb, hFKc, hFKd]

end Work.FTS_RegExport.RXT.SysAux
