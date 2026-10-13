import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkSliceSup
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkMomentJetSq
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T4bSlotAux
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.rowAux
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux.fkMomentAe
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux.topSlotZLe
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T5bPrep
import Submission.Work.FTS.TransportS.Slots

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux

open MeasureTheory Set Filter
open scoped Real Topology

/-!
# `fkShiftHigh_shiftF` — the `F²`-energy of the shifted `D_z`-row of `FK f`

For a level-six datum (`DatData α f M`), `4 ≤ b₁ ≤ 6` and a leaf weight
`ρ` of the angular slot `0`, the product-measure integral of

  `(D_z^{b₁}(FK f) z)² · ρ z θ · (D_z^{6-b₁}D_θ f z θ)²`

is finite and bounded by `C · HkSq α 4 f · (1 + HkSq α 6 f)` with a universal `C`.

The two analytic ingredients (both already in the tree) are

* the *uniform in `z`* angular slice bound `fkSliceSup_sliceSupGraded` at level `4`:
  `∫_θ sin(2θ)^{-η}(D_z^{6-b₁}D_θ f z θ)² ≤ 3 |f|²_{ℋ⁴}` for every `z > 0` — this is
  exactly where `b₁ ≥ 4` is used (`1 + (6-b₁) + 1 ≤ 4`);
* the *integrated* radial bound `fkMomentJetSq`: `∫_z (D_z^{b₁}(FK f) z)² w(z)² ≤ C|f|²_{ℋ⁶}`.

Since `ρ ≤ w² sin(2θ)^{-η}` on the quadrant and the radial factor `(D_z^{b₁}(FK f))²`
is constant in `θ`, Fubini turns the double integral into `∫_z (D_z^{b₁}(FK f) z)² ·
(∫_θ ρ z θ (D_z^{6-b₁}D_θ f z θ)²)`, whose inner factor is `≤ w(z)²·3|f|²_{ℋ⁴}`.
-/

/-- The `D_z`-jet of the angular moment, lifted to the product space, is a.e. strongly
measurable: it agrees a.e. with the angular moment of the `D_z`-jet, which is the
`θ`-marginal of a function continuous on the open quadrant. -/
private theorem aesm_fst_dzdIter_FK {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 6 f)
    {k : ℕ} (hk : k ≤ 6) :
    MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.Elliptic.DzdIter k (fun z => Work.Construction.FK f z) p.1)
      Work.FTS.StrongPersist.H6Rows.Npair6BWork.PM := by
  have hcont : ContinuousOn
      (fun p : ℝ × ℝ => Work.Spaces.DzIter k f p.1 p.2 * Work.Spaces.K p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    ((hF.DzIter k).continuousOn).mul (by unfold Work.Spaces.K; fun_prop)
  have hjoint := Work.Spaces.aesm_of_continuousOn_Qd _ hcont
  have h2 : MeasureTheory.AEStronglyMeasurable
      (fun z : ℝ => Work.Construction.FK (Work.Spaces.DzIter k f) z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    simpa only [Work.Construction.FK] using hjoint.integral_prod_right'
  have hae : (fun z : ℝ => Work.Elliptic.DzdIter k (fun z => Work.Construction.FK f z) z)
      =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iz]
      (fun z : ℝ => Work.Construction.FK (Work.Spaces.DzIter k f) z) := by
    have h := Work.FTS.StrongPersist.H6Rows.Npair6SupAux.DzIter_FK_eq_ae hF hmem k hk
    filter_upwards [h] with z hz
    rw [← Work.Elliptic.DzIter_rad (fun z => Work.Construction.FK f z) k z 0]
    exact hz 0
  exact (h2.congr hae.symm).comp_fst

theorem fkShiftHigh_shiftF : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (f : ℝ → ℝ → ℝ) (M : ℝ) (b₁ : ℕ) (ρ : ℝ → ℝ → ℝ),
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.DatData α f M →
      4 ≤ b₁ → b₁ ≤ 6 → Work.FTS.TransportS.IsLeafW α 0 ρ →
      MeasureTheory.Integrable (fun p : ℝ × ℝ =>
          (Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) p.1) ^ 2
            * ρ p.1 p.2 * (Work.Spaces.mixed (6 - b₁) 1 f p.1 p.2) ^ 2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
      (∫ p, (Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) p.1) ^ 2
            * ρ p.1 p.2 * (Work.Spaces.mixed (6 - b₁) 1 f p.1 p.2) ^ 2
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
        ≤ C * Work.Spaces.HkSq α 4 f * (1 + Work.Spaces.HkSq α 6 f) := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := fkMomentJetSq
  refine ⟨3 * C₁, mul_pos (by norm_num) hC₁pos, ?_⟩
  intro α hαI f M b₁ ρ hD hb₁lo hb₁hi hρ
  obtain ⟨hα0, hα1⟩ := hαI
  obtain ⟨hsm, h6, h7, hvanish, haxis, hbdd⟩ := hD
  have hmem4 : Work.Spaces.HkMem α 4 f :=
    Work.FTS.OpenPkg.HkMem_mono_open hsm 4 (by norm_num) h6
  have hS4 : (0 : ℝ) ≤ Work.Spaces.HkSq α 4 f := Work.Spaces.HkSq_nonneg α 4 f
  have hS6 : (0 : ℝ) ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
  obtain ⟨hMJint, hMJval⟩ := hC₁ α ⟨hα0, hα1⟩ f hsm h6 b₁ hb₁hi
  -- a.e. strong measurability of the three factors
  have haesm_g : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ =>
        (Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) p.1) ^ 2)
      Work.FTS.StrongPersist.H6Rows.Npair6BWork.PM :=
    (aesm_fst_dzdIter_FK hsm h6 hb₁hi).pow 2
  have haesm_A : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => (Work.Spaces.mixed (6 - b₁) 1 f p.1 p.2) ^ 2)
      Work.FTS.StrongPersist.H6Rows.Npair6BWork.PM :=
    (Work.FTS.StrongPersist.H6Rows.Npair6BWork.aesm_mixed hsm (6 - b₁) 1).pow 2
  have haesm_H : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ =>
        (Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) p.1) ^ 2
          * Work.FTS.TransportS.SlotT2.canonW Work.Spaces.eta p.1 p.2
          * (Work.Spaces.mixed (6 - b₁) 1 f p.1 p.2) ^ 2)
      Work.FTS.StrongPersist.H6Rows.Npair6BWork.PM :=
    (haesm_g.mul
      (Work.FTS.StrongPersist.H6Rows.Npair6BWork.aesm_canonW Work.Spaces.eta)).mul haesm_A
  have haesm_G : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ =>
        (Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) p.1) ^ 2
          * ρ p.1 p.2 * (Work.Spaces.mixed (6 - b₁) 1 f p.1 p.2) ^ 2)
      Work.FTS.StrongPersist.H6Rows.Npair6BWork.PM :=
    (haesm_g.mul (Work.FTS.StrongPersist.H6Rows.Npair6BWork.aesm_leafW hρ)).mul haesm_A
  -- nonnegativity of the dominating integrand on the angular interval
  have hHnn : ∀ z θ : ℝ, θ ∈ Work.Spaces.Iθ → 0 ≤
      (Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) z) ^ 2
        * Work.FTS.TransportS.SlotT2.canonW Work.Spaces.eta z θ
        * (Work.Spaces.mixed (6 - b₁) 1 f z θ) ^ 2 := by
    intro z θ hθ
    have hσ : 0 ≤ Real.sin (2 * θ) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    refine mul_nonneg (mul_nonneg (sq_nonneg _) ?_) (sq_nonneg _)
    rw [Work.FTS.TransportS.SlotT2.canonW]
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hσ _)
  -- the uniform-in-`z` angular slice bound, with the radial factor pulled out
  have hslice_bd : ∀ z : ℝ, 0 < z →
      (∫ θ, (Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) z) ^ 2
        * Work.FTS.TransportS.SlotT2.canonW Work.Spaces.eta z θ
        * (Work.Spaces.mixed (6 - b₁) 1 f z θ) ^ 2
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      ≤ (Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) z) ^ 2
          * (Work.Spaces.w z) ^ 2 * (3 * Work.Spaces.HkSq α 4 f) := by
    intro z hz
    have hbase := fkSliceSup_sliceSupGraded hα0 hsm hmem4 (j := 6 - b₁) (i := 1)
      (by omega) z hz
    have hfac : (∫ θ, (Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) z) ^ 2
          * Work.FTS.TransportS.SlotT2.canonW Work.Spaces.eta z θ
          * (Work.Spaces.mixed (6 - b₁) 1 f z θ) ^ 2
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
        = (Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) z) ^ 2
          * (Work.Spaces.w z) ^ 2
          * (∫ θ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
              * (Work.Spaces.mixed (6 - b₁) 1 f z θ) ^ 2
              ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
      have hcongr : (fun θ => (Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) z) ^ 2
            * Work.FTS.TransportS.SlotT2.canonW Work.Spaces.eta z θ
            * (Work.Spaces.mixed (6 - b₁) 1 f z θ) ^ 2)
          = (fun θ => ((Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) z) ^ 2
              * (Work.Spaces.w z) ^ 2) * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
              * (Work.Spaces.mixed (6 - b₁) 1 f z θ) ^ 2)) := by
        funext θ
        rw [Work.FTS.TransportS.SlotT2.canonW]
        ring
      rw [hcongr, MeasureTheory.integral_const_mul]
    rw [hfac]
    exact mul_le_mul_of_nonneg_left hbase (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  -- integrability of the angular slices of the dominating integrand
  have hsliceH : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.Integrable (fun θ =>
        (Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) z) ^ 2
          * Work.FTS.TransportS.SlotT2.canonW Work.Spaces.eta z θ
          * (Work.Spaces.mixed (6 - b₁) 1 f z θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    rw [MeasureTheory.ae_restrict_iff'
      (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici)]
    filter_upwards [MeasureTheory.Measure.ae_ne (MeasureTheory.volume) (0 : ℝ)] with z hne hzI
    have hz : 0 < z := lt_of_le_of_ne hzI (Ne.symm hne)
    have hbase := fkSliceSup_slice_integrable hα0 hsm hmem4 (j := 6 - b₁) (i := 1)
      (by omega) hz
    have heq : (fun θ => (Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) z) ^ 2
          * Work.FTS.TransportS.SlotT2.canonW Work.Spaces.eta z θ
          * (Work.Spaces.mixed (6 - b₁) 1 f z θ) ^ 2)
        = (fun θ => ((Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) z) ^ 2
            * (Work.Spaces.w z) ^ 2) * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
            * (Work.Spaces.mixed (6 - b₁) 1 f z θ) ^ 2)) := by
      funext θ
      rw [Work.FTS.TransportS.SlotT2.canonW]
      ring
    rw [heq]
    exact hbase.const_mul _
  -- the dominating radial majorant is integrable
  have hdomint : MeasureTheory.Integrable
      (fun z => (Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) z) ^ 2
        * (Work.Spaces.w z) ^ 2 * (3 * Work.Spaces.HkSq α 4 f))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    hMJint.mul_const (3 * Work.Spaces.HkSq α 4 f)
  -- integrability of the norm-marginal (`integrable_prod_iff` needs the norm)
  have hmargnn : ∀ z : ℝ, 0 ≤ ∫ θ,
      ‖(Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) z) ^ 2
        * Work.FTS.TransportS.SlotT2.canonW Work.Spaces.eta z θ
        * (Work.Spaces.mixed (6 - b₁) 1 f z θ) ^ 2‖
      ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    fun z => MeasureTheory.integral_nonneg (fun θ => norm_nonneg _)
  have hOutNorm : MeasureTheory.Integrable
      (fun z => ∫ θ,
        ‖(Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) z) ^ 2
          * Work.FTS.TransportS.SlotT2.canonW Work.Spaces.eta z θ
          * (Work.Spaces.mixed (6 - b₁) 1 f z θ) ^ 2‖
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    refine MeasureTheory.Integrable.mono' hdomint ?_ ?_
    · exact (haesm_H.norm).integral_prod_right'
    · rw [MeasureTheory.ae_restrict_iff'
        (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici)]
      filter_upwards [MeasureTheory.Measure.ae_ne (MeasureTheory.volume) (0 : ℝ)] with z hne hzI
      have hz : 0 < z := lt_of_le_of_ne hzI (Ne.symm hne)
      rw [Real.norm_of_nonneg (hmargnn z)]
      rw [MeasureTheory.setIntegral_congr_fun
        (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)
        (fun θ hθ => Real.norm_of_nonneg (hHnn z θ hθ))]
      exact hslice_bd z hz
  -- Fubini for the dominating integrand
  have hIntH : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
        (Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) p.1) ^ 2
          * Work.FTS.TransportS.SlotT2.canonW Work.Spaces.eta p.1 p.2
          * (Work.Spaces.mixed (6 - b₁) 1 f p.1 p.2) ^ 2)
      Work.FTS.StrongPersist.H6Rows.Npair6BWork.PM := by
    rw [MeasureTheory.integrable_prod_iff haesm_H]
    exact ⟨hsliceH, hOutNorm⟩
  have hOutMarg : MeasureTheory.Integrable
      (fun z => ∫ θ, (Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) z) ^ 2
        * Work.FTS.TransportS.SlotT2.canonW Work.Spaces.eta z θ
        * (Work.Spaces.mixed (6 - b₁) 1 f z θ) ^ 2
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have hae : ∀ᵐ z ∂(MeasureTheory.volume), z ∈ Work.Spaces.Iz →
        (∫ θ, ‖(Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) z) ^ 2
          * Work.FTS.TransportS.SlotT2.canonW Work.Spaces.eta z θ
          * (Work.Spaces.mixed (6 - b₁) 1 f z θ) ^ 2‖
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
        = (∫ θ, (Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) z) ^ 2
          * Work.FTS.TransportS.SlotT2.canonW Work.Spaces.eta z θ
          * (Work.Spaces.mixed (6 - b₁) 1 f z θ) ^ 2
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
      filter_upwards with z _
      exact MeasureTheory.setIntegral_congr_fun
        (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)
        (fun θ hθ => Real.norm_of_nonneg (hHnn z θ hθ))
    exact hOutNorm.congr ((MeasureTheory.ae_restrict_iff'
      (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici)).mpr hae)
  have hmarg_le : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      (∫ θ, (Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) z) ^ 2
        * Work.FTS.TransportS.SlotT2.canonW Work.Spaces.eta z θ
        * (Work.Spaces.mixed (6 - b₁) 1 f z θ) ^ 2
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      ≤ (Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) z) ^ 2
          * (Work.Spaces.w z) ^ 2 * (3 * Work.Spaces.HkSq α 4 f) := by
    rw [MeasureTheory.ae_restrict_iff'
      (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici)]
    filter_upwards [MeasureTheory.Measure.ae_ne (MeasureTheory.volume) (0 : ℝ)] with z hne hzI
    exact hslice_bd z (lt_of_le_of_ne hzI (Ne.symm hne))
  have hvalH : (∫ p, (Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) p.1) ^ 2
        * Work.FTS.TransportS.SlotT2.canonW Work.Spaces.eta p.1 p.2
        * (Work.Spaces.mixed (6 - b₁) 1 f p.1 p.2) ^ 2
      ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
      = ∫ z, (∫ θ, (Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) z) ^ 2
        * Work.FTS.TransportS.SlotT2.canonW Work.Spaces.eta z θ
        * (Work.Spaces.mixed (6 - b₁) 1 f z θ) ^ 2
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    MeasureTheory.integral_prod
      (fun p : ℝ × ℝ => (Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) p.1) ^ 2
        * Work.FTS.TransportS.SlotT2.canonW Work.Spaces.eta p.1 p.2
        * (Work.Spaces.mixed (6 - b₁) 1 f p.1 p.2) ^ 2) hIntH
  have hboundH : (∫ z, (∫ θ, (Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) z) ^ 2
        * Work.FTS.TransportS.SlotT2.canonW Work.Spaces.eta z θ
        * (Work.Spaces.mixed (6 - b₁) 1 f z θ) ^ 2
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iz))
      ≤ 3 * C₁ * Work.Spaces.HkSq α 4 f * Work.Spaces.HkSq α 6 f := by
    calc (∫ z, (∫ θ, (Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) z) ^ 2
          * Work.FTS.TransportS.SlotT2.canonW Work.Spaces.eta z θ
          * (Work.Spaces.mixed (6 - b₁) 1 f z θ) ^ 2
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iz))
        ≤ ∫ z, (Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) z) ^ 2
            * (Work.Spaces.w z) ^ 2 * (3 * Work.Spaces.HkSq α 4 f)
            ∂(MeasureTheory.volume.restrict Work.Spaces.Iz) :=
          MeasureTheory.integral_mono_ae hOutMarg hdomint hmarg_le
      _ = (3 * Work.Spaces.HkSq α 4 f)
            * (∫ z, (Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) z) ^ 2
                * (Work.Spaces.w z) ^ 2 ∂(MeasureTheory.volume.restrict Work.Spaces.Iz)) := by
          rw [show (fun z => (Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) z) ^ 2
                * (Work.Spaces.w z) ^ 2 * (3 * Work.Spaces.HkSq α 4 f))
              = (fun z => (3 * Work.Spaces.HkSq α 4 f)
                * ((Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) z) ^ 2
                  * (Work.Spaces.w z) ^ 2)) from by
            funext z; ring]
          rw [MeasureTheory.integral_const_mul]
      _ ≤ (3 * Work.Spaces.HkSq α 4 f) * (C₁ * Work.Spaces.HkSq α 6 f) :=
          mul_le_mul_of_nonneg_left hMJval (mul_nonneg (by norm_num) hS4)
      _ = 3 * C₁ * Work.Spaces.HkSq α 4 f * Work.Spaces.HkSq α 6 f := by ring
  -- the target integrand is dominated by the `canonW η` one
  have hpt_le : ∀ᵐ p ∂Work.FTS.StrongPersist.H6Rows.Npair6BWork.PM,
      (Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) p.1) ^ 2
          * ρ p.1 p.2 * (Work.Spaces.mixed (6 - b₁) 1 f p.1 p.2) ^ 2
      ≤ (Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) p.1) ^ 2
          * Work.FTS.TransportS.SlotT2.canonW Work.Spaces.eta p.1 p.2
          * (Work.Spaces.mixed (6 - b₁) 1 f p.1 p.2) ^ 2 := by
    filter_upwards [Work.FTS.StrongPersist.H6Rows.Npair6BWork.ae_PM_Q0] with p hp
    obtain ⟨hz, hθ0, hθ1⟩ := hp
    have hρle := Work.FTS.StrongPersist.H6Rows.Npair6BWork.leafW_le_canonW_eta
      hρ p.1 p.2 hz hθ0 hθ1
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hρle (sq_nonneg _)) (sq_nonneg _)
  have hGnn : ∀ᵐ p ∂Work.FTS.StrongPersist.H6Rows.Npair6BWork.PM, 0 ≤
      (Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) p.1) ^ 2
          * ρ p.1 p.2 * (Work.Spaces.mixed (6 - b₁) 1 f p.1 p.2) ^ 2 := by
    filter_upwards [Work.FTS.StrongPersist.H6Rows.Npair6BWork.ae_PM_Q0] with p hp
    obtain ⟨hz, hθ0, hθ1⟩ := hp
    exact mul_nonneg (mul_nonneg (sq_nonneg _)
      (Work.FTS.StrongPersist.H6Rows.Npair6BWork.leafW_nonneg hρ p.1 p.2 hz hθ0 hθ1))
      (sq_nonneg _)
  have hIntG : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
        (Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) p.1) ^ 2
          * ρ p.1 p.2 * (Work.Spaces.mixed (6 - b₁) 1 f p.1 p.2) ^ 2)
      Work.FTS.StrongPersist.H6Rows.Npair6BWork.PM :=
    MeasureTheory.Integrable.mono' hIntH haesm_G
      (by filter_upwards [hpt_le, hGnn] with p h1 h2
          rw [Real.norm_of_nonneg h2]; exact h1)
  have hvalG : (∫ p, (Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) p.1) ^ 2
        * ρ p.1 p.2 * (Work.Spaces.mixed (6 - b₁) 1 f p.1 p.2) ^ 2
      ∂Work.FTS.StrongPersist.H6Rows.Npair6BWork.PM)
      ≤ ∫ p, (Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) p.1) ^ 2
        * Work.FTS.TransportS.SlotT2.canonW Work.Spaces.eta p.1 p.2
        * (Work.Spaces.mixed (6 - b₁) 1 f p.1 p.2) ^ 2
      ∂Work.FTS.StrongPersist.H6Rows.Npair6BWork.PM :=
    MeasureTheory.integral_mono_ae hIntG hIntH hpt_le
  constructor
  · exact hIntG
  · calc (∫ p, (Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) p.1) ^ 2
          * ρ p.1 p.2 * (Work.Spaces.mixed (6 - b₁) 1 f p.1 p.2) ^ 2
        ∂Work.FTS.StrongPersist.H6Rows.Npair6BWork.PM)
        ≤ ∫ p, (Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) p.1) ^ 2
          * Work.FTS.TransportS.SlotT2.canonW Work.Spaces.eta p.1 p.2
          * (Work.Spaces.mixed (6 - b₁) 1 f p.1 p.2) ^ 2
        ∂Work.FTS.StrongPersist.H6Rows.Npair6BWork.PM := hvalG
      _ = ∫ z, (∫ θ, (Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) z) ^ 2
          * Work.FTS.TransportS.SlotT2.canonW Work.Spaces.eta z θ
          * (Work.Spaces.mixed (6 - b₁) 1 f z θ) ^ 2
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iz) := hvalH
      _ ≤ 3 * C₁ * Work.Spaces.HkSq α 4 f * Work.Spaces.HkSq α 6 f := hboundH
      _ ≤ 3 * C₁ * Work.Spaces.HkSq α 4 f * (1 + Work.Spaces.HkSq α 6 f) :=
          mul_le_mul_of_nonneg_left (by linarith)
            (mul_nonneg (mul_nonneg (by norm_num) hC₁pos.le) hS4)

end Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux
