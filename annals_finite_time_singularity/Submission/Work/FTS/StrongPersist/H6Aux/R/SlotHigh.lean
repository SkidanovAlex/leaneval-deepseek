/-
# `Work.FTS.StrongPersist.H6Aux.R.SlotHigh` — the two first-order slots of `base_R`

The two *first order* pairings of `H1IP α (Lhat h) h`:

* `wip ρ_η (D_z (Lhat h)) (D_z h) ≥ -4·|h|²_{ℋ¹}` (slot 1),
* `wip ρ_γ (D_θ (Lhat h)) (D_θ h) ≥ -3·|h|²_{ℋ¹}` (slot 4).

Both are proved in the same way.  First the `Lhat`-commutator identity of `LhatCommOpen`
(`D_θ Lhat = Lhat D_θ` exactly, `D_z Lhat = Lhat D_z + Ê₂`) is used, together with the a.e.
congruence `wip_congr_fst_ae`, to replace `T (Lhat h)` by `Lhat (T h)` (plus the defect in
the `D_z` case).  Then the `u`-parametric bound `WipLhatGe`
(`wip ρ_q (Lhat u) u ≥ -(5/2)∫∫u²ρ_q`, proved from the two integration by parts) is applied
with `u = T h`, and the defect is handled by the pointwise Cauchy–Schwarz bound
`(Ê₂h)²ρ_η ≤ 2·HkIntegrand α 1 h`.  Finally `∫∫ (T h)²ρ_q ≤ |h|²_{ℋ¹}`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.H6Aux.R.Slots
import Submission.Work.Coercivity.zQuad
import Submission.Work.FTS.StrongPersist.H6Aux.R.WipLhatGe

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Aux.R

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 3200000

/-- The a.e. hypothesis `(z,θ) ∈ Qd` (the open quadrant `(0,∞) × (0,π/2)`) of
`LhatCommOpen`. -/
theorem ae_mem_Qd :
    ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      (p.1, p.2) ∈ Work.Construction.Qd := by
  filter_upwards [ae_angle_Ioo, ae_radius_pos] with p hθ hz
  rw [Work.Construction.Qd, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo]
  exact ⟨hz, hθ.1, hθ.2⟩

/-- A nonnegative weight is a.e. nonnegative on the quadrant. -/
theorem ae_Rhoq_nonneg (β : ℝ) :
    ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)), 0 ≤ Rhoq β p.1 p.2 := by
  filter_upwards [ae_snd_mem_Iθ] with p hθ
  exact Work.FTS.CoercivityFix.Coer1.Rho_nonneg β p.1 p.2 hθ

/-- **The `D_z`-slot of `base_R`.** -/
theorem SlotOne (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) {h : Fn}
    (hs : Work.FTS.EllipticEst.SmoothOpen h) (hm : Work.Spaces.HkMem α 2 h) :
    -(4 : ℝ) * Work.Spaces.HkSq α 1 h
      ≤ Work.Coercivity.wip (Rhoq Work.Spaces.eta) (Work.Spaces.Dz
          (Work.FTS.CoercivityFix.Lhat h)) (Work.Spaces.Dz h) := by
  have hm1 : Work.Spaces.HkMem α 1 h := Work.FTS.IPGen.HkMem_mono_le hs 1 (by norm_num) hm
  -- ### the pointwise block bounds
  have hbDz1 : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      (Work.Spaces.Dz h p.1 p.2) ^ 2 * Rhoq Work.Spaces.eta p.1 p.2
        ≤ Work.Spaces.HkIntegrand α 1 h p.1 p.2 := by
    filter_upwards [sq_dz_le_Hk (h := h) (k := 1) α 1 (by norm_num)] with p hp
    simpa only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero, Work.Spaces.mixed] using hp
  have hbDz2 : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      (Work.Spaces.Dz h p.1 p.2) ^ 2 * Rhoq Work.Spaces.eta p.1 p.2
        ≤ Work.Spaces.HkIntegrand α 2 h p.1 p.2 := by
    filter_upwards [sq_dz_le_Hk (h := h) (k := 2) α 1 (by norm_num)] with p hp
    simpa only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero, Work.Spaces.mixed] using hp
  have hbDz2' : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      (Work.Spaces.DzIter 2 h p.1 p.2) ^ 2 * Rhoq Work.Spaces.eta p.1 p.2
        ≤ Work.Spaces.HkIntegrand α 2 h p.1 p.2 :=
    sq_dz_le_Hk (h := h) (k := 2) α 2 (by norm_num)
  have hbTDz : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      (Work.Spaces.Dth (Work.Spaces.Dz h) p.1 p.2) ^ 2 * Rhoq Work.Spaces.eta p.1 p.2
        ≤ Work.Spaces.HkIntegrand α 2 h p.1 p.2 :=
    sq_DthDz_le_Hk (h := h) (k := 2) α hα0 hs (by norm_num)
  have hbE1 : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      (Work.FTS.CoercivityFix.E2hat h p.1 p.2) ^ 2 * Rhoq Work.Spaces.eta p.1 p.2
        ≤ (2 : ℝ) * Work.Spaces.HkIntegrand α 2 h p.1 p.2 :=
    sq_E2_le_Hk (h := h) (k := 2) α hα0 (by norm_num)
  have hbE1' : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      (Work.FTS.CoercivityFix.E2hat h p.1 p.2) ^ 2 * Rhoq Work.Spaces.eta p.1 p.2
        ≤ (2 : ℝ) * Work.Spaces.HkIntegrand α 1 h p.1 p.2 :=
    sq_E2_le_Hk (h := h) (k := 1) α hα0 (by norm_num)
  -- ### the corresponding integrability facts
  have hUz : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (Work.Spaces.Dz h z θ) ^ 2
        * Rhoq Work.Spaces.eta z θ)) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    integrable_sq_of_bound α 1 hs hm1 (C := 1) (by norm_num)
      (hs.Dz.continuousOn) (continuousOn_Rhoq_Q0 _) (ae_Rhoq_nonneg _)
      (by filter_upwards [hbDz1] with p hp; simpa using hp)
  have hUzS : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Spaces.Dz h z θ * Work.Spaces.Dz h z θ
        * Rhoq Work.Spaces.eta z θ)) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    integrableOn_sq_to_mul hUz
  have hEz : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (Work.Spaces.DzIter 2 h z θ) ^ 2
        * Rhoq Work.Spaces.eta z θ)) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    integrable_sq_of_bound α 2 hs hm (C := 1) (by norm_num)
      ((hs.DzIter 2).continuousOn) (continuousOn_Rhoq_Q0 _) (ae_Rhoq_nonneg _)
      (by filter_upwards [hbDz2'] with p hp; simpa using hp)
  have hEz2 : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (Work.Spaces.Dth (Work.Spaces.Dz h) z θ) ^ 2
        * Rhoq Work.Spaces.eta z θ)) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    integrable_sq_of_bound α 2 hs hm (C := 1) (by norm_num)
      (continuousOn_Dth_Q0 hs.Dz) (continuousOn_Rhoq_Q0 _) (ae_Rhoq_nonneg _)
      (by filter_upwards [hbTDz] with p hp; simpa using hp)
  have hE2z : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (Work.FTS.CoercivityFix.E2hat h z θ) ^ 2
        * Rhoq Work.Spaces.eta z θ)) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    integrable_sq_of_bound α 2 hs hm (C := 2) (by norm_num)
      (continuousOn_E2hat_Q0 hs) (continuousOn_Rhoq_Q0 _) (ae_Rhoq_nonneg _) hbE1
  have hEzS : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Spaces.DzIter 2 h z θ * Work.Spaces.Dz h z θ
        * Rhoq Work.Spaces.eta z θ)) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    integrable_mul_of_sq α 2 hs hm (Cu := 1) (Cv := 1) (by norm_num) (by norm_num)
      ((hs.DzIter 2).continuousOn) (hs.Dz.continuousOn) (continuousOn_Rhoq_Q0 _)
      (ae_Rhoq_nonneg _)
      (by filter_upwards [hbDz2'] with p hp; simpa using hp)
      (by filter_upwards [hbDz2] with p hp; simpa using hp)
  have hEz2S : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Spaces.Dth (Work.Spaces.Dz h) z θ
        * Work.Spaces.Dz h z θ * Rhoq Work.Spaces.eta z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    integrable_mul_of_sq α 2 hs hm (Cu := 1) (Cv := 1) (by norm_num) (by norm_num)
      (continuousOn_Dth_Q0 hs.Dz) (hs.Dz.continuousOn) (continuousOn_Rhoq_Q0 _)
      (ae_Rhoq_nonneg _)
      (by filter_upwards [hbTDz] with p hp; simpa using hp)
      (by filter_upwards [hbDz2] with p hp; simpa using hp)
  have hE2zS : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.FTS.CoercivityFix.E2hat h z θ
        * Work.FTS.CoercivityFix.E2hat h z θ * Rhoq Work.Spaces.eta z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    integrableOn_sq_to_mul hE2z
  -- ### the slot norm
  have hNz : Work.Coercivity.wip (Rhoq Work.Spaces.eta) (Work.Spaces.Dz h)
      (Work.Spaces.Dz h) ≤ Work.Spaces.HkSq α 1 h :=
    wip_self_le_HkSq α 1 hs hm1 hUz hbDz1
  -- ### the two integrability facts for `wip_add`
  have hLz : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz h) z θ
        * Work.Spaces.Dz h z θ * Rhoq Work.Spaces.eta z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    integrable_mul_of_sq α 2 hs hm (Cu := 60) (Cv := 1) (by norm_num) (by norm_num)
      (continuousOn_Lhat_Q0 hs.Dz) (hs.Dz.continuousOn) (continuousOn_Rhoq_Q0 _)
      (ae_Rhoq_nonneg _)
      (sq_LhatDz_le_Hk (h := h) (k := 2) α hα0 hs (by norm_num))
      (by filter_upwards [hbDz2] with p hp; simpa using hp)
  have hDz : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.FTS.CoercivityFix.E2hat h z θ
        * Work.Spaces.Dz h z θ * Rhoq Work.Spaces.eta z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    integrable_mul_of_sq α 2 hs hm (Cu := 2) (Cv := 1) (by norm_num) (by norm_num)
      (continuousOn_E2hat_Q0 hs) (hs.Dz.continuousOn) (continuousOn_Rhoq_Q0 _)
      (ae_Rhoq_nonneg _) hbE1
      (by filter_upwards [hbDz2] with p hp; simpa using hp)
  -- ### the commutator identity
  have hcomm : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      Work.Spaces.Dz (Work.FTS.CoercivityFix.Lhat h) p.1 p.2
        = (fun z θ => Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz h) z θ
            + Work.FTS.CoercivityFix.E2hat h z θ) p.1 p.2 := by
    filter_upwards [ae_mem_Qd] with p hp
    exact (LhatCommOpen hs).2 p.1 p.2 hp
  rw [wip_congr_fst_ae (ρ := Rhoq Work.Spaces.eta)
      (A := Work.Spaces.Dz (Work.FTS.CoercivityFix.Lhat h))
      (B := fun z θ => Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz h) z θ
        + Work.FTS.CoercivityFix.E2hat h z θ) (g := Work.Spaces.Dz h) hcomm]
  rw [Work.Coercivity.wip_add _ _ _ _ hLz hDz]
  -- ### the defect bound via Cauchy–Schwarz
  have hdef : -(3 / 2) * Work.Spaces.HkSq α 1 h
      ≤ Work.Coercivity.wip (Rhoq Work.Spaces.eta) (Work.FTS.CoercivityFix.E2hat h)
          (Work.Spaces.Dz h) := by
    have h1 : Work.Coercivity.wip (Rhoq Work.Spaces.eta) (Work.FTS.CoercivityFix.E2hat h)
        (Work.FTS.CoercivityFix.E2hat h) ≤ 2 * Work.Spaces.HkSq α 1 h :=
      wip_self_le_mul_HkSq α 1 hs hm1 (C := 2) (by norm_num) hE2zS
        (by filter_upwards [hbE1'] with p hp; simpa only [sq] using hp)
    have h2 := Work.FTS.CoercivityFix.DzSelf.wip_abs_le_half
      (ρ := Rhoq Work.Spaces.eta) (ρ' := Rhoq Work.Spaces.eta)
      (u := Work.FTS.CoercivityFix.E2hat h) (v := Work.Spaces.Dz h)
      (ae_Rhoq_nonneg _) (Filter.Eventually.of_forall fun p => le_rfl) hE2zS hUzS hDz
    have h3 : -|Work.Coercivity.wip (Rhoq Work.Spaces.eta) (Work.FTS.CoercivityFix.E2hat h)
        (Work.Spaces.Dz h)| ≤ Work.Coercivity.wip (Rhoq Work.Spaces.eta)
          (Work.FTS.CoercivityFix.E2hat h) (Work.Spaces.Dz h) := neg_abs_le _
    linarith [h1, h2, h3, hNz]
  -- ### the main bound
  have hmain : -(5 / 2) * (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.Dz h z θ) ^ 2 * Rhoq Work.Spaces.eta z θ)
      ≤ Work.Coercivity.wip (Rhoq Work.Spaces.eta)
          (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz h)) (Work.Spaces.Dz h) :=
    WipLhatGe (u := Work.Spaces.Dz h) (q := Work.Spaces.eta) hs.Dz
      (by rw [Work.Spaces.eta]; norm_num) (by rw [Work.Spaces.eta]; norm_num)
      hEzS hEz2S hUzS
  have hUne : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.Dz h z θ) ^ 2 * Rhoq Work.Spaces.eta z θ)
      = Work.Coercivity.wip (Rhoq Work.Spaces.eta) (Work.Spaces.Dz h)
          (Work.Spaces.Dz h) := (wip_self_eq _ _).symm
  rw [hUne] at hmain
  have hE0 : 0 ≤ Work.Spaces.HkSq α 1 h := Work.Spaces.HkSq_nonneg α 1 h
  linarith [hmain, hdef, hNz, hE0]

/-- **The `D_θ`-slot of `base_R`.** -/
theorem SlotFour (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) {h : Fn}
    (hs : Work.FTS.EllipticEst.SmoothOpen h) (hm : Work.Spaces.HkMem α 2 h) :
    -(3 : ℝ) * Work.Spaces.HkSq α 1 h
      ≤ Work.Coercivity.wip (Rhoq (Work.Spaces.gam α)) (Work.Spaces.Dth
          (Work.FTS.CoercivityFix.Lhat h)) (Work.Spaces.Dth h) := by
  have hm1 : Work.Spaces.HkMem α 1 h := Work.FTS.IPGen.HkMem_mono_le hs 1 (by norm_num) hm
  have hγ0 : (0 : ℝ) ≤ Work.Spaces.gam α := by rw [Work.Spaces.gam]; linarith
  have hγ2 : Work.Spaces.gam α ≤ 2 := by rw [Work.Spaces.gam]; linarith
  -- ### the pointwise block bounds
  have hbDth1 : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      (Work.Spaces.Dth h p.1 p.2) ^ 2 * Rhoq (Work.Spaces.gam α) p.1 p.2
        ≤ Work.Spaces.HkIntegrand α 1 h p.1 p.2 :=
    sq_mixed_le_Hk_gam (h := h) (k := 1) (j := 0) (i := 1) α hα0 (by norm_num) (by norm_num)
  have hbDth2 : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      (Work.Spaces.Dth h p.1 p.2) ^ 2 * Rhoq (Work.Spaces.gam α) p.1 p.2
        ≤ Work.Spaces.HkIntegrand α 2 h p.1 p.2 :=
    sq_mixed_le_Hk_gam (h := h) (k := 2) (j := 0) (i := 1) α hα0 (by norm_num) (by norm_num)
  have hbZ : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      (Work.Spaces.Dz (Work.Spaces.Dth h) p.1 p.2) ^ 2 * Rhoq (Work.Spaces.gam α) p.1 p.2
        ≤ Work.Spaces.HkIntegrand α 2 h p.1 p.2 := by
    filter_upwards [sq_mixed_le_Hk_gam (h := h) (k := 2) (j := 1) (i := 1) α hα0
      (by norm_num) (by norm_num)] with p hp
    simpa only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero, Work.Spaces.mixed] using hp
  have hbT : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      (Work.Spaces.Dth (Work.Spaces.Dth h) p.1 p.2) ^ 2 * Rhoq (Work.Spaces.gam α) p.1 p.2
        ≤ Work.Spaces.HkIntegrand α 2 h p.1 p.2 := by
    filter_upwards [sq_mixed_le_Hk_gam (h := h) (k := 2) (j := 0) (i := 2) α hα0
      (by norm_num) (by norm_num)] with p hp
    simpa only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero, Work.Spaces.mixed] using hp
  -- ### integrability
  have hUt : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (Work.Spaces.Dth h z θ) ^ 2
        * Rhoq (Work.Spaces.gam α) z θ)) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    integrable_sq_of_bound α 1 hs hm1 (C := 1) (by norm_num)
      (hs.Dth.continuousOn) (continuousOn_Rhoq_Q0 _) (ae_Rhoq_nonneg _)
      (by filter_upwards [hbDth1] with p hp; simpa using hp)
  have hZt : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Spaces.Dz (Work.Spaces.Dth h) z θ
        * Work.Spaces.Dth h z θ * Rhoq (Work.Spaces.gam α) z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    integrable_mul_of_sq α 2 hs hm (Cu := 1) (Cv := 1) (by norm_num) (by norm_num)
      (((hs.Dth).Dz).continuousOn) (hs.Dth.continuousOn)
      (continuousOn_Rhoq_Q0 _) (ae_Rhoq_nonneg _)
      (by filter_upwards [hbZ] with p hp; simpa using hp)
      (by filter_upwards [hbDth2] with p hp; simpa using hp)
  have hTt : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Spaces.Dth (Work.Spaces.Dth h) z θ
        * Work.Spaces.Dth h z θ * Rhoq (Work.Spaces.gam α) z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    integrable_mul_of_sq α 2 hs hm (Cu := 1) (Cv := 1) (by norm_num) (by norm_num)
      (continuousOn_Dth_Q0 hs.Dth) (hs.Dth.continuousOn) (continuousOn_Rhoq_Q0 _)
      (ae_Rhoq_nonneg _)
      (by filter_upwards [hbT] with p hp; simpa using hp)
      (by filter_upwards [hbDth2] with p hp; simpa using hp)
  -- ### the slot norm
  have hUtS : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Spaces.Dth h z θ * Work.Spaces.Dth h z θ
        * Rhoq (Work.Spaces.gam α) z θ)) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    integrableOn_sq_to_mul hUt
  have hNt : Work.Coercivity.wip (Rhoq (Work.Spaces.gam α)) (Work.Spaces.Dth h)
      (Work.Spaces.Dth h) ≤ Work.Spaces.HkSq α 1 h :=
    wip_self_le_HkSq α 1 hs hm1 hUt hbDth1
  -- ### the commutator identity and the main bound
  have hcomm : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      Work.Spaces.Dth (Work.FTS.CoercivityFix.Lhat h) p.1 p.2
        = Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dth h) p.1 p.2 := by
    filter_upwards [ae_mem_Qd] with p hp
    exact (LhatCommOpen hs).1 p.1 p.2 hp
  rw [wip_congr_fst_ae (ρ := Rhoq (Work.Spaces.gam α))
      (A := Work.Spaces.Dth (Work.FTS.CoercivityFix.Lhat h))
      (B := Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dth h))
      (g := Work.Spaces.Dth h) hcomm]
  have hmain : -(5 / 2) * (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.Dth h z θ) ^ 2 * Rhoq (Work.Spaces.gam α) z θ)
      ≤ Work.Coercivity.wip (Rhoq (Work.Spaces.gam α))
          (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dth h)) (Work.Spaces.Dth h) :=
    WipLhatGe (u := Work.Spaces.Dth h) (q := Work.Spaces.gam α) hs.Dth hγ0 hγ2 hZt hTt hUtS
  have hUne : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.Dth h z θ) ^ 2 * Rhoq (Work.Spaces.gam α) z θ)
      = Work.Coercivity.wip (Rhoq (Work.Spaces.gam α)) (Work.Spaces.Dth h)
          (Work.Spaces.Dth h) := (wip_self_eq _ _).symm
  rw [hUne] at hmain
  have hE0 : 0 ≤ Work.Spaces.HkSq α 1 h := Work.Spaces.HkSq_nonneg α 1 h
  linarith [hmain, hNt, hE0]

end Work.FTS.StrongPersist.H6Aux.R
