import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.HarOp_pointwise_sq
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.LogInt
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.StarSlotPcs.DzdIterBound
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6
import Submission.Work.FTS.StrongPersist.SupOpenH2
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_EllLimOK.Pinning.integrableOn_sq_rpow_of_HkMem
import Submission.Work.FTS_RegExport.RXB.sup_bound_all_alpha
import Submission.Work.FTS_RegExport.RXT.Slots.JetCalc.Expand
import Submission.Work.H2.WPQ.m_term_le_smoothQuad
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.SmoothStripDefs
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Stability.ZcutSmoothCompact
-- ===== merged: Submission.Work.FTS.EllipticEst.Deleg.i1Paper_weakMixedAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Deleg

open MeasureTheory Set Filter
open scoped Real Topology

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- **The final assembly of the cut-off chain**, given its three analytic pieces: the collar bound,
the per-`(χ_n, ψ_δ)` inequality and the `ψ_δ ↓ 0` limit.  The rate constant is produced by
`I1Wk.aeGradTrace0` from the two mixed-honesty hypotheses, and the identification
`HkSq α 0 (∂_θ(grad u)) = Vfull u` is `AeColl.Vfull_eq_HkSq`. -/
theorem i1Paper_weakMixed_of
    (hcol : ∃ Cw : ℝ, 0 < Cw ∧ CollarBound Cw)
    (hpair : ∀ Cw : ℝ, 0 < Cw → CollarBound Cw → TruncPairLe Cw)
    (hplim : ∀ Cw : ℝ, 0 < Cw → PairLimit Cw) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ),
    Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
      Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u) →
      (∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
        MeasureTheory.IntegrableOn
          (fun θ => (z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
            * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iθ) →
      MeasureTheory.IntegrableOn
        (fun z => ∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
            * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iz →
      ((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta)) *
          (α ^ 2 * Work.Spaces.HkSq α 0
            (Work.Spaces.pth (Work.FTS.EllipticEst.H2W.Ae.grad u)))
        - C * α ^ 2 * (Work.FTS.EllipticEst.AngSecond.IP
              (Work.FTS.EllipticEst.H2W.Ae.grad u) (Work.FTS.EllipticEst.H2W.Ae.grad u)
            + Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP
                (Work.FTS.EllipticEst.H2W.Ae.grad u) (Work.FTS.EllipticEst.H2W.Ae.grad u))
              * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP
                  (Work.Spaces.pthIter 2 u) (Work.Spaces.pthIter 2 u)))
      ≤ α ^ 2 * Work.FTS.EllipticEst.AngSecond.IP
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) (Work.Spaces.pthIter 2 u) := by
  obtain ⟨Cw, hCw, hC⟩ := hcol
  obtain ⟨C1, hC1, hbound⟩ := mixedLimitBound
  refine ⟨C1, hC1, ?_⟩
  intro α u G hAe hU h1 h2
  have hmix : MixedHon u := ⟨h1, h2⟩
  -- the endpoint rate of the slices of `U`, from the two mixed-honesty hypotheses
  obtain ⟨K, hK, hrate0⟩ :=
    Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk.aeGradTrace0 α u G hAe hU h1 h2
  have hrate : SliceRate K u := by
    filter_upwards [hrate0] with z hz
    exact ⟨hz.2.2.2.1, hz.2.2.2.2⟩
  have hcut : ∀ n : ℕ,
      kap * Work.FTS.EllipticEst.AeColl.Pcut u n
        ≤ Work.FTS.EllipticEst.AeColl.Dcut u n + Work.FTS.EllipticEst.AeColl.Trcut u n
          - 2 * Work.Spaces.eta * Work.FTS.EllipticEst.AeColl.Acut u n :=
    hplim Cw hCw α u G hAe hU hmix K hK hrate
      (hpair Cw hCw hC α u G hAe hU hmix K hK hrate)
  have hmain := hbound α u G hAe hU hcut
  -- rewrite the `Az`/`Uz` aliases into the target's expressions
  have hmain' : kap * Work.FTS.EllipticEst.AeColl.Vfull u
      ≤ Work.FTS.EllipticEst.AngSecond.IP (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ)
            (Work.Spaces.pthIter 2 u)
        + C1 * (Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.H2W.Ae.grad u)
                (Work.FTS.EllipticEst.H2W.Ae.grad u)
              + Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.H2W.Ae.grad u)
                    (Work.FTS.EllipticEst.H2W.Ae.grad u))
                * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP (Work.Spaces.pthIter 2 u)
                    (Work.Spaces.pthIter 2 u))) := by
    have h1 : Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.AeColl.Az u)
        (Work.Spaces.pthIter 2 u)
        = Work.FTS.EllipticEst.AngSecond.IP (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ)
            (Work.Spaces.pthIter 2 u) := rfl
    have h2 : Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.AeColl.Uz u)
        (Work.FTS.EllipticEst.AeColl.Uz u)
        = Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.H2W.Ae.grad u)
            (Work.FTS.EllipticEst.H2W.Ae.grad u) := rfl
    rw [h1, h2] at hmain
    exact hmain
  -- identify `HkSq α 0 (∂_θ(z∂_zu))` with `Vfull u`
  have hV := Work.FTS.EllipticEst.AeColl.Vfull_eq_HkSq α u
    (Work.FTS.EllipticEst.H2W.Ae.AeData.smooth hAe)
  have hα2 : (0 : ℝ) ≤ α ^ 2 := sq_nonneg α
  have hstep := mul_le_mul_of_nonneg_left hmain' hα2
  have hgoal : kap * (α ^ 2 * Work.FTS.EllipticEst.AeColl.Vfull u)
      - C1 * α ^ 2 * (Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.H2W.Ae.grad u)
            (Work.FTS.EllipticEst.H2W.Ae.grad u)
          + Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.H2W.Ae.grad u)
                (Work.FTS.EllipticEst.H2W.Ae.grad u))
            * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP (Work.Spaces.pthIter 2 u)
                (Work.Spaces.pthIter 2 u)))
      ≤ α ^ 2 * Work.FTS.EllipticEst.AngSecond.IP (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ)
          (Work.Spaces.pthIter 2 u) := by
    have e1 : α ^ 2 * (kap * Work.FTS.EllipticEst.AeColl.Vfull u)
        = kap * (α ^ 2 * Work.FTS.EllipticEst.AeColl.Vfull u) := by ring
    have e2 : α ^ 2 * (Work.FTS.EllipticEst.AngSecond.IP
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) (Work.Spaces.pthIter 2 u)
          + C1 * (Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.H2W.Ae.grad u)
                (Work.FTS.EllipticEst.H2W.Ae.grad u)
              + Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.H2W.Ae.grad u)
                    (Work.FTS.EllipticEst.H2W.Ae.grad u))
                * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP (Work.Spaces.pthIter 2 u)
                    (Work.Spaces.pthIter 2 u))))
        = α ^ 2 * Work.FTS.EllipticEst.AngSecond.IP
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) (Work.Spaces.pthIter 2 u)
          + C1 * α ^ 2 * (Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.H2W.Ae.grad u)
                (Work.FTS.EllipticEst.H2W.Ae.grad u)
              + Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.H2W.Ae.grad u)
                    (Work.FTS.EllipticEst.H2W.Ae.grad u))
                * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP (Work.Spaces.pthIter 2 u)
                    (Work.Spaces.pthIter 2 u))) := by ring
    rw [e1, e2] at hstep
    linarith [hstep]
  rw [hV]
  simpa only [kap] using hgoal

end

end Work.FTS.EllipticEst.Deleg
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.LogWeightInt.logW_mul_sq_facts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `logW_mul_sq_facts` — integrability and value of the log-coordinate weight pairing

For a weight `w` and a profile `F`, the log-coordinate pairing of
`logW w` against the square of the pulled-back profile `logPull F` is the same object as the
flat (quadrant) pairing `wip w F F` of `w` against `F ^ 2`:

* it is Bochner-integrable on the plane, and
* its value is `wip w F F`.

The two halves are exactly the two directions of the log-coordinate substitution
`(z,θ) = (e^s, arctan (e^ζ))`:

* the integrability is transported from the quadrant by the `lintegral` substitution
  `HkSqAux.lintegral_quad_log_subst` (`JT.integrable_logW_sq_of_lintegral`), with the
  finiteness of the quadrant `∫⁻` read off from `Integrable` (the helper below);
* the value is the Bochner substitution `JepsTransfer.integral_quad_log_subst`, followed by
  Fubini (`MeasureTheory.integral_prod`) to turn the product-measure integral over `ℝ × ℝ`
  into the iterated one in the log coordinates.

The helper `lintegral_Iz_Iθ_ne_top_of_integrable` is the only new bookkeeping: `Integrable`
over the open quadrant `(0,∞) × (0,π/2)` gives the finiteness of the *iterated* `∫⁻` over
`[0,∞) × [0,π/2]` (the two differ by the two boundary lines and the point `z = 0`, all null),
which is the form in which the log-substitution consumes it.
-/

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.LogWeightInt

/-- **Finiteness of the iterated `∫⁻` over `[0,∞) × [0,π/2]` from quadrant integrability.**
If `Function.uncurry Φ` is Bochner-integrable on the open quadrant, then the iterated
`∫⁻ z ∈ [0,∞), ∫⁻ θ ∈ [0,π/2]` of `ofReal (Φ z θ)` is finite: the boundary lines and the
point `z = 0` are null, so this iterated integral is at most the norm integral over the open
quadrant, which is finite by `HasFiniteIntegral`. -/
theorem lintegral_Iz_Iθ_ne_top_of_integrable {Φ : ℝ → ℝ → ℝ}
    (h : MeasureTheory.Integrable (Function.uncurry Φ)
      (MeasureTheory.volume.restrict (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))) :
    (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (Φ z θ)) ≠ ⊤ := by
  -- the closed endpoints carry no mass
  have hIt : ∀ z, (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (Φ z θ))
      = ∫⁻ θ in Set.Ioo 0 (Real.pi / 2), ENNReal.ofReal (Φ z θ) :=
    fun z => MeasureTheory.setLIntegral_congr
      ((MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := 0) (b := Real.pi / 2)).symm)
  have hIz : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (Φ z θ))
      = ∫⁻ z in Set.Ioi 0, ∫⁻ θ in Set.Ioo 0 (Real.pi / 2), ENNReal.ofReal (Φ z θ) := by
    simp only [hIt]
    exact MeasureTheory.setLIntegral_congr
      ((MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0)).symm)
  -- Tonelli on the product of the two restricted measures
  have hmeas : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal ‖Function.uncurry Φ p‖)
      ((MeasureTheory.volume.restrict (Set.Ioi 0)).prod
        (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2)))) := by
    rw [Measure.prod_restrict]
    exact ((h.1.aemeasurable).norm).ennreal_ofReal
  have hfin' := (MeasureTheory.hasFiniteIntegral_iff_norm (Function.uncurry Φ)).mp h.2
  have hfin2 : (∫⁻ p, ENNReal.ofReal ‖Function.uncurry Φ p‖
      ∂((MeasureTheory.volume.restrict (Set.Ioi 0)).prod
        (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))))) < ⊤ := by
    rw [show (MeasureTheory.volume.restrict (Set.Ioi 0)).prod
        (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2)))
        = (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)).restrict
            (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) from
      Measure.prod_restrict (Set.Ioi 0) (Set.Ioo 0 (Real.pi / 2))]
    exact hfin'
  have hprod : (∫⁻ p, ENNReal.ofReal ‖Function.uncurry Φ p‖
      ∂((MeasureTheory.volume.restrict (Set.Ioi 0)).prod
        (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2)))))
      = ∫⁻ z in Set.Ioi 0, ∫⁻ θ in Set.Ioo 0 (Real.pi / 2), ENNReal.ofReal ‖Φ z θ‖ := by
    simpa only [Function.uncurry_apply_pair] using
      (MeasureTheory.lintegral_prod (fun p : ℝ × ℝ => ENNReal.ofReal ‖Function.uncurry Φ p‖) hmeas)
  -- `ofReal` is monotone and `Φ ≤ ‖Φ‖`
  have hpt : ∀ z θ, ENNReal.ofReal (Φ z θ) ≤ ENNReal.ofReal ‖Φ z θ‖ :=
    fun z θ => ENNReal.ofReal_le_ofReal (by rw [Real.norm_eq_abs]; exact le_abs_self _)
  have hmono : (∫⁻ z in Set.Ioi 0, ∫⁻ θ in Set.Ioo 0 (Real.pi / 2), ENNReal.ofReal (Φ z θ))
      ≤ ∫⁻ z in Set.Ioi 0, ∫⁻ θ in Set.Ioo 0 (Real.pi / 2), ENNReal.ofReal ‖Φ z θ‖ :=
    MeasureTheory.lintegral_mono fun z => MeasureTheory.lintegral_mono fun θ => hpt z θ
  have hlt : (∫⁻ z in Set.Ioi 0, ∫⁻ θ in Set.Ioo 0 (Real.pi / 2),
      ENNReal.ofReal ‖Φ z θ‖) < ⊤ := by
    rw [← hprod]
    exact hfin2
  rw [hIz]
  exact ne_top_of_lt (lt_of_le_of_lt hmono hlt)

theorem logW_mul_sq_facts {w : ℝ → ℝ → ℝ} {F : ℝ → ℝ → ℝ}
    (hw0 : ∀ y : ℝ × ℝ, 0 ≤ Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y)
    (hwm : Measurable (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w))
    (hFm : AEMeasurable (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull F) MeasureTheory.volume)
    (hF : MeasureTheory.Integrable
      (Function.uncurry (fun z θ => w z θ * F z θ ^ 2))
      (MeasureTheory.volume.restrict Work.FTS.StrongEps.Quad)) :
    MeasureTheory.Integrable
        (fun y : ℝ × ℝ => Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
          * (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull F y) ^ 2)
      ∧ (∫ y : ℝ × ℝ, Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
          * (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull F y) ^ 2)
        = Work.Coercivity.wip w F F := by
  -- log-side integrability, from the finiteness of the quadrant `∫⁻` of `w F²`
  have hfin : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
      ENNReal.ofReal (w z θ * F z θ ^ 2)) ≠ ⊤ :=
    lintegral_Iz_Iθ_ne_top_of_integrable hF
  have hI : MeasureTheory.Integrable (fun y : ℝ × ℝ =>
      Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
        * (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull F y) ^ 2) :=
    Work.FTS.StrongEps.E4R3.Apriori4Proofs.JT.integrable_logW_sq_of_lintegral hw0 hwm hFm hfin
  refine ⟨hI, ?_⟩
  -- Fubini: the plane integral is the iterated integral in the log coordinates
  have hfub := MeasureTheory.integral_prod (fun y : ℝ × ℝ =>
      Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
        * (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull F y) ^ 2) hI
  -- the quadrant side, substituted into the log coordinates
  have hquad : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, w z θ * F z θ ^ 2)
      = ∫ s, ∫ ζ, Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w (s, ζ)
          * (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull F (s, ζ)) ^ 2 := by
    rw [Work.FTS.CoercivityStep.Base.wip_eq_Ioi_Ioo (fun z θ => w z θ * F z θ ^ 2)]
    rw [Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.integral_quad_log_subst hF]
    refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun s => ?_)
    refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun ζ => ?_)
    simp only [Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW_apply,
      Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull_apply]
    ring
  -- `wip` with the weight in front
  have hwip : Work.Coercivity.wip w F F
      = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, w z θ * F z θ ^ 2 := by
    rw [Work.Coercivity.wip]
    refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun z => ?_)
    refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun θ => ?_)
    ring
  exact hfub.trans (hquad.symm.trans hwip.symm)

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.LogWeightInt
end
end
