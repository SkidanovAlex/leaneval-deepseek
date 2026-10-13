import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Defs
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.LogInt
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.integral_quad_log_subst
import Submission.Work.FTS.StrongEps.HkSqAux.lintegral_quad_log_subst
import Submission.Work.FTS.CoercivityStep.Base.H1IP_congr_qd
import Submission.Work.Coercivity.Defs
import Submission.Work.FTS.StrongEps.Basic

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
