import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.AeCrux.AeVLib.Meas

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open MeasureTheory Set Filter
open scoped Real Topology ENNReal

namespace Work.FTS.EllipticEst.AeCrux

local notation "Iθ" => Work.Spaces.Iθ
local notation "Iz" => Work.Spaces.Iz

set_option linter.unusedSimpArgs false

/-! ## 6. Continuity of the slot integrands

(The two lemmas `continuousOn_slot` and `continuousOn_slotT` live in `AeVLib.Meas`, which this
module imports; they were duplicated here by the module split.) -/

/-! ## 5. A slot transfer -/

theorem ae_strip_mem :
    ∀ᵐ q ∂(MeasureTheory.Measure.prod (volume : Measure ℝ) (volume.restrict Iθ)),
      q.2 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
  have hI : ∀ᵐ θ ∂(volume : Measure ℝ).restrict Iθ, θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    rw [Work.Spaces.Iθ]
    rw [← MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := Real.pi / 2))]
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => hθ)
  rw [MeasureTheory.Measure.ae_prod_iff_ae_ae (p := fun q : ℝ × ℝ => q.2 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2))
    (measurableSet_Ioo.preimage measurable_snd)]
  exact Filter.Eventually.of_forall fun _ => hI

/-- A pointwise inequality on the open strip gives an a.e. statement on the product. -/
theorem ae_strip_of {p : ℝ → ℝ → Prop} (hp : ∀ t θ, θ ∈ Set.Ioo 0 (Real.pi / 2) → p t θ) :
    ∀ᵐ q ∂(MeasureTheory.Measure.prod (volume : Measure ℝ) (volume.restrict Iθ)), p q.1 q.2 := by
  filter_upwards [ae_strip_mem] with q hq
  exact hp q.1 q.2 hq

theorem ae_Iθ_Ioo : ∀ᵐ θ ∂(volume : Measure ℝ).restrict Iθ, θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
  rw [Work.Spaces.Iθ]
  rw [← MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := Real.pi / 2))]
  exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => hθ)

theorem ae_Iθ_Ioo_aux :
    ∀ᵐ q ∂(MeasureTheory.Measure.prod (volume : Measure ℝ) (volume.restrict Iθ)), q.2 ∈ Iθ := by
  rw [MeasureTheory.Measure.ae_prod_iff_ae_ae (p := fun q : ℝ × ℝ => q.2 ∈ Iθ)
    (measurableSet_Icc.preimage measurable_snd)]
  exact Filter.Eventually.of_forall fun _ =>
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => hθ)


/-! ## 5. Slot transfers -/

/-- A pointwise inequality on the open strip gives an a.e. statement on the product. -/
theorem continuousOn_Phi {g Φ : ℝ → ℝ → ℝ}
    (hg : ContinuousOn (fun p : ℝ × ℝ => g p.1 p.2)
      ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hid : ∀ t θ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      Φ t θ = g t θ ^ 2 * Work.FTS.EllSol.HeavyFlat.omw t * Work.FTS.EllipticEst.sEta θ) :
    ContinuousOn (Function.uncurry Φ) ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
  have h := continuousOn_slotT hg
  refine (continuousOn_congr ?_).mpr h
  intro p hp
  show Φ p.1 p.2 = g p.1 p.2 ^ 2 * Work.FTS.EllSol.HeavyFlat.omw p.1 * Work.FTS.EllipticEst.sEta p.2
  exact hid p.1 p.2 hp.2

theorem Phi_nonneg {g Φ : ℝ → ℝ → ℝ}
    (hid : ∀ t θ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      Φ t θ = g t θ ^ 2 * Work.FTS.EllSol.HeavyFlat.omw t * Work.FTS.EllipticEst.sEta θ) :
    ∀ t θ, θ ∈ Set.Ioo 0 (Real.pi / 2) → 0 ≤ Φ t θ := by
  intro t θ hθ
  rw [hid t θ hθ]
  refine mul_nonneg (mul_nonneg (sq_nonneg _) ?_) ?_
  · rw [Work.FTS.EllSol.HeavyFlat.omw]
    positivity
  · exact le_of_lt (Real.rpow_pos_of_pos
      (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])) _)

theorem thEta_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Iθ) : 0 ≤ Work.FTS.EllipticEst.thEta θ :=
  Work.FTS.EllipticEst.thEta_nonneg hθ

theorem slot_integrableOn {F Φ : ℝ → ℝ → ℝ}
    (hFnn : ∀ z θ, 0 ≤ F z θ)
    (hΦnn : ∀ t θ, θ ∈ Set.Ioo 0 (Real.pi / 2) → 0 ≤ Φ t θ)
    (hid : ∀ t θ, θ ∈ Set.Ioo 0 (Real.pi / 2) → Φ t θ = Real.exp t * F (Real.exp t) θ)
    (hFcont : ContinuousOn (Function.uncurry F) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hΦcont : ContinuousOn (Function.uncurry Φ) ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hslices : ∀ z ∈ Iz, Integrable (fun θ => F z θ) (volume.restrict Iθ))
    (houter : Integrable (fun z => ∫ θ, F z θ ∂(volume.restrict Iθ)) (volume.restrict Iz)) :
    IntegrableOn (Function.uncurry Φ) ((Set.univ : Set ℝ) ×ˢ Iθ) := by
  have hIz : (volume : Measure ℝ).restrict Iz = volume.restrict (Set.Ioi (0 : ℝ)) :=
    MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0)).symm
  have hAEF : AEStronglyMeasurable (Function.uncurry F)
      ((volume : Measure ℝ).restrict Iz |>.prod (volume.restrict Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ hFcont
  have hslice_ae : ∀ᵐ z ∂((volume : Measure ℝ).restrict Iz),
      Integrable (fun θ => F z θ) (volume.restrict Iθ) :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici
      (fun z hz => hslices z hz)
  obtain ⟨hFint, _⟩ := Work.Spaces.integrable_prod_of_iterated
    (μ := (volume : Measure ℝ).restrict Iz) (ν := volume.restrict Iθ)
    hFnn hAEF hslice_ae houter
  have hfinF : ∫⁻ p, ENNReal.ofReal (F p.1 p.2)
      ∂((volume : Measure ℝ).restrict Iz |>.prod (volume.restrict Iθ)) < ⊤ := by
    refine lt_of_eq_of_lt ?_ hFint.hasFiniteIntegral
    refine lintegral_congr fun p => ?_
    show ENNReal.ofReal (F p.1 p.2) = ‖F p.1 p.2‖ₑ
    rw [Real.enorm_eq_ofReal (hFnn p.1 p.2)]
  have hfinF' : ∫⁻ p, ENNReal.ofReal (F p.1 p.2)
      ∂((volume : Measure ℝ).restrict (Set.Ioi 0) |>.prod (volume.restrict Iθ)) < ⊤ := by
    rw [← hIz]
    exact hfinF
  have hGcont : ContinuousOn (Function.uncurry (fun t θ => F (Real.exp t) θ))
      ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    have hφ : Continuous (fun p : ℝ × ℝ => (Real.exp p.1, p.2)) := by fun_prop
    have hmap : Set.MapsTo (fun p : ℝ × ℝ => (Real.exp p.1, p.2))
        ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
      fun p hp => ⟨Real.exp_pos p.1, hp.2⟩
    exact hFcont.comp (hφ.continuousOn (s := (Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2))) hmap
  have hAE1 : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal (F p.1 p.2))
      ((volume : Measure ℝ).restrict (Set.Ioi 0) |>.prod (volume.restrict Iθ)) := by
    rw [← hIz]
    exact ENNReal.measurable_ofReal.comp_aemeasurable hAEF.aemeasurable
  have hAE2 : AEMeasurable (fun q : ℝ × ℝ =>
      ENNReal.ofReal (Real.exp q.1) * ENNReal.ofReal (F (Real.exp q.1) q.2))
      (MeasureTheory.Measure.prod (volume : Measure ℝ) (volume.restrict Iθ)) := by
    have h1 : AEMeasurable (fun q : ℝ × ℝ => ENNReal.ofReal (Real.exp q.1))
        (MeasureTheory.Measure.prod (volume : Measure ℝ) (volume.restrict Iθ)) :=
      ENNReal.measurable_ofReal.comp_aemeasurable
        ((Real.measurable_exp.comp measurable_fst).aemeasurable)
    have h2 : AEMeasurable (fun q : ℝ × ℝ => ENNReal.ofReal (F (Real.exp q.1) q.2))
        (MeasureTheory.Measure.prod (volume : Measure ℝ) (volume.restrict Iθ)) := by
      have h3 := aesm_prod_univ_Iθ (f := fun t θ => F (Real.exp t) θ) hGcont
      exact ENNReal.measurable_ofReal.comp_aemeasurable h3.aemeasurable
    exact h1.mul h2
  have hsub := lintegral_box_exp (F := fun z θ => ENNReal.ofReal (F z θ)) hAE1 hAE2
  rw [hsub] at hfinF'
  have hfinΦ : ∫⁻ q, ENNReal.ofReal (Φ q.1 q.2)
      ∂(MeasureTheory.Measure.prod (volume : Measure ℝ) (volume.restrict Iθ)) < ⊤ := by
    refine lt_of_eq_of_lt ?_ hfinF'
    refine lintegral_congr_ae ?_
    filter_upwards [ae_strip_of (fun t θ hθ => hθ)] with q hq
    rw [hid q.1 q.2 hq, ENNReal.ofReal_mul (le_of_lt (Real.exp_pos q.1))]
  have hAEΦ : AEStronglyMeasurable (fun q : ℝ × ℝ => Φ q.1 q.2)
      (MeasureTheory.Measure.prod (volume : Measure ℝ) (volume.restrict Iθ)) := by
    simpa only [Measure.restrict_univ] using (aesm_prod_univ_Iθ hΦcont)
  change MeasureTheory.Integrable (Function.uncurry Φ)
    ((volume : Measure (ℝ × ℝ)).restrict ((Set.univ : Set ℝ) ×ˢ Iθ))
  rw [show (volume : Measure (ℝ × ℝ)).restrict ((Set.univ : Set ℝ) ×ˢ Iθ)
      = MeasureTheory.Measure.prod (volume : Measure ℝ) (volume.restrict Iθ) from by
    rw [Measure.volume_eq_prod ℝ ℝ, ← MeasureTheory.Measure.prod_restrict,
      Measure.restrict_univ]]
  refine ⟨hAEΦ, ?_⟩
  refine lt_of_eq_of_lt ?_ hfinΦ
  refine lintegral_congr_ae ?_
  filter_upwards [ae_strip_of (fun t θ hθ => hθ)] with q hq
  show ‖Φ q.1 q.2‖ₑ = ENNReal.ofReal (Φ q.1 q.2)
  rw [Real.enorm_eq_ofReal (hΦnn q.1 q.2 hq)]


end Work.FTS.EllipticEst.AeCrux
