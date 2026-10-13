import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllipticEst.AeCrux.AeVLib.Meas
import Submission.Work.FTS.EllipticEst.AeCrux.AeVLib.Slots
import Submission.Work.FTS.EllipticEst.AeCrux.AeVLib.Pullback

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

/-! ## 9. The reverse transfer -/

theorem lintegral_box_exp_rev {F : ℝ → ℝ → ℝ≥0∞}
    (hAE : AEMeasurable (fun p : ℝ × ℝ => F p.1 p.2)
      ((volume : Measure ℝ).restrict (Set.Ioi 0) |>.prod (volume.restrict Iθ)))
    (hAE₂ : AEMeasurable (fun q : ℝ × ℝ => ENNReal.ofReal (Real.exp q.1) * F (Real.exp q.1) q.2)
      (MeasureTheory.Measure.prod (volume : Measure ℝ) (volume.restrict Iθ)))
    {G : ℝ × ℝ → ℝ≥0∞}
    (hGF : G =ᵐ[MeasureTheory.Measure.prod (volume : Measure ℝ) (volume.restrict Iθ)]
      (fun q : ℝ × ℝ => ENNReal.ofReal (Real.exp q.1) * F (Real.exp q.1) q.2))
    (h : ∫⁻ q in (Set.univ : Set ℝ) ×ˢ Iθ, G q < ⊤) :
    ∫⁻ p, F p.1 p.2 ∂((volume : Measure ℝ).restrict (Set.Ioi 0) |>.prod (volume.restrict Iθ)) < ⊤ := by
  have h' : ∫⁻ q, G q ∂(MeasureTheory.Measure.prod (volume : Measure ℝ)
      (volume.restrict Iθ)) < ⊤ := by
    have hmeas : MeasureTheory.Measure.prod (volume : Measure ℝ) (volume.restrict Iθ)
        = (volume : Measure (ℝ × ℝ)).restrict ((Set.univ : Set ℝ) ×ˢ Iθ) := by
      rw [show (volume : Measure (ℝ × ℝ))
          = MeasureTheory.Measure.prod (volume : Measure ℝ) (volume : Measure ℝ) from
        Measure.volume_eq_prod ℝ ℝ]
      rw [← MeasureTheory.Measure.prod_restrict, Measure.restrict_univ]
    rw [hmeas]
    exact h
  rw [lintegral_box_exp (F := fun z θ => F z θ) hAE hAE₂]
  refine lt_of_eq_of_lt ?_ h'
  exact (lintegral_congr_ae hGF).symm

/-! ## 10. The main theorem -/

theorem mixIntS_integrableOn_Ioi {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (hOm : Work.FTS.EllSol.HeavyFlat.OmHeavy)
    (hAe : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    (hU : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u)) :
    MeasureTheory.IntegrableOn (Work.EllipticEst.Core.mixIntS u) (Set.Ioi (0 : ℝ)) := by
  have hSm : Work.FTS.EllipticEst.SmoothOpen u :=
    Work.FTS.EllipticEst.smoothOpen_of_forall hAe.smooth
  have hU' : Work.Spaces.HkMem α 0 (Work.Spaces.Dz u) := hU
  have hthEta : ∀ θ ∈ Iθ, 0 ≤ Work.FTS.EllipticEst.thEta θ :=
    fun θ hθ => Work.FTS.EllipticEst.thEta_nonneg hθ
  -- ## slot 1 (f = Dz u)
  have hF1nn : ∀ z θ, 0 ≤ Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz u) z θ := by
    intro z θ; rw [HkIntegrand_zero]; exact sq_nonneg _
  have hF1cont : ContinuousOn (fun p : ℝ × ℝ =>
      Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz u) p.1 p.2)
      ((Set.Ioi (0:ℝ)) ×ˢ Set.Ioo 0 (Real.pi / 2)) := hSm.Dz.continuousOn_HkIntegrand α 0
  have hg1 : ContinuousOn (fun p : ℝ × ℝ =>
      Real.exp p.1 * Work.Spaces.pz u (Real.exp p.1) p.2)
      ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    ((Real.continuous_exp.comp continuous_fst).continuousOn
        (s := (Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2))).mul
      (contOn_expComp hSm.pz.continuousOn)
  have hidg1 : ∀ t θ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      (Work.Spaces.pz (pb u) t θ) ^ 2 * Work.FTS.EllSol.HeavyFlat.omw t
          * Work.FTS.EllipticEst.sEta θ
        = (Real.exp t * Work.Spaces.pz u (Real.exp t) θ) ^ 2
          * Work.FTS.EllSol.HeavyFlat.omw t * Work.FTS.EllipticEst.sEta θ := by
    intro t θ hθ; rw [pb_pz hSm hθ]
  have hid1 : ∀ t θ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      (Work.Spaces.pz (pb u) t θ) ^ 2 * Work.FTS.EllSol.HeavyFlat.omw t
          * Work.FTS.EllipticEst.sEta θ
        = Real.exp t * Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz u) (Real.exp t) θ := by
    intro t θ hθ
    have hIθ : θ ∈ Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    rw [pb_pz hSm hθ, HkIntegrand_zero_eq α (Work.Spaces.Dz u) hIθ,
      Work.FTS.EllSol.HeavyFlat.omw_eq_w_sq_mul,
      show Work.Spaces.Dz u (Real.exp t) θ
        = Real.exp t * Work.Spaces.pz u (Real.exp t) θ from rfl]
    ring
  have hslot1 : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
      (Work.Spaces.pz (pb u) p.1 p.2) ^ 2 * Work.FTS.EllSol.HeavyFlat.omw p.1
        * Work.FTS.EllipticEst.sEta p.2) ((Set.univ : Set ℝ) ×ˢ Iθ) :=
    slot_integrableOn
      (F := fun z θ => Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz u) z θ)
      (Φ := fun t θ => (Work.Spaces.pz (pb u) t θ) ^ 2 * Work.FTS.EllSol.HeavyFlat.omw t
        * Work.FTS.EllipticEst.sEta θ)
      hF1nn (Phi_nonneg hidg1) hid1 hF1cont (continuousOn_Phi hg1 hidg1) hU'.1 hU'.2
  -- ## slot 3 (f = pthIter 2 u)
  have hF3nn : ∀ z θ, 0 ≤ Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 u) z θ := by
    intro z θ; rw [HkIntegrand_zero]; exact sq_nonneg _
  have hF3cont : ContinuousOn (fun p : ℝ × ℝ =>
      Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 u) p.1 p.2)
      ((Set.Ioi (0:ℝ)) ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    (hSm.pth.pth).continuousOn_HkIntegrand α 0
  have hg3 : ContinuousOn (fun p : ℝ × ℝ =>
      Work.Spaces.pthIter 2 u (Real.exp p.1) p.2)
      ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    contOn_expComp (hSm.pth.pth).continuousOn
  have hidg3 : ∀ t θ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      (Work.Spaces.pthIter 2 (pb u) t θ) ^ 2 * Work.FTS.EllSol.HeavyFlat.omw t
          * Work.FTS.EllipticEst.sEta θ
        = (Work.Spaces.pthIter 2 u (Real.exp t) θ) ^ 2
          * Work.FTS.EllSol.HeavyFlat.omw t * Work.FTS.EllipticEst.sEta θ := by
    intro t θ hθ; rw [pb_pthIter]
  have hid3 : ∀ t θ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      (Work.Spaces.pthIter 2 (pb u) t θ) ^ 2 * Work.FTS.EllSol.HeavyFlat.omw t
          * Work.FTS.EllipticEst.sEta θ
        = Real.exp t * Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 u) (Real.exp t) θ := by
    intro t θ hθ
    have hIθ : θ ∈ Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    rw [pb_pthIter, HkIntegrand_zero_eq α (Work.Spaces.pthIter 2 u) hIθ,
      Work.FTS.EllSol.HeavyFlat.omw_eq_w_sq_mul]
    ring
  have hslot3 : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
      (Work.Spaces.pthIter 2 (pb u) p.1 p.2) ^ 2 * Work.FTS.EllSol.HeavyFlat.omw p.1
        * Work.FTS.EllipticEst.sEta p.2) ((Set.univ : Set ℝ) ×ˢ Iθ) :=
    slot_integrableOn
      (F := fun z θ => Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 u) z θ)
      (Φ := fun t θ => (Work.Spaces.pthIter 2 (pb u) t θ) ^ 2 * Work.FTS.EllSol.HeavyFlat.omw t
        * Work.FTS.EllipticEst.sEta θ)
      hF3nn (Phi_nonneg hidg3) hid3 hF3cont (continuousOn_Phi hg3 hidg3)
      hAe.memAng2.1 hAe.memAng2.2
  -- ## slot 2 (f = Dz (Dz u))
  have hF2nn : ∀ z θ, 0 ≤ Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz (Work.Spaces.Dz u)) z θ := by
    intro z θ; rw [HkIntegrand_zero]; exact sq_nonneg _
  have hdom2 : ∀ z θ, θ ∈ Set.Ioo 0 (Real.pi / 2) → 0 < z →
      Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz (Work.Spaces.Dz u)) z θ
        ≤ 2 * Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz u) z θ
          + 2 * Work.Spaces.HkIntegrand α 0
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) z θ := by
    intro z θ hθ hz
    rw [HkIntegrand_zero, HkIntegrand_zero, HkIntegrand_zero]
    rw [show Work.Spaces.Dz (Work.Spaces.Dz u) z θ
        = Work.Spaces.Dz u z θ + z ^ 2 * Work.Spaces.pzIter 2 u z θ from pb_DzDz hSm hz hθ]
    nlinarith [sq_nonneg (Work.Spaces.Dz u z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
      - z ^ 2 * Work.Spaces.pzIter 2 u z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))]
  have hslices2 : ∀ z ∈ Work.Spaces.Iz, Integrable (fun θ =>
      Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz (Work.Spaces.Dz u)) z θ)
      (MeasureTheory.volume.restrict Iθ) := by
    intro z hz
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with h0 | hpos
    · rw [← h0]
      simp only [Work.Spaces.HkIntegrand_zero_z, Pi.zero_apply]
      exact MeasureTheory.integrable_zero ℝ ℝ _
    · refine MeasureTheory.Integrable.mono'
        (f := fun θ => Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz (Work.Spaces.Dz u)) z θ)
        (g := fun θ => 2 * Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz u) z θ
          + 2 * Work.Spaces.HkIntegrand α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) z θ)
        ?_ ?_ ?_
      · exact (hU'.1 z hz).const_mul 2 |>.add ((hAe.memRad2.1 z hz).const_mul 2)
      · exact Work.Spaces.aesm_slice_of_continuousOn_Qd _
          ((hSm.Dz.Dz).continuousOn_HkIntegrand α 0) hpos
      · filter_upwards [ae_Iθ_Ioo] with θ hθIoo
        rw [Real.norm_of_nonneg (hF2nn z θ)]
        exact hdom2 z θ hθIoo hpos
  have houter2 : Integrable (fun z => ∫ θ,
      Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz (Work.Spaces.Dz u)) z θ
        ∂(MeasureTheory.volume.restrict Iθ)) (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have hg : Integrable (fun z => ∫ θ, (2 * Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz u) z θ
        + 2 * Work.Spaces.HkIntegrand α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) z θ)
        ∂(MeasureTheory.volume.restrict Iθ)) (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
      refine ((hU'.2.const_mul 2).add (hAe.memRad2.2.const_mul 2)).congr ?_
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz => ?_
      show 2 * (∫ θ, Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz u) z θ
            ∂(MeasureTheory.volume.restrict Iθ))
          + 2 * (∫ θ, Work.Spaces.HkIntegrand α 0
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) z θ
            ∂(MeasureTheory.volume.restrict Iθ))
          = ∫ θ, (2 * Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz u) z θ
              + 2 * Work.Spaces.HkIntegrand α 0
                  (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) z θ)
            ∂(MeasureTheory.volume.restrict Iθ)
      rw [MeasureTheory.integral_add ((hU'.1 z hz).const_mul 2)
          ((hAe.memRad2.1 z hz).const_mul 2),
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    refine MeasureTheory.Integrable.mono'
      (f := fun z => ∫ θ, Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz (Work.Spaces.Dz u)) z θ
        ∂(MeasureTheory.volume.restrict Iθ))
      (g := fun z => ∫ θ, (2 * Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz u) z θ
        + 2 * Work.Spaces.HkIntegrand α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) z θ)
        ∂(MeasureTheory.volume.restrict Iθ)) ?_ ?_ ?_
    · exact hg
    · exact (Work.Spaces.aesm_of_continuousOn_Qd _
        ((hSm.Dz.Dz).continuousOn_HkIntegrand α 0)).integral_prod_right'
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz => ?_
      rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with h0 | hpos
      · rw [← h0]
        simp only [Work.Spaces.HkIntegrand_zero_z]
        simp
      · rw [Real.norm_of_nonneg (MeasureTheory.integral_nonneg_of_ae ?_)]
        swap
        · filter_upwards with θ
          exact hF2nn z θ
        refine MeasureTheory.integral_mono_of_nonneg
          (μ := MeasureTheory.volume.restrict Iθ)
          (f := fun θ => Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz (Work.Spaces.Dz u)) z θ)
          (g := fun θ => 2 * Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz u) z θ
            + 2 * Work.Spaces.HkIntegrand α 0
                (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) z θ) ?_ ?_ ?_
        · filter_upwards with θ; exact hF2nn z θ
        · exact (hU'.1 z hz).const_mul 2 |>.add ((hAe.memRad2.1 z hz).const_mul 2)
        · filter_upwards [ae_Iθ_Ioo] with θ hθIoo
          exact hdom2 z θ hθIoo hpos
  have hg2 : ContinuousOn (fun p : ℝ × ℝ =>
      Work.Spaces.Dz (Work.Spaces.Dz u) (Real.exp p.1) p.2)
      ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    contOn_expComp (hSm.Dz.Dz).continuousOn
  have hidg2 : ∀ t θ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      (Work.Spaces.pz (Work.Spaces.pz (pb u)) t θ) ^ 2 * Work.FTS.EllSol.HeavyFlat.omw t
          * Work.FTS.EllipticEst.sEta θ
        = (Work.Spaces.Dz (Work.Spaces.Dz u) (Real.exp t) θ) ^ 2
          * Work.FTS.EllSol.HeavyFlat.omw t * Work.FTS.EllipticEst.sEta θ := by
    intro t θ hθ; rw [pb_pz2 hSm hθ]
  have hid2 : ∀ t θ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      (Work.Spaces.pz (Work.Spaces.pz (pb u)) t θ) ^ 2 * Work.FTS.EllSol.HeavyFlat.omw t
          * Work.FTS.EllipticEst.sEta θ
        = Real.exp t * Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz (Work.Spaces.Dz u))
            (Real.exp t) θ := by
    intro t θ hθ
    have hIθ : θ ∈ Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    rw [pb_pz2 hSm hθ, HkIntegrand_zero_eq α (Work.Spaces.Dz (Work.Spaces.Dz u)) hIθ,
      Work.FTS.EllSol.HeavyFlat.omw_eq_w_sq_mul,
      show Work.Spaces.Dz (Work.Spaces.Dz u) (Real.exp t) θ
        = Real.exp t * Work.Spaces.pz (Work.Spaces.Dz u) (Real.exp t) θ from rfl]
    ring
  have hslot2 : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
      (Work.Spaces.pz (Work.Spaces.pz (pb u)) p.1 p.2) ^ 2 * Work.FTS.EllSol.HeavyFlat.omw p.1
        * Work.FTS.EllipticEst.sEta p.2) ((Set.univ : Set ℝ) ×ˢ Iθ) :=
    slot_integrableOn
      (F := fun z θ => Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz (Work.Spaces.Dz u)) z θ)
      (Φ := fun t θ => (Work.Spaces.pz (Work.Spaces.pz (pb u)) t θ) ^ 2
        * Work.FTS.EllSol.HeavyFlat.omw t * Work.FTS.EllipticEst.sEta θ)
      hF2nn (Phi_nonneg hidg2) hid2 ((hSm.Dz.Dz).continuousOn_HkIntegrand α 0)
      (continuousOn_Phi hg2 hidg2) hslices2 houter2
  -- ## the interface
  have hconcl := hOm (pb u) (pb_contDiff hAe.smooth 2)
    (fun t => hAe.dirZero (Real.exp t)) (fun t => hAe.dirPi (Real.exp t))
    hslot1 hslot2 hslot3
  -- ## the reverse transfer
  have hGcont : ContinuousOn (fun p : ℝ × ℝ =>
      Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz (Work.Spaces.pth u)) (Real.exp p.1) p.2)
      ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    contOn_expComp ((hSm.pth.Dz).continuousOn_HkIntegrand α 0)
  have hidM : ∀ t θ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      (Work.Spaces.pth (Work.Spaces.pz (pb u)) t θ) ^ 2 * Work.FTS.EllSol.HeavyFlat.omw t
          * Work.FTS.EllipticEst.sEta θ
        = Real.exp t * Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz (Work.Spaces.pth u))
            (Real.exp t) θ := by
    intro t θ hθ
    have hIθ : θ ∈ Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    rw [pb_pth_pz hSm hθ, HkIntegrand_zero_eq α (Work.Spaces.Dz (Work.Spaces.pth u)) hIθ,
      Work.FTS.EllSol.HeavyFlat.omw_eq_w_sq_mul,
      show Work.Spaces.Dz (Work.Spaces.pth u) (Real.exp t) θ
        = Real.exp t * Work.Spaces.pz (Work.Spaces.pth u) (Real.exp t) θ from rfl]
    ring
  have hGF : (fun q : ℝ × ℝ => ENNReal.ofReal
        ((Work.Spaces.pth (Work.Spaces.pz (pb u)) q.1 q.2) ^ 2 * Work.FTS.EllSol.HeavyFlat.omw q.1
          * Work.FTS.EllipticEst.sEta q.2))
      =ᵐ[MeasureTheory.Measure.prod (volume : Measure ℝ) (MeasureTheory.volume.restrict Iθ)]
      (fun q : ℝ × ℝ => ENNReal.ofReal (Real.exp q.1)
        * ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz (Work.Spaces.pth u))
            (Real.exp q.1) q.2)) := by
    filter_upwards [ae_strip_of hidM] with q hq
    rw [hq, ENNReal.ofReal_mul (le_of_lt (Real.exp_pos q.1))]
  have hAEz : AEMeasurable (fun p : ℝ × ℝ =>
      ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz (Work.Spaces.pth u)) p.1 p.2))
      ((volume : Measure ℝ).restrict (Set.Ioi 0) |>.prod (MeasureTheory.volume.restrict Iθ)) := by
    have h := Work.Spaces.aesm_of_continuousOn_Qd
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz (Work.Spaces.pth u)) p.1 p.2)
      ((hSm.pth.Dz).continuousOn_HkIntegrand α 0)
    rw [show (MeasureTheory.volume : Measure ℝ).restrict Work.Spaces.Iz
        = MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) from
      MeasureTheory.Measure.restrict_congr_set
        (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0)).symm] at h
    exact (ENNReal.measurable_ofReal.comp_aemeasurable h.aemeasurable)
  have hAEt : AEMeasurable (fun q : ℝ × ℝ => ENNReal.ofReal (Real.exp q.1)
      * ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz (Work.Spaces.pth u))
          (Real.exp q.1) q.2))
      (MeasureTheory.Measure.prod (volume : Measure ℝ) (MeasureTheory.volume.restrict Iθ)) := by
    refine (ENNReal.measurable_ofReal.comp_aemeasurable
      ((Real.measurable_exp.comp measurable_fst).aemeasurable)).mul ?_
    exact ENNReal.measurable_ofReal.comp_aemeasurable
      ((aesm_prod_univ_Iθ (f := fun t θ => Work.Spaces.HkIntegrand α 0
        (Work.Spaces.Dz (Work.Spaces.pth u)) (Real.exp t) θ) hGcont).aemeasurable)
  have hAEt' : AEMeasurable (fun q : ℝ × ℝ => ENNReal.ofReal (Real.exp q.1
      * Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz (Work.Spaces.pth u)) (Real.exp q.1) q.2))
      (MeasureTheory.Measure.prod (volume : Measure ℝ) (MeasureTheory.volume.restrict Iθ)) := by
    refine hAEt.congr ?_
    filter_upwards with q
    rw [ENNReal.ofReal_mul (le_of_lt (Real.exp_pos q.1))]
  have hfinT := lintegral_box_exp_rev (F := fun z θ =>
      ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz (Work.Spaces.pth u)) z θ))
    hAEz hAEt hGF hconcl
  -- ## conclude
  have hJnn : ∀ z, 0 ≤ ∫ θ in Iθ, (Work.Spaces.Dz (Work.Spaces.pth u) z θ) ^ 2
      * Work.FTS.EllipticEst.thEta θ := by
    intro z
    refine MeasureTheory.integral_nonneg_of_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
      (fun θ hθ => hθ)] with θ hθ
    exact mul_nonneg (sq_nonneg _) (hthEta θ hθ)
  have hcmp : ∀ z, ENNReal.ofReal (Work.EllipticEst.Core.mixIntS u z)
      ≤ ∫⁻ θ, ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz (Work.Spaces.pth u)) z θ)
          ∂(MeasureTheory.volume.restrict Iθ) := by
    intro z
    have hΦnn : ∀ θ ∈ Iθ, 0 ≤ (Work.Spaces.Dz (Work.Spaces.pth u) z θ) ^ 2
        * Work.FTS.EllipticEst.thEta θ := fun θ hθ => mul_nonneg (sq_nonneg _) (hthEta θ hθ)
    have h1 : ENNReal.ofReal (Work.EllipticEst.Core.mixIntS u z)
        = ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
          * ENNReal.ofReal (∫ θ in Iθ, (Work.Spaces.Dz (Work.Spaces.pth u) z θ) ^ 2
              * Work.FTS.EllipticEst.thEta θ) := by
      rw [Work.EllipticEst.Core.mixIntS, ENNReal.ofReal_mul (sq_nonneg (Work.Spaces.w z))]
    have h2 : ENNReal.ofReal (∫ θ in Iθ, (Work.Spaces.Dz (Work.Spaces.pth u) z θ) ^ 2
          * Work.FTS.EllipticEst.thEta θ)
        ≤ ∫⁻ θ, ENNReal.ofReal ((Work.Spaces.Dz (Work.Spaces.pth u) z θ) ^ 2
            * Work.FTS.EllipticEst.thEta θ) ∂(MeasureTheory.volume.restrict Iθ) := by
      by_cases h : MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.Dz (Work.Spaces.pth u) z θ) ^ 2
          * Work.FTS.EllipticEst.thEta θ) Iθ
      · rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal h
          (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc hΦnn)]
      · rw [MeasureTheory.integral_undef h, ENNReal.ofReal_zero]
        exact bot_le
    have h3 : ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
          * (∫⁻ θ, ENNReal.ofReal ((Work.Spaces.Dz (Work.Spaces.pth u) z θ) ^ 2
              * Work.FTS.EllipticEst.thEta θ) ∂(MeasureTheory.volume.restrict Iθ))
        = ∫⁻ θ, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
            * ENNReal.ofReal ((Work.Spaces.Dz (Work.Spaces.pth u) z θ) ^ 2
              * Work.FTS.EllipticEst.thEta θ) ∂(MeasureTheory.volume.restrict Iθ) :=
      (MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
    rw [h1]
    refine le_trans (mul_le_mul (le_refl _) h2 zero_le zero_le) (le_of_eq ?_)
    rw [h3]
    refine lintegral_congr_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
      (fun θ hθ => hθ)] with θ hθ
    rw [HkIntegrand_zero_eq α (Work.Spaces.Dz (Work.Spaces.pth u)) hθ]
    rw [show (Work.Spaces.Dz (Work.Spaces.pth u) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.sEta θ
        = (Work.Spaces.w z) ^ 2 * ((Work.Spaces.Dz (Work.Spaces.pth u) z θ) ^ 2
          * Work.FTS.EllipticEst.thEta θ) from by
      rw [show Work.FTS.EllipticEst.sEta = Work.FTS.EllipticEst.thEta from rfl]
      ring]
    rw [ENNReal.ofReal_mul (sq_nonneg (Work.Spaces.w z))]
  have hfinz : ∫⁻ z, ENNReal.ofReal (Work.EllipticEst.Core.mixIntS u z)
      ∂(MeasureTheory.volume.restrict (Set.Ioi 0)) < ⊤ := by
    refine lt_of_le_of_lt (MeasureTheory.lintegral_mono hcmp) ?_
    rw [show (∫⁻ z, (∫⁻ θ, ENNReal.ofReal (Work.Spaces.HkIntegrand α 0
          (Work.Spaces.Dz (Work.Spaces.pth u)) z θ) ∂(MeasureTheory.volume.restrict Iθ))
        ∂(MeasureTheory.volume.restrict (Set.Ioi 0)))
        = ∫⁻ p, ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz (Work.Spaces.pth u))
            p.1 p.2) ∂((MeasureTheory.volume : Measure ℝ).restrict (Set.Ioi 0)
              |>.prod (MeasureTheory.volume.restrict Iθ)) from
      (MeasureTheory.lintegral_prod _ hAEz).symm]
    exact hfinT
  -- ## integrability
  have hAESM : AEStronglyMeasurable (Work.EllipticEst.Core.mixIntS u)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
    have hjoint : AEStronglyMeasurable (fun p : ℝ × ℝ =>
        (Work.Spaces.Dz (Work.Spaces.pth u) p.1 p.2) ^ 2 * Work.FTS.EllipticEst.thEta p.2)
        ((MeasureTheory.volume : Measure ℝ).restrict (Set.Ioi 0)
          |>.prod (MeasureTheory.volume.restrict Iθ)) := by
      have hsinpos : ∀ p ∈ ((Set.Ioi (0:ℝ)) ×ˢ Set.Ioo 0 (Real.pi / 2)),
          0 < Real.sin (2 * p.2) := by
        intro p hp
        exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.2.1])
          (by linarith [hp.2.2, Real.pi_pos])
      have hcont : ContinuousOn (fun p : ℝ × ℝ =>
          (Work.Spaces.Dz (Work.Spaces.pth u) p.1 p.2) ^ 2 * Work.FTS.EllipticEst.thEta p.2)
          ((Set.Ioi (0:ℝ)) ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
        refine ((hSm.pth.Dz).continuousOn.pow 2).mul ?_
        have hfun : (fun p : ℝ × ℝ => Work.FTS.EllipticEst.thEta p.2)
            = fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)) := by
          funext p; rfl
        rw [hfun]
        exact ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
          (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))
      have h := Work.Spaces.aesm_of_continuousOn_Qd _ hcont
      rwa [show (MeasureTheory.volume : Measure ℝ).restrict Work.Spaces.Iz
          = MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) from
        MeasureTheory.Measure.restrict_congr_set
          (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0)).symm] at h
    have h1 := hjoint.integral_prod_right'
    have h2 : AEStronglyMeasurable (fun z : ℝ => (Work.Spaces.w z) ^ 2)
        (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
      refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
      have hfun : (fun z : ℝ => (Work.Spaces.w z) ^ 2)
          = fun z : ℝ => ((1 + z) ^ 2 / z ^ 2) ^ 2 := by funext z; rfl
      rw [hfun]
      exact (((continuousOn_const.add continuousOn_id).pow 2).div (continuousOn_id.pow 2)
        (fun z hz => pow_ne_zero 2 (ne_of_gt hz))).pow 2
    have hfun : ((fun z : ℝ => (Work.Spaces.w z) ^ 2) * (fun x : ℝ => ∫ y in Iθ,
        Work.Spaces.Dz (Work.Spaces.pth u) x y ^ 2 * Work.FTS.EllipticEst.thEta y))
        = Work.EllipticEst.Core.mixIntS u := by
      funext z
      simp only [Pi.mul_apply, Work.EllipticEst.Core.mixIntS]
    simpa only [hfun] using h2.mul h1
  rw [MeasureTheory.IntegrableOn]
  refine ⟨hAESM, ?_⟩
  refine lt_of_le_of_lt (MeasureTheory.lintegral_mono fun z => ?_) hfinz
  rw [Real.enorm_eq_ofReal (by
    rw [Work.EllipticEst.Core.mixIntS]
    exact mul_nonneg (sq_nonneg _) (hJnn z))]


end Work.FTS.EllipticEst.AeCrux
