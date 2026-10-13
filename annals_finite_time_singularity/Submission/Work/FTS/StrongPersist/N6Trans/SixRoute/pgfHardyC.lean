import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.pgfAux
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.tracePt6
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.slicePtBound
import Submission.Work.FTS.H2.HeasyBlocksId
import Submission.Work.FTS.H2.Defs
import Submission.Work.FTS.TransportS.SupDzAux.HalfLineWindow
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.pgfHardyA
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.pgfHardyB

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# pureGamFamSix — critical-weight slot (C): the product-measure bound
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.SixRoute

set_option autoImplicit false
set_option maxHeartbeats 3200000

/-! ## `z`-marginal facts -/

theorem restrict_Ioi0_eq_Iz :
    MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))
      = MeasureTheory.volume.restrict Work.Spaces.Iz :=
  MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0))

theorem ae_restrict_Iz_pos :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), 0 < z := by
  rw [← restrict_Ioi0_eq_Iz]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioi

theorem int_sig_beta_integrable_Iθ {α : ℝ}
    (hintB : MeasureTheory.IntegrableOn
      (fun θ => (Real.sin (2 * θ)) ^ (α / 10 - 1)) (Set.Ioo (0 : ℝ) (Real.pi / 2))) :
    MeasureTheory.IntegrableOn (fun θ => (Real.sin (2 * θ)) ^ (α / 10 - 1))
      Work.Spaces.Iθ :=
  hintB.congr_set_ae (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := 0)
    (b := Real.pi / 2)).symm

theorem mslot_marginal_canon {α : ℝ} (hα : 0 < α) {g : ℝ → ℝ → ℝ}
    (hgs : Work.FTS.EllipticEst.SmoothOpen g) (hgm : Work.Spaces.HkMem α 6 g)
    (m : ℕ) (hm : 1 + m ≤ 4) :
    MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2
      * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * (Work.Spaces.mixed m 1 g z θ) ^ 2)) Work.Spaces.Iz := by
  have h4 : Work.Spaces.HkMem α 4 g :=
    Work.FTS.OpenPkg.HkMem_mono_open hgs 4 (by norm_num) hgm
  have h := Work.FTS.TransportS.SlotT2.mslot_marginal_integrable (α := α)
    (q := Work.Spaces.gam α) (Work.Spaces.gam_pos hα) le_rfl hgs h4 m 1 (by norm_num) hm
  refine h.congr_fun (fun z _ => ?_) measurableSet_Ici
  simp only []
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ hθ => ?_
  rw [Work.FTS.TransportS.SlotT2.canonW_gam_eq α z θ hθ, Wt_sq_Iθ (gam_ne_zero hα) hθ]
  ring

theorem mixedSlot_marginal_le_HkSq {α : ℝ} (hα : 0 < α) {g : ℝ → ℝ → ℝ}
    (hgm : Work.Spaces.HkMem α 6 g) (m : ℕ) (hm : 1 + m ≤ 6) :
    (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
      * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * (Work.Spaces.mixed m 1 g z θ) ^ 2)) ≤ Work.Spaces.HkSq α 6 g := by
  have h := Work.Spaces.L2Sq_mixed_le_HkSq α 6 g hgm 1 m le_rfl hm
  rw [Work.Spaces.L2Sq] at h
  refine le_of_eq_of_le ?_ h
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only []
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ hθ => ?_
  rw [mul_pow, Wt_sq_Iθ (gam_ne_zero hα) hθ]
  ring

theorem ae_pm_fst_pos : ∀ᵐ p ∂pm, 0 < p.1 := by
  refine (MeasureTheory.Measure.ae_prod_iff_ae_ae (p := fun p : ℝ × ℝ => 0 < p.1)
    (measurableSet_Ioi.preimage measurable_fst)).mpr ?_
  exact ae_restrict_Iz_pos.mono fun x hx => Filter.Eventually.of_forall fun _ => hx

theorem ae_pm_snd_mem_Ioo : ∀ᵐ p ∂pm, p.2 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
  refine (MeasureTheory.Measure.ae_prod_iff_ae_ae (p := fun p : ℝ × ℝ =>
    p.2 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2))
    (measurableSet_Ioo.preimage measurable_snd)).mpr ?_
  refine Filter.Eventually.of_forall fun _ => ?_
  rw [← restrict_Ioo_eq_Iθ]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioo

/-! ## The critical slot on the product measure -/

theorem critSlot_prod {α Ctr : ℝ} (hα : α ∈ Set.Ioc 0 1) {g : ℝ → ℝ → ℝ}
    (hgs : Work.FTS.EllipticEst.SmoothOpen g) (hgm : Work.Spaces.HkMem α 6 g)
    (m : ℕ) (hm : m ≤ 2)
    (hintB : MeasureTheory.IntegrableOn
      (fun θ => (Real.sin (2 * θ)) ^ (α / 10 - 1)) (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (htr_int : MeasureTheory.IntegrableOn
      (fun z => (Work.Spaces.w z) ^ 2 * (Work.Spaces.DzIter m g z (Real.pi / 4)) ^ 2)
      Work.Spaces.Iz)
    (htr_bnd : (∫ z in Work.Spaces.Iz,
        (Work.Spaces.w z) ^ 2 * (Work.Spaces.DzIter m g z (Real.pi / 4)) ^ 2)
      ≤ Ctr * Work.Spaces.HkSq α 6 g) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
        * (Real.sin (2 * p.2)) ^ (-(1 - α / 10))
        * (Work.Spaces.DzIter m g p.1 p.2) ^ 2) pm ∧
      (∫ p : ℝ × ℝ, (Work.Spaces.w p.1) ^ 2
        * (Real.sin (2 * p.2)) ^ (-(1 - α / 10))
        * (Work.Spaces.DzIter m g p.1 p.2) ^ 2 ∂pm)
        ≤ 2 * critD α * (Ctr * Work.Spaces.HkSq α 6 g)
          + 2 * critD α * critD α * Work.Spaces.HkSq α 6 g := by
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  have hm6 : m + 1 ≤ 6 := by omega
  have hm4 : 1 + m ≤ 4 := by omega
  have hD0 : 0 ≤ critD α := critD_nonneg α
  have hH0 : 0 ≤ Work.Spaces.HkSq α 6 g := Work.Spaces.HkSq_nonneg α 6 g
  have hintIθ := int_sig_beta_integrable_Iθ hintB
  -- the `z`-marginal of the `γ`-slot
  have hQz_int := mslot_marginal_canon hα0 hgs hgm m hm4
  have hQz_bnd := mixedSlot_marginal_le_HkSq hα0 hgm m (by omega : 1 + m ≤ 6)
  -- the slicewise integrability
  have hslice : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.Integrable (fun θ => (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-(1 - α / 10))
        * (Work.Spaces.DzIter m g z θ) ^ 2) (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    refine ae_restrict_Iz_pos.mono fun z hz => ?_
    have hpt := sliceCritPt hα0 hα1 hgs hgm m hm6 hintB hz
    have haesm : AEStronglyMeasurable (fun θ => (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-(1 - α / 10))
        * (Work.Spaces.DzIter m g z θ) ^ 2) (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
      refine aesm_slice_Iθ ?_
      exact (continuousOn_const.mul (continuousOn_sin_two_rpow_Ioo _)).mul
        (((hgs.DzIter m).curry_θ hz).continuousOn.pow 2)
    refine MeasureTheory.Integrable.mono' (hintIθ.const_mul ((Work.Spaces.w z) ^ 2 *
      (2 * (Work.Spaces.DzIter m g z (Real.pi / 4)) ^ 2
        + 2 * (∫ θ' in Set.Ioo (0 : ℝ) (Real.pi / 2),
            (deriv (fun θ' => Work.Spaces.DzIter m g z θ') θ') ^ 2
              * (Real.sin (2 * θ')) ^ (1 - α / 10)) * critD α))) haesm ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ => ?_
    have hσ0 : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_Iθ hθ
    rw [Real.norm_of_nonneg (by
      have := Real.rpow_nonneg hσ0 (-(1 - α / 10))
      positivity)]
    rcases eq_or_lt_of_le hθ.1 with h0 | h0
    · rw [← h0, show Real.sin (2 * (0 : ℝ)) = 0 by simp,
        Real.zero_rpow (by intro h; linarith),
        Real.zero_rpow (by intro h; linarith)]
      simp
    rcases eq_or_lt_of_le hθ.2 with h2 | h2
    · rw [h2, show Real.sin (2 * (Real.pi / 2)) = 0 by
          rw [show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi],
        Real.zero_rpow (by intro h; linarith),
        Real.zero_rpow (by intro h; linarith)]
      simp
    · have hσ : 0 < Real.sin (2 * θ) := sin_two_pos_of_mem_Ioo ⟨h0, h2⟩
      have h1 := hpt θ ⟨h0, h2⟩
      have hw0 : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
      calc (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(1 - α / 10))
            * (Work.Spaces.DzIter m g z θ) ^ 2
          ≤ (Work.Spaces.w z) ^ 2
              * ((2 * (Work.Spaces.DzIter m g z (Real.pi / 4)) ^ 2
                + 2 * (∫ θ' in Set.Ioo (0 : ℝ) (Real.pi / 2),
                    (deriv (fun θ' => Work.Spaces.DzIter m g z θ') θ') ^ 2
                      * (Real.sin (2 * θ')) ^ (1 - α / 10)) * critD α)
                * (Real.sin (2 * θ)) ^ (α / 10 - 1)) := by
            have h1' : (Real.sin (2 * θ)) ^ (-(1 - α / 10))
                * (Work.Spaces.DzIter m g z θ) ^ 2
                ≤ (2 * (Work.Spaces.DzIter m g z (Real.pi / 4)) ^ 2
                  + 2 * (∫ θ' in Set.Ioo (0 : ℝ) (Real.pi / 2),
                      (deriv (fun θ' => Work.Spaces.DzIter m g z θ') θ') ^ 2
                        * (Real.sin (2 * θ')) ^ (1 - α / 10)) * critD α)
                  * (Real.sin (2 * θ)) ^ (α / 10 - 1) := h1
            calc (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(1 - α / 10))
                  * (Work.Spaces.DzIter m g z θ) ^ 2
                = (Work.Spaces.w z) ^ 2 * ((Real.sin (2 * θ)) ^ (-(1 - α / 10))
                    * (Work.Spaces.DzIter m g z θ) ^ 2) := by ring
              _ ≤ _ := mul_le_mul_of_nonneg_left h1' hw0
        _ = (Work.Spaces.w z) ^ 2
              * (2 * (Work.Spaces.DzIter m g z (Real.pi / 4)) ^ 2
                + 2 * (∫ θ' in Set.Ioo (0 : ℝ) (Real.pi / 2),
                    (deriv (fun θ' => Work.Spaces.DzIter m g z θ') θ') ^ 2
                      * (Real.sin (2 * θ')) ^ (1 - α / 10)) * critD α)
              * (Real.sin (2 * θ)) ^ (α / 10 - 1) := by ring
  -- the majorant of the outer function
  have hmajor : MeasureTheory.Integrable (fun z => 2 * critD α
        * ((Work.Spaces.w z) ^ 2 * (Work.Spaces.DzIter m g z (Real.pi / 4)) ^ 2)
      + 2 * critD α * critD α * ((Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * (Work.Spaces.mixed m 1 g z θ) ^ 2)))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    refine MeasureTheory.Integrable.add ?_ ?_
    · exact htr_int.const_mul (2 * critD α)
    · exact hQz_int.const_mul (2 * critD α * critD α)
  have haesmOut : AEStronglyMeasurable (fun z => ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(1 - α / 10))
        * (Work.Spaces.DzIter m g z θ) ^ 2) (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    (Work.Spaces.aesm_of_continuousOn_Qd _
      ((continuousOn_w2_sig_Qd (-(1 - α / 10))).mul
        ((hgs.DzIter m).continuousOn.pow 2))).integral_prod_right'
  have houter : MeasureTheory.Integrable (fun z => ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(1 - α / 10))
        * (Work.Spaces.DzIter m g z θ) ^ 2) (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    refine MeasureTheory.Integrable.mono' hmajor haesmOut ?_
    filter_upwards [ae_restrict_Iz_pos] with z hz
    have hb := sliceCritBound hα0 hα1 hgs hgm m hm6 hintB hz
    have hw0 : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
    have hnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-(1 - α / 10)) * (Work.Spaces.DzIter m g z θ) ^ 2 :=
      MeasureTheory.setIntegral_nonneg measurableSet_Icc fun θ hθ =>
        mul_nonneg (mul_nonneg (sq_nonneg _)
          (Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _)) (sq_nonneg _)
    have hpull : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (-(1 - α / 10)) * (Work.Spaces.DzIter m g z θ) ^ 2)
        = (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
            (Real.sin (2 * θ)) ^ (-(1 - α / 10)) * (Work.Spaces.DzIter m g z θ) ^ 2 := by
      rw [← MeasureTheory.integral_const_mul]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ _ => ?_
      ring
    rw [Real.norm_of_nonneg hnn, hpull]
    calc (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
            (Real.sin (2 * θ)) ^ (-(1 - α / 10)) * (Work.Spaces.DzIter m g z θ) ^ 2
        ≤ (Work.Spaces.w z) ^ 2
            * (2 * critD α * (Work.Spaces.DzIter m g z (Real.pi / 4)) ^ 2
              + 2 * critD α * critD α * (∫ θ in Work.Spaces.Iθ,
                  (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
                    * (Work.Spaces.mixed m 1 g z θ) ^ 2)) :=
          mul_le_mul_of_nonneg_left hb hw0
      _ = 2 * critD α * ((Work.Spaces.w z) ^ 2 * (Work.Spaces.DzIter m g z (Real.pi / 4)) ^ 2)
            + 2 * critD α * critD α * ((Work.Spaces.w z) ^ 2
              * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
                  * (Work.Spaces.mixed m 1 g z θ) ^ 2)) := by ring
  -- Fubini
  have hnn : ∀ᵐ p ∂pm, 0 ≤ (Work.Spaces.w p.1) ^ 2
      * (Real.sin (2 * p.2)) ^ (-(1 - α / 10)) * (Work.Spaces.DzIter m g p.1 p.2) ^ 2 := by
    filter_upwards [ae_pm_snd_mem_Ioo] with p hp
    exact mul_nonneg (mul_nonneg (sq_nonneg _)
      (Real.rpow_nonneg (le_of_lt (sin_two_pos_of_mem_Ioo hp)) _)) (sq_nonneg _)
  have haesm : AEStronglyMeasurable (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
      * (Real.sin (2 * p.2)) ^ (-(1 - α / 10))
      * (Work.Spaces.DzIter m g p.1 p.2) ^ 2) pm :=
    Work.Spaces.aesm_of_continuousOn_Qd _ ((continuousOn_w2_sig_Qd (-(1 - α / 10))).mul
      ((hgs.DzIter m).continuousOn.pow 2))
  obtain ⟨hint, hval⟩ := integrable_prod_of_iterated_ae hnn haesm hslice houter
  refine ⟨hint, ?_⟩
  rw [hval]
  have hmono2 : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-(1 - α / 10)) * (Work.Spaces.DzIter m g z θ) ^ 2)
      ≤ ∫ z in Work.Spaces.Iz, 2 * critD α
          * ((Work.Spaces.w z) ^ 2 * (Work.Spaces.DzIter m g z (Real.pi / 4)) ^ 2)
        + 2 * critD α * critD α * ((Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
            (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
              * (Work.Spaces.mixed m 1 g z θ) ^ 2)) := by
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun z => MeasureTheory.setIntegral_nonneg measurableSet_Icc
        (fun θ hθ => mul_nonneg (mul_nonneg (sq_nonneg _)
          (Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _)) (sq_nonneg _)))
      hmajor ?_
    filter_upwards [ae_restrict_Iz_pos] with z hz
    have hb := sliceCritBound hα0 hα1 hgs hgm m hm6 hintB hz
    have hw0 : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
    have hpull : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (-(1 - α / 10)) * (Work.Spaces.DzIter m g z θ) ^ 2)
        = (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
            (Real.sin (2 * θ)) ^ (-(1 - α / 10)) * (Work.Spaces.DzIter m g z θ) ^ 2 := by
      rw [← MeasureTheory.integral_const_mul]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ _ => ?_
      ring
    rw [hpull]
    calc (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
            (Real.sin (2 * θ)) ^ (-(1 - α / 10)) * (Work.Spaces.DzIter m g z θ) ^ 2
        ≤ (Work.Spaces.w z) ^ 2
            * (2 * critD α * (Work.Spaces.DzIter m g z (Real.pi / 4)) ^ 2
              + 2 * critD α * critD α * (∫ θ in Work.Spaces.Iθ,
                  (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
                    * (Work.Spaces.mixed m 1 g z θ) ^ 2)) :=
          mul_le_mul_of_nonneg_left hb hw0
      _ = 2 * critD α * ((Work.Spaces.w z) ^ 2 * (Work.Spaces.DzIter m g z (Real.pi / 4)) ^ 2)
            + 2 * critD α * critD α * ((Work.Spaces.w z) ^ 2
              * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
                  * (Work.Spaces.mixed m 1 g z θ) ^ 2)) := by ring
  refine hmono2.trans ?_
  rw [MeasureTheory.integral_add (htr_int.const_mul _) (hQz_int.const_mul _),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  have hQzb := mixedSlot_marginal_le_HkSq hα0 hgm m (by omega : 1 + m ≤ 6)
  have hD2 : 0 ≤ 2 * critD α := by linarith
  have hD22 : 0 ≤ 2 * critD α * critD α := by positivity
  have h1 : 2 * critD α * (∫ z in Work.Spaces.Iz,
        (Work.Spaces.w z) ^ 2 * (Work.Spaces.DzIter m g z (Real.pi / 4)) ^ 2)
      ≤ 2 * critD α * (Ctr * Work.Spaces.HkSq α 6 g) := mul_le_mul_of_nonneg_left htr_bnd hD2
  have h2 : 2 * critD α * critD α * (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * (Work.Spaces.mixed m 1 g z θ) ^ 2))
      ≤ 2 * critD α * critD α * Work.Spaces.HkSq α 6 g := mul_le_mul_of_nonneg_left hQzb hD22
  linarith [h1, h2]


end Work.FTS.StrongPersist.N6Trans.SixRoute
