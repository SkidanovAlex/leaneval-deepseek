import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.TransportS.SlotT2.Basic
import Submission.Work.H2.T1Q.HardBoundQ
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.H2.T1Q.Cutoff
import Submission.Work.H2.T1Q.ShrinkInt
import Submission.Work.H2.T1Q.SliceLimit
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.SixZeroAux.IbpCutoffNonneg
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.SixZeroAux.singleSlotCutBoundMine

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.T1SixAux

set_option maxHeartbeats 1200000

theorem hardSlotSliceSixZero : ∃ C : ℝ, 0 < C ∧ ∀ (q Kf z : ℝ) (f Y : ℝ → ℝ → ℝ),
    0 ≤ q → q ≤ 2 → 0 ≤ Kf → z ∈ Work.Spaces.Iz →
    Work.FTS.EllipticEst.SmoothOpen f → Work.FTS.EllipticEst.SmoothOpen Y →
    (∀ θ : ℝ, 0 < θ → θ < π / 2 → |f z θ| ≤ Kf) →
    (∀ θ : ℝ, 0 < θ → θ < π / 2 → |Work.Spaces.Dth f z θ| ≤ Kf) →
    MeasureTheory.IntegrableOn (fun θ : ℝ =>
      Work.FTS.TransportS.SlotT2.canonW q z θ * (Y z θ) ^ 2) Work.Spaces.Iθ →
    |∫ θ in Work.Spaces.Iθ, Work.FTS.TransportS.SlotT2.canonW q z θ * f z θ
        * Work.Spaces.Dth Y z θ * Y z θ|
      ≤ C * Kf * ∫ θ in Work.Spaces.Iθ, Work.FTS.TransportS.SlotT2.canonW q z θ * (Y z θ) ^ 2 := by
  refine ⟨3 / 2, by norm_num, ?_⟩
  intro q Kf z f Y hq0 hq2 hKf0 hz hSf hSY hfb hdb hVint
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · -- the degenerate radius `z = 0`, where the radial weight vanishes
    subst hz0
    have hL : (fun θ : ℝ => Work.FTS.TransportS.SlotT2.canonW q 0 θ * f 0 θ
        * Work.Spaces.Dth Y 0 θ * Y 0 θ) = fun _ => (0 : ℝ) := by
      funext θ
      simp only [Work.FTS.TransportS.SlotT2.canonW, Work.Spaces.w]
      norm_num
    have hR : (fun θ : ℝ => Work.FTS.TransportS.SlotT2.canonW q 0 θ * (Y 0 θ) ^ 2)
        = fun _ => (0 : ℝ) := by
      funext θ
      simp only [Work.FTS.TransportS.SlotT2.canonW, Work.Spaces.w]
      norm_num
    rw [hL, hR, MeasureTheory.integral_zero, abs_zero, mul_zero]
  · -- the open quadrant
    obtain ⟨chi, B, hB, hsm, hnn, hle, hone, hz0l, hz0r, hd0l, hd0r, hbd, hten⟩ :=
      Work.H2.T1Q.Cutoff
    have hIθ : MeasurableSet Work.Spaces.Iθ := by
      rw [Work.Spaces.Iθ]; exact measurableSet_Icc
    have hFcd : ContDiffOn ℝ 1 (fun θ : ℝ => f z θ) (Set.Ioo 0 (π / 2)) :=
      (hSf.curry_θ hzpos).of_le (m := (1 : ℕ∞)) (by simp)
    have hVcd : ContDiffOn ℝ 1 (fun θ : ℝ => Y z θ) (Set.Ioo 0 (π / 2)) :=
      (hSY.curry_θ hzpos).of_le (m := (1 : ℕ∞)) (by simp)
    have hwne : (Work.Spaces.w z) ^ 2 ≠ 0 := by
      have h1 : Work.Spaces.w z ≠ 0 := by
        rw [Work.Spaces.w]
        exact div_ne_zero (pow_ne_zero 2 (by linarith)) (pow_ne_zero 2 (ne_of_gt hzpos))
      exact pow_ne_zero 2 h1
    -- the `q`-weighted slice energy is integrable
    have hVintq : MeasureTheory.IntegrableOn
        (fun θ : ℝ => (Y z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) Work.Spaces.Iθ := by
      have h2 : MeasureTheory.IntegrableOn
          (fun θ : ℝ => (Work.Spaces.w z) ^ 2
            * ((Y z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q))) Work.Spaces.Iθ :=
        hVint.congr_fun (fun θ _ => by
          simp only [Work.FTS.TransportS.SlotT2.canonW]; ring) hIθ
      exact (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hwne) _).mp h2
    -- the pointwise bounds
    have hFb : ∀ θ : ℝ, 0 < θ → θ < π / 2 → |f z θ| ≤ Kf :=
      fun θ hθ hθ2 => hfb θ hθ hθ2
    have hFdb : ∀ θ : ℝ, 0 < θ → θ < π / 2 →
        |Real.sin (2 * θ) * deriv (fun θ' => f z θ') θ| ≤ Kf := by
      intro θ hθ hθ2
      have h := hdb θ hθ hθ2
      simpa only [Work.Spaces.Dth, Work.Spaces.pth] using h
    have hWq : ∀ θ : ℝ, 0 < θ → θ < π / 2 →
        |(1 / 2) * (Real.sin (2 * θ) * deriv (fun θ' => f z θ') θ)
          + (1 - q) * Real.cos (2 * θ) * f z θ| ≤ (3 / 2) * Kf := by
      intro θ hθ hθ2
      refine Work.H2.T1Q.Wq_bound hKf0 (hFdb θ hθ hθ2) (hFb θ hθ hθ2) ?_
      rw [abs_le]; constructor <;> linarith
    -- the cut-off parameters tend to `0`
    have hbase : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 4)) atTop (𝓝 0) := by
      have hshift : Filter.Tendsto (fun n : ℕ => n + 3) Filter.atTop Filter.atTop :=
        Filter.tendsto_atTop_mono (fun n => Nat.le_add_right n 3) Filter.tendsto_id
      have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hshift
      refine h.congr (fun n => ?_)
      simp only [Function.comp_apply]
      push_cast
      ring_nf
    have hlimeq : Tendsto (fun n : ℕ => (1 : ℝ) / (2 * ((n : ℝ) + 4))) atTop (𝓝 0) := by
      have h2 : Filter.Tendsto (fun n : ℕ => (1 / 2 : ℝ) * (1 / ((n : ℝ) + 4)))
          Filter.atTop (𝓝 0) := by
        simpa using hbase.const_mul (1 / 2 : ℝ)
      refine h2.congr' ?_
      filter_upwards with n
      have hx : (4 + (n : ℝ)) ≠ 0 := by positivity
      field_simp
    have hlimpos : Tendsto (fun n : ℕ => (1 : ℝ) / (2 * ((n : ℝ) + 4))) atTop
        (𝓝[>] (0 : ℝ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨hlimeq, ?_⟩
      filter_upwards with n
      exact Set.mem_Ioi.mpr (by positivity)
    -- the cut-off converges to `1`
    have hchi_lim : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        Tendsto (fun n : ℕ => chi (1 / (2 * ((n : ℝ) + 4))) θ) atTop (𝓝 1) := by
      filter_upwards [Work.H2.T1Q.ae_Iθ_mem_Ioo] with θ hθ
      exact (hten θ hθ.1 hθ.2).comp hlimpos
    have hchi_meas : ∀ n : ℕ, MeasureTheory.AEStronglyMeasurable
        (fun θ : ℝ => chi (1 / (2 * ((n : ℝ) + 4))) θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      fun n => (hsm (1 / (2 * ((n : ℝ) + 4)))).continuous.aestronglyMeasurable
    have hchi_le : ∀ (n : ℕ) (θ : ℝ), |chi (1 / (2 * ((n : ℝ) + 4))) θ| ≤ 1 := by
      intro n θ
      rw [abs_of_nonneg (hnn _ θ)]
      exact hle _ θ
    -- the per-`n` bound of the localised integral
    have hbd_seq : ∀ n : ℕ,
        |∫ θ in Work.Spaces.Iθ, chi (1 / (2 * ((n : ℝ) + 4))) θ
            * ((Real.sin (2 * θ)) ^ (-q) * f z θ * Work.Spaces.Dth Y z θ * Y z θ)|
          ≤ (3 / 2) * Kf * (∫ θ in Work.Spaces.Iθ,
              (Y z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q))
            + (Kf * B / 2) * ((∫ θ in Set.Ioc 0 (1 / ((n : ℝ) + 4)),
                  (Y z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q))
              + ∫ θ in Set.Ioc (π / 2 - 1 / ((n : ℝ) + 4)) (π / 2),
                  (Y z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) := by
      intro n
      have hζn : 0 < (1 : ℝ) / (2 * ((n : ℝ) + 4)) := by positivity
      have hζn4 : (1 : ℝ) / (2 * ((n : ℝ) + 4)) ≤ 1 / 4 := by
        rw [div_le_iff₀ (by positivity)]
        push_cast
        linarith [Nat.cast_nonneg (α := ℝ) n]
      have h := SixZeroAux.singleSlotCutBoundMine (q := q) (Kf := Kf) (B := B) (z := z) (f := f)
        (Y := Y) (chi := chi) (ζ := 1 / (2 * ((n : ℝ) + 4)))
        hq0 hKf0 hB.le hzpos hsm hnn hle hone hz0l hz0r hd0l hd0r hbd
        hFcd hVcd hFb hWq hVintq hζn hζn4
      have h2ζ : 2 * (1 / (2 * ((n : ℝ) + 4))) = 1 / ((n : ℝ) + 4) := by
        have hx : ((n : ℝ) + 4) ≠ 0 := by positivity
        field_simp
      rw [h2ζ] at h
      exact h
    -- the shrinking boundary contributions vanish
    have herr : Tendsto (fun n : ℕ => (Kf * B / 2) *
        ((∫ θ in Set.Ioc 0 (1 / ((n : ℝ) + 4)),
            (Y z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q))
          + ∫ θ in Set.Ioc (π / 2 - 1 / ((n : ℝ) + 4)) (π / 2),
              (Y z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q))) atTop (𝓝 0) := by
      have h := Work.H2.T1Q.ShrinkInt hVintq
      simpa using h.const_mul (Kf * B / 2)
    by_cases hint : MeasureTheory.IntegrableOn
        (fun θ : ℝ => Work.FTS.TransportS.SlotT2.canonW q z θ * f z θ
          * Work.Spaces.Dth Y z θ * Y z θ) Work.Spaces.Iθ
    · -- the integrable case: pass to the limit `n → ∞` in the cut-off bound
      have hφint : MeasureTheory.IntegrableOn
          (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-q) * f z θ * Work.Spaces.Dth Y z θ * Y z θ)
          Work.Spaces.Iθ := by
        have h2 : MeasureTheory.IntegrableOn
            (fun θ : ℝ => (Work.Spaces.w z) ^ 2
              * ((Real.sin (2 * θ)) ^ (-q) * f z θ * Work.Spaces.Dth Y z θ * Y z θ))
            Work.Spaces.Iθ :=
          hint.congr_fun (fun θ _ => by
            simp only [Work.FTS.TransportS.SlotT2.canonW]; ring) hIθ
        exact (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hwne) _).mp h2
      have hS := Work.H2.T1Q.SliceLimit
        (M := (3 / 2) * Kf * (∫ θ in Work.Spaces.Iθ,
            (Y z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)))
        (φ := fun θ : ℝ => (Real.sin (2 * θ)) ^ (-q) * f z θ * Work.Spaces.Dth Y z θ * Y z θ)
        (chi := fun n θ => chi (1 / (2 * ((n : ℝ) + 4))) θ)
        (err := fun n : ℕ => (Kf * B / 2) *
          ((∫ θ in Set.Ioc 0 (1 / ((n : ℝ) + 4)),
              (Y z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q))
            + ∫ θ in Set.Ioc (π / 2 - 1 / ((n : ℝ) + 4)) (π / 2),
                (Y z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)))
        herr hφint hchi_meas hchi_le hchi_lim hbd_seq
      have hAeq : (∫ θ in Work.Spaces.Iθ, Work.FTS.TransportS.SlotT2.canonW q z θ * f z θ
            * Work.Spaces.Dth Y z θ * Y z θ)
          = (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
              (Real.sin (2 * θ)) ^ (-q) * f z θ * Work.Spaces.Dth Y z θ * Y z θ := by
        rw [← MeasureTheory.integral_const_mul]
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun θ => ?_))
        simp only [Work.FTS.TransportS.SlotT2.canonW]
        ring
      have hBstep : (∫ θ in Work.Spaces.Iθ,
            Work.FTS.TransportS.SlotT2.canonW q z θ * (Y z θ) ^ 2)
          = (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
              (Y z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q) := by
        rw [← MeasureTheory.integral_const_mul]
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun θ => ?_))
        simp only [Work.FTS.TransportS.SlotT2.canonW]
        ring
      rw [hAeq, abs_mul, abs_of_nonneg (sq_nonneg (Work.Spaces.w z))]
      refine le_trans (mul_le_mul_of_nonneg_left hS (sq_nonneg (Work.Spaces.w z))) ?_
      rw [hBstep]
      exact le_of_eq (by ring)
    · -- the non-integrable case: the integral is `0` by definition
      rw [MeasureTheory.integral_undef hint, abs_zero]
      refine mul_nonneg (mul_nonneg (by norm_num) hKf0)
        (MeasureTheory.integral_nonneg_of_ae
          (MeasureTheory.ae_restrict_of_forall_mem hIθ (fun θ hθ => ?_)))
      have hs : 0 ≤ Real.sin (2 * θ) := Work.Spaces.bt_sin_nonneg hθ
      exact mul_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs _)) (sq_nonneg _)

end Work.FTS.StrongPersist.N6Trans.T1SixAux
