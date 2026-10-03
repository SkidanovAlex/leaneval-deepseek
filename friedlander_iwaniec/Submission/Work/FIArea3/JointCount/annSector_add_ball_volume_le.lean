import Mathlib
import Submission.Work.FIArea3.JointCount.sharp_defs
import Submission.Work.FIArea3.JointCount.polarBand_volume
import Submission.Work.FIArea3.JointCount.volume_iUnion_Icc_int_le
import Submission.Work.FIArea3.JointCount.arg_add_sub_mem_Icc
import Submission.Work.FIArea3.JointCount.annSector_arith_gt

set_option maxHeartbeats 1600000

namespace Work.FIArea3.JointCount

open MeasureTheory Set
open scoped ENNReal

noncomputable section

attribute [local instance] Classical.propDecidable

lemma annSector_arith_main (a θ r : ℝ) (ha : 0 < a) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hr0 : 0 ≤ r) (hr2 : r ≤ 1.2 * θ * a) :
    ((a * Real.sqrt (1 + θ) + r) ^ 2 - (a - r) ^ 2) / 2 * (2 * Real.pi * θ + Real.pi * (r / a))
      ≤ Real.pi * (θ * a) ^ 2 + 32 * (θ * a) * r := by
  have h1θ : 0 ≤ 1 + θ := by linarith
  have hs0 : 0 ≤ Real.sqrt (1 + θ) := Real.sqrt_nonneg _
  have hs2 : Real.sqrt (1 + θ) ^ 2 = 1 + θ := Real.sq_sqrt h1θ
  have hsle : Real.sqrt (1 + θ) ≤ 3 / 2 := by
    have h : Real.sqrt (1 + θ) ^ 2 ≤ (3 / 2 : ℝ) ^ 2 := by rw [hs2]; nlinarith
    nlinarith [hs0, h]
  have hsr : Real.sqrt (1 + θ) + 1 ≤ 5 / 2 := by linarith
  have hpi : Real.pi < 3.1416 := Real.pi_lt_d4
  have hpipos : 0 < Real.pi := Real.pi_pos
  rw [show (2 * Real.pi * θ + Real.pi * (r / a)) = (2 * Real.pi * θ * a + Real.pi * r) / a by
        rw [eq_div_iff (ne_of_gt ha)]; field_simp]
  rw [← mul_div_assoc]
  rw [div_le_iff₀ ha]
  have he : (a * Real.sqrt (1 + θ) + r) ^ 2 - (a - r) ^ 2
      = a ^ 2 * θ + 2 * a * r * (Real.sqrt (1 + θ) + 1) := by nlinarith [hs2]
  rw [he]
  have hAr : 0 ≤ a * r := by positivity
  have h1 : (a ^ 2 * θ + 2 * a * r * (Real.sqrt (1 + θ) + 1)) / 2 * (2 * Real.pi * θ * a + Real.pi * r)
      = Real.pi * θ ^ 2 * a ^ 3 + a * r * ((Real.pi / 2) * θ * a
          + 2 * Real.pi * θ * a * (Real.sqrt (1 + θ) + 1)
          + Real.pi * r * (Real.sqrt (1 + θ) + 1)) := by ring
  have h2 : (Real.pi * (θ * a) ^ 2 + 32 * (θ * a) * r) * a
      = Real.pi * θ ^ 2 * a ^ 3 + a * r * (32 * θ * a) := by ring
  rw [h1, h2]
  have hA : 2 * Real.pi * θ * a * (Real.sqrt (1 + θ) + 1) ≤ 2 * Real.pi * θ * a * (5 / 2) :=
    mul_le_mul_of_nonneg_left hsr (by positivity)
  have hB : Real.pi * r * (Real.sqrt (1 + θ) + 1) ≤ Real.pi * r * (5 / 2) :=
    mul_le_mul_of_nonneg_left hsr (by positivity)
  have hC : Real.pi * r * (5 / 2) ≤ Real.pi * (1.2 * θ * a) * (5 / 2) := by
    have h := mul_le_mul_of_nonneg_left hr2 (show (0 : ℝ) ≤ Real.pi * (5 / 2) by positivity)
    nlinarith [h]
  have hD : (Real.pi / 2) * θ * a + 2 * Real.pi * θ * a * (Real.sqrt (1 + θ) + 1)
      + Real.pi * r * (Real.sqrt (1 + θ) + 1) ≤ 32 * θ * a := by
    nlinarith [hA, hB, hC, hpi, hpipos, hθ0, ha.le]
  have hX : a * r * ((Real.pi / 2) * θ * a + 2 * Real.pi * θ * a * (Real.sqrt (1 + θ) + 1)
      + Real.pi * r * (Real.sqrt (1 + θ) + 1)) ≤ a * r * (32 * θ * a) :=
    mul_le_mul_of_nonneg_left hD hAr
  linarith [hX]

theorem annSector_add_ball_volume_le (a θ φ r : ℝ) (ha : 0 < a) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hr0 : 0 ≤ r) (hr1 : r ≤ a) (hr2 : r ≤ 1.2 * θ * a) :
    (MeasureTheory.volume (Set.image2 (· + ·)
        (Work.FIArea3.JointCount.annSector a (a * Real.sqrt (1 + θ)) φ (2 * Real.pi * θ))
        (Metric.closedBall (0 : ℂ) r))).toReal
      ≤ Real.pi * (θ * a) ^ 2 + 32 * (θ * a) * r := by
  set T : ℝ := Real.pi * (θ * a) ^ 2 + 32 * (θ * a) * r with hT
  have hT0 : 0 ≤ T := by
    rw [hT]; positivity
  suffices hmain : MeasureTheory.volume (Set.image2 (· + ·)
        (Work.FIArea3.JointCount.annSector a (a * Real.sqrt (1 + θ)) φ (2 * Real.pi * θ))
        (Metric.closedBall (0 : ℂ) r)) ≤ ENNReal.ofReal T by
    calc (MeasureTheory.volume (Set.image2 (· + ·)
        (Work.FIArea3.JointCount.annSector a (a * Real.sqrt (1 + θ)) φ (2 * Real.pi * θ))
        (Metric.closedBall (0 : ℂ) r))).toReal
        ≤ (ENNReal.ofReal T).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmain
      _ = T := ENNReal.toReal_ofReal hT0
      _ = Real.pi * (θ * a) ^ 2 + 32 * (θ * a) * r := by rw [hT]
  rcases le_total r a with hrle | hrgt
  · -- Case A: r ≤ a
    set δ : ℝ := Real.pi / 2 * (r / a) with hδdef
    set out : ℝ := a - r with houtdef
    set Rr : ℝ := a * Real.sqrt (1 + θ) + r with hRdef
    set A : Set ℝ := ⋃ k : ℤ, Set.Icc (φ - δ + 2 * Real.pi * k)
        (φ + 2 * Real.pi * θ + δ + 2 * Real.pi * k) with hAdef
    set P : Set ℂ := {z : ℂ | out < ‖z‖ ∧ ‖z‖ ≤ Rr ∧ Complex.arg z ∈ A} with hPdef
    have hAmeas : MeasurableSet A := by
      rw [hAdef]; exact MeasurableSet.iUnion (fun k => measurableSet_Icc)
    have hδ0 : 0 ≤ δ := by rw [hδdef]; positivity
    have hs1 : 1 ≤ Real.sqrt (1 + θ) := by
      rw [Real.one_le_sqrt]; linarith
    have hout0 : 0 ≤ out := by rw [houtdef]; linarith
    have hout_le_R : out ≤ Rr := by
      rw [houtdef, hRdef]
      have : a ≤ a * Real.sqrt (1 + θ) := by
        calc a = a * 1 := by ring
          _ ≤ a * Real.sqrt (1 + θ) := mul_le_mul_of_nonneg_left hs1 (le_of_lt ha)
      linarith
    have hKP : Set.image2 (· + ·)
        (Work.FIArea3.JointCount.annSector a (a * Real.sqrt (1 + θ)) φ (2 * Real.pi * θ))
        (Metric.closedBall (0 : ℂ) r) ⊆ P := by
      rintro w ⟨z, hz, u, hu, rfl⟩
      rw [hPdef, Set.mem_ofPred_eq, houtdef, hRdef]
      obtain ⟨hza, hzb, hzφ, hzφ'⟩ := hz
      have hznorm : ‖u‖ ≤ r := by
        rw [Metric.mem_closedBall, dist_zero_right] at hu; exact hu
      refine ⟨?_, ?_, ?_⟩
      · show out < ‖z + u‖
        have h1 : ‖z‖ - ‖u‖ ≤ ‖z + u‖ := norm_sub_le_norm_add z u
        linarith
      · show ‖z + u‖ ≤ Rr
        have h2 : ‖z + u‖ ≤ ‖z‖ + ‖u‖ := norm_add_le z u
        linarith
      · show Complex.arg (z + u) ∈ A
        obtain ⟨k, hk⟩ := arg_add_sub_mem_Icc z u a r ha hr0 hrle hza hznorm
        have hk2 : (z + u).arg + 2 * Real.pi * (k : ℝ) ∈ Set.Icc (z.arg - δ) (z.arg + δ) := by
          rw [hδdef]; exact hk
        rw [Set.mem_Icc] at hk2
        rw [hAdef]
        refine Set.mem_iUnion.mpr ⟨-k, Set.mem_Icc.mpr ⟨?_, ?_⟩⟩
        · push_cast; linarith [hk2.1, hzφ]
        · push_cast; linarith [hk2.2, hzφ']
    have hPvol : MeasureTheory.volume P
        = ENNReal.ofReal ((Rr ^ 2 - out ^ 2) / 2
            * (MeasureTheory.volume (A ∩ Set.Ioo (-Real.pi) Real.pi)).toReal) := by
      rw [hPdef]
      exact polarBand_volume out Rr A hout0 hout_le_R hAmeas
    have hAvol : MeasureTheory.volume (A ∩ Set.Ioo (-Real.pi) Real.pi)
        ≤ ENNReal.ofReal (2 * Real.pi * θ + 2 * δ) := by
      have hsub : A ∩ Set.Ioo (-Real.pi) Real.pi ⊆ ⋃ k : ℤ,
          Set.Icc (φ - δ + 2 * Real.pi * k)
            (φ + 2 * Real.pi * θ + δ + 2 * Real.pi * k) ∩ Set.Ioc (-Real.pi) Real.pi := by
        intro t ht
        rw [Set.mem_inter_iff] at ht
        obtain ⟨htA, htIoo⟩ := ht
        rw [hAdef, Set.mem_iUnion] at htA
        obtain ⟨k, hk⟩ := htA
        exact Set.mem_iUnion.mpr ⟨k, ⟨hk, Set.Ioo_subset_Ioc_self htIoo⟩⟩
      calc MeasureTheory.volume (A ∩ Set.Ioo (-Real.pi) Real.pi)
          ≤ MeasureTheory.volume (⋃ k : ℤ,
              Set.Icc (φ - δ + 2 * Real.pi * k)
                (φ + 2 * Real.pi * θ + δ + 2 * Real.pi * k) ∩ Set.Ioc (-Real.pi) Real.pi) :=
            measure_mono hsub
        _ ≤ ENNReal.ofReal ((φ + 2 * Real.pi * θ + δ) - (φ - δ)) :=
            volume_iUnion_Icc_int_le _ _
        _ = ENNReal.ofReal (2 * Real.pi * θ + 2 * δ) := by
            rw [show (φ + 2 * Real.pi * θ + δ) - (φ - δ) = 2 * Real.pi * θ + 2 * δ by ring]
    have hcoef0 : 0 ≤ (Rr ^ 2 - out ^ 2) / 2 := by
      have hR0 : 0 ≤ Rr := by rw [hRdef]; positivity
      nlinarith [hout0, hout_le_R, hR0]
    have hAvol' : (MeasureTheory.volume (A ∩ Set.Ioo (-Real.pi) Real.pi)).toReal
        ≤ 2 * Real.pi * θ + 2 * δ := by
      have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hAvol
      rwa [ENNReal.toReal_ofReal (by positivity)] at h
    have hPle : MeasureTheory.volume P
        ≤ ENNReal.ofReal ((Rr ^ 2 - out ^ 2) / 2 * (2 * Real.pi * θ + 2 * δ)) := by
      rw [hPvol]
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul_of_nonneg_left hAvol' hcoef0
    have harith : (Rr ^ 2 - out ^ 2) / 2 * (2 * Real.pi * θ + 2 * δ) ≤ T := by
      have hδeq : 2 * δ = Real.pi * (r / a) := by rw [hδdef]; ring
      rw [hRdef, houtdef, hT, hδeq]
      exact annSector_arith_main a θ r ha hθ0 hθ1 hr0 hr2
    calc MeasureTheory.volume (Set.image2 (· + ·)
          (Work.FIArea3.JointCount.annSector a (a * Real.sqrt (1 + θ)) φ (2 * Real.pi * θ))
          (Metric.closedBall (0 : ℂ) r))
        ≤ MeasureTheory.volume P := measure_mono hKP
      _ ≤ ENNReal.ofReal ((Rr ^ 2 - out ^ 2) / 2 * (2 * Real.pi * θ + 2 * δ)) := hPle
      _ ≤ ENNReal.ofReal T := ENNReal.ofReal_le_ofReal harith
  · -- Case B: a < r
    have har : a ≤ r := hrgt
    set Rr : ℝ := a * Real.sqrt (1 + θ) + r with hRdef
    have hRr0 : 0 ≤ Rr := by rw [hRdef]; positivity
    have hKB : Set.image2 (· + ·)
        (Work.FIArea3.JointCount.annSector a (a * Real.sqrt (1 + θ)) φ (2 * Real.pi * θ))
        (Metric.closedBall (0 : ℂ) r) ⊆ Metric.closedBall (0 : ℂ) Rr := by
      rintro w ⟨z, hz, u, hu, rfl⟩
      obtain ⟨hza, hzb, hzφ, hzφ'⟩ := hz
      have hznorm : ‖u‖ ≤ r := by
        rw [Metric.mem_closedBall, dist_zero_right] at hu; exact hu
      rw [Metric.mem_closedBall, dist_zero_right]
      show ‖z + u‖ ≤ Rr
      calc ‖z + u‖ ≤ ‖z‖ + ‖u‖ := norm_add_le z u
        _ ≤ a * Real.sqrt (1 + θ) + r := by linarith
    have hvolEq : (ENNReal.ofReal Rr ^ 2 * ↑NNReal.pi : ENNReal)
        = ENNReal.ofReal (Real.pi * Rr ^ 2) := by
      have h1 : (↑NNReal.pi : ENNReal) = ENNReal.ofReal Real.pi := by
        rw [← ENNReal.ofReal_coe_nnreal]
        rw [show (((↑NNReal.pi : NNReal)) : ℝ) = Real.pi from rfl]
      rw [h1, ← ENNReal.ofReal_pow hRr0 2, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring
    have harith : Real.pi * Rr ^ 2 ≤ T := by
      rw [hRdef, hT]
      exact annSector_arith_gt a θ r ha hθ0 hθ1 hr0 hr2 har
    calc MeasureTheory.volume (Set.image2 (· + ·)
          (Work.FIArea3.JointCount.annSector a (a * Real.sqrt (1 + θ)) φ (2 * Real.pi * θ))
          (Metric.closedBall (0 : ℂ) r))
        ≤ MeasureTheory.volume (Metric.closedBall (0 : ℂ) Rr) := measure_mono hKB
      _ = ENNReal.ofReal Rr ^ 2 * ↑NNReal.pi := Complex.volume_closedBall 0 Rr
      _ = ENNReal.ofReal (Real.pi * Rr ^ 2) := hvolEq
      _ ≤ ENNReal.ofReal T := ENNReal.ofReal_le_ofReal harith

end

end Work.FIArea3.JointCount
