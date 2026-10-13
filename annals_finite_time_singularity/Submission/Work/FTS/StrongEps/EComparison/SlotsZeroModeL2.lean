import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Construction.Defs
import Submission.Work.FTS.PhiStar.Series.eFam_sup_le
import Submission.Work.FTS.StrongEps.EComparison.SZML2.Local
import Submission.Work.FTS.StrongEps.EComparison.sin_two_rpow_integral_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EComparison

noncomputable section

set_option autoImplicit false

set_option maxHeartbeats 1000000


theorem SlotsZeroModeL2 {α : ℝ} {Φ : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Φ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hHk : Work.Spaces.HkMem α 6 (fun z θ => Φ z θ / Work.Construction.s2 θ)) :
    (∀ m : ℕ,
      MeasureTheory.LocallyIntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
        Φ z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ) (Set.Ioi 0) ∧
      MeasureTheory.IntegrableOn (fun z => (∫ θ in Work.Spaces.Iθ,
        Φ z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ) ^ 2 * z ^ (-4 : ℝ))
        (Set.Ioi 0)) ∧
    (∀ z ∈ Set.Ioi (0 : ℝ),
      MeasureTheory.IntegrableOn (fun θ => |Φ z θ|) Work.Spaces.Iθ) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ z ∈ Set.Ioi (0 : ℝ),
      ∫ θ in Work.Spaces.Iθ, |Φ z θ|
        ≤ C * Real.sqrt (Work.FTS.StrongEps.EComparison.sliceEnergy Φ z)) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ z ∈ Set.Ioi (0 : ℝ), ∀ δ ∈ Set.Ioc (0 : ℝ) (π / 4),
      (∫ θ in Set.Ioo 0 δ, |Φ z θ|
          ≤ C * Real.sqrt (Work.FTS.StrongEps.EComparison.sliceEnergy Φ z)
              * δ ^ ((3 + Work.Spaces.eta) / 2)) ∧
      (∫ θ in Set.Ioo (π / 2 - δ) (π / 2), |Φ z θ|
          ≤ C * Real.sqrt (Work.FTS.StrongEps.EComparison.sliceEnergy Φ z)
              * δ ^ ((3 + Work.Spaces.eta) / 2))) ∧
    (∀ a b : ℝ, 0 < a → a ≤ b →
      MeasureTheory.IntegrableOn (fun z => Real.sqrt (Work.FTS.StrongEps.EComparison.sliceEnergy Φ z))
        (Set.Icc a b)) ∧
    (∀ a b : ℝ, 0 < a → a ≤ b →
      MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
        Φ z θ ^ 2 * Work.FTS.StrongEps.EComparison.rootWeight θ) (Set.Icc a b)) ∧
    (∀ a b : ℝ, 0 < a → a ≤ b →
      MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, |Φ z θ|) (Set.Icc a b)) := by
  have hHk' : Work.Spaces.HkMem α 6 (psi Φ) := hHk
  have hHk_int : MeasureTheory.IntegrableOn (fun z => sliceHk α Φ z) Work.Spaces.Iz := hHk.2
  -- ### the `(0,0)`-slot of `Ψ` is `θ`-integrable for `z > 0`
  have hint : ∀ z ∈ Set.Ioi (0 : ℝ), MeasureTheory.IntegrableOn
      (fun θ => (psi Φ z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) Work.Spaces.Iθ :=
    fun z hz => integrableOn_psi_sq_rpow hsm hHk' hz
  -- ### conjunct 2 : `|Φ z ·|` is `θ`-integrable on `Iθ`
  have claim2 : ∀ z ∈ Set.Ioi (0 : ℝ),
      MeasureTheory.IntegrableOn (fun θ => |Φ z θ|) Work.Spaces.Iθ :=
    fun z hz => integrableOn_abs_Phi hsm hz (hint z hz)
  -- ### conjunct 3 : the slice Cauchy–Schwarz bound
  have claim3 : ∃ C : ℝ, 0 < C ∧ ∀ z ∈ Set.Ioi (0 : ℝ),
      ∫ θ in Work.Spaces.Iθ, |Φ z θ| ≤ C * Real.sqrt (sliceEnergy Φ z) := by
    refine ⟨K3, K3_pos, fun z hz => ?_⟩
    calc ∫ θ in Work.Spaces.Iθ, |Φ z θ|
        ≤ Real.sqrt (sliceEnergy Φ z)
            * Real.sqrt (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (2 + Work.Spaces.eta)) :=
          slice_abs_le_sqrt hint hz (fun _ hθ => hθ)
      _ ≤ Real.sqrt (sliceEnergy Φ z) * K3 :=
          mul_le_mul_of_nonneg_left sqrt_sin_int_Iθ_le (Real.sqrt_nonneg _)
      _ = K3 * Real.sqrt (sliceEnergy Φ z) := by ring
  have claim3c := claim3
  obtain ⟨C3, hC3pos, hC3⟩ := claim3c
  -- ### conjunct 4 : the boundary-layer decay
  have claim4 : ∃ C : ℝ, 0 < C ∧ ∀ z ∈ Set.Ioi (0 : ℝ), ∀ δ ∈ Set.Ioc (0 : ℝ) (π / 4),
      (∫ θ in Set.Ioo 0 δ, |Φ z θ|
          ≤ C * Real.sqrt (sliceEnergy Φ z) * δ ^ ((3 + Work.Spaces.eta) / 2)) ∧
      (∫ θ in Set.Ioo (π / 2 - δ) (π / 2), |Φ z θ|
          ≤ C * Real.sqrt (sliceEnergy Φ z) * δ ^ ((3 + Work.Spaces.eta) / 2)) := by
    refine ⟨K4, K4_pos, fun z hz δ hδ => ?_⟩
    obtain ⟨hδ0, hδ4⟩ := hδ
    obtain ⟨hL, hR⟩ := sqrt_sin_int_layer_le hδ0 hδ4
    have hsub1 : Set.Ioo (0 : ℝ) δ ⊆ Work.Spaces.Iθ := fun θ hθ =>
      ⟨le_of_lt hθ.1, by linarith [hθ.2, hδ4, Real.pi_pos]⟩
    have hsub2 : Set.Ioo (π / 2 - δ) (π / 2) ⊆ Work.Spaces.Iθ := fun θ hθ =>
      ⟨by linarith [hθ.1, hδ4, Real.pi_pos], le_of_lt hθ.2⟩
    have h1 := slice_abs_le_sqrt hint hz hsub1
    have h2 := slice_abs_le_sqrt hint hz hsub2
    refine ⟨?_, ?_⟩
    · calc ∫ θ in Set.Ioo 0 δ, |Φ z θ|
          ≤ Real.sqrt (sliceEnergy Φ z)
              * Real.sqrt (∫ θ in Set.Ioo 0 δ, (Real.sin (2 * θ)) ^ (2 + Work.Spaces.eta)) := h1
        _ ≤ Real.sqrt (sliceEnergy Φ z) * (K4 * δ ^ ((3 + Work.Spaces.eta) / 2)) :=
            mul_le_mul_of_nonneg_left hL (Real.sqrt_nonneg _)
        _ = K4 * Real.sqrt (sliceEnergy Φ z) * δ ^ ((3 + Work.Spaces.eta) / 2) := by ring
    · calc ∫ θ in Set.Ioo (π / 2 - δ) (π / 2), |Φ z θ|
          ≤ Real.sqrt (sliceEnergy Φ z)
              * Real.sqrt (∫ θ in Set.Ioo (π / 2 - δ) (π / 2),
                  (Real.sin (2 * θ)) ^ (2 + Work.Spaces.eta)) := h2
        _ ≤ Real.sqrt (sliceEnergy Φ z) * (K4 * δ ^ ((3 + Work.Spaces.eta) / 2)) :=
            mul_le_mul_of_nonneg_left hR (Real.sqrt_nonneg _)
        _ = K4 * Real.sqrt (sliceEnergy Φ z) * δ ^ ((3 + Work.Spaces.eta) / 2) := by ring
  -- ### the `z`-integrability of `sliceHk` on compact subintervals of `(0,∞)`
  have hSliceHk_Icc : ∀ a b : ℝ, 0 < a → a ≤ b →
      MeasureTheory.IntegrableOn (fun z => sliceHk α Φ z) (Set.Icc a b) := fun a b ha _ =>
    hHk_int.mono_set (fun z hz => le_trans (le_of_lt ha) hz.1)
  have hOne_Icc : ∀ a b : ℝ, 0 < a → a ≤ b →
      MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Icc a b) := by
    intro a b _ _
    haveI : MeasureTheory.IsFiniteMeasure (volume.restrict (Set.Icc a b)) := ⟨by
      rw [MeasureTheory.Measure.restrict_apply_univ, Real.volume_Icc]
      exact ENNReal.ofReal_lt_top⟩
    exact MeasureTheory.integrable_const (1 : ℝ)
  -- ### conjunct 6 : `sliceEnergy` is `z`-integrable on `[a,b]`
  have claim6 : ∀ a b : ℝ, 0 < a → a ≤ b → MeasureTheory.IntegrableOn
      (fun z => ∫ θ in Work.Spaces.Iθ, Φ z θ ^ 2 * rootWeight θ) (Set.Icc a b) := by
    intro a b ha hab
    have hs : Set.Icc a b ⊆ Work.Spaces.Iz := fun z hz => le_trans (le_of_lt ha) hz.1
    have hAESM : AEStronglyMeasurable
        (fun z => ∫ θ in Work.Spaces.Iθ, Φ z θ ^ 2 * rootWeight θ)
        (volume.restrict (Set.Icc a b)) :=
      aesm_sliceIntegral_of_subset (continuousOn_PhiSqRoot hsm) hs measurableSet_Icc
    refine MeasureTheory.Integrable.mono'
      ((hSliceHk_Icc a b ha hab).add (hOne_Icc a b ha hab)) hAESM ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with z hz
    have hz0 : 0 < z := lt_of_lt_of_le ha hz.1
    rw [Real.norm_eq_abs, abs_of_nonneg (show (0 : ℝ) ≤ ∫ θ in Work.Spaces.Iθ,
      Φ z θ ^ 2 * rootWeight θ from sliceEnergy_nonneg Φ z)]
    exact le_trans (sliceEnergy_le_sliceHk hHk' hz0) (le_add_of_nonneg_right zero_le_one)
  -- ### conjunct 5 : `√(sliceEnergy)` is `z`-integrable on `[a,b]`
  have claim5 : ∀ a b : ℝ, 0 < a → a ≤ b → MeasureTheory.IntegrableOn
      (fun z => Real.sqrt (sliceEnergy Φ z)) (Set.Icc a b) := by
    intro a b ha hab
    have hs : Set.Icc a b ⊆ Work.Spaces.Iz := fun z hz => le_trans (le_of_lt ha) hz.1
    have hAESM : AEStronglyMeasurable (fun z => Real.sqrt (sliceEnergy Φ z))
        (volume.restrict (Set.Icc a b)) :=
      Real.continuous_sqrt.comp_aestronglyMeasurable
        (aesm_sliceIntegral_of_subset (continuousOn_PhiSqRoot hsm) hs measurableSet_Icc)
    refine MeasureTheory.Integrable.mono'
      ((hSliceHk_Icc a b ha hab).add (hOne_Icc a b ha hab)) hAESM ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with z hz
    have hz0 : 0 < z := lt_of_lt_of_le ha hz.1
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact le_trans (Real.sqrt_le_sqrt (sliceEnergy_le_sliceHk hHk' hz0))
      (sqrt_le_add_one (sliceHk_nonneg Φ z))
  -- ### conjunct 7 : the slice integral `∫_θ |Φ z θ|` is `z`-integrable on `[a,b]`
  have claim7 : ∀ a b : ℝ, 0 < a → a ≤ b → MeasureTheory.IntegrableOn
      (fun z => ∫ θ in Work.Spaces.Iθ, |Φ z θ|) (Set.Icc a b) := by
    intro a b ha hab
    have hs : Set.Icc a b ⊆ Work.Spaces.Iz := fun z hz => le_trans (le_of_lt ha) hz.1
    have hAESM : AEStronglyMeasurable (fun z => ∫ θ in Work.Spaces.Iθ, |Φ z θ|)
        (volume.restrict (Set.Icc a b)) :=
      aesm_sliceIntegral_of_subset (continuousOn_absPhi hsm) hs measurableSet_Icc
    refine MeasureTheory.Integrable.mono'
      (((hSliceHk_Icc a b ha hab).add (hOne_Icc a b ha hab)).const_mul C3) hAESM ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with z hz
    have hz0 : 0 < z := lt_of_lt_of_le ha hz.1
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun θ => abs_nonneg _)]
    calc ∫ θ in Work.Spaces.Iθ, |Φ z θ| ≤ C3 * Real.sqrt (sliceEnergy Φ z) := hC3 z hz0
      _ ≤ C3 * (sliceHk α Φ z + 1) :=
          mul_le_mul_of_nonneg_left
            (le_trans (Real.sqrt_le_sqrt (sliceEnergy_le_sliceHk hHk' hz0))
              (sqrt_le_add_one (sliceHk_nonneg Φ z))) (le_of_lt hC3pos)
  -- ### conjunct 1 : the modal coefficients
  obtain ⟨Ce, hCe, heFam⟩ := Work.FTS.PhiStar.Series.eFam_sup_le
  have claim1 : ∀ m : ℕ, MeasureTheory.LocallyIntegrableOn
        (fun z => ∫ θ in Work.Spaces.Iθ,
          Φ z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ) (Set.Ioi 0) ∧
      MeasureTheory.IntegrableOn (fun z => (∫ θ in Work.Spaces.Iθ,
        Φ z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ) ^ 2
          * z ^ (-4 : ℝ)) (Set.Ioi 0) := by
    intro m
    -- the pointwise moment bound
    have hmode_le : ∀ z : ℝ, 0 < z → |modeCoeff Φ m z| ≤
        Ce * ((m : ℝ) + 1) * (∫ θ in Work.Spaces.Iθ, |Φ z θ|) := by
      intro z hz
      have hint2 := claim2 z hz
      have hbnd : ∀ θ ∈ Work.Spaces.Iθ,
          |Φ z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ| ≤
            (Ce * ((m : ℝ) + 1)) * |Φ z θ| := by
        intro θ hθ
        have h1 : |Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ Ce * ((m : ℝ) + 1) :=
          heFam m θ hθ
        have h2 : |Real.cos θ| ≤ 1 := Real.abs_cos_le_one θ
        have h3 : (0 : ℝ) ≤ Ce * ((m : ℝ) + 1) := by positivity
        calc |Φ z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ|
            = |Φ z θ| * |Work.FTS.PhiStar.Gegenbauer.eFam m θ| * |Real.cos θ| := by
              rw [abs_mul, abs_mul]
          _ ≤ |Φ z θ| * (Ce * ((m : ℝ) + 1)) * 1 :=
              mul_le_mul (mul_le_mul_of_nonneg_left h1 (abs_nonneg _)) h2 (abs_nonneg _)
                (by positivity)
          _ = (Ce * ((m : ℝ) + 1)) * |Φ z θ| := by ring
      calc |modeCoeff Φ m z|
          = |∫ θ in Work.Spaces.Iθ,
              Φ z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ| := by
            simp only [modeCoeff]
        _ ≤ ∫ θ in Work.Spaces.Iθ,
              |Φ z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ| :=
            abs_integral_le_integral_abs
        _ ≤ ∫ θ in Work.Spaces.Iθ, (Ce * ((m : ℝ) + 1)) * |Φ z θ| :=
            MeasureTheory.integral_mono_of_nonneg (Eventually.of_forall fun θ => abs_nonneg _)
              (hint2.const_mul _)
              (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc hbnd)
        _ = Ce * ((m : ℝ) + 1) * ∫ θ in Work.Spaces.Iθ, |Φ z θ| :=
            MeasureTheory.integral_const_mul _ _
    have hmode_le' : ∀ z : ℝ, 0 < z → |modeCoeff Φ m z| ≤
        Ce * ((m : ℝ) + 1) * (C3 * Real.sqrt (sliceEnergy Φ z)) := by
      intro z hz
      refine le_trans (hmode_le z hz) ?_
      exact mul_le_mul_of_nonneg_left (hC3 z hz) (by positivity)
    -- a.e. strong measurability of the moment
    have haesm_m : ∀ {s : Set ℝ}, s ⊆ Work.Spaces.Iz → MeasurableSet s →
        AEStronglyMeasurable (fun z => modeCoeff Φ m z) (volume.restrict s) := by
      intro s hs hms
      exact aesm_sliceIntegral_of_subset (continuousOn_mode hsm m) hs hms
    have hzpow_aesm : AEStronglyMeasurable (fun z : ℝ => z ^ (-4 : ℝ))
        (volume.restrict (Set.Ioi 0)) :=
      (continuousOn_id.rpow_const (fun z hz => Or.inl (ne_of_gt hz))).aestronglyMeasurable
        measurableSet_Ioi
    refine ⟨?_, ?_⟩
    · -- local integrability in `z`
      rw [MeasureTheory.locallyIntegrableOn_iff isOpen_Ioi.isLocallyClosed]
      intro k hks hk
      rcases Set.eq_empty_or_nonempty k with hk0 | hne
      · rw [hk0]
        exact MeasureTheory.integrableOn_empty
      · obtain ⟨a, hak, ha⟩ := hk.exists_isMinOn hne continuous_id.continuousOn
        obtain ⟨b, hbk, hb⟩ := hk.exists_isMaxOn hne continuous_id.continuousOn
        have ha0 : 0 < a := hks hak
        have hab : a ≤ b := ha hbk
        have hs : Set.Icc a b ⊆ Work.Spaces.Iz := fun z hz => le_trans (le_of_lt ha0) hz.1
        have hInt : MeasureTheory.IntegrableOn (fun z => modeCoeff Φ m z) (Set.Icc a b) := by
          refine MeasureTheory.Integrable.mono'
            (((hSliceHk_Icc a b ha0 hab).add (hOne_Icc a b ha0 hab)).const_mul
              (Ce * ((m : ℝ) + 1) * C3)) (haesm_m hs measurableSet_Icc) ?_
          filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with z hz
          have hz0 : 0 < z := lt_of_lt_of_le ha0 hz.1
          rw [Real.norm_eq_abs]
          calc |modeCoeff Φ m z| ≤ Ce * ((m : ℝ) + 1) * (C3 * Real.sqrt (sliceEnergy Φ z)) :=
                hmode_le' z hz0
            _ ≤ Ce * ((m : ℝ) + 1) * (C3 * (sliceHk α Φ z + 1)) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_left
                    (le_trans (Real.sqrt_le_sqrt (sliceEnergy_le_sliceHk hHk' hz0))
                      (sqrt_le_add_one (sliceHk_nonneg Φ z))) (le_of_lt hC3pos))
                  (by positivity)
            _ = (Ce * ((m : ℝ) + 1) * C3) * (sliceHk α Φ z + 1) := by ring
        exact hInt.mono_set (fun z hz => ⟨ha hz, hb hz⟩)
    · -- integrability of the squared moment against `z^{-4}`
      have hdom : ∀ z ∈ Set.Ioi (0 : ℝ),
          ‖(modeCoeff Φ m z) ^ 2 * z ^ (-4 : ℝ)‖
            ≤ (Ce * ((m : ℝ) + 1) * C3) ^ 2 * sliceHk α Φ z := by
        intro z hz
        have hb := hmode_le' z hz
        have hsq : |modeCoeff Φ m z| ^ 2
            ≤ (Ce * ((m : ℝ) + 1) * C3) ^ 2 * sliceEnergy Φ z := by
          have h1 := pow_le_pow_left₀ (abs_nonneg _) hb 2
          have h2 : (Ce * ((m : ℝ) + 1) * (C3 * Real.sqrt (sliceEnergy Φ z))) ^ 2
              = (Ce * ((m : ℝ) + 1) * C3) ^ 2 * sliceEnergy Φ z := by
            rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt (sliceEnergy_nonneg Φ z)]
            ring
          rwa [h2] at h1
        rw [Real.norm_eq_abs, abs_mul, abs_pow,
          abs_of_nonneg (Real.rpow_nonneg (le_of_lt hz) _)]
        calc |modeCoeff Φ m z| ^ 2 * z ^ (-4 : ℝ)
            ≤ ((Ce * ((m : ℝ) + 1) * C3) ^ 2 * sliceEnergy Φ z) * z ^ (-4 : ℝ) :=
              mul_le_mul_of_nonneg_right hsq (Real.rpow_nonneg (le_of_lt hz) _)
          _ = (Ce * ((m : ℝ) + 1) * C3) ^ 2 * (sliceEnergy Φ z * z ^ (-4 : ℝ)) := by ring
          _ ≤ (Ce * ((m : ℝ) + 1) * C3) ^ 2 * sliceHk α Φ z :=
              mul_le_mul_of_nonneg_left (sliceEnergy_mul_rpow_le_sliceHk hHk' hz) (sq_nonneg _)
      refine MeasureTheory.Integrable.mono'
        ((hHk_int.mono_set (s := Set.Ioi 0) (fun z hz => mem_Iz_of_mem_Ioi hz)).const_mul
          ((Ce * ((m : ℝ) + 1) * C3) ^ 2))
        (((haesm_m (fun z hz => mem_Iz_of_mem_Ioi hz) measurableSet_Ioi).pow 2).mul
          hzpow_aesm) ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
      exact hdom z hz
  exact ⟨claim1, claim2, claim3, claim4, claim5, claim6, claim7⟩


end

end Work.FTS.StrongEps.EComparison
