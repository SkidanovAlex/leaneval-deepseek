import Mathlib
import Submission.Work.A6Clean.vrLiftDataP_packetFamG_le_sum_mono
import Submission.Work.A6Clean.vrLiftDataP_packetFamG_integral_le
import Submission.Work.KMTPlan.A6.MdlSliceLinG
import Submission.Port.Aesm

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.A6Clean

open MeasureTheory Finset
open scoped ENNReal NNReal BigOperators

local notation "Circ" => Work.Analysis.IonescuWainger.Circle

noncomputable section

/-- **The floors of a lacunary scale sequence with values `≥ 1` are monotone.** -/
lemma pfGZ_floor_mono {Λ : NNReal} (hΛ : 1 < Λ) {a : ℕ → NNReal}
    (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n : ℕ, 1 ≤ a n) :
    Monotone (fun n : ℕ => Nat.floor (a n)) := by
  have hmono : Monotone a := by
    refine monotone_nat_of_le_succ fun k => ?_
    have hpos : (0 : NNReal) < a k := lt_of_lt_of_le zero_lt_one (ha1 k)
    have h1 : (Λ : NNReal) < a (k + 1) / a k := ha k
    have hmul : (Λ : NNReal) * a k < a (k + 1) := by
      rw [lt_div_iff₀ hpos] at h1
      exact h1
    calc a k = 1 * a k := (one_mul _).symm
      _ ≤ (Λ : NNReal) * a k :=
          mul_le_mul_of_nonneg_right (le_of_lt hΛ) (show (0 : NNReal) ≤ a k from bot_le)
      _ ≤ a (k + 1) := le_of_lt hmul
  exact fun m n hmn => Nat.floor_mono (hmono hmn)

/-- **In the channel `0` the `g`-side packet family is the gated lift itself**: the arithmetic
frequency set `(ℚ/ℤ)_{≤0}` is the singleton `{0}`, so the character sum collapses. -/
lemma pfGZ_packetFamG_zero (ρ : ℝ) (a : ℕ → NNReal) (l₁ k₁ k₂ : ℕ)
    (W : ℕ → Circ → ℝ → ℂ) (n : ℕ) (X : ℝ) :
    Work.KMTPlan.A6Clean.packetFamG ρ a l₁ 0 k₁ k₂ W n X
      = fun θ : ZMod (Work.KMTAreas.A7.arithQ ρ (max l₁ 0)) =>
          if Work.KMTPlan.A6.goodScale (Work.KMTAreas.A7.arithQ ρ (max l₁ 0))
              (Work.KMTPlan.A6.lcL l₁ 0 k₁ k₂) (Nat.floor (a n)) then W n 0 X else 0 := by
  funext θ
  rw [Work.KMTPlan.A6Clean.packetFamG_apply]
  by_cases hg : Work.KMTPlan.A6.goodScale (Work.KMTAreas.A7.arithQ ρ (max l₁ 0))
      (Work.KMTPlan.A6.lcL l₁ 0 k₁ k₂) (Nat.floor (a n))
  · rw [if_pos hg, if_pos hg, Work.KMTAreas.A7.iwArithFreqs_zero, Finset.sum_singleton]
    simp
  · rw [if_neg hg, if_neg hg]

/-- The nonnegative square root of a real number, as an `NNReal`. -/
noncomputable def pfGZ_sqrtNN (D : ℝ) : NNReal := ⟨Real.sqrt D, Real.sqrt_nonneg D⟩

/-- The coercion of `pfGZ_sqrtNN` to `ℝ≥0∞`. -/
lemma pfGZ_sqrtNN_coe (D : ℝ) :
    ((pfGZ_sqrtNN D : NNReal) : ENNReal) = ENNReal.ofReal (Real.sqrt D) :=
  (ENNReal.ofReal_coe_nnreal).symm

/-- **The pointwise `V^R`-datum of the height-`0` packet family is the single-channel variational
norm** of the lift, with the (datum-independent) constant `3·(#(ℚ/ℤ)_{≤0} + 2) ≤ 9`. -/
lemma pfGZ_vrLift_le (ρ : ℝ) (a : ℕ → NNReal) (l₁ k₁ k₂ : ℕ) (W : ℕ → Circ → ℝ → ℂ)
    (R : NNReal) (hR : 1 ≤ R) (hmono : Monotone (fun n : ℕ => Nat.floor (a n)))
    (Cq : ℝ) (hCq : ((3 * ((Work.Analysis.IonescuWainger.iwArithFreqs ρ 0).card + 2) : ℕ)
        : ENNReal) = ENNReal.ofReal Cq) (X : ℝ) :
    Work.KMTPlan.A6.VrLiftDataP (R : ℝ) (Work.KMTAreas.A7.arithQ ρ (max l₁ 0))
        (fun n : ℕ => Work.KMTPlan.A6Clean.packetFamG ρ a l₁ 0 k₁ k₂ W n X)
      ≤ ENNReal.ofReal Cq *
          PointwiseErgodicTheorems.variationalNorm R (fun n : ℕ => W n (0 : Circ) X) := by
  have h1 := Work.A6Clean.vrLiftDataP_packetFamG_le_sum_mono ρ a l₁ 0 k₁ k₂ W R hR X hmono
  have hsum : (∑ β ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ 0,
        PointwiseErgodicTheorems.variationalNorm R (fun n : ℕ => W n β X))
      = PointwiseErgodicTheorems.variationalNorm R (fun n : ℕ => W n (0 : Circ) X) := by
    rw [Work.KMTAreas.A7.iwArithFreqs_zero, Finset.sum_singleton]
  rw [hsum, hCq] at h1
  exact h1

theorem PacketFamGZeroUniform (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (R : NNReal) (hR : 2 < R) (j₂ : ℤ) (hj₂ : j₂ ∈ ({-1, 0, 1} : Finset ℤ)) : ∃ A : ℝ, 0 ≤ A ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ K : NNReal → NNReal, ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ k₁ k₂ : ℕ) (t : ℝ) (g : ℤ → ℂ) (W : ℕ → Work.Analysis.IonescuWainger.Circle → ℝ → ℂ), 1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) → MeasureTheory.MemLp g 2 MeasureTheory.Measure.count → t ∈ Set.Icc (1 / 2 : ℝ) 1 → (k₂ = 0 → j₂ ≠ -1) → (∀ (n : ℕ) (α : Work.Analysis.IonescuWainger.Circle), Work.KMTAreas.A7Rep.HasRealFreqSupport (W n α) (Set.Icc (-(1 / 4 : ℝ)) (1 / 4))) → (∀ n : ℕ, ∀ α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ 0, ∀ x : ℤ, W n α (x : ℝ) = Work.KMTAreas.A7.winConvR (Work.KMTAreas.A7.mStargF P.natDegree (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ 0 k₁ k₂))) (Work.KMTAreas.A7.winModR (-α) (Work.KMTPlan.A6.mdlSliceG ρ P C₀ a l₁ 0 k₁ k₂ j₂ t g n)) x) → ∫⁻ X : ℝ, (Work.KMTPlan.A6.VrLiftDataP (R : ℝ) (Work.KMTAreas.A7.arithQ ρ (max l₁ 0)) (fun n : ℕ => Work.KMTPlan.A6Clean.packetFamG ρ a l₁ 0 k₁ k₂ W n X)) ^ (2 : ℕ) ≤ (K Λ : ENNReal) ^ (2 : ℕ) * (ENNReal.ofReal (Work.KMTAreas.A7.lossWeight A ρ l₁ 0 k₁ k₂)) ^ (2 : ℕ) * (MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count) ^ (2 : ℕ) := by
  classical
  -- the model input, with all constants chosen before the datum
  obtain ⟨A₀, hA₀, ρ₀, hρ0pos, hMdl⟩ := Work.KMTPlan.A6.MdlSliceLinG P hd C₀ hC₀ R hR j₂ hj₂
  refine ⟨A₀, hA₀, ρ₀, hρ0pos, ?_⟩
  intro ρ hρ hρle
  have hR1 : (1 : NNReal) ≤ R := le_trans (by norm_num) (le_of_lt hR)
  -- the two uniform constants (sampling and window-kernel mass)
  obtain ⟨Cs, hCspos, hCs⟩ := Work.KMTAreas.A7Hi.vrsdIntegralLeSamples 2 (by norm_num) R hR1
  obtain ⟨Cst, hCstpos, hCst⟩ := Work.A7.exists_cw_mStargF_tsum_le P.natDegree (by omega)
  obtain ⟨K₀, hK₀⟩ := hMdl ρ hρ hρle
  -- the packet constant `3·(#(ℚ/ℤ)_{≤0} + 2) = 9`
  have hcard : (Work.Analysis.IonescuWainger.iwArithFreqs ρ 0).card = 1 := by
    rw [Work.KMTAreas.A7.iwArithFreqs_zero]
    simp
  let Kf : NNReal → NNReal := fun Λ => pfGZ_sqrtNN (9 ^ 2 * Cs * Cst ^ 2) * K₀ Λ
  refine ⟨Kf, ?_⟩
  intro a Λ l₁ k₁ k₂ t g W hΛ ha ha1 hg ht hk₂ hWb hWs
  -- abbreviations
  let V0 : ℝ → ENNReal := fun X => PointwiseErgodicTheorems.variationalNorm R
    (fun n : ℕ => W n (0 : Circ) X)
  let G : ℤ → ENNReal := fun x => PointwiseErgodicTheorems.variationalNorm R
    (fun n : ℕ => Work.KMTPlan.A6.mdlSliceG ρ P C₀ a l₁ 0 k₁ k₂ j₂ t g n x)
  let kern : ℤ → ENNReal := fun j => ‖Work.KMTAreas.A7.cw
    (Work.KMTAreas.A7.mStargF P.natDegree (Work.KMTAreas.A7.uScale ρ
      (Work.KMTPlan.A6.lcL l₁ 0 k₁ k₂))) j‖ₑ
  have hmono : Monotone (fun n : ℕ => Nat.floor (a n)) := pfGZ_floor_mono hΛ ha ha1
  have hCq : ((3 * ((Work.Analysis.IonescuWainger.iwArithFreqs ρ 0).card + 2) : ℕ) : ENNReal)
      = ENNReal.ofReal 9 := by
    rw [hcard]
    norm_num
  -- measurability of the single channel
  have hV0meas : Measurable V0 := by
    show Measurable (fun X : ℝ => PointwiseErgodicTheorems.variationalNorm R
      (fun n : ℕ => W n (0 : Circ) X))
    exact Work.KMTPlan.A6.measurable_variationalNorm_of_hasRealFreqSupport (r := R)
      (lt_of_lt_of_le zero_lt_one hR1) (fun n : ℕ => fun X : ℝ => W n (0 : Circ) X)
      (fun n => hWb n (0 : Circ))
  have hV0sqmeas : Measurable (fun X : ℝ => (V0 X) ^ (2 : ℕ)) := hV0meas.pow_const 2
  -- (A) the pointwise comparison with the single channel
  have hpoint : ∀ X : ℝ, Work.KMTPlan.A6.VrLiftDataP (R : ℝ)
        (Work.KMTAreas.A7.arithQ ρ (max l₁ 0))
        (fun n : ℕ => Work.KMTPlan.A6Clean.packetFamG ρ a l₁ 0 k₁ k₂ W n X)
      ≤ ENNReal.ofReal 9 * V0 X := by
    intro X
    have h := pfGZ_vrLift_le ρ a l₁ k₁ k₂ W R hR1 hmono 9 (by rw [hCq]) X
    simpa only [V0] using h
  -- (B) the sampling comparison for the single channel
  obtain ⟨amp, hamp⟩ : ∃ amp : ℕ → ℝ → ℂ,
      (∀ n : ℕ, Integrable (amp n)) ∧
      (∀ (n : ℕ) (ξ : ℝ), ξ ∉ Set.Icc (-(1 / 4 : ℝ)) (1 / 4) → amp n ξ = 0) ∧
      (∀ (n : ℕ) (x : ℝ), W n (0 : Circ) x = FourierTransformInv.fourierInv (amp n) x) := by
    choose amp hamp using fun n : ℕ => hWb n (0 : Circ)
    exact ⟨amp, fun n => (hamp n).1, fun n ξ hξ => (hamp n).2.1 ξ hξ,
      fun n x => (hamp n).2.2 x⟩
  have hsamp_raw := hCs amp (fun n => hamp.1 n) (fun n ξ hξ => hamp.2.1 n ξ hξ)
  have hsamp : ∫⁻ X : ℝ, (V0 X) ^ (2 : ℕ) ≤ ENNReal.ofReal Cs *
      ∑' m : ℤ, (V0 ((m : ℤ) : ℝ)) ^ (2 : ℕ) := by
    have hI : ∫⁻ X : ℝ, (V0 X) ^ (2 : ℕ) = ∫⁻ X : ℝ,
        (PointwiseErgodicTheorems.variationalNorm R
          (fun n : ℕ => FourierTransformInv.fourierInv (amp n) X)) ^ (2 : ℕ) := by
      refine lintegral_congr (fun X => ?_)
      have hfam : (fun n : ℕ => W n (0 : Circ) X)
          = fun n : ℕ => FourierTransformInv.fourierInv (amp n) X :=
        funext (fun n => hamp.2.2 n X)
      show (PointwiseErgodicTheorems.variationalNorm R (fun n : ℕ => W n (0 : Circ) X)) ^ (2 : ℕ)
          = _
      rw [hfam]
    have hS : (∑' m : ℤ, (V0 ((m : ℤ) : ℝ)) ^ (2 : ℕ)) = ∑' m : ℤ,
        (PointwiseErgodicTheorems.variationalNorm R
          (fun n : ℕ => FourierTransformInv.fourierInv (amp n) ((m : ℤ) : ℝ))) ^ (2 : ℕ) := by
      refine tsum_congr (fun m => ?_)
      have hfam : (fun n : ℕ => W n (0 : Circ) ((m : ℤ) : ℝ))
          = fun n : ℕ => FourierTransformInv.fourierInv (amp n) ((m : ℤ) : ℝ) :=
        funext (fun n => hamp.2.2 n ((m : ℤ) : ℝ))
      show (PointwiseErgodicTheorems.variationalNorm R
          (fun n : ℕ => W n (0 : Circ) ((m : ℤ) : ℝ))) ^ (2 : ℕ) = _
      rw [hfam]
    rw [hI, hS]
    simpa only [← pow_two_eq_rpow_two] using hsamp_raw
  -- (C) the integer samples are the window convolution of the model slice
  have hsampint : ∀ m : ℤ, V0 ((m : ℤ) : ℝ) ≤ ∑' j : ℤ, kern j * G (m - j) := by
    intro m
    have h0mem : (0 : Circ) ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ 0 := by
      rw [Work.KMTAreas.A7.iwArithFreqs_zero]
      simp
    have hWu : ∀ n : ℕ, W n (0 : Circ) ((m : ℤ) : ℝ) = Work.KMTAreas.A7.winConvR
        (Work.KMTAreas.A7.mStargF P.natDegree (Work.KMTAreas.A7.uScale ρ
          (Work.KMTPlan.A6.lcL l₁ 0 k₁ k₂)))
        (Work.KMTAreas.A7.winModR (-(0 : Circ))
          (Work.KMTPlan.A6.mdlSliceG ρ P C₀ a l₁ 0 k₁ k₂ j₂ t g n)) m :=
      fun n => hWs n (0 : Circ) h0mem m
    have heq : V0 ((m : ℤ) : ℝ) = PointwiseErgodicTheorems.variationalNorm R (fun n : ℕ =>
        Work.KMTAreas.A7.winConvR (Work.KMTAreas.A7.mStargF P.natDegree
          (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ 0 k₁ k₂)))
          (Work.KMTAreas.A7.winModR (-(0 : Circ))
            (Work.KMTPlan.A6.mdlSliceG ρ P C₀ a l₁ 0 k₁ k₂ j₂ t g n)) m) := by
      show (PointwiseErgodicTheorems.variationalNorm R
          (fun n : ℕ => W n (0 : Circ) ((m : ℤ) : ℝ))) = _
      congr 1
      funext n
      exact hWu n
    rw [heq]
    have h := Work.A6Clean.vr_winConvR_winMod_le R hR1
      (Work.KMTAreas.A7.mStargF P.natDegree (Work.KMTAreas.A7.uScale ρ
        (Work.KMTPlan.A6.lcL l₁ 0 k₁ k₂))) (0 : Circ)
      (fun n : ℕ => Work.KMTPlan.A6.mdlSliceG ρ P C₀ a l₁ 0 k₁ k₂ j₂ t g n) m
    refine h.trans ?_
    refine ENNReal.tsum_le_tsum (fun j => ?_)
    refine mul_le_mul' le_rfl ?_
    exact le_of_eq (rfl : G (m - j) = _)
  -- (D) Young's inequality on the samples
  have hsumm : Summable (fun j : ℤ => ‖Work.KMTAreas.A7.cw
      (Work.KMTAreas.A7.mStargF P.natDegree (Work.KMTAreas.A7.uScale ρ
        (Work.KMTPlan.A6.lcL l₁ 0 k₁ k₂))) j‖) :=
    Work.KMTAreas.A7.summable_norm_cw_mStargF P _
  have hyoung : (∑' m : ℤ, (V0 ((m : ℤ) : ℝ)) ^ (2 : ℕ))
      ≤ (∑' j : ℤ, kern j) ^ (2 : ℕ) * ∑' m : ℤ, (G m) ^ (2 : ℕ) :=
    (ENNReal.tsum_le_tsum (fun m => pow_le_pow_left' (hsampint m) 2)).trans
      (Work.A6Clean.ennreal_tsum_conv_sq_le kern G)
  -- (E) the `ℓ²`-sum of the model variational datum
  have hGle : (∑' m : ℤ, (G m) ^ (2 : ℕ))
      ≤ (MeasureTheory.eLpNorm G 2 MeasureTheory.Measure.count) ^ (2 : ℕ) := by
    have hE : MeasureTheory.eLpNorm G 2 MeasureTheory.Measure.count
        = (∫⁻ x : ℤ, ‖G x‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count) ^ ((1 : ℝ) / 2) := by
      rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) (by norm_num) (by norm_num)]
      norm_num
    rw [hE]
    rw [show (∑' m : ℤ, (G m) ^ (2 : ℕ))
        = ∫⁻ x : ℤ, ‖G x‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count from by
      rw [MeasureTheory.lintegral_count]
      exact tsum_congr (fun m => by rw [enorm_eq_self, pow_two_eq_rpow_two])]
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    rw [show ((1 : ℝ) / 2 * ((2 : ℕ) : ℝ)) = 1 from by norm_num, ENNReal.rpow_one]
  -- (F) the uniform mass bound on the window kernel
  have hmass1 : (∑' j : ℤ, kern j) = ENNReal.ofReal (∑' j : ℤ, ‖Work.KMTAreas.A7.cw
      (Work.KMTAreas.A7.mStargF P.natDegree (Work.KMTAreas.A7.uScale ρ
        (Work.KMTPlan.A6.lcL l₁ 0 k₁ k₂))) j‖) := by
    show (∑' j : ℤ, ‖Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStargF P.natDegree
        (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ 0 k₁ k₂))) j‖ₑ) = _
    rw [tsum_congr (f := fun j : ℤ => ‖Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStargF P.natDegree
        (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ 0 k₁ k₂))) j‖ₑ)
      (g := fun j : ℤ => ENNReal.ofReal ‖Work.KMTAreas.A7.cw
        (Work.KMTAreas.A7.mStargF P.natDegree (Work.KMTAreas.A7.uScale ρ
          (Work.KMTPlan.A6.lcL l₁ 0 k₁ k₂))) j‖)
      (fun j => Work.A6Clean.enorm_complex_eq_ofReal _)]
    exact (ENNReal.ofReal_tsum_of_nonneg (fun j => norm_nonneg _) hsumm).symm
  have hmass2 : (∑' j : ℤ, kern j) ≤ ENNReal.ofReal Cst := by
    rw [hmass1]
    exact ENNReal.ofReal_le_ofReal (hCst (Work.KMTAreas.A7.uScale ρ
      (Work.KMTPlan.A6.lcL l₁ 0 k₁ k₂)))
  have hmass : (∑' j : ℤ, kern j) ^ (2 : ℕ) ≤ ENNReal.ofReal (Cst ^ 2) := by
    rw [ENNReal.ofReal_pow hCstpos.le]
    exact pow_le_pow_left' hmass2 2
  -- (G) the model input
  have hmodel : MeasureTheory.eLpNorm G 2 MeasureTheory.Measure.count
      ≤ (K₀ Λ : ENNReal) * ENNReal.ofReal (Work.KMTAreas.A7.lossWeight A₀ ρ l₁ 0 k₁ k₂)
        * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
    have h := hK₀ a Λ l₁ 0 k₁ k₂ t g hΛ ha ha1 ht hk₂
    have heq : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R (fun n : ℕ =>
        if Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ 0 k₁ k₂ n then
          Work.KMTAreas.A7.Tle ρ 0 (Work.KMTPlan.A6.varphitildeNtj P (Nat.floor (a n)) k₂ j₂ t)
            (Work.KMTPlan.A6.mdlG ρ P (Work.KMTAreas.A7.uScale ρ (max (max l₁ 0) (max k₁ k₂)))
              0 g) x
        else 0)) = G := by
      funext x
      show (PointwiseErgodicTheorems.variationalNorm R (fun n : ℕ =>
        if Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ 0 k₁ k₂ n then
          Work.KMTAreas.A7.Tle ρ 0 (Work.KMTPlan.A6.varphitildeNtj P (Nat.floor (a n)) k₂ j₂ t)
            (Work.KMTPlan.A6.mdlG ρ P (Work.KMTAreas.A7.uScale ρ (max (max l₁ 0) (max k₁ k₂)))
              0 g) x
        else 0)) = PointwiseErgodicTheorems.variationalNorm R (fun n : ℕ =>
          Work.KMTPlan.A6.mdlSliceG ρ P C₀ a l₁ 0 k₁ k₂ j₂ t g n x)
      congr 1
      funext n
      by_cases hc : Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ 0 k₁ k₂ n
      · simp only [hc, if_true, Work.KMTPlan.A6.mdlSliceG]
      · simp only [hc, if_false, Work.KMTPlan.A6.mdlSliceG]
        rfl
    rw [heq] at h
    exact h
  -- (H) the final chain
  have hD0 : 0 ≤ 9 ^ 2 * Cs * Cst ^ 2 := by positivity
  have hKsq : (Kf Λ : ENNReal) ^ (2 : ℕ)
      = ENNReal.ofReal (9 ^ 2 * Cs * Cst ^ 2) * (K₀ Λ : ENNReal) ^ (2 : ℕ) := by
    have h : (Kf Λ : ENNReal)
        = (pfGZ_sqrtNN (9 ^ 2 * Cs * Cst ^ 2) : ENNReal) * (K₀ Λ : ENNReal) := rfl
    rw [h, pfGZ_sqrtNN_coe, mul_pow, ← ENNReal.ofReal_pow (Real.sqrt_nonneg _),
      Real.sq_sqrt hD0]
  calc ∫⁻ X : ℝ, (Work.KMTPlan.A6.VrLiftDataP (R : ℝ) (Work.KMTAreas.A7.arithQ ρ (max l₁ 0))
        (fun n : ℕ => Work.KMTPlan.A6Clean.packetFamG ρ a l₁ 0 k₁ k₂ W n X)) ^ (2 : ℕ)
      ≤ ENNReal.ofReal 9 ^ (2 : ℕ) * ∫⁻ X : ℝ, (V0 X) ^ (2 : ℕ) := by
        calc ∫⁻ X : ℝ, (Work.KMTPlan.A6.VrLiftDataP (R : ℝ) (Work.KMTAreas.A7.arithQ ρ (max l₁ 0))
              (fun n : ℕ => Work.KMTPlan.A6Clean.packetFamG ρ a l₁ 0 k₁ k₂ W n X)) ^ (2 : ℕ)
            ≤ ∫⁻ X : ℝ, (ENNReal.ofReal 9 * V0 X) ^ (2 : ℕ) :=
              lintegral_mono (fun X => pow_le_pow_left' (hpoint X) 2)
          _ = ENNReal.ofReal 9 ^ (2 : ℕ) * ∫⁻ X : ℝ, (V0 X) ^ (2 : ℕ) := by
              rw [← lintegral_const_mul ((ENNReal.ofReal 9) ^ (2 : ℕ)) hV0sqmeas]
              refine lintegral_congr (fun X => ?_)
              rw [mul_pow]
    _ ≤ ENNReal.ofReal 9 ^ (2 : ℕ) * (ENNReal.ofReal Cs *
          ∑' m : ℤ, (V0 ((m : ℤ) : ℝ)) ^ (2 : ℕ)) := mul_le_mul' le_rfl hsamp
    _ ≤ ENNReal.ofReal 9 ^ (2 : ℕ) * (ENNReal.ofReal Cs *
          ((∑' j : ℤ, kern j) ^ (2 : ℕ) * ∑' m : ℤ, (G m) ^ (2 : ℕ))) :=
        mul_le_mul' le_rfl (mul_le_mul' le_rfl hyoung)
    _ ≤ ENNReal.ofReal 9 ^ (2 : ℕ) * (ENNReal.ofReal Cs *
          (ENNReal.ofReal (Cst ^ 2) * ∑' m : ℤ, (G m) ^ (2 : ℕ))) :=
        mul_le_mul' le_rfl (mul_le_mul' le_rfl (mul_le_mul' hmass le_rfl))
    _ ≤ ENNReal.ofReal 9 ^ (2 : ℕ) * (ENNReal.ofReal Cs *
          (ENNReal.ofReal (Cst ^ 2) *
            (MeasureTheory.eLpNorm G 2 MeasureTheory.Measure.count) ^ (2 : ℕ))) :=
        mul_le_mul' le_rfl (mul_le_mul' le_rfl (mul_le_mul' le_rfl hGle))
    _ = ENNReal.ofReal (9 ^ 2 * Cs * Cst ^ 2) *
          (MeasureTheory.eLpNorm G 2 MeasureTheory.Measure.count) ^ (2 : ℕ) := by
        rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 9 ^ 2 * Cs),
          ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 9 ^ 2),
          ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 9)]
        ring
    _ ≤ ENNReal.ofReal (9 ^ 2 * Cs * Cst ^ 2) *
          ((K₀ Λ : ENNReal) * ENNReal.ofReal (Work.KMTAreas.A7.lossWeight A₀ ρ l₁ 0 k₁ k₂)
            * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count) ^ (2 : ℕ) :=
        mul_le_mul' le_rfl (pow_le_pow_left' hmodel 2)
    _ = (Kf Λ : ENNReal) ^ (2 : ℕ)
          * (ENNReal.ofReal (Work.KMTAreas.A7.lossWeight A₀ ρ l₁ 0 k₁ k₂)) ^ (2 : ℕ)
          * (MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count) ^ (2 : ℕ) := by
        rw [hKsq, mul_pow, mul_pow]
        ring

end

end Work.A6Clean
