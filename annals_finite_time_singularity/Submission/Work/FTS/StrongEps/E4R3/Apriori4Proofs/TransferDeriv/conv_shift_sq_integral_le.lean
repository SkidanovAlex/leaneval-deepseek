import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Order.Group.Lattice
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces.dabsIntLe
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces.integrable_mul_of_sq_integrable
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces.integral_mul_le_sqrt_mul_sqrt
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces.shiftNormLe

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv

open MeasureTheory

/-!
# The weighted `L²` Young inequality for the plane convolution

`conv_shift_sq_integral_le`: if `k` is integrable with `∫ |k| ≤ 1` and supported in the `ℓ¹`-ball
of radius `2ε`, and `Q ≥ 0` is a weight which is comparable to its translates
(`Q y ≤ e^{Cw |p|₁} Q (y + p)`), then the convolution `k * G` satisfies

  `∫ y, Q y * (∫ p, k p * G (y - p))² ≤ e^{2 Cw ε} ∫ y, Q y * G y²`,

and the left-hand side is integrable as soon as `Q G²` is.

The proof is the weighted Young inequality: the pointwise Cauchy–Schwarz estimate in the finite
measure `|k p| dp` (carried out in `ℝ≥0∞`, so that no a-priori finiteness of
`∫ p, |k p| G (y - p)²` is needed), the weight-shift bound `shiftNormLe` in the `p`-variable, and
Tonelli's theorem.
-/

/-- `x ^ (1/2) * x ^ (1/2) = x` for `x : ℝ≥0∞`. -/
theorem ennreal_half_mul_self (x : ENNReal) : x ^ (1/2:ℝ) * x ^ (1/2:ℝ) = x := by
  rcases eq_or_ne x ⊤ with h | h
  · simp [h]
  · rw [← ENNReal.rpow_add_of_add_pos h (1/2) (1/2) (by norm_num)]
    norm_num

/-- `(x ^ (1/2)) ^ 2 = x` for `x : ℝ≥0∞`. -/
theorem ennreal_half_sq (x : ENNReal) : (x ^ (1/2:ℝ)) ^ 2 = x := by
  rw [pow_two, ennreal_half_mul_self]

/-- `(x ^ 2) ^ (1/2) = x` for `x : ℝ≥0∞`. -/
theorem ennreal_sq_half (x : ENNReal) : (x ^ 2) ^ (1/2:ℝ) = x := by
  rw [← ENNReal.rpow_natCast x 2, ← ENNReal.rpow_mul,
    show ((2:ℕ):ℝ) * (1/2) = 1 by norm_num, ENNReal.rpow_one]

/-- **Cauchy–Schwarz for `ℝ≥0∞`-valued functions**: `(∫ A C)² ≤ (∫ A) (∫ A C²)`.

Equivalently Cauchy–Schwarz in the measure `A dμ` for the functions `1` and `C`. This is the form
of the estimate that requires no finiteness of `∫ A C²`; both sides are allowed to be `⊤`. -/
theorem ennreal_cs_sq {α : Type*} [MeasurableSpace α] {μ : Measure α} {A C : α → ENNReal}
    (hA : AEMeasurable A μ) (hC : AEMeasurable C μ) :
    (∫⁻ a, A a * C a ∂μ) ^ 2 ≤ (∫⁻ a, A a ∂μ) * ∫⁻ a, A a * (C a) ^ 2 ∂μ := by
  have hg : AEMeasurable (fun a => A a * C a ^ 2) μ := hA.mul (hC.pow_const 2)
  have hmain := ENNReal.lintegral_mul_norm_pow_le hA hg (p := 1/2) (q := 1/2)
    (by norm_num) (by norm_num) (by norm_num)
  have hL : (fun a => A a ^ (1/2:ℝ) * (A a * C a ^ 2) ^ (1/2:ℝ)) = (fun a => A a * C a) := by
    funext a
    have h1 : (A a * C a ^ 2) ^ (1/2:ℝ) = A a ^ (1/2:ℝ) * C a := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 1/2), ennreal_sq_half]
    rw [h1, ← mul_assoc, ennreal_half_mul_self]
  rw [hL] at hmain
  have hsq : (∫⁻ a, A a * C a ∂μ) * (∫⁻ a, A a * C a ∂μ)
      ≤ ((∫⁻ a, A a ∂μ) ^ (1/2:ℝ) * (∫⁻ a, A a * C a ^ 2 ∂μ) ^ (1/2:ℝ)) *
        ((∫⁻ a, A a ∂μ) ^ (1/2:ℝ) * (∫⁻ a, A a * C a ^ 2 ∂μ) ^ (1/2:ℝ)) :=
    mul_le_mul' hmain hmain
  calc (∫⁻ a, A a * C a ∂μ) ^ 2
      = (∫⁻ a, A a * C a ∂μ) * (∫⁻ a, A a * C a ∂μ) := pow_two _
    _ ≤ ((∫⁻ a, A a ∂μ) ^ (1/2:ℝ) * (∫⁻ a, A a * C a ^ 2 ∂μ) ^ (1/2:ℝ)) *
        ((∫⁻ a, A a ∂μ) ^ (1/2:ℝ) * (∫⁻ a, A a * C a ^ 2 ∂μ) ^ (1/2:ℝ)) := hsq
    _ = ((∫⁻ a, A a ∂μ) ^ (1/2:ℝ)) ^ 2 * ((∫⁻ a, A a * C a ^ 2 ∂μ) ^ (1/2:ℝ)) ^ 2 := by
        rw [← pow_two, mul_pow]
    _ = (∫⁻ a, A a ∂μ) * ∫⁻ a, A a * C a ^ 2 ∂μ := by rw [ennreal_half_sq, ennreal_half_sq]

set_option linter.unusedVariables false in
theorem conv_shift_sq_integral_le {k Q G : ℝ × ℝ → ℝ} {Cw ε : ℝ}
    (hε0 : 0 < ε) (hCw : 0 ≤ Cw)
    (hk : MeasureTheory.Integrable k) (hk1 : (∫ p : ℝ × ℝ, |k p|) ≤ 1)
    (hksupp : ∀ p : ℝ × ℝ, k p ≠ 0 → |p.1| + |p.2| ≤ 2 * ε)
    (hQ0 : ∀ y : ℝ × ℝ, 0 ≤ Q y) (hQm : Measurable Q)
    (hQsh' : ∀ y p : ℝ × ℝ, Q y ≤ Real.exp (Cw * (|p.1| + |p.2|)) * Q (y + p))
    (hGm : Measurable G)
    (hconv : ∀ y : ℝ × ℝ, MeasureTheory.Integrable (fun p : ℝ × ℝ => k p * G (y - p)))
    (hI : MeasureTheory.Integrable (fun y : ℝ × ℝ => Q y * G y ^ 2)) :
    MeasureTheory.Integrable (fun y : ℝ × ℝ => Q y * (∫ p : ℝ × ℝ, k p * G (y - p)) ^ 2)
      ∧ (∫ y : ℝ × ℝ, Q y * (∫ p : ℝ × ℝ, k p * G (y - p)) ^ 2)
          ≤ Real.exp (2 * Cw * ε) * (∫ y : ℝ × ℝ, Q y * G y ^ 2) := by
  classical
  set M : ℝ := ∫ p : ℝ × ℝ, |k p| with hM
  set T : ℝ := ∫ y : ℝ × ℝ, Q y * G y ^ 2 with hT
  set E : ℝ := Real.exp (2 * Cw * ε) with hE
  have hKint : MeasureTheory.Integrable (fun p : ℝ × ℝ => |k p|) := hk.abs
  have hK0 : ∀ p : ℝ × ℝ, 0 ≤ |k p| := fun p => abs_nonneg _
  have hM0 : 0 ≤ M := by rw [hM]; exact MeasureTheory.integral_nonneg hK0
  have hM1 : M ≤ 1 := by rw [hM]; exact hk1
  have hT0 : 0 ≤ T := by
    rw [hT]
    exact MeasureTheory.integral_nonneg (fun y => mul_nonneg (hQ0 y) (sq_nonneg _))
  have hE0 : 0 ≤ E := by rw [hE]; exact Real.exp_nonneg _
  have hkae : AEMeasurable (fun p : ℝ × ℝ => |k p|) := hk.aemeasurable.abs
  -- the forward shift bound for the weight `Q`
  have hQfwd : ∀ y p : ℝ × ℝ, Q (y + p) ≤ Real.exp (Cw * (|p.1| + |p.2|)) * Q y := by
    intro y p
    simpa using hQsh' (y + p) (-p)
  -- the weighted `L²` shift bound (`shiftNormLe`)
  have hshift : ∀ p : ℝ × ℝ,
      MeasureTheory.Integrable (fun y : ℝ × ℝ => Q y * G (y - p) ^ 2) ∧
        (∫ y : ℝ × ℝ, Q y * G (y - p) ^ 2)
          ≤ Real.exp (Cw * (|p.1| + |p.2|)) * T := by
    intro p
    have h := Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces.shiftNormLe
      hCw hQ0 hQm hQfwd hGm hI p
    rw [hT]
    exact h
  -- the exponential moment of the kernel
  have hKexp : ∀ p : ℝ × ℝ, |k p| * Real.exp (Cw * (|p.1| + |p.2|)) ≤ |k p| * E := by
    intro p
    rcases eq_or_ne (k p) 0 with hp | hp
    · simp [hp]
    · have h1 : |p.1| + |p.2| ≤ 2 * ε := hksupp p hp
      rw [hE]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (abs_nonneg _)
      calc Cw * (|p.1| + |p.2|) ≤ Cw * (2 * ε) := mul_le_mul_of_nonneg_left h1 hCw
        _ = 2 * Cw * ε := by ring
  have hKexpInt : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => |k p| * Real.exp (Cw * (|p.1| + |p.2|))) := by
    refine (hKint.mul_const E).mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
    · exact hk.abs.aestronglyMeasurable.mul
        ((Real.continuous_exp.measurable.comp (measurable_const.mul
          (measurable_fst.abs.add measurable_snd.abs))).aestronglyMeasurable)
    · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (Real.exp_nonneg _))]
      exact hKexp p
  have hKexpBound : (∫ p : ℝ × ℝ, |k p| * Real.exp (Cw * (|p.1| + |p.2|))) ≤ E * M := by
    have hm := MeasureTheory.integral_mono hKexpInt (hKint.mul_const E) hKexp
    rw [MeasureTheory.integral_mul_const] at hm
    rw [hM]
    exact le_trans hm (le_of_eq (mul_comm _ _))
  -- ## the pointwise Cauchy–Schwarz bound
  have hpt : ∀ y : ℝ × ℝ, ENNReal.ofReal (Q y * (∫ p : ℝ × ℝ, k p * G (y - p)) ^ 2)
      ≤ ENNReal.ofReal M * ∫⁻ p, ENNReal.ofReal (Q y * (|k p| * G (y - p) ^ 2)) := by
    intro y
    set c : ℝ := ∫ p : ℝ × ℝ, k p * G (y - p) with hc
    have hcint : MeasureTheory.Integrable (fun p : ℝ × ℝ => k p * G (y - p)) := hconv y
    have hA : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal |k p|) := hkae.ennreal_ofReal
    have hC : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal |G (y - p)|) :=
      ((hGm.comp (measurable_const.sub measurable_id)).aemeasurable.abs).ennreal_ofReal
    have hcs := ennreal_cs_sq hA hC
    -- bound the left factor by the `lintegral`
    have h1 : ENNReal.ofReal |c| ≤ ∫⁻ p, ENNReal.ofReal (|k p| * |G (y - p)|) := by
      rw [hc]
      calc ENNReal.ofReal |∫ p : ℝ × ℝ, k p * G (y - p)|
          ≤ ENNReal.ofReal (∫ p : ℝ × ℝ, |k p * G (y - p)|) :=
            ENNReal.ofReal_le_ofReal MeasureTheory.abs_integral_le_integral_abs
        _ = ∫⁻ p, ENNReal.ofReal (|k p * G (y - p)|) :=
            MeasureTheory.ofReal_integral_eq_lintegral_ofReal hcint.abs
              (Filter.Eventually.of_forall fun p => abs_nonneg _)
        _ = ∫⁻ p, ENNReal.ofReal (|k p| * |G (y - p)|) :=
            MeasureTheory.lintegral_congr (fun p => by rw [abs_mul])
    -- the rewritten Cauchy–Schwarz
    have hcs' : (∫⁻ p, ENNReal.ofReal (|k p| * |G (y - p)|)) ^ 2
        ≤ ENNReal.ofReal M * ∫⁻ p, ENNReal.ofReal (|k p| * G (y - p) ^ 2) := by
      have hL : (∫⁻ p, ENNReal.ofReal (|k p| * |G (y - p)|))
          = ∫⁻ p, ENNReal.ofReal |k p| * ENNReal.ofReal |G (y - p)| :=
        MeasureTheory.lintegral_congr (fun p => ENNReal.ofReal_mul (abs_nonneg (k p)))
      have hR1 : (∫⁻ p : ℝ × ℝ, ENNReal.ofReal |k p|) = ENNReal.ofReal M := by
        rw [hM]
        exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hKint
          (Filter.Eventually.of_forall hK0)).symm
      have hR2 : (∫⁻ p, ENNReal.ofReal |k p| * (ENNReal.ofReal |G (y - p)|) ^ 2)
          = ∫⁻ p, ENNReal.ofReal (|k p| * G (y - p) ^ 2) :=
        MeasureTheory.lintegral_congr (fun p => by
          rw [← ENNReal.ofReal_pow (abs_nonneg (G (y - p))) 2, sq_abs,
            ENNReal.ofReal_mul (abs_nonneg (k p))])
      calc (∫⁻ p, ENNReal.ofReal (|k p| * |G (y - p)|)) ^ 2
          = (∫⁻ p, ENNReal.ofReal |k p| * ENNReal.ofReal |G (y - p)|) ^ 2 := by rw [hL]
        _ ≤ (∫⁻ p, ENNReal.ofReal |k p|)
              * ∫⁻ p, ENNReal.ofReal |k p| * (ENNReal.ofReal |G (y - p)|) ^ 2 := hcs
        _ = ENNReal.ofReal M * ∫⁻ p, ENNReal.ofReal (|k p| * G (y - p) ^ 2) := by rw [hR1, hR2]
    have h2 : (ENNReal.ofReal |c|) ^ 2
        ≤ ENNReal.ofReal M * ∫⁻ p, ENNReal.ofReal (|k p| * G (y - p) ^ 2) :=
      le_trans (pow_le_pow_left' h1 2) hcs'
    -- transport the weight `Q y` inside the integral
    have h3 : ENNReal.ofReal (Q y * c ^ 2) = ENNReal.ofReal (Q y) * (ENNReal.ofReal |c|) ^ 2 := by
      rw [ENNReal.ofReal_mul (hQ0 y), ← ENNReal.ofReal_pow (abs_nonneg c) 2, sq_abs]
    have h4 : ENNReal.ofReal (Q y) * (ENNReal.ofReal M
          * ∫⁻ p, ENNReal.ofReal (|k p| * G (y - p) ^ 2))
        = ENNReal.ofReal M * ∫⁻ p, ENNReal.ofReal (Q y * (|k p| * G (y - p) ^ 2)) := by
      have hmeas : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal (|k p| * G (y - p) ^ 2)) :=
        ((hkae.mul (((hGm.comp (measurable_const.sub measurable_id)).aemeasurable).pow_const 2)
          ).ennreal_ofReal)
      have hsplit : (∫⁻ p, ENNReal.ofReal (Q y * (|k p| * G (y - p) ^ 2)))
          = ENNReal.ofReal (Q y) * ∫⁻ p, ENNReal.ofReal (|k p| * G (y - p) ^ 2) := by
        rw [← MeasureTheory.lintegral_const_mul'' (ENNReal.ofReal (Q y)) hmeas]
        exact MeasureTheory.lintegral_congr (fun p => ENNReal.ofReal_mul (hQ0 y))
      rw [hsplit]
      ring
    calc ENNReal.ofReal (Q y * (∫ p : ℝ × ℝ, k p * G (y - p)) ^ 2)
        = ENNReal.ofReal (Q y) * (ENNReal.ofReal |c|) ^ 2 := h3
      _ ≤ ENNReal.ofReal (Q y) * (ENNReal.ofReal M
            * ∫⁻ p, ENNReal.ofReal (|k p| * G (y - p) ^ 2)) :=
          mul_le_mul_of_nonneg_left h2 bot_le
      _ = ENNReal.ofReal M * ∫⁻ p, ENNReal.ofReal (Q y * (|k p| * G (y - p) ^ 2)) := h4
  -- ## measurability of the two-variable integrand
  have hΨm : AEMeasurable (Function.uncurry fun y p : ℝ × ℝ =>
      ENNReal.ofReal (Q y * (|k p| * G (y - p) ^ 2)))
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
    have hQ1 : AEMeasurable (fun z : (ℝ × ℝ) × (ℝ × ℝ) => ENNReal.ofReal (Q z.1))
        (MeasureTheory.volume.prod MeasureTheory.volume) :=
      hQm.aemeasurable.ennreal_ofReal.comp_fst
    have hk1' : AEMeasurable (fun z : (ℝ × ℝ) × (ℝ × ℝ) => ENNReal.ofReal |k z.2|)
        (MeasureTheory.volume.prod MeasureTheory.volume) :=
      hkae.ennreal_ofReal.comp_snd
    have hG1 : AEMeasurable (fun z : (ℝ × ℝ) × (ℝ × ℝ) => ENNReal.ofReal |G (z.1 - z.2)|)
        (MeasureTheory.volume.prod MeasureTheory.volume) :=
      ((hGm.comp (measurable_fst.sub measurable_snd)).aemeasurable.abs).ennreal_ofReal
    have hprod : AEMeasurable (fun z : (ℝ × ℝ) × (ℝ × ℝ) =>
        ENNReal.ofReal (Q z.1) * ENNReal.ofReal |k z.2| * (ENNReal.ofReal |G (z.1 - z.2)|) ^ 2)
        (MeasureTheory.volume.prod MeasureTheory.volume) :=
      (hQ1.mul hk1').mul (hG1.pow_const 2)
    refine hprod.congr (Filter.Eventually.of_forall fun z => ?_)
    show ENNReal.ofReal (Q z.1) * ENNReal.ofReal |k z.2| * (ENNReal.ofReal |G (z.1 - z.2)|) ^ 2
        = ENNReal.ofReal (Q z.1 * (|k z.2| * G (z.1 - z.2) ^ 2))
    rw [ENNReal.ofReal_mul (hQ0 z.1), ENNReal.ofReal_mul (abs_nonneg (k z.2)),
      ← ENNReal.ofReal_pow (abs_nonneg (G (z.1 - z.2))) 2, sq_abs]
    ring_nf
  -- ## the Tonelli computation
  have hswap : (∫⁻ y : ℝ × ℝ, ∫⁻ p, ENNReal.ofReal (Q y * (|k p| * G (y - p) ^ 2)))
      = ∫⁻ p : ℝ × ℝ, ∫⁻ y, ENNReal.ofReal (Q y * (|k p| * G (y - p) ^ 2)) :=
    MeasureTheory.lintegral_lintegral_swap hΨm
  have hinner : ∀ p : ℝ × ℝ, (∫⁻ y, ENNReal.ofReal (Q y * (|k p| * G (y - p) ^ 2)))
      = ENNReal.ofReal |k p| * ENNReal.ofReal (∫ y : ℝ × ℝ, Q y * G (y - p) ^ 2) := by
    intro p
    have hmeas : AEMeasurable (fun y : ℝ × ℝ => ENNReal.ofReal (Q y * G (y - p) ^ 2)) :=
      (hQm.aemeasurable.mul
        (((hGm.comp (measurable_id.sub measurable_const)).aemeasurable).pow_const 2)).ennreal_ofReal
    have hpt2 : ∀ y : ℝ × ℝ, ENNReal.ofReal (Q y * (|k p| * G (y - p) ^ 2))
        = ENNReal.ofReal |k p| * ENNReal.ofReal (Q y * G (y - p) ^ 2) := by
      intro y
      calc ENNReal.ofReal (Q y * (|k p| * G (y - p) ^ 2))
          = ENNReal.ofReal (Q y) * ENNReal.ofReal (|k p| * G (y - p) ^ 2) :=
            ENNReal.ofReal_mul (hQ0 y)
        _ = ENNReal.ofReal (Q y)
              * (ENNReal.ofReal |k p| * ENNReal.ofReal (G (y - p) ^ 2)) := by
            rw [ENNReal.ofReal_mul (abs_nonneg (k p))]
        _ = ENNReal.ofReal |k p| * (ENNReal.ofReal (Q y) * ENNReal.ofReal (G (y - p) ^ 2)) := by
            ring
        _ = ENNReal.ofReal |k p| * ENNReal.ofReal (Q y * G (y - p) ^ 2) := by
            rw [ENNReal.ofReal_mul (hQ0 y)]
    calc (∫⁻ y, ENNReal.ofReal (Q y * (|k p| * G (y - p) ^ 2)))
        = ∫⁻ y, ENNReal.ofReal |k p| * ENNReal.ofReal (Q y * G (y - p) ^ 2) :=
          MeasureTheory.lintegral_congr hpt2
      _ = ENNReal.ofReal |k p| * ∫⁻ y, ENNReal.ofReal (Q y * G (y - p) ^ 2) :=
          MeasureTheory.lintegral_const_mul'' _ hmeas
      _ = ENNReal.ofReal |k p| * ENNReal.ofReal (∫ y : ℝ × ℝ, Q y * G (y - p) ^ 2) := by
          rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hshift p).1
            (Filter.Eventually.of_forall fun y => mul_nonneg (hQ0 y) (sq_nonneg _))]
  have hYmeas : AEMeasurable (fun y : ℝ × ℝ =>
      ∫⁻ p, ENNReal.ofReal (Q y * (|k p| * G (y - p) ^ 2))) MeasureTheory.volume :=
    hΨm.lintegral_prod_right
  have hstep2 : (∫⁻ p, ENNReal.ofReal |k p|
        * ENNReal.ofReal (∫ y : ℝ × ℝ, Q y * G (y - p) ^ 2))
      ≤ ∫⁻ p, ENNReal.ofReal (|k p| * Real.exp (Cw * (|p.1| + |p.2|)) * T) := by
    refine MeasureTheory.lintegral_mono (fun p => ?_)
    have hle := mul_le_mul_of_nonneg_left (hshift p).2 (abs_nonneg (k p))
    calc ENNReal.ofReal |k p| * ENNReal.ofReal (∫ y : ℝ × ℝ, Q y * G (y - p) ^ 2)
        = ENNReal.ofReal (|k p| * ∫ y : ℝ × ℝ, Q y * G (y - p) ^ 2) :=
          (ENNReal.ofReal_mul (abs_nonneg (k p))).symm
      _ ≤ ENNReal.ofReal (|k p| * Real.exp (Cw * (|p.1| + |p.2|)) * T) := by
          refine ENNReal.ofReal_le_ofReal ?_
          simpa [mul_assoc] using hle
  have hstep3 : (∫⁻ p, ENNReal.ofReal (|k p| * Real.exp (Cw * (|p.1| + |p.2|)) * T))
      = ENNReal.ofReal ((∫ p : ℝ × ℝ, |k p| * Real.exp (Cw * (|p.1| + |p.2|))) * T) := by
    have hmeas : AEMeasurable
        (fun p : ℝ × ℝ => ENNReal.ofReal (|k p| * Real.exp (Cw * (|p.1| + |p.2|)))) :=
      hKexpInt.aemeasurable.ennreal_ofReal
    have hX0 : 0 ≤ ∫ p : ℝ × ℝ, |k p| * Real.exp (Cw * (|p.1| + |p.2|)) :=
      MeasureTheory.integral_nonneg (fun p => mul_nonneg (abs_nonneg _) (Real.exp_nonneg _))
    calc (∫⁻ p, ENNReal.ofReal (|k p| * Real.exp (Cw * (|p.1| + |p.2|)) * T))
        = ∫⁻ p, ENNReal.ofReal T
            * ENNReal.ofReal (|k p| * Real.exp (Cw * (|p.1| + |p.2|))) := by
          refine MeasureTheory.lintegral_congr (fun p => ?_)
          rw [ENNReal.ofReal_mul (mul_nonneg (abs_nonneg _) (Real.exp_nonneg _)), mul_comm]
      _ = ENNReal.ofReal T
            * ∫⁻ p, ENNReal.ofReal (|k p| * Real.exp (Cw * (|p.1| + |p.2|))) :=
          MeasureTheory.lintegral_const_mul'' _ hmeas
      _ = (∫⁻ p, ENNReal.ofReal (|k p| * Real.exp (Cw * (|p.1| + |p.2|)))) * ENNReal.ofReal T :=
          mul_comm _ _
      _ = ENNReal.ofReal (∫ p : ℝ × ℝ, |k p| * Real.exp (Cw * (|p.1| + |p.2|)))
            * ENNReal.ofReal T := by
          rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hKexpInt
            (Filter.Eventually.of_forall fun p =>
              mul_nonneg (abs_nonneg _) (Real.exp_nonneg _))]
      _ = ENNReal.ofReal ((∫ p : ℝ × ℝ, |k p| * Real.exp (Cw * (|p.1| + |p.2|))) * T) :=
          (ENNReal.ofReal_mul hX0).symm
  have hMid : (∫ p : ℝ × ℝ, |k p| * Real.exp (Cw * (|p.1| + |p.2|))) * T ≤ E * T := by
    have h1 : (∫ p : ℝ × ℝ, |k p| * Real.exp (Cw * (|p.1| + |p.2|))) * T ≤ (E * M) * T :=
      mul_le_mul_of_nonneg_right hKexpBound hT0
    have h3 : M * T ≤ 1 * T := mul_le_mul_of_nonneg_right hM1 hT0
    have h2 : (E * M) * T ≤ E * T := by nlinarith [hE0, hM0, hT0, h3]
    exact le_trans h1 h2
  have hEnd : M * (E * T) ≤ E * T := by
    have h3 : M * (E * T) ≤ 1 * (E * T) := mul_le_mul_of_nonneg_right hM1 (mul_nonneg hE0 hT0)
    simpa using h3
  have hlin : (∫⁻ y : ℝ × ℝ, ENNReal.ofReal (Q y * (∫ p : ℝ × ℝ, k p * G (y - p)) ^ 2))
      ≤ ENNReal.ofReal (E * T) := by
    calc (∫⁻ y : ℝ × ℝ, ENNReal.ofReal (Q y * (∫ p : ℝ × ℝ, k p * G (y - p)) ^ 2))
        ≤ ∫⁻ y : ℝ × ℝ, ENNReal.ofReal M
            * ∫⁻ p, ENNReal.ofReal (Q y * (|k p| * G (y - p) ^ 2)) :=
          MeasureTheory.lintegral_mono hpt
      _ = ENNReal.ofReal M * (∫⁻ y : ℝ × ℝ,
            ∫⁻ p, ENNReal.ofReal (Q y * (|k p| * G (y - p) ^ 2))) :=
          MeasureTheory.lintegral_const_mul'' _ hYmeas
      _ = ENNReal.ofReal M * (∫⁻ p : ℝ × ℝ,
            ∫⁻ y, ENNReal.ofReal (Q y * (|k p| * G (y - p) ^ 2))) := by rw [hswap]
      _ = ENNReal.ofReal M * (∫⁻ p, ENNReal.ofReal |k p|
            * ENNReal.ofReal (∫ y : ℝ × ℝ, Q y * G (y - p) ^ 2)) := by
          rw [MeasureTheory.lintegral_congr hinner]
      _ ≤ ENNReal.ofReal M
            * ∫⁻ p, ENNReal.ofReal (|k p| * Real.exp (Cw * (|p.1| + |p.2|)) * T) :=
          mul_le_mul_of_nonneg_left hstep2 bot_le
      _ = ENNReal.ofReal M
            * ENNReal.ofReal ((∫ p : ℝ × ℝ, |k p| * Real.exp (Cw * (|p.1| + |p.2|))) * T) := by
          rw [hstep3]
      _ ≤ ENNReal.ofReal M * ENNReal.ofReal (E * T) :=
          mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal hMid) bot_le
      _ = ENNReal.ofReal (M * (E * T)) := (ENNReal.ofReal_mul hM0).symm
      _ ≤ ENNReal.ofReal (E * T) := ENNReal.ofReal_le_ofReal hEnd
  -- ## conclusion
  have hFmeas : AEStronglyMeasurable
      (fun y : ℝ × ℝ => Q y * (∫ p : ℝ × ℝ, k p * G (y - p)) ^ 2) MeasureTheory.volume := by
    have hjoint : AEStronglyMeasurable
        (fun z : (ℝ × ℝ) × (ℝ × ℝ) => k z.2 * G (z.1 - z.2))
        (MeasureTheory.volume.prod MeasureTheory.volume) :=
      (hk.aestronglyMeasurable.comp_snd).mul
        ((hGm.comp (measurable_fst.sub measurable_snd)).aestronglyMeasurable)
    have hconvmeas : AEStronglyMeasurable
        (fun y : ℝ × ℝ => ∫ p : ℝ × ℝ, k p * G (y - p)) MeasureTheory.volume :=
      hjoint.integral_prod_right'
    exact hQm.aestronglyMeasurable.mul (hconvmeas.pow 2)
  have hFnn : 0 ≤ᵐ[MeasureTheory.volume]
      (fun y : ℝ × ℝ => Q y * (∫ p : ℝ × ℝ, k p * G (y - p)) ^ 2) :=
    Filter.Eventually.of_forall (fun y => mul_nonneg (hQ0 y) (sq_nonneg _))
  refine ⟨(MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hFmeas hFnn).mp ?_, ?_⟩
  · exact ne_top_of_lt (lt_of_le_of_lt hlin ENNReal.ofReal_lt_top)
  · calc (∫ y : ℝ × ℝ, Q y * (∫ p : ℝ × ℝ, k p * G (y - p)) ^ 2)
        = (∫⁻ y : ℝ × ℝ,
            ENNReal.ofReal (Q y * (∫ p : ℝ × ℝ, k p * G (y - p)) ^ 2)).toReal :=
          MeasureTheory.integral_eq_lintegral_of_nonneg_ae hFnn hFmeas
      _ ≤ (ENNReal.ofReal (E * T)).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hlin
      _ = E * T := ENNReal.toReal_ofReal (mul_nonneg hE0 hT0)
      _ = Real.exp (2 * Cw * ε) * (∫ y : ℝ × ℝ, Q y * G y ^ 2) := by rw [hE, hT]

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv
