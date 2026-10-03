import Mathlib
import Submission.Work.Analysis.Concentration.Basic
import Submission.Commons.Analysis.Convolution.eLpNorm_convolution_le
import Submission.Port.Aesm

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Young's convolution inequality on `ℤ/Qℤ`

For functions `u v : ℤ/Qℤ → ℂ` and exponents `p r s ≥ 1` with `1/s = 1/p + 1/r - 1`, the
convolution `u ∗ v` with respect to the Haar probability measure on the finite group `ℤ/Qℤ`
satisfies `‖u ∗ v‖_{L^s} ≤ ‖u‖_{L^p} ‖v‖_{L^r}` (`LpNormZMod`, `convZMod`).

The proof reduces the statement to the general Young inequality for convolution with respect to
an invariant measure (`Commons.Analysis.Convolution.eLpNorm_convolution_le_ennreal`), applied to
the counting measure on `ℤ/Qℤ`, and then translates back to the real normalized norms.
-/

namespace Work.Analysis.Concentration

open MeasureTheory Finset
open scoped ENNReal

/-- `eLpNorm` with respect to the counting measure on `ZMod Q` is the `ofReal`-image of the
elementary finite `ℓ^p` sum. -/
lemma eLpNorm_count_eq_ofReal (Q : ℕ) [NeZero Q] {p : ℝ} (hp : 0 < p) (f : ZMod Q → ℂ) :
    eLpNorm f (ENNReal.ofReal p) Measure.count
      = ENNReal.ofReal ((∑ x : ZMod Q, ‖f x‖ ^ p) ^ (1 / p)) := by
  have hp0 : ENNReal.ofReal p ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hp
  have hptop : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) hp0 hptop]
  simp only [ENNReal.toReal_ofReal hp.le]
  rw [lintegral_count, tsum_fintype,
    show (∑ x : ZMod Q, ‖f x‖ₑ ^ p) = ENNReal.ofReal (∑ x : ZMod Q, ‖f x‖ ^ p) from by
      rw [ENNReal.ofReal_sum_of_nonneg (fun x _ => Real.rpow_nonneg (norm_nonneg _) p)]
      exact Finset.sum_congr rfl fun x _ => by
        rw [show ‖f x‖ₑ = ENNReal.ofReal ‖f x‖ from by simp]
        exact ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp.le]
  rw [ENNReal.ofReal_rpow_of_nonneg
    (Finset.sum_nonneg fun x _ => Real.rpow_nonneg (norm_nonneg _) p) (by positivity)]

/-- Real form of `eLpNorm` with respect to the counting measure. -/
lemma eLpNorm_count_toReal (Q : ℕ) [NeZero Q] {p : ℝ} (hp : 0 < p) (f : ZMod Q → ℂ) :
    (eLpNorm f (ENNReal.ofReal p) Measure.count).toReal
      = (∑ x : ZMod Q, ‖f x‖ ^ p) ^ (1 / p) := by
  rw [eLpNorm_count_eq_ofReal Q hp f]
  exact ENNReal.toReal_ofReal (Real.rpow_nonneg
    (Finset.sum_nonneg fun x _ => Real.rpow_nonneg (norm_nonneg _) p) (1 / p))

/-- Finiteness of `eLpNorm` with respect to the counting measure. -/
lemma eLpNorm_count_lt_top (Q : ℕ) [NeZero Q] {p : ℝ} (hp : 0 < p) (f : ZMod Q → ℂ) :
    eLpNorm f (ENNReal.ofReal p) Measure.count < ⊤ := by
  rw [eLpNorm_count_eq_ofReal Q hp f]
  exact ENNReal.ofReal_lt_top

/-- `LpNormZMod` expressed through `eLpNorm` with respect to the counting measure. -/
lemma LpNormZMod_eq_eLpNorm_count (Q : ℕ) [NeZero Q] {p : ℝ} (hp : 0 < p)
    (f : ZMod Q → ℂ) :
    LpNormZMod Q p f
      = (Q : ℝ) ^ (-(1 / p)) * (eLpNorm f (ENNReal.ofReal p) Measure.count).toReal := by
  have hQnn : (0 : ℝ) ≤ (Q : ℝ) := Nat.cast_nonneg Q
  rw [eLpNorm_count_toReal Q hp f]
  unfold LpNormZMod
  rw [Real.mul_rpow (inv_nonneg.mpr hQnn)
    (Finset.sum_nonneg fun x _ => Real.rpow_nonneg (norm_nonneg _) p)]
  rw [Real.inv_rpow hQnn, Real.rpow_neg hQnn]

/-- **Young's convolution inequality on `ℤ/Qℤ`** with respect to the normalized counting
(Haar probability) measure: if `1/s = 1/p + 1/r - 1` and `p, r, s ≥ 1`, then
`‖u ∗ v‖_{L^s} ≤ ‖u‖_{L^p} ‖v‖_{L^r}`. -/
lemma young_zmod (Q : ℕ) [NeZero Q] {p r s : ℝ} (hp : 1 ≤ p) (hr : 1 ≤ r) (hs : 1 ≤ s)
    (hrel : 1 / s = 1 / p + 1 / r - 1) (u v : ZMod Q → ℂ) :
    LpNormZMod Q s (convZMod Q u v) ≤ LpNormZMod Q p u * LpNormZMod Q r v := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne Q)
  have hQposE : (0 : ℝ≥0∞) < (Q : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_pos.mpr hQpos
  -- **Step 1**: Young's inequality for the counting measure.
  have hYoung : eLpNorm (fun x : ZMod Q => ∫⁻ y, ‖v (x - y)‖ₑ * ‖u y‖ₑ ∂Measure.count)
        (ENNReal.ofReal s) Measure.count
      ≤ eLpNorm v (ENNReal.ofReal r) Measure.count
        * eLpNorm u (ENNReal.ofReal p) Measure.count := by
    have h := Commons.Analysis.Convolution.eLpNorm_convolution_le_ennreal (G := ZMod Q)
      (μ := Measure.count)
      (K := fun z : ZMod Q => ‖v z‖ₑ) (Φ := fun z : ZMod Q => ‖u z‖ₑ)
      (p := p) (q := s) (r := r) hp hr hrel
      (measurable_of_finite (fun z : ZMod Q => ‖v z‖ₑ)).aemeasurable
      (measurable_of_finite (fun z : ZMod Q => ‖u z‖ₑ)).aemeasurable
    simpa only [eLpNorm_enorm, MeasureTheory.AEStronglyMeasurable.of_discrete] using h
  -- **Step 2**: pointwise domination of `u ∗ v` by the Young integral, times `Q⁻¹`.
  have hstep : ∀ x : ZMod Q, ‖convZMod Q u v x‖ₑ ≤ (Q : ℝ≥0∞)⁻¹
      * (∫⁻ y, ‖v (x - y)‖ₑ * ‖u y‖ₑ ∂Measure.count) := by
    intro x
    have hQnorm : ‖((Q : ℂ))⁻¹‖ₑ = (Q : ℝ≥0∞)⁻¹ := by
      have h1 : ‖((Q : ℂ))⁻¹‖ = (Q : ℝ)⁻¹ := by rw [norm_inv, Complex.norm_natCast]
      rw [← ofReal_norm, h1, ENNReal.ofReal_inv_of_pos hQpos, ENNReal.ofReal_natCast]
    have hsum : ‖∑ z : ZMod Q, u z * v (x - z)‖ₑ
        ≤ ∑ z : ZMod Q, ‖u z‖ₑ * ‖v (x - z)‖ₑ := by
      simpa only [enorm_mul] using enorm_sum_le Finset.univ (fun z : ZMod Q => u z * v (x - z))
    have hW : (∑ z : ZMod Q, ‖u z‖ₑ * ‖v (x - z)‖ₑ)
        = (∫⁻ y, ‖v (x - y)‖ₑ * ‖u y‖ₑ ∂Measure.count) := by
      rw [lintegral_count, tsum_fintype]
      exact Finset.sum_congr rfl fun y _ => mul_comm _ _
    calc ‖convZMod Q u v x‖ₑ
        = (Q : ℝ≥0∞)⁻¹ * ‖∑ z : ZMod Q, u z * v (x - z)‖ₑ := by
          simp only [convZMod]
          rw [enorm_mul, hQnorm]
      _ ≤ (Q : ℝ≥0∞)⁻¹ * ∑ z : ZMod Q, ‖u z‖ₑ * ‖v (x - z)‖ₑ :=
          mul_le_mul_of_nonneg_left hsum zero_le
      _ = (Q : ℝ≥0∞)⁻¹ * (∫⁻ y, ‖v (x - y)‖ₑ * ‖u y‖ₑ ∂Measure.count) := by rw [hW]
  -- **Step 3**: assembly in `ℝ≥0∞`.
  have hEc : eLpNorm (convZMod Q u v) (ENNReal.ofReal s) Measure.count
      ≤ (Q : ℝ≥0∞)⁻¹ * (eLpNorm v (ENNReal.ofReal r) Measure.count
          * eLpNorm u (ENNReal.ofReal p) Measure.count) := by
    calc eLpNorm (convZMod Q u v) (ENNReal.ofReal s) Measure.count
        ≤ eLpNorm (fun x : ZMod Q =>
              (Q : ℝ≥0∞)⁻¹ * (∫⁻ y, ‖v (x - y)‖ₑ * ‖u y‖ₑ ∂Measure.count))
            (ENNReal.ofReal s) Measure.count := by
          refine eLpNorm_mono_enorm (hf := by pw_aesm) fun x => ?_
          simpa only [enorm_eq_self] using hstep x
      _ = (Q : ℝ≥0∞)⁻¹ * eLpNorm (fun x : ZMod Q =>
              ∫⁻ y, ‖v (x - y)‖ₑ * ‖u y‖ₑ ∂Measure.count)
            (ENNReal.ofReal s) Measure.count :=
          Commons.Analysis.Convolution.eLpNorm_const_mul_ennreal_of_pos
            (measurable_of_finite _).aemeasurable (Q : ℝ≥0∞)⁻¹ hs0
      _ ≤ (Q : ℝ≥0∞)⁻¹ * (eLpNorm v (ENNReal.ofReal r) Measure.count
            * eLpNorm u (ENNReal.ofReal p) Measure.count) :=
          mul_le_mul_of_nonneg_left hYoung zero_le
  -- **Step 4**: pass to real numbers.
  have hEv_ne : eLpNorm v (ENNReal.ofReal r) Measure.count ≠ ⊤ :=
    ne_of_lt (eLpNorm_count_lt_top Q hr0 v)
  have hEu_ne : eLpNorm u (ENNReal.ofReal p) Measure.count ≠ ⊤ :=
    ne_of_lt (eLpNorm_count_lt_top Q hp0 u)
  have hRHS_ne : (Q : ℝ≥0∞)⁻¹ * (eLpNorm v (ENNReal.ofReal r) Measure.count
      * eLpNorm u (ENNReal.ofReal p) Measure.count) ≠ ⊤ :=
    ENNReal.mul_ne_top (ne_of_lt (ENNReal.inv_lt_top.mpr hQposE))
      (ENNReal.mul_ne_top hEv_ne hEu_ne)
  have hreal : (eLpNorm (convZMod Q u v) (ENNReal.ofReal s) Measure.count).toReal
      ≤ (Q : ℝ)⁻¹ * ((eLpNorm v (ENNReal.ofReal r) Measure.count).toReal
          * (eLpNorm u (ENNReal.ofReal p) Measure.count).toReal) := by
    have h1 := ENNReal.toReal_mono hRHS_ne hEc
    rwa [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_inv,
      ENNReal.toReal_natCast] at h1
  -- **Step 5**: the scalar identity `Q^{-1/s} Q^{-1} = Q^{-1/p} Q^{-1/r}`.
  have hQpow : (Q : ℝ) ^ (-(1 / s)) * (Q : ℝ)⁻¹
      = (Q : ℝ) ^ (-(1 / p)) * (Q : ℝ) ^ (-(1 / r)) := by
    rw [← Real.rpow_neg_one (Q : ℝ), ← Real.rpow_add hQpos, ← Real.rpow_add hQpos]
    congr 1
    rw [hrel]
    ring
  rw [LpNormZMod_eq_eLpNorm_count Q hs0 (convZMod Q u v),
    LpNormZMod_eq_eLpNorm_count Q hp0 u, LpNormZMod_eq_eLpNorm_count Q hr0 v]
  calc (Q : ℝ) ^ (-(1 / s))
        * (eLpNorm (convZMod Q u v) (ENNReal.ofReal s) Measure.count).toReal
      ≤ (Q : ℝ) ^ (-(1 / s)) * ((Q : ℝ)⁻¹
          * ((eLpNorm v (ENNReal.ofReal r) Measure.count).toReal
            * (eLpNorm u (ENNReal.ofReal p) Measure.count).toReal)) :=
        mul_le_mul_of_nonneg_left hreal (Real.rpow_nonneg hQpos.le _)
    _ = ((Q : ℝ) ^ (-(1 / s)) * (Q : ℝ)⁻¹)
          * ((eLpNorm v (ENNReal.ofReal r) Measure.count).toReal
            * (eLpNorm u (ENNReal.ofReal p) Measure.count).toReal) := by rw [mul_assoc]
    _ = ((Q : ℝ) ^ (-(1 / p)) * (Q : ℝ) ^ (-(1 / r)))
          * ((eLpNorm v (ENNReal.ofReal r) Measure.count).toReal
            * (eLpNorm u (ENNReal.ofReal p) Measure.count).toReal) := by rw [hQpow]
    _ = (Q : ℝ) ^ (-(1 / p)) * (eLpNorm u (ENNReal.ofReal p) Measure.count).toReal
          * ((Q : ℝ) ^ (-(1 / r))
            * (eLpNorm v (ENNReal.ofReal r) Measure.count).toReal) := by ac_rfl

end Work.Analysis.Concentration
