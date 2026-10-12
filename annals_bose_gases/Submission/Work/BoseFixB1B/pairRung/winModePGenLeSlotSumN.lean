import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.BoxFrameAux
import Submission.Work.BoseFixB1.boxTauGen_mode_bound_meas
import Submission.Work.BoseFixB1.slotInvariant_indicator_integral
import Submission.Work.BoseFixB1.tBamp_boxQInd_integrableOn_sq
import Submission.Work.BoseFixB1.tBamp_boxQInd_normSq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1B.pairRung.winModePGenLeSlotSumN`

The sharp pointwise (in the momentum `q`) Cauchy–Schwarz bound for the genuine windowed
`q`-diagonal frame content at an arbitrary measurable box `Ac ⊆ acube a`:

`boxWinModePGen a volA Ac χ Ψ q ≤ n · Σ_i (a³)⁻¹ ∫_{abox n a} ‖tBamp χ q (Q_{Ac,i}Ψ) i x‖²`.

The statement is the sector-free (`k = n`) version of the corpus's
`Work.BoseFixB1.boxWinModePGen_le_count_tBamp`, and the same statement as the (never compiling)
`Work.BoseFixB1.boxWinModePGen_le_slotSum`.  The import cone of this file is deliberately kept
*below* `Work.BoseFixB1.boxWords_eq_sum_sectorPiece`, whose `Work.BoseFixB1.exists_bound_abox`
clashes with the copy in the cone of `Work.BoseFixB1B.pairRungImports`; hence the handful of
elementary auxiliaries (integrability of the slot amplitudes, the boundedness of the two genuine
windowed modes, the disjoint-slot Cauchy–Schwarz) are proved here rather than imported from
`Work.BoseFixB1.boxFramePGen`.

Route:

1. `boxTauAnnGen volA Ac g Ψ x = (√volA)⁻¹ Σ_i 1_{Ac}(x_i)·∫_{Ac} g·Ψ(x_{i←·})`, so the
   slot Cauchy–Schwarz `(Σ_i a_i)² ≤ n Σ_i a_i²` gives
   `(boxTauAnnGen g Ψ x)² ≤ volA⁻¹·n·Σ_i 1_{Ac}(x_i)·(∫_{Ac} g·Ψ(x_{i←·}))²`
   (`boxTauAnnGen_sq_le`);
2. integrating (`integral_mono_of_nonneg`) and pulling the constants/the finite sum out of the
   integral (`half_le`) reduces `boxModePGen` to the slot integrals;
3. summing the two halves `g = Re_q`, `Im_q` and using the amplitude dictionary
   `tBamp_boxQInd_normSq` identifies the two slot amplitudes with `‖tBamp χ q (Q_{Ac,i}Ψ)‖²`;
4. the slot peel `slotInvariant_indicator_integral` (with `tBamp_indep_slot`) converts the
   indicator-weighted slot integral into the plain one with the factor `volA/a³`, cancelling
   the `volA⁻¹` of step 1.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseFixB1B.pairRung

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## 1. Elementary auxiliary estimates -/

private lemma sq_inv_sqrt {volA : ℝ} (hvolpos : 0 < volA) :
    (Real.sqrt volA)⁻¹ ^ 2 = volA⁻¹ := by
  rw [inv_pow, Real.sq_sqrt hvolpos.le]

/-- The integral of a function bounded by `C` on `Ac` is bounded by `C·volA`. -/
private lemma abs_setIntegral_le_of_bound {a volA C : ℝ} (ha : 0 < a)
    {Ac : Set E3} (hAc : Ac ⊆ Submission.BoseGases.acube a)
    (hvol : volA = (volume Ac).toReal) {f : E3 → ℝ} (hf : ∀ z ∈ Ac, |f z| ≤ C) :
    |∫ w in Ac, f w| ≤ C * volA := by
  have hfin : (volume : Measure E3) Ac < ⊤ :=
    lt_of_le_of_lt (measure_mono hAc) (Submission.BoseGases.acube_compact ha).measure_lt_top
  have hb : ∀ w ∈ Ac, ‖f w‖ ≤ C := fun w hw => by
    rw [Real.norm_eq_abs]; exact hf w hw
  have h1 : ‖∫ w in Ac, f w‖ ≤ C * (volume : Measure E3).real Ac :=
    norm_setIntegral_le_of_norm_le_const hfin hb
  rw [Real.norm_eq_abs, Measure.real_def, ← hvol] at h1
  exact h1

/-- The box **mean** of a function bounded by `C` on `Ac` is bounded by `C`. -/
private lemma abs_mean_le {a volA C : ℝ} (ha : 0 < a) (hvolpos : 0 < volA)
    {Ac : Set E3} (hAc : Ac ⊆ Submission.BoseGases.acube a)
    (hvol : volA = (volume Ac).toReal) {f : E3 → ℝ} (hf : ∀ z ∈ Ac, |f z| ≤ C) :
    |volA⁻¹ * ∫ w in Ac, f w| ≤ C := by
  have h1 := abs_setIntegral_le_of_bound (C := C) ha hAc hvol hf
  rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr hvolpos.le)]
  calc volA⁻¹ * |∫ w in Ac, f w| ≤ volA⁻¹ * (C * volA) :=
        mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hvolpos.le)
    _ = C := by rw [mul_comm C volA, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hvolpos), one_mul]

/-- **The genuine real windowed mode is globally bounded by `2κ`**, whenever `0 ≤ χ ≤ κ` on the
box. -/
private lemma abs_boxWinModeReGen_le2 {a volA κ : ℝ} (ha : 0 < a) (hvolpos : 0 < volA)
    {Ac : Set E3} (hAc : Ac ⊆ Submission.BoseGases.acube a)
    (hvol : volA = (volume Ac).toReal) (hκ0 : 0 ≤ κ) {χ : E3 → ℝ}
    (hχnn : ∀ z, 0 ≤ χ z) (hκ : ∀ z, χ z ≤ κ) (q z : E3) :
    |Work.BoseFixB1.boxWinModeReGen volA Ac χ q z| ≤ 2 * κ := by
  have hχabs : ∀ w ∈ Ac, |χ w| ≤ κ := fun w _ => by
    rw [abs_of_nonneg (hχnn w)]; exact hκ w
  have hcs : ∀ w ∈ Ac, |χ w * Real.cos (inner ℝ q w)| ≤ κ := fun w hw => by
    rw [abs_mul]
    calc |χ w| * |Real.cos (inner ℝ q w)| ≤ κ * 1 :=
          mul_le_mul (hχabs w hw) (Real.abs_cos_le_one _) (abs_nonneg _) hκ0
      _ = κ := mul_one κ
  have hmean : |volA⁻¹ * ∫ w in Ac, χ w * Real.cos (inner ℝ q w)| ≤ κ :=
    abs_mean_le ha hvolpos hAc hvol hcs
  rw [Work.BoseFixB1.boxWinModeReGen]
  by_cases hz : z ∈ Ac
  · rw [Set.indicator_of_mem hz, one_mul]
    calc |χ z * Real.cos (inner ℝ q z) - volA⁻¹ * ∫ w in Ac, χ w * Real.cos (inner ℝ q w)|
        ≤ |χ z * Real.cos (inner ℝ q z)|
            + |volA⁻¹ * ∫ w in Ac, χ w * Real.cos (inner ℝ q w)| := abs_sub _ _
      _ ≤ κ + κ := add_le_add (hcs z hz) hmean
      _ = 2 * κ := by ring
  · rw [Set.indicator_of_notMem hz, zero_mul, abs_zero]
    linarith

/-- **The genuine imaginary windowed mode is globally bounded by `2κ`**. -/
private lemma abs_boxWinModeImGen_le2 {a volA κ : ℝ} (ha : 0 < a) (hvolpos : 0 < volA)
    {Ac : Set E3} (hAc : Ac ⊆ Submission.BoseGases.acube a)
    (hvol : volA = (volume Ac).toReal) (hκ0 : 0 ≤ κ) {χ : E3 → ℝ}
    (hχnn : ∀ z, 0 ≤ χ z) (hκ : ∀ z, χ z ≤ κ) (q z : E3) :
    |Work.BoseFixB1.boxWinModeImGen volA Ac χ q z| ≤ 2 * κ := by
  have hχabs : ∀ w ∈ Ac, |χ w| ≤ κ := fun w _ => by
    rw [abs_of_nonneg (hχnn w)]; exact hκ w
  have hcs : ∀ w ∈ Ac, |χ w * Real.sin (inner ℝ q w)| ≤ κ := fun w hw => by
    rw [abs_mul]
    calc |χ w| * |Real.sin (inner ℝ q w)| ≤ κ * 1 :=
          mul_le_mul (hχabs w hw) (Real.abs_sin_le_one _) (abs_nonneg _) hκ0
      _ = κ := mul_one κ
  have hmean : |volA⁻¹ * ∫ w in Ac, χ w * Real.sin (inner ℝ q w)| ≤ κ :=
    abs_mean_le ha hvolpos hAc hvol hcs
  rw [Work.BoseFixB1.boxWinModeImGen, abs_neg]
  by_cases hz : z ∈ Ac
  · rw [Set.indicator_of_mem hz, one_mul]
    calc |χ z * Real.sin (inner ℝ q z) - volA⁻¹ * ∫ w in Ac, χ w * Real.sin (inner ℝ q w)|
        ≤ |χ z * Real.sin (inner ℝ q z)|
            + |volA⁻¹ * ∫ w in Ac, χ w * Real.sin (inner ℝ q w)| := abs_sub _ _
      _ ≤ κ + κ := add_le_add (hcs z hz) hmean
      _ = 2 * κ := by ring
  · rw [Set.indicator_of_notMem hz, zero_mul, abs_zero]
    linarith

/-- Measurability of the genuine real windowed mode. -/
private lemma measurable_boxWinModeReGen2 {volA : ℝ} {Ac : Set E3} (hAcm : MeasurableSet Ac)
    {χ : E3 → ℝ} (hχc : Continuous χ) (q : E3) :
    Measurable (Work.BoseFixB1.boxWinModeReGen volA Ac χ q) := by
  have hcont : Continuous (fun z : E3 => χ z * Real.cos (inner ℝ q z)) :=
    hχc.mul (Real.continuous_cos.comp (continuous_const.inner continuous_id))
  show Measurable (fun z : E3 => Ac.indicator (fun _ => (1 : ℝ)) z
    * (χ z * Real.cos (inner ℝ q z) - volA⁻¹ * ∫ w in Ac, χ w * Real.cos (inner ℝ q w)))
  exact (measurable_const.indicator hAcm).mul (hcont.measurable.sub measurable_const)

/-- Measurability of the genuine imaginary windowed mode. -/
private lemma measurable_boxWinModeImGen2 {volA : ℝ} {Ac : Set E3} (hAcm : MeasurableSet Ac)
    {χ : E3 → ℝ} (hχc : Continuous χ) (q : E3) :
    Measurable (Work.BoseFixB1.boxWinModeImGen volA Ac χ q) := by
  have hcont : Continuous (fun z : E3 => χ z * Real.sin (inner ℝ q z)) :=
    hχc.mul (Real.continuous_sin.comp (continuous_const.inner continuous_id))
  show Measurable (fun z : E3 => - (Ac.indicator (fun _ => (1 : ℝ)) z
    * (χ z * Real.sin (inner ℝ q z) - volA⁻¹ * ∫ w in Ac, χ w * Real.sin (inner ℝ q w))))
  exact ((measurable_const.indicator hAcm).mul (hcont.measurable.sub measurable_const)).neg

/-! ## 2. The slot Cauchy–Schwarz for the genuine box amplitude -/

/-- `(Σ_i a_i)² ≤ n Σ_i a_i²` applied to the slot decomposition of the genuine box amplitude. -/
private lemma boxTauAnnGen_sq_le {n : ℕ} {volA : ℝ} (hvolpos : 0 < volA) {Ac : Set E3}
    (g : E3 → ℝ) (Ψ : Submission.BoseGases.X n → ℝ) (x : Submission.BoseGases.X n) :
    (Work.BoseFixB1.boxTauAnnGen volA Ac g Ψ x) ^ 2 ≤ volA⁻¹ * ((n : ℝ) *
      ∑ i : Fin n, Ac.indicator (fun _ => (1 : ℝ)) (x i)
        * (∫ z in Ac, g z * Ψ (Function.update x i z)) ^ 2) := by
  have hsq := sq_inv_sqrt (volA := volA) hvolpos
  have hidem : ∀ (i : Fin n) (y : ℝ),
      (Ac.indicator (fun _ => (1 : ℝ)) (x i) * y) ^ 2
        = Ac.indicator (fun _ => (1 : ℝ)) (x i) * y ^ 2 := by
    intro i y
    by_cases h : x i ∈ Ac
    · rw [Set.indicator_of_mem h, one_mul, one_mul]
    · rw [Set.indicator_of_notMem h]; ring
  have hcs := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n)))
    (f := fun i : Fin n => Ac.indicator (fun _ => (1 : ℝ)) (x i)
      * ∫ z in Ac, g z * Ψ (Function.update x i z))
  rw [Finset.card_fin] at hcs
  have hsum_eq : (∑ i : Fin n, (Ac.indicator (fun _ => (1 : ℝ)) (x i)
        * ∫ z in Ac, g z * Ψ (Function.update x i z)) ^ 2)
      = ∑ i : Fin n, Ac.indicator (fun _ => (1 : ℝ)) (x i)
        * (∫ z in Ac, g z * Ψ (Function.update x i z)) ^ 2 :=
    Finset.sum_congr rfl (fun i _ => hidem i _)
  calc (Work.BoseFixB1.boxTauAnnGen volA Ac g Ψ x) ^ 2
      = volA⁻¹ * (∑ i : Fin n, (Ac.indicator (fun _ => (1 : ℝ)) (x i)
            * ∫ z in Ac, g z * Ψ (Function.update x i z))) ^ 2 := by
        rw [Work.BoseFixB1.boxTauAnnGen, mul_pow, hsq]
    _ ≤ volA⁻¹ * ((n : ℝ) * ∑ i : Fin n, (Ac.indicator (fun _ => (1 : ℝ)) (x i)
            * ∫ z in Ac, g z * Ψ (Function.update x i z)) ^ 2) :=
        mul_le_mul_of_nonneg_left (by simpa using hcs) (inv_nonneg.mpr hvolpos.le)
    _ = volA⁻¹ * ((n : ℝ) * ∑ i : Fin n, Ac.indicator (fun _ => (1 : ℝ)) (x i)
          * (∫ z in Ac, g z * Ψ (Function.update x i z)) ^ 2) := by
        rw [hsum_eq]

/-! ## 3. Integrability of the slot amplitudes -/

/-- A measurable real function with a uniform sup bound on `abox n a` has integrable square
over the finite-measure box `abox n a`. -/
private lemma integrableOn_sq_of_bound {n : ℕ} {a : ℝ} (ha : 0 < a)
    {g : Submission.BoseGases.X n → ℝ} (hg : Measurable g) {C : ℝ}
    (hC : ∀ x ∈ Submission.BoseGases.abox n a, |g x| ≤ C) :
    MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n => g x ^ 2)
      (Submission.BoseGases.abox n a) MeasureTheory.volume := by
  refine MeasureTheory.IntegrableOn.of_bound (Submission.BoseGases.abox_lt_top n a ha.le)
    (hg.pow_const 2).aestronglyMeasurable (max C 0 ^ 2) ?_
  filter_upwards [MeasureTheory.ae_restrict_mem (Submission.BoseGases.abox_measurable n a)]
    with x hx
  have h1 : |g x| ≤ max C 0 := le_trans (hC x hx) (le_max_left _ _)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) h1 2

/-- The indicator-weighted square of a slot fibre mean is integrable on the box. -/
private lemma integrableOn_slotAmp_sq {n : ℕ} {a volA : ℝ} (ha : 0 < a) (hvolpos : 0 < volA)
    {Ac : Set E3} (hAcm : MeasurableSet Ac) (hAc : Ac ⊆ Submission.BoseGases.acube a)
    (hvol : volA = (volume Ac).toReal) {g : E3 → ℝ} (hgm : Measurable g) {Cg : ℝ}
    (hg : ∀ z, |g z| ≤ Cg) {Ψ : Submission.BoseGases.X n → ℝ} (hΨm : Measurable Ψ) {CΨ : ℝ}
    (hΨb : ∀ x ∈ Submission.BoseGases.abox n a, |Ψ x| ≤ CΨ) (i : Fin n) :
    MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n =>
        Ac.indicator (fun _ => (1 : ℝ)) (x i)
          * (∫ z in Ac, g z * Ψ (Function.update x i z)) ^ 2)
      (Submission.BoseGases.abox n a) MeasureTheory.volume := by
  have hfib : Measurable (fun x : Submission.BoseGases.X n =>
      ∫ z in Ac, g z * Ψ (Function.update x i z)) :=
    Work.BoseFixB1.measurable_fibreMean_mul hAcm i hgm hΨm
  have hbnd : ∀ x ∈ Submission.BoseGases.abox n a,
      |∫ z in Ac, g z * Ψ (Function.update x i z)| ≤ max Cg 0 * max CΨ 0 * volA := by
    intro x hx
    have h := Work.BoseFixB1.abs_fibreMean_mul_le (ℓ := a) ha (A := Ac) hAc (h := g) hg
      (Φ := Ψ) hΨb hx i
    rwa [← hvol] at h
  have hint : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n =>
      (∫ z in Ac, g z * Ψ (Function.update x i z)) ^ 2)
      (Submission.BoseGases.abox n a) MeasureTheory.volume :=
    integrableOn_sq_of_bound ha hfib hbnd
  refine Integrable.bdd_mul (f := fun x : Submission.BoseGases.X n =>
      Ac.indicator (fun _ => (1 : ℝ)) (x i))
    (g := fun x : Submission.BoseGases.X n =>
      (∫ z in Ac, g z * Ψ (Function.update x i z)) ^ 2) hint ?_ (c := 1) ?_
  · exact ((measurable_const.indicator hAcm).comp (measurable_pi_apply i)).aestronglyMeasurable
  · filter_upwards with x
    by_cases h : x i ∈ Ac
    · rw [Set.indicator_of_mem h]; norm_num
    · rw [Set.indicator_of_notMem h]; norm_num

/-! ## 4. One half of the frame bound -/

/-- **The one-mode (half) frame bound.**  For a measurable, bounded weight `g`, the `x`-integral
of the squared genuine box amplitude is bounded by `volA⁻¹·n` times the sum of the
indicator-weighted slot integrals. -/
private lemma half_le {n : ℕ} {a volA : ℝ} (ha : 0 < a) (hvolpos : 0 < volA)
    {Ac : Set E3} (hAcm : MeasurableSet Ac) (hAc : Ac ⊆ Submission.BoseGases.acube a)
    (hvol : volA = (volume Ac).toReal) {g : E3 → ℝ} (hgm : Measurable g) {Cg : ℝ}
    (hg : ∀ z, |g z| ≤ Cg) {Ψ : Submission.BoseGases.X n → ℝ} (hΨm : Measurable Ψ) {CΨ : ℝ}
    (hΨb : ∀ x ∈ Submission.BoseGases.abox n a, |Ψ x| ≤ CΨ) :
    (∫ x in Submission.BoseGases.abox n a,
        (Work.BoseFixB1.boxTauAnnGen volA Ac g Ψ x) ^ 2)
      ≤ volA⁻¹ * ((n : ℝ) * ∑ i : Fin n,
          ∫ x in Submission.BoseGases.abox n a,
            Ac.indicator (fun _ => (1 : ℝ)) (x i)
              * (∫ z in Ac, g z * Ψ (Function.update x i z)) ^ 2) := by
  have hSlot : ∀ i : Fin n, MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n =>
      Ac.indicator (fun _ => (1 : ℝ)) (x i)
        * (∫ z in Ac, g z * Ψ (Function.update x i z)) ^ 2)
      (Submission.BoseGases.abox n a) MeasureTheory.volume :=
    fun i => integrableOn_slotAmp_sq ha hvolpos hAcm hAc hvol hgm hg hΨm hΨb i
  have hsum : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n =>
      ∑ i : Fin n, Ac.indicator (fun _ => (1 : ℝ)) (x i)
        * (∫ z in Ac, g z * Ψ (Function.update x i z)) ^ 2)
      (Submission.BoseGases.abox n a) MeasureTheory.volume :=
    integrable_finsetSum _ (fun i _ => hSlot i)
  have hint : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n =>
      volA⁻¹ * ((n : ℝ) * ∑ i : Fin n, Ac.indicator (fun _ => (1 : ℝ)) (x i)
        * (∫ z in Ac, g z * Ψ (Function.update x i z)) ^ 2))
      (Submission.BoseGases.abox n a) MeasureTheory.volume :=
    (hsum.const_mul (n : ℝ)).const_mul volA⁻¹
  have hmono := integral_mono_of_nonneg
    (f := fun x : Submission.BoseGases.X n => (Work.BoseFixB1.boxTauAnnGen volA Ac g Ψ x) ^ 2)
    (g := fun x : Submission.BoseGases.X n =>
      volA⁻¹ * ((n : ℝ) * ∑ i : Fin n, Ac.indicator (fun _ => (1 : ℝ)) (x i)
        * (∫ z in Ac, g z * Ψ (Function.update x i z)) ^ 2))
    (Filter.Eventually.of_forall fun x => sq_nonneg _)
    hint
    ((ae_restrict_iff' (Submission.BoseGases.abox_measurable n a)).mpr
      (ae_of_all _ (fun x _ => boxTauAnnGen_sq_le (Ac := Ac) hvolpos g Ψ x)))
  refine hmono.trans (le_of_eq ?_)
  rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_finsetSum _ (fun i _ => hSlot i)]

/-! ## 5. The target -/

theorem winModePGenLeSlotSumN {n : ℕ} {a volA : ℝ} (ha : 0 < a) (hvolpos : 0 < volA)
    {Ac : Set (EuclideanSpace ℝ (Fin 3))} (hAcm : MeasurableSet Ac)
    (hAcsub : Ac ⊆ Submission.BoseGases.acube a)
    (hvol : volA = (MeasureTheory.volume Ac).toReal)
    {χ : EuclideanSpace ℝ (Fin 3) → ℝ} (hχc : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχs : HasCompactSupport χ) (hχsupp : ∀ z, z ∉ Ac → χ z = 0) (hχnn : ∀ z, 0 ≤ χ z)
    {Ψ : Submission.BoseGases.X n → ℝ} (hΨc : ContDiff ℝ (⊤ : ℕ∞) Ψ)
    (q : EuclideanSpace ℝ (Fin 3)) :
    Work.BoseFixB1.boxWinModePGen a volA Ac χ Ψ q
      ≤ (n : ℝ) * ∑ i : Fin n, (a ^ 3)⁻¹ *
          ∫ x in Submission.BoseGases.abox n a,
            ‖Work.SmallBoxTBWord.tBamp χ q (Work.UBBInputs8.boxQInd volA Ac i Ψ) i x‖ ^ 2 := by
  classical
  -- ## bounds on `χ` and `Ψ`
  obtain ⟨Cχ, hCχ⟩ := (Submission.BoseGases.acube_compact ha).exists_bound_of_continuousOn
    hχc.continuous.continuousOn
  set κ : ℝ := max Cχ 0 with hκdef
  have hκ0 : 0 ≤ κ := le_max_right _ _
  have hκ : ∀ z : E3, χ z ≤ κ := by
    intro z
    by_cases hz : z ∈ Submission.BoseGases.acube a
    · exact le_trans (le_trans (le_abs_self (χ z)) (hCχ z hz)) (le_max_left _ _)
    · rw [hχsupp z (fun h => hz (hAcsub h))]
      exact hκ0
  obtain ⟨Cψ, hCψ⟩ := (Submission.BoseGases.abox_compact n ha).exists_bound_of_continuousOn
    hΨc.continuous.continuousOn
  set BΨ : ℝ := max Cψ 0 with hBΨdef
  have hBΨ0 : 0 ≤ BΨ := le_max_right _ _
  have hΨb : ∀ x ∈ Submission.BoseGases.abox n a, |Ψ x| ≤ BΨ := by
    intro x hx
    have h1 : ‖Ψ x‖ ≤ Cψ := hCψ x hx
    rw [Real.norm_eq_abs] at h1
    exact le_trans h1 (le_max_left _ _)
  -- ## the two mode bounds and their measurability
  have hR_abs : ∀ z : E3, |Work.BoseFixB1.boxWinModeReGen volA Ac χ q z| ≤ 2 * κ :=
    fun z => abs_boxWinModeReGen_le2 ha hvolpos hAcsub hvol hκ0 hχnn hκ q z
  have hI_abs : ∀ z : E3, |Work.BoseFixB1.boxWinModeImGen volA Ac χ q z| ≤ 2 * κ :=
    fun z => abs_boxWinModeImGen_le2 ha hvolpos hAcsub hvol hκ0 hχnn hκ q z
  have hR_meas : Measurable (Work.BoseFixB1.boxWinModeReGen volA Ac χ q) :=
    measurable_boxWinModeReGen2 hAcm hχc.continuous q
  have hI_meas : Measurable (Work.BoseFixB1.boxWinModeImGen volA Ac χ q) :=
    measurable_boxWinModeImGen2 hAcm hχc.continuous q
  -- ## the two halves
  have hR := half_le ha hvolpos hAcm hAcsub hvol (g := Work.BoseFixB1.boxWinModeReGen volA Ac χ q)
    hR_meas (Cg := 2 * κ) hR_abs hΨc.continuous.measurable (CΨ := BΨ) hΨb
  have hI := half_le ha hvolpos hAcm hAcsub hvol (g := Work.BoseFixB1.boxWinModeImGen volA Ac χ q)
    hI_meas (Cg := 2 * κ) hI_abs hΨc.continuous.measurable (CΨ := BΨ) hΨb
  -- ## integrability of the four slot amplitudes
  have hSlotR : ∀ i : Fin n, MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n =>
      Ac.indicator (fun _ => (1 : ℝ)) (x i)
        * (∫ z in Ac, Work.BoseFixB1.boxWinModeReGen volA Ac χ q z
            * Ψ (Function.update x i z)) ^ 2)
      (Submission.BoseGases.abox n a) MeasureTheory.volume := fun i =>
    integrableOn_slotAmp_sq ha hvolpos hAcm hAcsub hvol hR_meas (Cg := 2 * κ) hR_abs
      hΨc.continuous.measurable (CΨ := BΨ) hΨb i
  have hSlotI : ∀ i : Fin n, MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n =>
      Ac.indicator (fun _ => (1 : ℝ)) (x i)
        * (∫ z in Ac, Work.BoseFixB1.boxWinModeImGen volA Ac χ q z
            * Ψ (Function.update x i z)) ^ 2)
      (Submission.BoseGases.abox n a) MeasureTheory.volume := fun i =>
    integrableOn_slotAmp_sq ha hvolpos hAcm hAcsub hvol hI_meas (Cg := 2 * κ) hI_abs
      hΨc.continuous.measurable (CΨ := BΨ) hΨb i
  -- ## the slot peel
  have hpeel : ∀ i : Fin n,
      (∫ x in Submission.BoseGases.abox n a,
          Ac.indicator (fun _ => (1 : ℝ)) (x i)
            * ‖Work.SmallBoxTBWord.tBamp χ q (Work.UBBInputs8.boxQInd volA Ac i Ψ) i x‖ ^ 2)
        = volA * ((a ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox n a,
            ‖Work.SmallBoxTBWord.tBamp χ q (Work.UBBInputs8.boxQInd volA Ac i Ψ) i x‖ ^ 2) := by
    intro i
    have hInt := Work.BoseFixB1.tBamp_boxQInd_integrableOn_sq (n := n) (volA := volA) ha hAcm
      hAcsub hχc.continuous hχs hΨc.continuous i q
    have hinv := Work.BoseFixB1.slotInvariant_indicator_integral (n := n) ha hvolpos hAcm hAcsub
      hvol i (G := fun x : Submission.BoseGases.X n =>
        ‖Work.SmallBoxTBWord.tBamp χ q (Work.UBBInputs8.boxQInd volA Ac i Ψ) i x‖ ^ 2)
      (fun x t => by rw [Work.SmallBoxTBWord.tBamp_indep_slot]) hInt
    calc (∫ x in Submission.BoseGases.abox n a,
          Ac.indicator (fun _ => (1 : ℝ)) (x i)
            * ‖Work.SmallBoxTBWord.tBamp χ q (Work.UBBInputs8.boxQInd volA Ac i Ψ) i x‖ ^ 2)
        = volA * (volA⁻¹ * ∫ x in Submission.BoseGases.abox n a,
            Ac.indicator (fun _ => (1 : ℝ)) (x i)
              * ‖Work.SmallBoxTBWord.tBamp χ q (Work.UBBInputs8.boxQInd volA Ac i Ψ) i x‖ ^ 2)
          := by rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hvolpos), one_mul]
      _ = volA * ((a ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox n a,
            ‖Work.SmallBoxTBWord.tBamp χ q (Work.UBBInputs8.boxQInd volA Ac i Ψ) i x‖ ^ 2)
          := by rw [hinv]
  -- ## the combination identity
  have hcomb :
      (∑ i : Fin n, ∫ x in Submission.BoseGases.abox n a,
          Ac.indicator (fun _ => (1 : ℝ)) (x i)
            * (∫ z in Ac, Work.BoseFixB1.boxWinModeReGen volA Ac χ q z
                * Ψ (Function.update x i z)) ^ 2)
        + (∑ i : Fin n, ∫ x in Submission.BoseGases.abox n a,
          Ac.indicator (fun _ => (1 : ℝ)) (x i)
            * (∫ z in Ac, Work.BoseFixB1.boxWinModeImGen volA Ac χ q z
                * Ψ (Function.update x i z)) ^ 2)
        = ∑ i : Fin n, ∫ x in Submission.BoseGases.abox n a,
            Ac.indicator (fun _ => (1 : ℝ)) (x i)
              * ‖Work.SmallBoxTBWord.tBamp χ q (Work.UBBInputs8.boxQInd volA Ac i Ψ) i x‖ ^ 2 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← MeasureTheory.integral_add (hSlotR i) (hSlotI i)]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem
      (Submission.BoseGases.abox_measurable n a)] with x hx
    rw [Work.BoseFixB1.tBamp_boxQInd_normSq (n := n) (volA := volA) ha hvolpos hAcm hAcsub
      hχc.continuous hχs hΨc.continuous i hx q]
    ring
  -- ## the final chain
  calc Work.BoseFixB1.boxWinModePGen a volA Ac χ Ψ q
      = (∫ x in Submission.BoseGases.abox n a,
            (Work.BoseFixB1.boxTauAnnGen volA Ac
              (Work.BoseFixB1.boxWinModeReGen volA Ac χ q) Ψ x) ^ 2)
        + (∫ x in Submission.BoseGases.abox n a,
            (Work.BoseFixB1.boxTauAnnGen volA Ac
              (Work.BoseFixB1.boxWinModeImGen volA Ac χ q) Ψ x) ^ 2) := by
        rw [Work.BoseFixB1.boxWinModePGen, Work.BoseFixB1.boxModePGen, Work.BoseFixB1.boxModePGen]
    _ ≤ volA⁻¹ * ((n : ℝ) * ∑ i : Fin n,
          ∫ x in Submission.BoseGases.abox n a,
            Ac.indicator (fun _ => (1 : ℝ)) (x i)
              * (∫ z in Ac, Work.BoseFixB1.boxWinModeReGen volA Ac χ q z
                  * Ψ (Function.update x i z)) ^ 2)
        + volA⁻¹ * ((n : ℝ) * ∑ i : Fin n,
          ∫ x in Submission.BoseGases.abox n a,
            Ac.indicator (fun _ => (1 : ℝ)) (x i)
              * (∫ z in Ac, Work.BoseFixB1.boxWinModeImGen volA Ac χ q z
                  * Ψ (Function.update x i z)) ^ 2) := add_le_add hR hI
    _ = volA⁻¹ * ((n : ℝ) *
          ((∑ i : Fin n, ∫ x in Submission.BoseGases.abox n a,
              Ac.indicator (fun _ => (1 : ℝ)) (x i)
                * (∫ z in Ac, Work.BoseFixB1.boxWinModeReGen volA Ac χ q z
                    * Ψ (Function.update x i z)) ^ 2)
            + (∑ i : Fin n, ∫ x in Submission.BoseGases.abox n a,
              Ac.indicator (fun _ => (1 : ℝ)) (x i)
                * (∫ z in Ac, Work.BoseFixB1.boxWinModeImGen volA Ac χ q z
                    * Ψ (Function.update x i z)) ^ 2))) := by ring
    _ = volA⁻¹ * ((n : ℝ) * ∑ i : Fin n,
          ∫ x in Submission.BoseGases.abox n a,
            Ac.indicator (fun _ => (1 : ℝ)) (x i)
              * ‖Work.SmallBoxTBWord.tBamp χ q (Work.UBBInputs8.boxQInd volA Ac i Ψ) i x‖ ^ 2) := by
        rw [hcomb]
    _ = volA⁻¹ * ((n : ℝ) * ∑ i : Fin n, volA * ((a ^ 3)⁻¹ *
          ∫ x in Submission.BoseGases.abox n a,
            ‖Work.SmallBoxTBWord.tBamp χ q (Work.UBBInputs8.boxQInd volA Ac i Ψ) i x‖ ^ 2)) := by
        rw [Finset.sum_congr rfl (fun i _ => hpeel i)]
    _ = (n : ℝ) * ∑ i : Fin n, (a ^ 3)⁻¹ *
          ∫ x in Submission.BoseGases.abox n a,
            ‖Work.SmallBoxTBWord.tBamp χ q (Work.UBBInputs8.boxQInd volA Ac i Ψ) i x‖ ^ 2 := by
        rw [← Finset.mul_sum]
        field_simp

end Work.BoseFixB1B.pairRung
