import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.BoxFrameDefs
import Submission.Work.BoseFixB1.boxQInd_update_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.BoxFrameAux` — elementary frame lemmas

Self-contained ingredients of the frame bound `Work.BoseFixB1.boxFramePGen`:

* `slotFibre_eq` — on `Ac` the mean-free fibre is the bare mean-subtracted fibre;
* `integrableOn_slotFibre_sq` — the mean-free fibre is square-integrable on the box;
* `winModeRe_mean_zero` / `winModeIm_mean_zero` — the genuine windowed modes have vanishing
  mean over the box `Ac`;
* `slotAmp_re_eq` / `slotAmp_im_eq` — the slot amplitude against the genuine windowed mode is
  the `χ·cos` resp. `χ·sin` overlap against the *mean-free* fibre;
* `slotFibre_sq_weight_le` — the window weight: `∫_Ac (χ·Q)² ≤ κ²∫_Ac Q²` for `0 ≤ χ ≤ κ`;
* `frameIntegrand_le` — Cauchy–Schwarz over the slots.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1

open _root_.BoseGases Submission.BoseGases

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

/-- On `Ac` the mean-free fibre `slotFibre` is the bare mean-subtracted fibre. -/
lemma slotFibre_eq {n : ℕ} (volA : ℝ) {Ac : Set (EuclideanSpace ℝ (Fin 3))} {i : Fin n}
    {Ψ : X n → ℝ} (x : X n) :
    ∀ z ∈ Ac, slotFibre volA Ac i Ψ x z
      = Ψ (Function.update x i z) - volA⁻¹ * ∫ w in Ac, Ψ (Function.update x i w) := by
  intro z hz
  rw [slotFibre, boxQInd_update_eq, Set.indicator_of_mem hz, one_mul, div_eq_inv_mul,
    mul_one]

/-- The square of the mean-free fibre is integrable on the box `Ac`. -/
lemma integrableOn_slotFibre_sq {n : ℕ} {a volA : ℝ} (ha : 0 < a)
    {Ac : Set (EuclideanSpace ℝ (Fin 3))} (hAcm : MeasurableSet Ac)
    (hAc : Ac ⊆ Submission.BoseGases.acube a)
    {Ψ : X n → ℝ} (hΨ : Continuous Ψ) (i : Fin n) (x : X n) :
    IntegrableOn (fun z => (slotFibre volA Ac i Ψ x z) ^ 2) Ac volume := by
  set m : ℝ := volA⁻¹ * ∫ w in Ac, Ψ (Function.update x i w) with hm
  have hcont : Continuous (fun z : EuclideanSpace ℝ (Fin 3) =>
      Ψ (Function.update x i z) - m) :=
    (hΨ.comp (continuous_const.update i continuous_id)).sub continuous_const
  have h1 : IntegrableOn (fun z : EuclideanSpace ℝ (Fin 3) =>
      (Ψ (Function.update x i z) - m) ^ 2) Ac volume :=
    (((hcont.pow 2)).continuousOn.integrableOn_compact
      (Submission.BoseGases.acube_compact ha)).mono_set hAc
  exact h1.congr_fun (fun z hz => by rw [slotFibre_eq volA x z hz, hm]) hAcm

/-- **The windowed real mode is mean-free on the box.** -/
lemma winModeRe_mean_zero {n : ℕ} {a volA : ℝ} (ha : 0 < a)
    {Ac : Set (EuclideanSpace ℝ (Fin 3))} (hAcm : MeasurableSet Ac)
    (hAc : Ac ⊆ Submission.BoseGases.acube a)
    (hvol : volA = (MeasureTheory.volume Ac).toReal) (hvolpos : 0 < volA)
    {χ : EuclideanSpace ℝ (Fin 3) → ℝ} (hχ : Continuous χ)
    (q : EuclideanSpace ℝ (Fin 3)) :
    (∫ z in Ac, boxWinModeReGen volA Ac χ q z) = 0 := by
  have hcont : Continuous (fun z : EuclideanSpace ℝ (Fin 3) =>
      χ z * Real.cos (inner ℝ q z)) :=
    hχ.mul (Real.continuous_cos.comp (continuous_const.inner continuous_id))
  have hint : IntegrableOn (fun z : EuclideanSpace ℝ (Fin 3) =>
      χ z * Real.cos (inner ℝ q z)) Ac volume :=
    (hcont.continuousOn.integrableOn_compact
      (Submission.BoseGases.acube_compact ha)).mono_set hAc
  haveI : IsFiniteMeasure ((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict Ac) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact lt_of_le_of_lt (measure_mono hAc) (Submission.BoseGases.acube_lt_top a ha.le)
  have hpt : ∀ z ∈ Ac, boxWinModeReGen volA Ac χ q z
      = χ z * Real.cos (inner ℝ q z)
        - volA⁻¹ * ∫ w in Ac, χ w * Real.cos (inner ℝ q w) := by
    intro z hz
    rw [boxWinModeReGen, Set.indicator_of_mem hz, one_mul]
  have hconstInt : (∫ _z in Ac, volA⁻¹ * ∫ w in Ac, χ w * Real.cos (inner ℝ q w))
      = (volA⁻¹ * ∫ w in Ac, χ w * Real.cos (inner ℝ q w)) * volA := by
    rw [MeasureTheory.setIntegral_const, Measure.real_def, ← hvol]
    rw [smul_eq_mul, mul_comm]
  rw [setIntegral_congr_fun hAcm hpt,
    integral_sub hint (integrable_const (volA⁻¹ * ∫ w in Ac, χ w * Real.cos (inner ℝ q w))),
    hconstInt]
  field_simp
  ring

/-- **The windowed imaginary mode is mean-free on the box.** -/
lemma winModeIm_mean_zero {n : ℕ} {a volA : ℝ} (ha : 0 < a)
    {Ac : Set (EuclideanSpace ℝ (Fin 3))} (hAcm : MeasurableSet Ac)
    (hAc : Ac ⊆ Submission.BoseGases.acube a)
    (hvol : volA = (MeasureTheory.volume Ac).toReal) (hvolpos : 0 < volA)
    {χ : EuclideanSpace ℝ (Fin 3) → ℝ} (hχ : Continuous χ)
    (q : EuclideanSpace ℝ (Fin 3)) :
    (∫ z in Ac, boxWinModeImGen volA Ac χ q z) = 0 := by
  have hcont : Continuous (fun z : EuclideanSpace ℝ (Fin 3) =>
      χ z * Real.sin (inner ℝ q z)) :=
    hχ.mul (Real.continuous_sin.comp (continuous_const.inner continuous_id))
  have hint : IntegrableOn (fun z : EuclideanSpace ℝ (Fin 3) =>
      χ z * Real.sin (inner ℝ q z)) Ac volume :=
    (hcont.continuousOn.integrableOn_compact
      (Submission.BoseGases.acube_compact ha)).mono_set hAc
  haveI : IsFiniteMeasure ((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict Ac) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact lt_of_le_of_lt (measure_mono hAc) (Submission.BoseGases.acube_lt_top a ha.le)
  have hpt : ∀ z ∈ Ac, boxWinModeImGen volA Ac χ q z
      = -(χ z * Real.sin (inner ℝ q z)
        - volA⁻¹ * ∫ w in Ac, χ w * Real.sin (inner ℝ q w)) := by
    intro z hz
    rw [boxWinModeImGen, Set.indicator_of_mem hz, one_mul]
  have hconstInt : (∫ _z in Ac, volA⁻¹ * ∫ w in Ac, χ w * Real.sin (inner ℝ q w))
      = (volA⁻¹ * ∫ w in Ac, χ w * Real.sin (inner ℝ q w)) * volA := by
    rw [MeasureTheory.setIntegral_const, Measure.real_def, ← hvol]
    rw [smul_eq_mul, mul_comm]
  rw [setIntegral_congr_fun hAcm hpt, integral_neg,
    integral_sub hint (integrable_const (volA⁻¹ * ∫ w in Ac, χ w * Real.sin (inner ℝ q w))),
    hconstInt]
  field_simp
  ring

/-- **The real slot amplitude is a `χ·cos` overlap against the mean-free fibre.** -/
lemma slotAmp_re_eq {n : ℕ} {a volA : ℝ} (ha : 0 < a)
    {Ac : Set (EuclideanSpace ℝ (Fin 3))} (hAcm : MeasurableSet Ac)
    (hAc : Ac ⊆ Submission.BoseGases.acube a)
    (hvol : volA = (MeasureTheory.volume Ac).toReal) (hvolpos : 0 < volA)
    {χ : EuclideanSpace ℝ (Fin 3) → ℝ} (hχ : Continuous χ)
    {Ψ : X n → ℝ} (hΨ : Continuous Ψ) (i : Fin n) (x : X n)
    (q : EuclideanSpace ℝ (Fin 3)) :
    (∫ z in Ac, boxWinModeReGen volA Ac χ q z * Ψ (Function.update x i z))
      = ∫ z in Ac, χ z * Real.cos (inner ℝ q z) * slotFibre volA Ac i Ψ x z := by
  set g : EuclideanSpace ℝ (Fin 3) → ℝ := fun z => χ z * Real.cos (inner ℝ q z) with hg
  set c : ℝ := volA⁻¹ * ∫ z in Ac, g z with hc
  set mm : ℝ := volA⁻¹ * ∫ z in Ac, Ψ (Function.update x i z) with hm
  have hcontG : Continuous g :=
    hχ.mul (Real.continuous_cos.comp (continuous_const.inner continuous_id))
  have hcontU : Continuous (fun z : EuclideanSpace ℝ (Fin 3) =>
      Ψ (Function.update x i z)) :=
    hΨ.comp (continuous_const.update i continuous_id)
  have hKG : IsCompact (Submission.BoseGases.acube a) :=
    Submission.BoseGases.acube_compact ha
  have hintG : IntegrableOn g Ac volume :=
    (hcontG.continuousOn.integrableOn_compact hKG).mono_set hAc
  have hintU : IntegrableOn (fun z : EuclideanSpace ℝ (Fin 3) =>
      Ψ (Function.update x i z)) Ac volume :=
    (hcontU.continuousOn.integrableOn_compact hKG).mono_set hAc
  have hprod : IntegrableOn (fun z : EuclideanSpace ℝ (Fin 3) =>
      g z * Ψ (Function.update x i z)) Ac volume :=
    ((hcontG.mul hcontU).continuousOn.integrableOn_compact hKG).mono_set hAc
  have hptL : ∀ z ∈ Ac, boxWinModeReGen volA Ac χ q z * Ψ (Function.update x i z)
      = (g z - c) * Ψ (Function.update x i z) := by
    intro z hz
    rw [boxWinModeReGen, hg, hc, Set.indicator_of_mem hz, one_mul]
  have hL : (∫ z in Ac, boxWinModeReGen volA Ac χ q z * Ψ (Function.update x i z))
      = (∫ z in Ac, g z * Ψ (Function.update x i z))
        - c * (∫ z in Ac, Ψ (Function.update x i z)) := by
    rw [setIntegral_congr_fun hAcm hptL]
    rw [show (∫ z in Ac, (g z - c) * Ψ (Function.update x i z))
        = ∫ z in Ac, (g z * Ψ (Function.update x i z)
            - c * Ψ (Function.update x i z)) from
      setIntegral_congr_fun hAcm (fun z _ => by ring)]
    rw [integral_sub hprod (hintU.const_mul c), integral_const_mul]
  have hptR : ∀ z ∈ Ac, χ z * Real.cos (inner ℝ q z) * slotFibre volA Ac i Ψ x z
      = g z * (Ψ (Function.update x i z) - mm) := by
    intro z hz
    rw [slotFibre_eq volA x z hz, hg, hm]
  have hR : (∫ z in Ac, χ z * Real.cos (inner ℝ q z) * slotFibre volA Ac i Ψ x z)
      = (∫ z in Ac, g z * Ψ (Function.update x i z))
        - mm * (∫ z in Ac, g z) := by
    rw [setIntegral_congr_fun hAcm hptR]
    rw [show (∫ z in Ac, g z * (Ψ (Function.update x i z) - mm))
        = ∫ z in Ac, (g z * Ψ (Function.update x i z) - mm * g z) from
      setIntegral_congr_fun hAcm (fun z _ => by ring)]
    rw [integral_sub hprod (hintG.const_mul mm), integral_const_mul]
  rw [hL, hR, hc, hm]
  ring

/-- **The imaginary slot amplitude is (minus) a `χ·sin` overlap against the mean-free fibre.** -/
lemma slotAmp_im_eq {n : ℕ} {a volA : ℝ} (ha : 0 < a)
    {Ac : Set (EuclideanSpace ℝ (Fin 3))} (hAcm : MeasurableSet Ac)
    (hAc : Ac ⊆ Submission.BoseGases.acube a)
    (hvol : volA = (MeasureTheory.volume Ac).toReal) (hvolpos : 0 < volA)
    {χ : EuclideanSpace ℝ (Fin 3) → ℝ} (hχ : Continuous χ)
    {Ψ : X n → ℝ} (hΨ : Continuous Ψ) (i : Fin n) (x : X n)
    (q : EuclideanSpace ℝ (Fin 3)) :
    (∫ z in Ac, boxWinModeImGen volA Ac χ q z * Ψ (Function.update x i z))
      = -(∫ z in Ac, χ z * Real.sin (inner ℝ q z) * slotFibre volA Ac i Ψ x z) := by
  set g : EuclideanSpace ℝ (Fin 3) → ℝ := fun z => χ z * Real.sin (inner ℝ q z) with hg
  set c : ℝ := volA⁻¹ * ∫ z in Ac, g z with hc
  set mm : ℝ := volA⁻¹ * ∫ z in Ac, Ψ (Function.update x i z) with hm
  have hcontG : Continuous g :=
    hχ.mul (Real.continuous_sin.comp (continuous_const.inner continuous_id))
  have hcontU : Continuous (fun z : EuclideanSpace ℝ (Fin 3) =>
      Ψ (Function.update x i z)) :=
    hΨ.comp (continuous_const.update i continuous_id)
  have hKG : IsCompact (Submission.BoseGases.acube a) :=
    Submission.BoseGases.acube_compact ha
  have hintG : IntegrableOn g Ac volume :=
    (hcontG.continuousOn.integrableOn_compact hKG).mono_set hAc
  have hintU : IntegrableOn (fun z : EuclideanSpace ℝ (Fin 3) =>
      Ψ (Function.update x i z)) Ac volume :=
    (hcontU.continuousOn.integrableOn_compact hKG).mono_set hAc
  have hprod : IntegrableOn (fun z : EuclideanSpace ℝ (Fin 3) =>
      g z * Ψ (Function.update x i z)) Ac volume :=
    ((hcontG.mul hcontU).continuousOn.integrableOn_compact hKG).mono_set hAc
  have hptL : ∀ z ∈ Ac, boxWinModeImGen volA Ac χ q z * Ψ (Function.update x i z)
      = -(g z - c) * Ψ (Function.update x i z) := by
    intro z hz
    rw [boxWinModeImGen, hg, hc, Set.indicator_of_mem hz, one_mul]
  have hL : (∫ z in Ac, boxWinModeImGen volA Ac χ q z * Ψ (Function.update x i z))
      = -((∫ z in Ac, g z * Ψ (Function.update x i z))
        - c * (∫ z in Ac, Ψ (Function.update x i z))) := by
    rw [setIntegral_congr_fun hAcm hptL]
    rw [show (∫ z in Ac, -(g z - c) * Ψ (Function.update x i z))
        = - ∫ z in Ac, (g z * Ψ (Function.update x i z)
            - c * Ψ (Function.update x i z)) from by
      rw [← integral_neg]
      exact setIntegral_congr_fun hAcm (fun z _ => by ring)]
    rw [integral_sub hprod (hintU.const_mul c), integral_const_mul]
  have hptR : ∀ z ∈ Ac, χ z * Real.sin (inner ℝ q z) * slotFibre volA Ac i Ψ x z
      = g z * (Ψ (Function.update x i z) - mm) := by
    intro z hz
    rw [slotFibre_eq volA x z hz, hg, hm]
  have hR : (∫ z in Ac, χ z * Real.sin (inner ℝ q z) * slotFibre volA Ac i Ψ x z)
      = (∫ z in Ac, g z * Ψ (Function.update x i z))
        - mm * (∫ z in Ac, g z) := by
    rw [setIntegral_congr_fun hAcm hptR]
    rw [show (∫ z in Ac, g z * (Ψ (Function.update x i z) - mm))
        = ∫ z in Ac, (g z * Ψ (Function.update x i z) - mm * g z) from
      setIntegral_congr_fun hAcm (fun z _ => by ring)]
    rw [integral_sub hprod (hintG.const_mul mm), integral_const_mul]
  rw [hL, hR, hc, hm]
  ring

/-- **The window weight bound**: `∫_Ac (χ·Q)² ≤ κ²∫_Ac Q²` for `0 ≤ χ ≤ κ`. -/
lemma slotFibre_sq_weight_le {n : ℕ} {a volA κ : ℝ} (ha : 0 < a)
    {Ac : Set (EuclideanSpace ℝ (Fin 3))} (hAcm : MeasurableSet Ac)
    (hAc : Ac ⊆ Submission.BoseGases.acube a)
    {χ : EuclideanSpace ℝ (Fin 3) → ℝ} (hχnn : ∀ z, 0 ≤ χ z) (hκ : ∀ z, χ z ≤ κ)
    (hκ0 : 0 ≤ κ)
    {Ψ : X n → ℝ} (hΨ : Continuous Ψ) (i : Fin n) (x : X n) :
    (∫ z in Ac, (χ z * slotFibre volA Ac i Ψ x z) ^ 2)
      ≤ κ ^ 2 * ∫ z in Ac, (slotFibre volA Ac i Ψ x z) ^ 2 := by
  have hInt : IntegrableOn (fun z => κ ^ 2 * (slotFibre volA Ac i Ψ x z) ^ 2) Ac volume :=
    (integrableOn_slotFibre_sq ha hAcm hAc hΨ i x).const_mul (κ ^ 2)
  have hmono := integral_mono_of_nonneg
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict Ac)
    (f := fun z => (χ z * slotFibre volA Ac i Ψ x z) ^ 2)
    (g := fun z => κ ^ 2 * (slotFibre volA Ac i Ψ x z) ^ 2)
    (Eventually.of_forall fun z => sq_nonneg _) hInt
    (Eventually.of_forall fun z => by
      show (χ z * slotFibre volA Ac i Ψ x z) ^ 2
        ≤ κ ^ 2 * (slotFibre volA Ac i Ψ x z) ^ 2
      rw [mul_pow]
      have h1 : (χ z) ^ 2 ≤ κ ^ 2 := by nlinarith [hχnn z, hκ z, hκ0]
      have h2 : 0 ≤ (slotFibre volA Ac i Ψ x z) ^ 2 := sq_nonneg _
      nlinarith)
  have hconst : (∫ z, κ ^ 2 * (slotFibre volA Ac i Ψ x z) ^ 2
      ∂((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict Ac))
      = κ ^ 2 * ∫ z in Ac, (slotFibre volA Ac i Ψ x z) ^ 2 :=
    integral_const_mul _ _
  rw [hconst] at hmono
  exact hmono

/-- **Cauchy–Schwarz over the slots.**  The `q`-frame integrand is bounded by
`volA⁻¹(N+1)` times the sum of the slot amplitudes. -/
lemma frameIntegrand_le {N : ℕ} {volA : ℝ} (hvolpos : 0 < volA)
    {Ac : Set (EuclideanSpace ℝ (Fin 3))}
    {χ : EuclideanSpace ℝ (Fin 3) → ℝ} {Ψ : X (N + 1) → ℝ}
    (q : EuclideanSpace ℝ (Fin 3)) (x : X (N + 1)) :
    frameIntegrand volA Ac χ Ψ q x
      ≤ volA⁻¹ * (((N + 1 : ℕ)) : ℝ) * ∑ i : Fin (N + 1),
          Ac.indicator (fun _ => (1 : ℝ)) (x i) *
            ((∫ z in Ac, boxWinModeReGen volA Ac χ q z * Ψ (Function.update x i z)) ^ 2
              + (∫ z in Ac, boxWinModeImGen volA Ac χ q z * Ψ (Function.update x i z)) ^ 2) := by
  have hsq : (Real.sqrt volA)⁻¹ ^ 2 = volA⁻¹ := by
    rw [inv_pow, Real.sq_sqrt hvolpos.le]
  have hidem : ∀ (i : Fin (N + 1)) (y : ℝ),
      (Ac.indicator (fun _ => (1 : ℝ)) (x i) * y) ^ 2
        = Ac.indicator (fun _ => (1 : ℝ)) (x i) * y ^ 2 := by
    intro i y
    by_cases h : x i ∈ Ac
    · rw [Set.indicator_of_mem h, one_mul, one_mul]
    · rw [Set.indicator_of_notMem h]; ring
  have hpos : (0 : ℝ) ≤ volA⁻¹ := inv_nonneg.mpr hvolpos.le
  -- ### the real half
  have hRe : (boxTauAnnGen volA Ac (boxWinModeReGen volA Ac χ q) Ψ x) ^ 2
      ≤ volA⁻¹ * (((N + 1 : ℕ)) : ℝ) * ∑ i : Fin (N + 1),
          Ac.indicator (fun _ => (1 : ℝ)) (x i) *
            (∫ z in Ac, boxWinModeReGen volA Ac χ q z * Ψ (Function.update x i z)) ^ 2 := by
    have hdef : boxTauAnnGen volA Ac (boxWinModeReGen volA Ac χ q) Ψ x
        = (Real.sqrt volA)⁻¹ * ∑ i : Fin (N + 1),
            Ac.indicator (fun _ => (1 : ℝ)) (x i) *
              ∫ z in Ac, boxWinModeReGen volA Ac χ q z * Ψ (Function.update x i z) := rfl
    have hcs := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin (N + 1))))
      (f := fun i : Fin (N + 1) => Ac.indicator (fun _ => (1 : ℝ)) (x i) *
        ∫ z in Ac, boxWinModeReGen volA Ac χ q z * Ψ (Function.update x i z))
    rw [Finset.card_fin] at hcs
    push_cast at hcs
    have hsumeq : (∑ i : Fin (N + 1), (Ac.indicator (fun _ => (1 : ℝ)) (x i) *
          ∫ z in Ac, boxWinModeReGen volA Ac χ q z * Ψ (Function.update x i z)) ^ 2)
        = ∑ i : Fin (N + 1), Ac.indicator (fun _ => (1 : ℝ)) (x i) *
            (∫ z in Ac, boxWinModeReGen volA Ac χ q z * Ψ (Function.update x i z)) ^ 2 :=
      Finset.sum_congr rfl (fun i _ => hidem i _)
    calc (boxTauAnnGen volA Ac (boxWinModeReGen volA Ac χ q) Ψ x) ^ 2
        = volA⁻¹ * (∑ i : Fin (N + 1), (Ac.indicator (fun _ => (1 : ℝ)) (x i) *
              ∫ z in Ac, boxWinModeReGen volA Ac χ q z
                * Ψ (Function.update x i z))) ^ 2 := by
          rw [hdef, mul_pow, hsq]
      _ ≤ volA⁻¹ * ((((N + 1 : ℕ)) : ℝ) * ∑ i : Fin (N + 1),
            (Ac.indicator (fun _ => (1 : ℝ)) (x i) *
              ∫ z in Ac, boxWinModeReGen volA Ac χ q z
                * Ψ (Function.update x i z)) ^ 2) :=
          mul_le_mul_of_nonneg_left (by simpa using hcs) hpos
      _ = volA⁻¹ * (((N + 1 : ℕ)) : ℝ) * ∑ i : Fin (N + 1),
            Ac.indicator (fun _ => (1 : ℝ)) (x i) *
              (∫ z in Ac, boxWinModeReGen volA Ac χ q z * Ψ (Function.update x i z)) ^ 2 := by
          rw [hsumeq]; ring
  -- ### the imaginary half
  have hIm : (boxTauAnnGen volA Ac (boxWinModeImGen volA Ac χ q) Ψ x) ^ 2
      ≤ volA⁻¹ * (((N + 1 : ℕ)) : ℝ) * ∑ i : Fin (N + 1),
          Ac.indicator (fun _ => (1 : ℝ)) (x i) *
            (∫ z in Ac, boxWinModeImGen volA Ac χ q z * Ψ (Function.update x i z)) ^ 2 := by
    have hdef : boxTauAnnGen volA Ac (boxWinModeImGen volA Ac χ q) Ψ x
        = (Real.sqrt volA)⁻¹ * ∑ i : Fin (N + 1),
            Ac.indicator (fun _ => (1 : ℝ)) (x i) *
              ∫ z in Ac, boxWinModeImGen volA Ac χ q z * Ψ (Function.update x i z) := rfl
    have hcs := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin (N + 1))))
      (f := fun i : Fin (N + 1) => Ac.indicator (fun _ => (1 : ℝ)) (x i) *
        ∫ z in Ac, boxWinModeImGen volA Ac χ q z * Ψ (Function.update x i z))
    rw [Finset.card_fin] at hcs
    push_cast at hcs
    have hsumeq : (∑ i : Fin (N + 1), (Ac.indicator (fun _ => (1 : ℝ)) (x i) *
          ∫ z in Ac, boxWinModeImGen volA Ac χ q z * Ψ (Function.update x i z)) ^ 2)
        = ∑ i : Fin (N + 1), Ac.indicator (fun _ => (1 : ℝ)) (x i) *
            (∫ z in Ac, boxWinModeImGen volA Ac χ q z * Ψ (Function.update x i z)) ^ 2 :=
      Finset.sum_congr rfl (fun i _ => hidem i _)
    calc (boxTauAnnGen volA Ac (boxWinModeImGen volA Ac χ q) Ψ x) ^ 2
        = volA⁻¹ * (∑ i : Fin (N + 1), (Ac.indicator (fun _ => (1 : ℝ)) (x i) *
              ∫ z in Ac, boxWinModeImGen volA Ac χ q z
                * Ψ (Function.update x i z))) ^ 2 := by
          rw [hdef, mul_pow, hsq]
      _ ≤ volA⁻¹ * ((((N + 1 : ℕ)) : ℝ) * ∑ i : Fin (N + 1),
            (Ac.indicator (fun _ => (1 : ℝ)) (x i) *
              ∫ z in Ac, boxWinModeImGen volA Ac χ q z
                * Ψ (Function.update x i z)) ^ 2) :=
          mul_le_mul_of_nonneg_left (by simpa using hcs) hpos
      _ = volA⁻¹ * (((N + 1 : ℕ)) : ℝ) * ∑ i : Fin (N + 1),
            Ac.indicator (fun _ => (1 : ℝ)) (x i) *
              (∫ z in Ac, boxWinModeImGen volA Ac χ q z * Ψ (Function.update x i z)) ^ 2 := by
          rw [hsumeq]; ring
  -- ### combine
  have hsumsplit : (∑ i : Fin (N + 1), Ac.indicator (fun _ => (1 : ℝ)) (x i) *
        ((∫ z in Ac, boxWinModeReGen volA Ac χ q z * Ψ (Function.update x i z)) ^ 2
          + (∫ z in Ac, boxWinModeImGen volA Ac χ q z
              * Ψ (Function.update x i z)) ^ 2))
      = (∑ i : Fin (N + 1), Ac.indicator (fun _ => (1 : ℝ)) (x i) *
          (∫ z in Ac, boxWinModeReGen volA Ac χ q z * Ψ (Function.update x i z)) ^ 2)
        + (∑ i : Fin (N + 1), Ac.indicator (fun _ => (1 : ℝ)) (x i) *
          (∫ z in Ac, boxWinModeImGen volA Ac χ q z * Ψ (Function.update x i z)) ^ 2) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [frameIntegrand, hsumsplit]
  nlinarith [hRe, hIm]

end Work.BoseFixB1
