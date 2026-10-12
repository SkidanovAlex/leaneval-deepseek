import Mathlib.Order.CompletePartialOrder
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB1.BoxFrameDefs
import Submission.Work.BoseFixB1.aesm_wSmallPair_pair
import Submission.Work.BoseFixB1.measurable_tBamp_boxQInd_pair
import Submission.Work.SlotWord.integrable_fibre_tBdiagFormInd_of_decay
import Submission.Work.SmallBoxTBWord.tBamp_norm_le_of_bound
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S

open MeasureTheory Filter

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-!
# `Work.BoseFixB1S.mfSpecGeDivDirichletB1`

The sliding small-box spectral word dominates half of the full (windowed, `Q_B`-projected)
Dirichlet form, minus the mass term, **at the corpus cutoff `χ_B = chiB ℓ d u` and an arbitrary
positive normalisation `volA`**:

    `tBwordKinInd ℓ (dlBox ℓ d u) volA (chiB ℓ d u) c Φ`
      `≥ ½·tBdiagFormInd … (·)² Φ − 2c²·tBdiagFormInd … 1 Φ`.

This is `Work.BoseFixB1S.sbKin_ge_half_fullSpectral` with the repointed cutoff `chiSmallB M`
replaced by the corpus cutoff `chiB` (and the volume `boxMass` by an arbitrary `volA > 0`).
The argument is identical and purely pointwise in the momentum: for `r ≥ 0`,

    `r² ≤ 2·[r−c]₊² + 4c²`,

so the symbol comparison is immediate; the only work is the bookkeeping of Lean's
`¬Integrable ⇒ 0` convention for the Bochner integral, controlled by the abstract lemma
`half_integral_le_of_bdd` (here `transfer_le_of_bdd`): whenever `∫⁻(‖p‖²·K)` is infinite the
Bochner integrals vanish, and otherwise the boundedness of `K` (from
`Work.SmallBoxTBWord.tBamp_norm_le_of_bound`) makes all three integrals finite.

The only new ingredient relative to `sbKin_ge_half_fullSpectral` is `abs_boxQInd_le_general`:
FS's box projection `P_{B,i}` at an *arbitrary* normalisation `volA > 0` is bounded on the
ambient box by `(1/volA)·|A|·B` whenever `|Φ| ≤ B` there.
-/

/-! ## 1. The abstract transfer lemma (sharp, `ε`-parametrised) -/

/-- **Symbol comparison with the mass term.**  For measurable nonnegative `K, S, R` with
`S ≤ R` and `(1−ε)·R ≤ S + (1+1/ε)c²` (some `0 < ε ≤ 1`), if `K` is bounded on the region
`{R ≤ 1}` (which has finite measure), then

    `(1−ε)∫R·K ≤ ∫S·K + (1+1/ε)c²∫K`.

The hypotheses `hfin`, `hD` control the `ℝ`-valued integral's `¬Integrable ⇒ 0` convention:
they force `∫⁻K < ∞` as soon as `∫⁻R·K < ∞`. -/
private theorem transfer_le_of_bdd {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {K S R : α → ℝ} (hKm : Measurable K) (hSm : Measurable S) (hRm : Measurable R)
    (hK0 : ∀ a, 0 ≤ K a) (hS0 : ∀ a, 0 ≤ S a) (hR0 : ∀ a, 0 ≤ R a)
    {ε c : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hSR : ∀ a, (1 - ε) * R a ≤ S a + (1 + 1 / ε) * c ^ 2) (hSleR : ∀ a, S a ≤ R a)
    (hfin : μ {a | R a ≤ 1} < ⊤) {D : ℝ} (hD0 : 0 ≤ D)
    (hD : ∀ a, R a ≤ 1 → K a ≤ D) :
    (1 - ε) * (∫ a, R a * K a ∂μ)
      ≤ (∫ a, S a * K a ∂μ) + (1 + 1 / ε) * c ^ 2 * (∫ a, K a ∂μ) := by
  classical
  have h1e : (0 : ℝ) ≤ 1 - ε := by linarith
  have hAeq : (∫ a, S a * K a ∂μ) = (∫⁻ a, ENNReal.ofReal (S a * K a) ∂μ).toReal :=
    integral_eq_lintegral_of_nonneg_ae (f := fun a => S a * K a)
      (ae_of_all _ fun a => mul_nonneg (hS0 a) (hK0 a)) (hSm.mul hKm).aestronglyMeasurable
  have hCeq : (∫ a, K a ∂μ) = (∫⁻ a, ENNReal.ofReal (K a) ∂μ).toReal :=
    integral_eq_lintegral_of_nonneg_ae (f := K) (ae_of_all _ hK0) hKm.aestronglyMeasurable
  have hBeq : (∫ a, R a * K a ∂μ) = (∫⁻ a, ENNReal.ofReal (R a * K a) ∂μ).toReal :=
    integral_eq_lintegral_of_nonneg_ae (f := fun a => R a * K a)
      (ae_of_all _ fun a => mul_nonneg (hR0 a) (hK0 a)) (hRm.mul hKm).aestronglyMeasurable
  rw [hAeq, hCeq, hBeq]
  by_cases hZ : (∫⁻ a, ENNReal.ofReal (R a * K a) ∂μ) = ⊤
  · rw [hZ, ENNReal.toReal_top, mul_zero]
    exact add_nonneg ENNReal.toReal_nonneg (mul_nonneg (by positivity) ENNReal.toReal_nonneg)
  · have hP : MeasurableSet {a | R a ≤ 1} := by
      have h : MeasurableSet (R ⁻¹' Set.Iic (1 : ℝ)) := hRm measurableSet_Iic
      have heq : {a | R a ≤ 1} = R ⁻¹' Set.Iic (1 : ℝ) := by ext a; simp
      rwa [heq]
    have hIndnn : ∀ a, 0 ≤ ({a | R a ≤ 1}.indicator (fun _ => (1 : ℝ)) a) := fun a =>
      Set.indicator_nonneg (fun _ _ => zero_le_one) a
    have hpt : ∀ a, K a ≤ D * ({a | R a ≤ 1}.indicator (fun _ => (1 : ℝ)) a) + R a * K a := by
      intro a
      by_cases ha : R a ≤ 1
      · rw [Set.indicator_of_mem (show a ∈ {a | R a ≤ 1} from ha), mul_one]
        nlinarith [hD a ha, mul_nonneg (hR0 a) (hK0 a)]
      · rw [Set.indicator_of_notMem (show a ∉ {a | R a ≤ 1} from ha), mul_zero, zero_add]
        nlinarith [hK0 a, not_le.mp ha]
    have hWmeas : Measurable
        (fun a : α => ENNReal.ofReal (D * ({a | R a ≤ 1}.indicator (fun _ => (1 : ℝ)) a))) :=
      ENNReal.measurable_ofReal.comp (measurable_const.mul (measurable_const.indicator hP))
    have hYle : (∫⁻ a, ENNReal.ofReal (K a) ∂μ)
        ≤ ENNReal.ofReal D * μ {a | R a ≤ 1} + ∫⁻ a, ENNReal.ofReal (R a * K a) ∂μ := by
      have h1 : (∫⁻ a, ENNReal.ofReal (D * ({a | R a ≤ 1}.indicator (fun _ => (1 : ℝ)) a))
            ∂μ)
          = ENNReal.ofReal D * (∫⁻ a, ({a | R a ≤ 1}.indicator
              (fun _ => (1 : ENNReal)) a) ∂μ) := by
        calc (∫⁻ a, ENNReal.ofReal (D * ({a | R a ≤ 1}.indicator (fun _ => (1 : ℝ)) a)) ∂μ)
            = ∫⁻ a, ENNReal.ofReal D * ({a | R a ≤ 1}.indicator
                (fun _ => (1 : ENNReal)) a) ∂μ := by
              refine lintegral_congr fun a => ?_
              rw [ENNReal.ofReal_mul hD0]
              congr 1
              by_cases ha : a ∈ {a | R a ≤ 1}
              · rw [Set.indicator_of_mem ha, Set.indicator_of_mem ha]; simp
              · rw [Set.indicator_of_notMem ha, Set.indicator_of_notMem ha]; simp
          _ = ENNReal.ofReal D * (∫⁻ a, ({a | R a ≤ 1}.indicator
                (fun _ => (1 : ENNReal)) a) ∂μ) :=
              lintegral_const_mul _ (measurable_const.indicator hP)
      calc (∫⁻ a, ENNReal.ofReal (K a) ∂μ)
          ≤ ∫⁻ a, ENNReal.ofReal (D * ({a | R a ≤ 1}.indicator (fun _ => (1 : ℝ)) a)
              + R a * K a) ∂μ :=
            lintegral_mono fun a => ENNReal.ofReal_le_ofReal (hpt a)
        _ = ∫⁻ a, (ENNReal.ofReal (D * ({a | R a ≤ 1}.indicator (fun _ => (1 : ℝ)) a))
              + ENNReal.ofReal (R a * K a)) ∂μ := by
            refine lintegral_congr fun a => ?_
            rw [ENNReal.ofReal_add (mul_nonneg hD0 (hIndnn a)) (mul_nonneg (hR0 a) (hK0 a))]
        _ = (∫⁻ a, ENNReal.ofReal (D * ({a | R a ≤ 1}.indicator (fun _ => (1 : ℝ)) a)) ∂μ)
              + ∫⁻ a, ENNReal.ofReal (R a * K a) ∂μ :=
            lintegral_add_left hWmeas (fun a => ENNReal.ofReal (R a * K a))
        _ = ENNReal.ofReal D * μ {a | R a ≤ 1} + ∫⁻ a, ENNReal.ofReal (R a * K a) ∂μ := by
            rw [h1, lintegral_indicator_const hP 1, one_mul]
    have hYfin : (∫⁻ a, ENNReal.ofReal (K a) ∂μ) ≠ ⊤ := by
      refine ne_of_lt (lt_of_le_of_lt hYle ?_)
      exact ENNReal.add_lt_top.mpr
        ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin, lt_top_iff_ne_top.mpr hZ⟩
    have hXfin : (∫⁻ a, ENNReal.ofReal (S a * K a) ∂μ) ≠ ⊤ := by
      refine ne_of_lt (lt_of_le_of_lt ?_ (lt_top_iff_ne_top.mpr hZ))
      exact lintegral_mono fun a =>
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (hSleR a) (hK0 a))
    have hpt2 : ∀ a, ENNReal.ofReal ((1 - ε) * (R a * K a))
        ≤ ENNReal.ofReal (S a * K a) + ENNReal.ofReal ((1 + 1 / ε) * c ^ 2 * K a) := by
      intro a
      rw [← ENNReal.ofReal_add (mul_nonneg (hS0 a) (hK0 a))
        (mul_nonneg (by positivity) (hK0 a))]
      refine ENNReal.ofReal_le_ofReal ?_
      nlinarith [hSR a, hK0 a]
    have hkey : ENNReal.ofReal (1 - ε) * (∫⁻ a, ENNReal.ofReal (R a * K a) ∂μ)
        ≤ (∫⁻ a, ENNReal.ofReal (S a * K a) ∂μ)
          + ENNReal.ofReal ((1 + 1 / ε) * c ^ 2) * (∫⁻ a, ENNReal.ofReal (K a) ∂μ) := by
      calc ENNReal.ofReal (1 - ε) * (∫⁻ a, ENNReal.ofReal (R a * K a) ∂μ)
          = ∫⁻ a, ENNReal.ofReal (1 - ε) * ENNReal.ofReal (R a * K a) ∂μ :=
            (lintegral_const_mul _ (ENNReal.measurable_ofReal.comp
              (hRm.mul hKm))).symm
        _ = ∫⁻ a, ENNReal.ofReal ((1 - ε) * (R a * K a)) ∂μ := by
            refine lintegral_congr fun a => ?_
            rw [ENNReal.ofReal_mul h1e]
        _ ≤ ∫⁻ a, (ENNReal.ofReal (S a * K a)
              + ENNReal.ofReal ((1 + 1 / ε) * c ^ 2 * K a)) ∂μ :=
            lintegral_mono hpt2
        _ = (∫⁻ a, ENNReal.ofReal (S a * K a) ∂μ)
              + ∫⁻ a, ENNReal.ofReal ((1 + 1 / ε) * c ^ 2 * K a) ∂μ :=
            lintegral_add_left (ENNReal.measurable_ofReal.comp (hSm.mul hKm))
              (fun a => ENNReal.ofReal ((1 + 1 / ε) * c ^ 2 * K a))
        _ = (∫⁻ a, ENNReal.ofReal (S a * K a) ∂μ)
              + ENNReal.ofReal ((1 + 1 / ε) * c ^ 2) * (∫⁻ a, ENNReal.ofReal (K a) ∂μ) := by
            congr 1
            calc ∫⁻ a, ENNReal.ofReal ((1 + 1 / ε) * c ^ 2 * K a) ∂μ
                = ∫⁻ a, ENNReal.ofReal ((1 + 1 / ε) * c ^ 2) * ENNReal.ofReal (K a) ∂μ := by
                  refine lintegral_congr fun a => ?_
                  rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (1 + 1 / ε) * c ^ 2)]
              _ = ENNReal.ofReal ((1 + 1 / ε) * c ^ 2) * (∫⁻ a, ENNReal.ofReal (K a) ∂μ) :=
                  lintegral_const_mul _ (ENNReal.measurable_ofReal.comp hKm)
    have hfin2 : ENNReal.ofReal ((1 + 1 / ε) * c ^ 2) * (∫⁻ a, ENNReal.ofReal (K a) ∂μ) < ⊤ :=
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.mpr hYfin)
    have hmono := ENNReal.toReal_mono
      (a := ENNReal.ofReal (1 - ε) * (∫⁻ a, ENNReal.ofReal (R a * K a) ∂μ))
      (b := (∫⁻ a, ENNReal.ofReal (S a * K a) ∂μ)
        + ENNReal.ofReal ((1 + 1 / ε) * c ^ 2) * (∫⁻ a, ENNReal.ofReal (K a) ∂μ))
      (lt_top_iff_ne_top.mp (ENNReal.add_lt_top.mpr ⟨lt_top_iff_ne_top.mpr hXfin, hfin2⟩))
      hkey
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal h1e,
      ENNReal.toReal_add hXfin (ne_of_lt hfin2), ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ (1 + 1 / ε) * c ^ 2)] at hmono
    linarith [hmono]

/-! ## 2. The pointwise symbol comparison -/

/-- `[r−c]₊²`-continuity (for measurability of the symbol). -/
private lemma continuous_fsKinCoeff (c : ℝ) : Continuous (Submission.BoseGases.fsKinCoeff c) := by
  unfold Submission.BoseGases.fsKinCoeff
  exact ((continuous_id.sub continuous_const).max continuous_const).pow 2

/-- **The sharp pointwise symbol inequality.**  For `r ≥ 0`, `c ∈ ℝ` and `0 < ε ≤ 1`,

    `(1−ε)·r² ≤ [r−c]₊² + (1+1/ε)·c²`.

(For `r ≥ c` this is `ε(r−c/ε)² + 2εc² ≥ 0` after multiplying by `ε`; for `r ≤ c` it is
`(1−ε)r² ≤ (1−ε)c² ≤ (1+1/ε)c²`.) -/
private lemma sharp_le_fsKinCoeff_add {c ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (r : ℝ)
    (hr : 0 ≤ r) :
    (1 - ε) * r ^ 2 ≤ Submission.BoseGases.fsKinCoeff c r + (1 + 1 / ε) * c ^ 2 := by
  by_cases h : r ≤ c
  · rw [Submission.BoseGases.fsKinCoeff_of_le h]
    have h1e : (0 : ℝ) ≤ 1 - ε := by linarith
    have h1 : (1 - ε) * r ^ 2 ≤ (1 - ε) * c ^ 2 :=
      mul_le_mul_of_nonneg_left (by nlinarith) h1e
    have h2 : (1 - ε) * c ^ 2 ≤ (1 + 1 / ε) * c ^ 2 := by
      refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg c)
      have : (0 : ℝ) < 1 / ε := by positivity
      linarith
    linarith
  · push_neg at h
    rw [Submission.BoseGases.fsKinCoeff, max_eq_left (by linarith : (0 : ℝ) ≤ r - c)]
    have hid : ε * ((r - c) ^ 2 + (1 + 1 / ε) * c ^ 2 - (1 - ε) * r ^ 2)
        = ε ^ 2 * (r - c / ε) ^ 2 + 2 * ε * c ^ 2 := by
      field_simp
      ring
    have key : 0 ≤ (r - c) ^ 2 + (1 + 1 / ε) * c ^ 2 - (1 - ε) * r ^ 2 := by
      refine (mul_nonneg_iff_of_pos_left hε).mp ?_
      rw [hid]
      positivity
    linarith

/-! ## 3. Measurability of the slot density in the momentum -/

/-- The `p`-density of a slot is measurable: the `(p,x)`-integrand is jointly measurable
(`Work.BoseFixB1.measurable_tBamp_boxQInd_pair`), so the parametric Bochner integral over
`x ∈ abox N ℓ` is strongly measurable in `p`
(`StronglyMeasurable.integral_prod_right'`). -/
private theorem measurable_slotDensity {N : ℕ} {A : Set ℝ³} (hA : MeasurableSet A)
    {volA : ℝ} {χ : ℝ³ → ℝ} (hχ : Continuous χ) {ℓ : ℝ}
    {Φ : Submission.BoseGases.X N → ℝ} (hΦ : Continuous Φ) (i : Fin N) :
    Measurable (fun p : ℝ³ => ∫ x in Submission.BoseGases.abox N ℓ,
      ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA A i Φ) i x‖ ^ 2) := by
  have hpair : Measurable (fun q : ℝ³ × Submission.BoseGases.X N =>
      ‖Work.SmallBoxTBWord.tBamp χ q.1 (Work.UBBInputs8.boxQInd volA A i Φ) i q.2‖ ^ 2) :=
    Work.BoseFixB1.measurable_tBamp_boxQInd_pair hA hχ hΦ.measurable i
  have hsm : StronglyMeasurable (fun p : ℝ³ => ∫ x : Submission.BoseGases.X N,
      ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA A i Φ) i x‖ ^ 2
        ∂((volume : Measure (Submission.BoseGases.X N)).restrict
            (Submission.BoseGases.abox N ℓ))) :=
    hpair.stronglyMeasurable.integral_prod_right'
      (ν := (volume : Measure (Submission.BoseGases.X N)).restrict
        (Submission.BoseGases.abox N ℓ))
  exact hsm.measurable

/-! ## 4. The box-projection bound at an arbitrary normalisation -/

/-- Replacing one coordinate of a point of the ambient box by a point of a set
`A ⊆ acube L` keeps the configuration in the ambient box. -/
private lemma update_mem_abox {N : ℕ} {L : ℝ} {A : Set ℝ³}
    (hAsub : A ⊆ Submission.BoseGases.acube L)
    {x : Submission.BoseGases.X N} (hx : x ∈ Submission.BoseGases.abox N L) {z : ℝ³}
    (hz : z ∈ A) (i : Fin N) : Function.update x i z ∈ Submission.BoseGases.abox N L := by
  rw [Submission.BoseGases.mem_abox_iff] at hx ⊢
  intro j
  rw [Function.update_apply]
  by_cases hj : j = i
  · rw [if_pos hj]; exact hAsub hz
  · rw [if_neg hj]; exact hx j

/-- The centred cube of side `a` is contained in the centred cube of side `max a 0`
(the latter has finite measure unconditionally). -/
private lemma acube_subset_acube_max (a : ℝ) :
    Submission.BoseGases.acube a ⊆ Submission.BoseGases.acube (max a 0) := by
  intro z hz
  simp only [Submission.BoseGases.mem_acube_iff] at hz ⊢
  intro m
  obtain ⟨h1, h2⟩ := hz m
  rcases le_total a 0 with ha | ha
  · rw [max_eq_right ha]
    exact ⟨by linarith, by linarith⟩
  · rw [max_eq_left ha]
    exact ⟨h1, h2⟩

/-- **The box projection is bounded by `(1 + (1/volA)·|A|)·B`.**  If `A ⊆ acube L` and
`|Φ| ≤ B` on the ambient box `abox N L`, then for every `x` in the ambient box the slot-`i`
mean-free projection `boxQInd volA A i Φ` is bounded by `B + (1/volA)·|A|·B` — with the
normalisation `volA` *arbitrary* positive (the mean is bounded by `|A|·B/volA`). -/
private lemma abs_boxQInd_le_general {N : ℕ} {A : Set ℝ³} {volA L : ℝ} (hvol : 0 < volA)
    (hAsub : A ⊆ Submission.BoseGases.acube L) {Φ : Submission.BoseGases.X N → ℝ} {B : ℝ}
    (hB : 0 ≤ B) (hb : ∀ y ∈ Submission.BoseGases.abox N L, |Φ y| ≤ B)
    (i : Fin N) {x : Submission.BoseGases.X N} (hx : x ∈ Submission.BoseGases.abox N L) :
    |Work.UBBInputs8.boxQInd volA A i Φ x|
      ≤ B + (1 / volA) * (volume : Measure ℝ³).real A * B := by
  have hQeq : Work.UBBInputs8.boxQInd volA A i Φ x
      = A.indicator (fun _ => (1 : ℝ)) (x i)
          * (Φ x - (1 / volA) * ∫ z in A, Φ (Function.update x i z)) := by
    simp only [Work.UBBInputs8.boxQInd, Work.UBBInputs8.boxPInd]
    ring
  have hAfin : (volume : Measure ℝ³) A < ⊤ :=
    lt_of_le_of_lt (measure_mono (hAsub.trans (acube_subset_acube_max L)))
      (Submission.BoseGases.acube_lt_top (max L 0) (le_max_right L 0))
  rw [hQeq]
  by_cases hxi : x i ∈ A
  · rw [Set.indicator_of_mem hxi, one_mul]
    have h1 : |Φ x| ≤ B := hb x hx
    have h2 : |(1 / volA) * ∫ z in A, Φ (Function.update x i z)|
        ≤ (1 / volA) * (volume : Measure ℝ³).real A * B := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / volA)]
      have hint : |∫ z in A, Φ (Function.update x i z)|
          ≤ (volume : Measure ℝ³).real A * B := by
        have hle := MeasureTheory.norm_setIntegral_le_of_norm_le_const (μ := (volume : Measure ℝ³))
          (s := A) (f := fun z : ℝ³ => Φ (Function.update x i z)) (C := B) hAfin ?_
        · simpa only [Real.norm_eq_abs, mul_comm] using hle
        · intro z hz
          rw [Real.norm_eq_abs]
          exact hb _ (update_mem_abox hAsub hx hz i)
      have hnn : (0 : ℝ) ≤ 1 / volA := by positivity
      calc (1 / volA) * |∫ z in A, Φ (Function.update x i z)|
          ≤ (1 / volA) * ((volume : Measure ℝ³).real A * B) :=
            mul_le_mul_of_nonneg_left hint hnn
        _ = (1 / volA) * (volume : Measure ℝ³).real A * B := by ring
    calc |Φ x - (1 / volA) * ∫ z in A, Φ (Function.update x i z)|
        ≤ |Φ x| + |(1 / volA) * ∫ z in A, Φ (Function.update x i z)| := abs_sub _ _
      _ ≤ B + (1 / volA) * (volume : Measure ℝ³).real A * B := add_le_add h1 h2
  · rw [Set.indicator_of_notMem hxi, zero_mul, abs_zero]
    exact add_nonneg hB (mul_nonneg (mul_nonneg (by positivity) measureReal_nonneg) hB)

/-! ## 5. The general domination theorem -/

/-- **Spectral domination at an arbitrary window and normalisation.**  For a continuous window
`χ` supported in the cube `acube ℓ`, a measurable box `A ⊆ acube ℓ` and any `volA > 0`,

    `tBwordKinInd ℓ A volA χ c Φ ≥ ½·tBdiagFormInd ℓ A volA χ (·)² Φ
        − 2c²·tBdiagFormInd ℓ A volA χ 1 Φ`. -/
theorem sbKin_ge_sharp_of_chi {ℓ : ℝ} (hℓ : 0 < ℓ) {A : Set ℝ³} (hA : MeasurableSet A)
    (hAsub : A ⊆ Submission.BoseGases.acube ℓ) {volA : ℝ} (hvol : 0 < volA)
    {χ : ℝ³ → ℝ} (hχc : Continuous χ)
    (hχsub : tsupport χ ⊆ Submission.BoseGases.acube ℓ)
    {N : ℕ} {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) (c : ℝ) (hc : 0 ≤ c)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    Work.UBBInputs8.tBwordKinInd ℓ A volA χ c Φ
      ≥ (1 - ε) * (Work.UBBInputs8.tBdiagFormInd ℓ A volA χ (fun r : ℝ => r ^ 2) Φ)
        - ((1 + 1 / ε) * c ^ 2) * (Work.UBBInputs8.tBdiagFormInd ℓ A volA χ
            (fun _ : ℝ => (1 : ℝ)) Φ) := by
  have hpi : (0 : ℝ) < ((2 * Real.pi) ^ 3)⁻¹ := Work.SmallBoxTBWord.twoPiInv3_pos
  -- the slot density
  set Kf : Fin N → ℝ³ → ℝ := fun i p => (ℓ ^ 3)⁻¹ *
      ∫ x in Submission.BoseGases.abox N ℓ,
        ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA A i Φ) i x‖ ^ 2 with hKf
  -- it is measurable
  have hKmeas : ∀ i : Fin N, Measurable (Kf i) := by
    intro i
    simp only [hKf]
    exact (measurable_slotDensity hA hχc hΦc i).const_mul _
  -- ## the uniform bound on the windowed amplitude
  obtain ⟨D₁, hD₁0, hD₁⟩ : ∃ D : ℝ, 0 ≤ D ∧ ∀ (i : Fin N) (p : ℝ³)
      (x : Submission.BoseGases.X N), x ∈ Submission.BoseGases.abox N ℓ →
      ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA A i Φ) i x‖ ≤ D := by
    obtain ⟨C₀, hC₀⟩ := (Submission.BoseGases.abox_compact N hℓ).exists_bound_of_continuousOn
      (s := Submission.BoseGases.abox N ℓ) (f := Φ) hΦc.continuousOn
    have hC₀' : ∀ y ∈ Submission.BoseGases.abox N ℓ, |Φ y| ≤ max C₀ 0 := by
      intro y hy
      have h1 : ‖Φ y‖ ≤ C₀ := hC₀ y hy
      rw [Real.norm_eq_abs] at h1
      exact le_trans h1 (le_max_left _ _)
    have hB0 : (0 : ℝ) ≤ max C₀ 0 := le_max_right _ _
    obtain ⟨Dχ, hDχ⟩ := (Submission.BoseGases.acube_compact hℓ).exists_bound_of_continuousOn
      (s := Submission.BoseGases.acube ℓ) (f := χ) hχc.continuousOn
    have hχb : ∀ z ∈ tsupport χ, |χ z| ≤ max Dχ 0 := by
      intro z hz
      have h1 : ‖χ z‖ ≤ Dχ := hDχ z (hχsub hz)
      rw [Real.norm_eq_abs] at h1
      exact le_trans h1 (le_max_left _ _)
    have hCχ0 : (0 : ℝ) ≤ max Dχ 0 := le_max_right _ _
    have hM0 : (0 : ℝ) ≤ max C₀ 0
        + (1 / volA) * (volume : Measure ℝ³).real A * max C₀ 0 :=
      add_nonneg hB0 (mul_nonneg (mul_nonneg (by positivity) measureReal_nonneg) hB0)
    refine ⟨max Dχ 0 * (max C₀ 0 + (1 / volA) * (volume : Measure ℝ³).real A * max C₀ 0)
        * (volume : Measure ℝ³).real (tsupport χ), by positivity, ?_⟩
    intro i p x hx
    exact Work.SmallBoxTBWord.tBamp_norm_le_of_bound hCχ0 hχb hχsub
      (fun y hy => abs_boxQInd_le_general hvol hAsub hB0 hC₀' i hy) i p hx
  -- the slot density is bounded
  have hKbdd : ∀ (i : Fin N) (p : ℝ³), Kf i p ≤ (ℓ ^ 3)⁻¹ *
      ((volume : Measure (Submission.BoseGases.X N)).real (Submission.BoseGases.abox N ℓ)
        * D₁ ^ 2) := by
    intro i p
    simp only [hKf]
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (pow_nonneg hℓ.le 3))
    have hconst : IntegrableOn (fun _ : Submission.BoseGases.X N => D₁ ^ 2)
        (Submission.BoseGases.abox N ℓ) volume :=
      IntegrableOn.of_bound (Submission.BoseGases.abox_lt_top N ℓ hℓ.le)
        aestronglyMeasurable_const (D₁ ^ 2)
        (Eventually.of_forall fun _ => by rw [Real.norm_of_nonneg (sq_nonneg D₁)])
    have hle : ∀ᵐ x ∂((volume : Measure (Submission.BoseGases.X N)).restrict
        (Submission.BoseGases.abox N ℓ)),
        ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA A i Φ) i x‖ ^ 2
          ≤ D₁ ^ 2 := by
      rw [ae_restrict_iff' (Submission.BoseGases.abox_measurable N ℓ)]
      exact Eventually.of_forall fun x hx =>
        pow_le_pow_left₀ (norm_nonneg _) (hD₁ i p x hx) 2
    calc (∫ x in Submission.BoseGases.abox N ℓ,
            ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA A i Φ) i x‖ ^ 2)
        ≤ ∫ x in Submission.BoseGases.abox N ℓ, D₁ ^ 2 :=
          integral_mono_of_nonneg (Eventually.of_forall fun x => sq_nonneg _) hconst hle
      _ = (volume : Measure (Submission.BoseGases.X N)).real (Submission.BoseGases.abox N ℓ)
            * D₁ ^ 2 := by
          rw [setIntegral_const, smul_eq_mul]
  -- the unit ball has finite volume
  have hball : (volume : Measure ℝ³) {p : ℝ³ | ‖p‖ ^ 2 ≤ 1} < ⊤ := by
    have hsub : {p : ℝ³ | ‖p‖ ^ 2 ≤ 1} ⊆ Metric.closedBall (0 : ℝ³) 1 := by
      intro p hp
      simp only [Metric.mem_closedBall, dist_zero_right]
      have hp' : ‖p‖ ^ 2 ≤ 1 := hp
      nlinarith [norm_nonneg p]
    exact lt_of_le_of_lt (measure_mono hsub) (isCompact_closedBall 0 1).measure_lt_top
  -- the per-slot comparison
  have key : ∀ i : Fin N, (1 - ε) * (∫ p : ℝ³, (fun r : ℝ => r ^ 2) ‖p‖ * Kf i p)
      ≤ (∫ p : ℝ³, Submission.BoseGases.fsKinCoeff c ‖p‖ * Kf i p)
        + (1 + 1 / ε) * c ^ 2 * (∫ p : ℝ³, Kf i p) := by
    intro i
    refine transfer_le_of_bdd (μ := (volume : Measure ℝ³)) (K := Kf i)
      (S := fun p : ℝ³ => Submission.BoseGases.fsKinCoeff c ‖p‖)
      (R := fun p : ℝ³ => ‖p‖ ^ 2) (ε := ε) (c := c)
      (D := (ℓ ^ 3)⁻¹ * ((volume : Measure (Submission.BoseGases.X N)).real
        (Submission.BoseGases.abox N ℓ) * D₁ ^ 2))
      (hKmeas i) ?_ ?_ ?_ ?_ ?_ hε0 hε1 ?_ ?_ hball ?_ ?_
    · exact (continuous_fsKinCoeff c).measurable.comp continuous_norm.measurable
    · exact (continuous_norm.pow 2).measurable
    · intro p
      simp only [hKf]
      exact mul_nonneg (inv_nonneg.mpr (pow_nonneg hℓ.le 3))
        (integral_nonneg fun x => sq_nonneg _)
    · exact fun p => Submission.BoseGases.fsKinCoeff_nonneg c ‖p‖
    · exact fun p => sq_nonneg ‖p‖
    · exact fun p => sharp_le_fsKinCoeff_add hε0 hε1 ‖p‖ (norm_nonneg p)
    · exact fun p => Submission.BoseGases.fsKinCoeff_le_sq hc (norm_nonneg p)
    · exact mul_nonneg (inv_nonneg.mpr (pow_nonneg hℓ.le 3))
        (mul_nonneg measureReal_nonneg (sq_nonneg _))
    · exact fun p _ => hKbdd i p
  -- scale by `(2π)⁻³`
  have keym : ∀ i : Fin N,
      (1 - ε) * (((2 * Real.pi) ^ 3)⁻¹ * (∫ p : ℝ³, (fun r : ℝ => r ^ 2) ‖p‖ * Kf i p))
        ≤ ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : ℝ³, Submission.BoseGases.fsKinCoeff c ‖p‖ * Kf i p)
          + (1 + 1 / ε) * c ^ 2 * (((2 * Real.pi) ^ 3)⁻¹ * (∫ p : ℝ³, Kf i p)) := by
    intro i
    calc (1 - ε) * (((2 * Real.pi) ^ 3)⁻¹ * (∫ p : ℝ³, (fun r : ℝ => r ^ 2) ‖p‖ * Kf i p))
        = ((2 * Real.pi) ^ 3)⁻¹ *
            ((1 - ε) * (∫ p : ℝ³, (fun r : ℝ => r ^ 2) ‖p‖ * Kf i p)) := by ring
      _ ≤ ((2 * Real.pi) ^ 3)⁻¹ *
            ((∫ p : ℝ³, Submission.BoseGases.fsKinCoeff c ‖p‖ * Kf i p)
              + (1 + 1 / ε) * c ^ 2 * (∫ p : ℝ³, Kf i p)) :=
          mul_le_mul_of_nonneg_left (key i) (le_of_lt hpi)
      _ = ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : ℝ³, Submission.BoseGases.fsKinCoeff c ‖p‖ * Kf i p)
          + (1 + 1 / ε) * c ^ 2 * (((2 * Real.pi) ^ 3)⁻¹ * (∫ p : ℝ³, Kf i p)) := by ring
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin N))) => keym i)
  have he1 : (1 - ε) * (∑ i : Fin N, ((2 * Real.pi) ^ 3)⁻¹ *
        (∫ p : ℝ³, (fun r : ℝ => r ^ 2) ‖p‖ * Kf i p))
      = ∑ i : Fin N, (1 - ε) * (((2 * Real.pi) ^ 3)⁻¹ *
        (∫ p : ℝ³, (fun r : ℝ => r ^ 2) ‖p‖ * Kf i p)) :=
    Finset.mul_sum Finset.univ _ (1 - ε)
  have he2 : (∑ i : Fin N, ((2 * Real.pi) ^ 3)⁻¹ *
          (∫ p : ℝ³, Submission.BoseGases.fsKinCoeff c ‖p‖ * Kf i p))
        + (1 + 1 / ε) * c ^ 2 * (∑ i : Fin N, ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : ℝ³, Kf i p))
      = ∑ i : Fin N, (((2 * Real.pi) ^ 3)⁻¹ *
            (∫ p : ℝ³, Submission.BoseGases.fsKinCoeff c ‖p‖ * Kf i p)
          + (1 + 1 / ε) * c ^ 2 * (((2 * Real.pi) ^ 3)⁻¹ * (∫ p : ℝ³, Kf i p))) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  have main : (∑ i : Fin N, ((2 * Real.pi) ^ 3)⁻¹ *
        (∫ p : ℝ³, Submission.BoseGases.fsKinCoeff c ‖p‖ * Kf i p))
      ≥ (1 - ε) * (∑ i : Fin N, ((2 * Real.pi) ^ 3)⁻¹ *
            (∫ p : ℝ³, (fun r : ℝ => r ^ 2) ‖p‖ * Kf i p))
        - ((1 + 1 / ε) * c ^ 2) * (∑ i : Fin N, ((2 * Real.pi) ^ 3)⁻¹ *
            (∫ p : ℝ³, Kf i p)) := by
    rw [he1]
    have hab : (∑ i : Fin N, (1 - ε) * (((2 * Real.pi) ^ 3)⁻¹ *
          (∫ p : ℝ³, (fun r : ℝ => r ^ 2) ‖p‖ * Kf i p)))
        ≤ (∑ i : Fin N, ((2 * Real.pi) ^ 3)⁻¹ *
            (∫ p : ℝ³, Submission.BoseGases.fsKinCoeff c ‖p‖ * Kf i p))
          + (1 + 1 / ε) * c ^ 2 * (∑ i : Fin N, ((2 * Real.pi) ^ 3)⁻¹ *
            (∫ p : ℝ³, Kf i p)) := by
      rw [he2]
      exact hsum
    linarith [hab]
  simpa only [Work.UBBInputs8.tBwordKinInd, Work.UBBInputs8.tBdiagFormInd, hKf, one_mul]
    using main

/-! ## 5b. Nonnegativity of the two Dirichlet forms at a positive side length -/

/-- `tBdiagFormInd` is nonnegative for a nonnegative symbol and a **positive** side length
(the general case is `Work.UBBInputs9.A.tBdiagFormInd_nonneg_of_nonneg`, private). -/
private lemma tBdiagFormInd_nonneg_of_pos {ℓ : ℝ} (hℓ : 0 < ℓ) {A : Set ℝ³} {volA : ℝ}
    {χ : ℝ³ → ℝ} {F : ℝ → ℝ} (hF : ∀ r, 0 ≤ F r) {N : ℕ} {Ψ : Submission.BoseGases.X N → ℝ} :
    0 ≤ Work.UBBInputs8.tBdiagFormInd ℓ A volA χ F Ψ := by
  unfold Work.UBBInputs8.tBdiagFormInd
  refine Finset.sum_nonneg fun i _ => ?_
  refine mul_nonneg (le_of_lt Work.SmallBoxTBWord.twoPiInv3_pos) ?_
  refine integral_nonneg fun p => mul_nonneg (hF ‖p‖) ?_
  exact mul_nonneg (inv_nonneg.mpr (pow_nonneg hℓ.le 3))
    (integral_nonneg fun x => sq_nonneg _)

/-! ## 6. The target -/

/-- **The sharp spectral-vs-Dirichlet comparison.**  At the corpus cutoff `χ_B = chiB ℓ d u`, an
arbitrary positive normalisation `volA > 0`, `c ≥ 0` and any `ε > 0`,

    `tBwordKinInd … c Φ ≥ (1−ε)·tBdiagFormInd … (·)² Φ − (1+1/ε)c²·tBdiagFormInd … 1 Φ`,

because the symbol satisfies the pointwise `(1−ε)r² ≤ [r−c]₊² + (1+1/ε)c²` for every `r`
(`sharp_le_fsKinCoeff_add`; the quadratic `ε(r−c/ε)² + 2εc² ≥ 0` after multiplying by `ε`).
For `ε ≤ 1` this is `sbKin_ge_sharp_of_chi`; for `ε ≥ 1` both terms of the difference are
`≤ 0` while the right-hand side is `≥ 0`.  This strictly improves the `½, 2c²` constants of
`Work.BoseFixB1S.mfSpecGeDivDirichletB1`. -/
theorem mfSpecGeSharpDivDirichletB1 {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (u : EuclideanSpace ℝ (Fin 3))
    {volA : ℝ} (hvol : 0 < volA) {N : ℕ} {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
    (c : ℝ) (hc : 0 ≤ c) {ε : ℝ} (hε : 0 < ε) :
    (1 - ε) * (Work.UBBInputs8.tBdiagFormInd ℓ (Submission.BoseGases.dlBox ℓ d u) volA
          (Submission.BoseGases.chiB ℓ d u) (fun r : ℝ => r ^ 2) Φ)
      - ((1 + 1 / ε) * c ^ 2) * (Work.UBBInputs8.tBdiagFormInd ℓ (Submission.BoseGases.dlBox ℓ d u) volA
          (Submission.BoseGases.chiB ℓ d u) (fun _ : ℝ => (1 : ℝ)) Φ)
      ≤ Work.UBBInputs8.tBwordKinInd ℓ (Submission.BoseGases.dlBox ℓ d u) volA
          (Submission.BoseGases.chiB ℓ d u) c Φ := by
  by_cases hε1 : ε ≤ 1
  · exact sbKin_ge_sharp_of_chi hℓ (Work.SmallBoxSliding.measurableSet_dlBox ℓ d u)
      (Work.SmallBoxSliding.dlBox_subset_acube ℓ d u) hvol
      ((Work.SmallBoxTBWord.contDiff_chiB hℓ hd u).continuous)
      (Work.SmallBoxTBWord.tsupport_chiB_subset_acube hℓ hd u) hΦc c hc hε hε1
  · push_neg at hε1
    have hK := tBdiagFormInd_nonneg_of_pos (ℓ := ℓ) hℓ (A := Submission.BoseGases.dlBox ℓ d u)
      (volA := volA) (χ := Submission.BoseGases.chiB ℓ d u)
      (F := fun r : ℝ => r ^ 2) (fun r => sq_nonneg r) (Ψ := Φ)
    have hM := tBdiagFormInd_nonneg_of_pos (ℓ := ℓ) hℓ (A := Submission.BoseGases.dlBox ℓ d u)
      (volA := volA) (χ := Submission.BoseGases.chiB ℓ d u)
      (F := fun _ : ℝ => (1 : ℝ)) (fun _ => zero_le_one) (Ψ := Φ)
    have hspec : 0 ≤ Work.UBBInputs8.tBwordKinInd ℓ (Submission.BoseGases.dlBox ℓ d u) volA
        (Submission.BoseGases.chiB ℓ d u) c Φ := by
      unfold Work.UBBInputs8.tBwordKinInd
      exact tBdiagFormInd_nonneg_of_pos (ℓ := ℓ) hℓ (A := Submission.BoseGases.dlBox ℓ d u)
        (volA := volA) (χ := Submission.BoseGases.chiB ℓ d u)
        (F := Submission.BoseGases.fsKinCoeff c)
        (fun r => Submission.BoseGases.fsKinCoeff_nonneg c r) (Ψ := Φ)
    have h1 : (1 - ε) * (Work.UBBInputs8.tBdiagFormInd ℓ (Submission.BoseGases.dlBox ℓ d u) volA
          (Submission.BoseGases.chiB ℓ d u) (fun r : ℝ => r ^ 2) Φ) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) hK
    have h2 : 0 ≤ ((1 + 1 / ε) * c ^ 2) * (Work.UBBInputs8.tBdiagFormInd ℓ
        (Submission.BoseGases.dlBox ℓ d u) volA (Submission.BoseGases.chiB ℓ d u)
        (fun _ : ℝ => (1 : ℝ)) Φ) :=
      mul_nonneg (by positivity) hM
    linarith

end Work.BoseFixB1S
