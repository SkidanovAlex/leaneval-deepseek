import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB1.boxRelDens
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.BoxPairIntGenC2.boxRelDensC2` — the relative-coordinate decomposition
of `boxA2` for a merely *continuous* window

    boxA2 ℓ volA A (χ(xᵢ)χ(xⱼ)W(xᵢ−xⱼ)) Φ
      = ∫_u W(u)·boxPairDensSum volA ℓ A χ Φ u .

This is the C²-window ingredient P1 of the `boxPairIntGenC2` route
(`FINDING_boxPairIntGenC2_route.md` §1), in the strongest honest form: the relative-coordinate
substitution only ever reads the window through the values `χ y`, `χ (y − u)`, so continuity
(plus compact support, for boundedness) is all that the identity needs — no derivative of `χ`
ever occurs.  Consequently `ContDiff ℝ 2 χ` (the profile available in the application) and
`ContDiff ℝ ⊤ χ` (`Work.BoseFixB1.boxRelDens`) both specialise to the statement below.

The proof is the corpus's `Work.BoseFixB1.boxRelDens_assembly` replayed against the
`Continuous`-form of the two integrability inputs; those are the only places where the
smoothness of the window was consumed in the `C^∞` version, and both consumed it only through
`ContDiff.continuous`.  They are reproduced here (private) as
`integrableOnBoxPairKernelC0` / `integrableRelDensJointAltC0`, transcriptions of
`Work.BoseFixB1.integrableOn_boxPairKernel` and `Work.BoseFixB1.integrable_relDensJointAlt`
with the one hypothesis relaxed.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1.BoxPairIntGenC2

open _root_.BoseGases Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## 1. The two integrability inputs, with `Continuous χ` in place of `ContDiff ℝ ⊤ χ` -/

/-- A real-valued continuous function with compact support is bounded in absolute value. -/
private lemma exists_abs_le_of_hasCompactSupportC0 {f : E3 → ℝ}
    (hf : Continuous f) (hs : HasCompactSupport f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |f x| ≤ C := by
  obtain ⟨C, hC⟩ := hs.exists_bound_of_continuous hf
  refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
  have hx : |f x| ≤ C := by simpa [Real.norm_eq_abs] using hC x
  exact hx.trans (le_max_left _ _)

/-- **`Work.BoseFixB1.integrableOn_boxPairKernel` with a continuous window.**  The per-pair box
integrand of `boxA2` is integrable on the box `abox (N+2) ℓ`: the box projections `boxPInd` /
`boxQInd` are bounded on the box by a multiple of the bound of their argument, and the window
is bounded by compact support. -/
private theorem integrableOnBoxPairKernelC0 {N : ℕ} {ℓ volA : ℝ} {A : Set E3}
    (hA : MeasurableSet A) (hℓ : 0 < ℓ) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    (hvolA : volA = (MeasureTheory.volume A).toReal) (hvolpos : 0 < volA)
    {χ : E3 → ℝ} (hχc : Continuous χ) (hχs : HasCompactSupport χ)
    {Φ : X (N + 2) → ℝ} (hΦc : ContDiff ℝ (⊤ : ℕ∞) Φ)
    {W : E3 → ℝ} (hWint : MeasureTheory.Integrable W)
    {i j : Fin (N + 2)} (hij : i ≠ j) :
    MeasureTheory.IntegrableOn (fun x : X (N + 2) =>
      Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x
        * Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x
        * (χ (x i) * χ (x j) * W (x i - x j)))
      (abox (N + 2) ℓ) MeasureTheory.volume := by
  have hΦcont : Continuous Φ := hΦc.continuous
  have hΦm : Measurable Φ := hΦcont.measurable
  -- a bound for `Φ` on the analysis box
  obtain ⟨C, hC⟩ := (abox_compact (N + 2) hℓ).exists_bound_of_continuousOn
    (s := abox (N + 2) ℓ) (f := Φ) hΦcont.continuousOn
  have hCΦ : ∀ x ∈ abox (N + 2) ℓ, |Φ x| ≤ C :=
    fun x hx => by simpa [Real.norm_eq_abs] using hC x hx
  -- a bound for the window `χ`
  obtain ⟨Cχ, hCχ0, hCχ⟩ := exists_abs_le_of_hasCompactSupportC0 hχc hχs
  -- normalise both bounds to be nonnegative
  obtain ⟨B, hB0, hΦB⟩ : ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ abox (N + 2) ℓ, |Φ x| ≤ B :=
    ⟨max C 0, le_max_right _ _, fun x hx => (hCΦ x hx).trans (le_max_left _ _)⟩
  obtain ⟨Cc, hCc0, hχb⟩ : ∃ C : ℝ, 0 ≤ C ∧ ∀ z : E3, |χ z| ≤ C :=
    ⟨max Cχ 0, le_max_right _ _, fun z => (hCχ z).trans (le_max_left _ _)⟩
  have hvolreal : volA = MeasureTheory.volume.real A := by
    rw [hvolA, MeasureTheory.Measure.real_def]
  -- the two box projections are bounded on the box
  have hP : ∀ x ∈ abox (N + 2) ℓ,
      |Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x| ≤ B :=
    Work.BoseFixB1S.abs_boxPInd_le hℓ hvolpos hA hvolA hAc i
      (fun x hx => Work.BoseFixB1S.abs_boxPInd_le hℓ hvolpos hA hvolA hAc j hΦB x hx)
  have hQ : ∀ x ∈ abox (N + 2) ℓ,
      |Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x| ≤ 4 * B := by
    have h1 : ∀ x ∈ abox (N + 2) ℓ,
        |Work.UBBInputs8.boxQInd volA A i Φ x| ≤ 2 * B :=
      Work.BoseFixB1S.abs_boxQInd_le hℓ hvolpos hA hvolreal hAc i hΦB
    have h2 : ∀ x ∈ abox (N + 2) ℓ,
        |Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x| ≤ 2 * (2 * B) :=
      Work.BoseFixB1S.abs_boxQInd_le (N := N + 2) hℓ hvolpos hA hvolreal hAc j h1
    intro x hx
    have h3 := h2 x hx
    linarith
  -- the dominating function `K·|W(xᵢ − xⱼ)|` is integrable on the box
  set K : ℝ := B * (4 * B) * (Cc * Cc) with hKdef
  have hbase : MeasureTheory.IntegrableOn (fun x : X (N + 2) =>
      |W (x i - x j)|) (abox (N + 2) ℓ) MeasureTheory.volume :=
    Submission.BoseGases.integrableOn_abs_sub_abox hℓ hWint i j hij
  have hmaj : MeasureTheory.Integrable
      (fun x : X (N + 2) => K * |W (x i - x j)|)
      ((MeasureTheory.volume : Measure (X (N + 2))).restrict (abox (N + 2) ℓ)) :=
    MeasureTheory.Integrable.const_mul hbase K
  -- measurability of the integrand
  have hPm : Measurable (Work.UBBInputs8.boxPInd volA A i
      (Work.UBBInputs8.boxPInd volA A j Φ)) :=
    Work.BoseFixB1S.measurable_boxPInd volA A hA i
      (Work.BoseFixB1S.measurable_boxPInd volA A hA j hΦm)
  have hQm : Measurable (Work.UBBInputs8.boxQInd volA A j
      (Work.UBBInputs8.boxQInd volA A i Φ)) :=
    Work.BoseFixB1S.measurable_boxQInd volA hA j
      (Work.BoseFixB1S.measurable_boxQInd volA hA i hΦm)
  have hχim : Measurable (fun x : X (N + 2) => χ (x i)) :=
    hχc.measurable.comp (measurable_pi_apply i)
  have hχjm : Measurable (fun x : X (N + 2) => χ (x j)) :=
    hχc.measurable.comp (measurable_pi_apply j)
  have hWaesm : AEStronglyMeasurable
      (fun x : X (N + 2) => W (x i - x j))
      ((MeasureTheory.volume : Measure (X (N + 2))).restrict (abox (N + 2) ℓ)) :=
    (Work.BoseFixB1.WinPair.aemeasurable_comp_pair hℓ hWint.aemeasurable i j hij).aestronglyMeasurable
  have haesm : AEStronglyMeasurable
      (fun x : X (N + 2) =>
        Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x
          * Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x
          * (χ (x i) * χ (x j) * W (x i - x j)))
      ((MeasureTheory.volume : Measure (X (N + 2))).restrict (abox (N + 2) ℓ)) :=
    (hPm.aestronglyMeasurable.mul hQm.aestronglyMeasurable).mul
      ((hχim.aestronglyMeasurable.mul hχjm.aestronglyMeasurable).mul hWaesm)
  -- the pointwise domination
  refine MeasureTheory.Integrable.mono' hmaj haesm ?_
  filter_upwards [ae_restrict_mem (abox_measurable (N + 2) ℓ)] with x hx
  have h1 := hP x hx
  have h2 := hQ x hx
  have h3 := hχb (x i)
  have h4 := hχb (x j)
  have hb1 : (0 : ℝ) ≤ B * (4 * B) := mul_nonneg hB0 (by linarith)
  have hb2 : (0 : ℝ) ≤ Cc * Cc * |W (x i - x j)| :=
    mul_nonneg (mul_nonneg hCc0 hCc0) (abs_nonneg _)
  have hb3 : (0 : ℝ) ≤ |W (x i - x j)| := abs_nonneg _
  rw [Real.norm_eq_abs]
  calc |Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x
          * Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x
          * (χ (x i) * χ (x j) * W (x i - x j))|
      = |Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x|
          * |Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x|
          * (|χ (x i)| * |χ (x j)| * |W (x i - x j)|) := by
        rw [abs_mul, abs_mul, abs_mul, abs_mul]
    _ ≤ B * (4 * B) * (Cc * Cc * |W (x i - x j)|) :=
        mul_le_mul (mul_le_mul h1 h2 (abs_nonneg _) hB0)
          (mul_le_mul_of_nonneg_right (mul_le_mul h3 h4 (abs_nonneg _) hCc0) hb3)
          (mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _)) hb1
    _ = K * |W (x i - x j)| := by rw [hKdef]; ring

/-- **`Work.BoseFixB1.integrable_relDensJointAlt` with a continuous window.**  Joint
integrability of the relative-coordinate integrand: the fibre is bounded by `4C²ℓ^{3N}` on
`acube ℓ × acube ℓ`, and `winChi ℓ χ` vanishes off the cube. -/
private theorem integrableRelDensJointAltC0 {N : ℕ} {ℓ volA : ℝ} {A : Set E3}
    (hA : MeasurableSet A) (hℓ : 0 < ℓ) (hAc : A ⊆ acube ℓ)
    (hvolA : volA = (MeasureTheory.volume A).toReal) (hvolpos : 0 < volA)
    {χ : E3 → ℝ} (hχc : Continuous χ) (hχs : HasCompactSupport χ)
    {Φ : X (N + 2) → ℝ} (hΦc : ContDiff ℝ (⊤ : ℕ∞) Φ)
    {W : E3 → ℝ} (hWint : Integrable W) {i j : Fin (N + 2)} (hij : i ≠ j) :
    Integrable (Function.uncurry (fun y u : E3 =>
      winChi ℓ χ y * W u * winChi ℓ χ (y - u)
        * boxPairFibreFun volA ℓ A Φ i j y (y - u)))
      (volume.prod volume) := by
  obtain ⟨Cχ, hCχ0, hCχ⟩ := WinPair.exists_abs_winChi_le (s := ℓ) hℓ hχc
  obtain ⟨B, hB0, hBΦ⟩ := exists_abox_bound (N := N + 2) (ℓ := ℓ) hℓ hΦc.continuous
  have hQb : ∀ y z : E3, y ∈ acube ℓ → z ∈ acube ℓ →
      |boxPairFibreFun volA ℓ A Φ i j y z| ≤ 4 * B ^ 2 * ℓ ^ (3 * N) :=
    fun y z hy hz => boxPairFibreAbsLe hA hℓ hAc hvolA hvolpos hB0 hBΦ hij hy hz
  have hInd : Integrable (Set.indicator (acube ℓ) (fun _ : E3 => (1 : ℝ))) (volume : Measure E3) :=
    (integrableOn_const (μ := (volume : Measure E3)) (s := acube ℓ) (C := (1 : ℝ))
      (hs := ne_of_lt (acube_lt_top ℓ hℓ.le)) (hC := by simp)).integrable_indicator
      (acube_measurable ℓ)
  have hmaj : Integrable (Function.uncurry (fun y u : E3 =>
      (Cχ * (Cχ * (4 * B ^ 2 * ℓ ^ (3 * N))))
        * Set.indicator (acube ℓ) (fun _ : E3 => (1 : ℝ)) y * |W u|))
      (volume.prod volume) :=
    (hInd.const_mul _).mul_prod hWint.abs
  have hmeas : AEStronglyMeasurable (Function.uncurry (fun y u : E3 =>
      winChi ℓ χ y * W u * winChi ℓ χ (y - u)
        * boxPairFibreFun volA ℓ A Φ i j y (y - u))) (volume.prod volume) := by
    have h1 : AEStronglyMeasurable (fun q : E3 × E3 => winChi ℓ χ q.1)
        (volume.prod volume) :=
      ((measurable_winChi hχc.measurable).comp measurable_fst).aestronglyMeasurable
    have h2 : AEStronglyMeasurable (fun q : E3 × E3 => W q.2) (volume.prod volume) :=
      hWint.aestronglyMeasurable.comp_snd
    have h3 : AEStronglyMeasurable (fun q : E3 × E3 => winChi ℓ χ (q.1 - q.2))
        (volume.prod volume) :=
      ((measurable_winChi hχc.measurable).comp
        (measurable_fst.sub measurable_snd)).aestronglyMeasurable
    have h4 : AEStronglyMeasurable
        (fun q : E3 × E3 => boxPairFibreFun volA ℓ A Φ i j q.1 (q.1 - q.2))
        (volume.prod volume) :=
      aestronglyMeasurable_boxPairFibreFun_shift hℓ hA hΦc.continuous.measurable hij
    exact ((h1.mul h2).mul h3).mul (by simpa only [Function.uncurry] using h4)
  refine Integrable.mono' hmaj hmeas ?_
  filter_upwards with q
  simp only [Function.uncurry]
  have hmajnn : (0 : ℝ) ≤ (Cχ * (Cχ * (4 * B ^ 2 * ℓ ^ (3 * N))))
      * Set.indicator (acube ℓ) (fun _ : E3 => (1 : ℝ)) q.1 * |W q.2| :=
    mul_nonneg (mul_nonneg (mul_nonneg hCχ0 (mul_nonneg hCχ0 (by positivity)))
      (Set.indicator_nonneg (fun _ _ => zero_le_one) q.1)) (abs_nonneg _)
  by_cases hy : winChi ℓ χ q.1 = 0
  · have hz0 : winChi ℓ χ q.1 * W q.2 * winChi ℓ χ (q.1 - q.2)
        * boxPairFibreFun volA ℓ A Φ i j q.1 (q.1 - q.2) = 0 := by
      rw [hy]; ring
    rw [hz0, norm_zero]
    exact hmajnn
  · by_cases hz : winChi ℓ χ (q.1 - q.2) = 0
    · have hz0 : winChi ℓ χ q.1 * W q.2 * winChi ℓ χ (q.1 - q.2)
          * boxPairFibreFun volA ℓ A Φ i j q.1 (q.1 - q.2) = 0 := by
        rw [hz]; ring
      rw [hz0, norm_zero]
      exact hmajnn
    · have hb1 : q.1 ∈ acube ℓ := winChi_support hy
      have hb2 : q.1 - q.2 ∈ acube ℓ := winChi_support hz
      have hind : Set.indicator (acube ℓ) (fun _ : E3 => (1 : ℝ)) q.1 = 1 :=
        Set.indicator_of_mem hb1 _
      have hQ : |boxPairFibreFun volA ℓ A Φ i j q.1 (q.1 - q.2)| ≤ 4 * B ^ 2 * ℓ ^ (3 * N) :=
        hQb _ _ hb1 hb2
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul]
      have hstep : |winChi ℓ χ q.1| * |W q.2| * |winChi ℓ χ (q.1 - q.2)|
            * |boxPairFibreFun volA ℓ A Φ i j q.1 (q.1 - q.2)|
          ≤ Cχ * |W q.2| * Cχ * (4 * B ^ 2 * ℓ ^ (3 * N)) :=
        mul_le_mul
          (mul_le_mul
            (mul_le_mul (hCχ q.1) le_rfl (abs_nonneg _) hCχ0)
            (hCχ (q.1 - q.2)) (abs_nonneg _) (mul_nonneg hCχ0 (abs_nonneg _)))
          hQ (abs_nonneg _)
          (mul_nonneg (mul_nonneg hCχ0 (abs_nonneg _)) hCχ0)
      calc |winChi ℓ χ q.1| * |W q.2| * |winChi ℓ χ (q.1 - q.2)|
              * |boxPairFibreFun volA ℓ A Φ i j q.1 (q.1 - q.2)|
          ≤ Cχ * |W q.2| * Cχ * (4 * B ^ 2 * ℓ ^ (3 * N)) := hstep
        _ = (Cχ * (Cχ * (4 * B ^ 2 * ℓ ^ (3 * N)))) * |W q.2| := by ring
        _ = (Cχ * (Cχ * (4 * B ^ 2 * ℓ ^ (3 * N))))
              * Set.indicator (acube ℓ) (fun _ : E3 => (1 : ℝ)) q.1 * |W q.2| := by
            rw [hind, mul_one]

/-! ## 2. The finite-sum assembly

The `C^∞` assembly of `Work.BoseFixB1.boxRelDens` with the two integrability inputs replaced by
their `Continuous`-window forms; the pointwise relative-coordinate identity itself is the
public `Work.BoseFixB1.boxA2Summand`. -/

private theorem boxRelDensC2_assembly {N : ℕ} {ℓ volA : ℝ} {A : Set E3}
    (hℓ : 0 < ℓ) (hAc : A ⊆ acube ℓ)
    {χ : E3 → ℝ} (hχsupp : ∀ z, z ∉ A → χ z = 0)
    {Φ : X (N + 2) → ℝ} {W : E3 → ℝ}
    (hFAll : ∀ p ∈ Submission.BoseGases.pairSet (N + 2),
      MeasureTheory.IntegrableOn (fun x : X (N + 2) =>
      Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxPInd volA A p.2 Φ) x
        * Work.UBBInputs8.boxQInd volA A p.2 (Work.UBBInputs8.boxQInd volA A p.1 Φ) x
        * (χ (x p.1) * χ (x p.2) * W (x p.1 - x p.2)))
      (abox (N + 2) ℓ) MeasureTheory.volume)
    (hIntAll : ∀ p ∈ Submission.BoseGases.pairSet (N + 2),
      MeasureTheory.Integrable (Function.uncurry (fun y u : E3 =>
      winChi ℓ χ y * W u * winChi ℓ χ (y - u)
        * boxPairFibreFun volA ℓ A Φ p.1 p.2 y (y - u)))
      (MeasureTheory.volume.prod MeasureTheory.volume)) :
    boxA2 ℓ volA A (fun x y => χ x * χ y * W (x - y)) Φ
      = ∫ u, W u * boxPairDensSum volA ℓ A χ Φ u := by
  have hpair : ∀ p ∈ Submission.BoseGases.pairSet (N + 2),
      (∫ x in abox (N + 2) ℓ,
        Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxPInd volA A p.2 Φ) x
          * Work.UBBInputs8.boxQInd volA A p.2 (Work.UBBInputs8.boxQInd volA A p.1 Φ) x
          * (χ (x p.1) * χ (x p.2) * W (x p.1 - x p.2)))
        = ∫ u, W u * boxPairDens volA ℓ A χ Φ p.1 p.2 u := by
    intro p hp
    exact boxA2Summand (i := p.1) (j := p.2) hℓ hAc hχsupp
      (Finset.mem_filter.mp hp).2 (hFAll p hp) (hIntAll p hp)
  simp only [boxA2, boxPairDensSum]
  rw [show (∫ u, W u * ∑ p ∈ Submission.BoseGases.pairSet (N + 2),
        boxPairDens volA ℓ A χ Φ p.1 p.2 u)
      = ∑ p ∈ Submission.BoseGases.pairSet (N + 2),
          ∫ u, W u * boxPairDens volA ℓ A χ Φ p.1 p.2 u from by
    rw [show (fun u : E3 => W u * ∑ p ∈ Submission.BoseGases.pairSet (N + 2),
              boxPairDens volA ℓ A χ Φ p.1 p.2 u)
        = (fun u : E3 => ∑ p ∈ Submission.BoseGases.pairSet (N + 2),
              W u * boxPairDens volA ℓ A χ Φ p.1 p.2 u) from by
      funext u
      rw [Finset.mul_sum]]
    rw [integral_finsetSum]
    intro p hp
    exact integrable_W_mul_boxPairDens hℓ hAc hχsupp
      (Finset.mem_filter.mp hp).2 (hIntAll p hp)]
  exact Finset.sum_congr rfl hpair

/-! ## 3. The relative-coordinate decomposition with a continuous window -/

theorem boxRelDensC2 {N : ℕ} {ℓ volA : ℝ} {A : Set (EuclideanSpace ℝ (Fin 3))}
    (hA : MeasurableSet A) (hℓ : 0 < ℓ) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    (hvolA : volA = (MeasureTheory.volume A).toReal) (hvolpos : 0 < volA)
    {χ : EuclideanSpace ℝ (Fin 3) → ℝ} (hχc : Continuous χ) (hχs : HasCompactSupport χ)
    (hχsupp : ∀ z, z ∉ A → χ z = 0)
    {Ψ : Submission.BoseGases.X (N + 2) → ℝ} (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ)
    {W : EuclideanSpace ℝ (Fin 3) → ℝ} (hWint : MeasureTheory.Integrable W) :
    Work.BoseFixB1.boxA2 ℓ volA A (fun x y => χ x * χ y * W (x - y)) Ψ
      = ∫ u, W u * Work.BoseFixB1.boxPairDensSum volA ℓ A χ Ψ u :=
  boxRelDensC2_assembly hℓ hAc hχsupp
    (fun p hp => integrableOnBoxPairKernelC0 hA hℓ hAc hvolA hvolpos hχc hχs hΨ hWint
      (Finset.mem_filter.mp hp).2)
    (fun p hp => integrableRelDensJointAltC0 hA hℓ hAc hvolA hvolpos hχc hχs hΨ hWint
      (Finset.mem_filter.mp hp).2)

end Work.BoseFixB1.BoxPairIntGenC2
