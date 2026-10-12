import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB1.WinPair.WinChiFacts
import Submission.Work.BoseFixB1.boxPairFibreAbsLe
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.integrable_relDensJointAlt` — joint integrability of the relative integral

The joint integrability input of the relative-coordinate decomposition of `boxA2`
(`Work.BoseFixB1.boxRelDens`): for `W ∈ L¹`, a smooth compactly supported `χ` and smooth `Φ`,

  `(y,u) ↦ winChi ℓ χ y · W u · winChi ℓ χ (y − u) · boxPairFibreFun volA ℓ A Φ i j y (y − u)`

is integrable for `volume.prod volume`.  The proof is the box analogue of
`Work.BoseFixB1.WinPair.integrable_win_subst`: the fibre is bounded by `4C²ℓ^{3N}` on
`acube ℓ × acube ℓ` (`Work.BoseFixB1.boxPairFibreAbsLe`), `winChi` vanishes off the cube, so the
majorant is a constant times `1_{acube}(y)·|W u|`, which is integrable.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1

open Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- `boxPairFibreFun` unfolded with a *fixed* proof of `i ≠ j`, so that the `sucAboveInv`
index is under control in rewrites. -/
lemma boxPairFibreFun_eq {N : ℕ} (volA ℓ : ℝ) {A : Set E3} (Φ : X (N + 2) → ℝ)
    {i j : Fin (N + 2)} (hij : i ≠ j) (y z : E3) :
    boxPairFibreFun volA ℓ A Φ i j y z
      = ∫ r2 in abox N ℓ,
          (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ)
              (ins2 i (sucAboveInv i j hij) y z r2))
            * (Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ)
                (ins2 i (sucAboveInv i j hij) y z r2)) := by
  rw [boxPairFibreFun, dif_pos hij]

/-- The shifted peeled pair fibre of the box is a.e. strongly measurable. -/
lemma aestronglyMeasurable_boxPairFibreFun_shift {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ)
    {A : Set E3} (hA : MeasurableSet A) {Φ : X (N + 2) → ℝ} (hΦm : Measurable Φ)
    {i j : Fin (N + 2)} (hij : i ≠ j) :
    AEStronglyMeasurable (fun q : E3 × E3 => boxPairFibreFun volA ℓ A Φ i j q.1 (q.1 - q.2))
      (volume.prod volume) := by
  have hPj : Measurable (Work.UBBInputs8.boxPInd volA A j Φ) :=
    Work.BoseFixB1S.measurable_boxPInd volA A hA j hΦm
  have hP : Measurable (Work.UBBInputs8.boxPInd volA A i
      (Work.UBBInputs8.boxPInd volA A j Φ)) :=
    Work.BoseFixB1S.measurable_boxPInd volA A hA i hPj
  have hQ : Measurable (Work.UBBInputs8.boxQInd volA A j
      (Work.UBBInputs8.boxQInd volA A i Φ)) :=
    Work.BoseFixB1S.measurable_boxQInd volA hA j
      (Work.BoseFixB1S.measurable_boxQInd volA hA i hΦm)
  have hpair : Measurable (fun p : (E3 × E3) × X N => ((p.1.1, p.1.1 - p.1.2), p.2)) :=
    Measurable.prodMk
      (Measurable.prodMk (measurable_fst.comp measurable_fst)
        ((measurable_fst.comp measurable_fst).sub (measurable_snd.comp measurable_fst)))
      measurable_snd
  have hins : Measurable (fun p : (E3 × E3) × X N =>
      ins2 i (sucAboveInv i j hij) p.1.1 (p.1.1 - p.1.2) p.2) :=
    (Work.BoseFixB1S.Q0C.eIns2 i (sucAboveInv i j hij)).measurable.comp hpair
  have hmeas : Measurable (fun p : (E3 × E3) × X N =>
      Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ)
          (ins2 i (sucAboveInv i j hij) p.1.1 (p.1.1 - p.1.2) p.2)
        * Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ)
          (ins2 i (sucAboveInv i j hij) p.1.1 (p.1.1 - p.1.2) p.2)) :=
    (hP.comp hins).mul (hQ.comp hins)
  haveI : IsFiniteMeasure ((volume : Measure (X N)).restrict (abox N ℓ)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact abox_lt_top N ℓ hℓ.le⟩
  have h2 : StronglyMeasurable (fun q : E3 × E3 => ∫ r2 in abox N ℓ,
      Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ)
          (ins2 i (sucAboveInv i j hij) q.1 (q.1 - q.2) r2)
        * Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ)
          (ins2 i (sucAboveInv i j hij) q.1 (q.1 - q.2) r2)) :=
    StronglyMeasurable.integral_prod_right (ν := (volume : Measure (X N)).restrict (abox N ℓ))
      hmeas.stronglyMeasurable
  refine h2.aestronglyMeasurable.congr ?_
  filter_upwards with q
  exact (boxPairFibreFun_eq volA ℓ Φ hij q.1 (q.1 - q.2)).symm

/-- **Joint integrability** of the relative-coordinate integrand of `boxA2`. -/
theorem integrable_relDensJointAlt {N : ℕ} {ℓ volA : ℝ} {A : Set E3}
    (hA : MeasurableSet A) (hℓ : 0 < ℓ) (hAc : A ⊆ acube ℓ)
    (hvolA : volA = (MeasureTheory.volume A).toReal) (hvolpos : 0 < volA)
    {χ : E3 → ℝ} (hχc : ContDiff ℝ (⊤ : ℕ∞) χ) (hχs : HasCompactSupport χ)
    {Φ : X (N + 2) → ℝ} (hΦc : ContDiff ℝ (⊤ : ℕ∞) Φ)
    {W : E3 → ℝ} (hWint : Integrable W) {i j : Fin (N + 2)} (hij : i ≠ j) :
    Integrable (Function.uncurry (fun y u : E3 =>
      winChi ℓ χ y * W u * winChi ℓ χ (y - u)
        * boxPairFibreFun volA ℓ A Φ i j y (y - u)))
      (volume.prod volume) := by
  obtain ⟨Cχ, hCχ0, hCχ⟩ := WinPair.exists_abs_winChi_le (s := ℓ) hℓ hχc.continuous
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
      ((measurable_winChi hχc.continuous.measurable).comp measurable_fst).aestronglyMeasurable
    have h2 : AEStronglyMeasurable (fun q : E3 × E3 => W q.2) (volume.prod volume) :=
      hWint.aestronglyMeasurable.comp_snd
    have h3 : AEStronglyMeasurable (fun q : E3 × E3 => winChi ℓ χ (q.1 - q.2))
        (volume.prod volume) :=
      ((measurable_winChi hχc.continuous.measurable).comp
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

end Work.BoseFixB1
