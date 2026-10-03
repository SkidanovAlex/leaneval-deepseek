import Mathlib

/-!
# Decay of the conjugate-Poisson kernel `1 / sqrt (δ² + (y - Y)²)`

We prove that for a nonnegative integrable `F : ℝ → ℝ` and any `δ > 0`, the "kernel average"

  `Y ↦ ∫ y, F y / sqrt (δ ^ 2 + (y - Y) ^ 2)`

tends to `0` both at `atTop` and at `atBot`.  The argument is a dominated-convergence /
`ε`-splitting argument, because `atTop` on `ℝ` is *not* countably generated, so the filter
form of the dominated convergence theorem of Mathlib does not apply directly with `l = atTop`.

The kernel is globally dominated by `F y / δ`, and on a compact region `|y| < R` it is bounded
by `F y / (|Y| - R)` as soon as `|Y| > R`; the mass of the complement of that region against
`F / δ` tends to `0` as `R → ∞`.
-/

open MeasureTheory Filter
open scoped Topology

namespace Work.FatouL1

/-- The total mass of an integrable function on the exterior of a symmetric interval tends to
zero as the radius tends to infinity. -/
theorem hcKernelDecay_tail {G : ℝ → ℝ} (hG : Integrable G) :
    Tendsto (fun n : ℕ => ∫ y : ℝ in {y : ℝ | (n : ℝ) ≤ |y|}, G y) atTop (nhds 0) := by
  have hsm : ∀ n : ℕ, MeasurableSet {y : ℝ | (n : ℝ) ≤ |y|} := fun n =>
    measurableSet_le measurable_const continuous_abs.measurable
  have hanti : Antitone (fun n : ℕ => {y : ℝ | (n : ℝ) ≤ |y|}) := by
    intro i j hij y hy
    simp only [Set.mem_ofPred_eq] at hy ⊢
    exact le_trans (by exact_mod_cast hij) hy
  have hfi : IntegrableOn G {y : ℝ | ((0 : ℕ) : ℝ) ≤ |y|} := hG.integrableOn
  have h := Antitone.tendsto_setIntegral hsm hanti hfi
  have hinter : (⋂ n : ℕ, {y : ℝ | (n : ℝ) ≤ |y|}) = ∅ := by
    ext y
    simp only [Set.mem_iInter, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_forall,
      not_le]
    obtain ⟨n, hn⟩ := exists_nat_gt |y|
    exact ⟨n, hn⟩
  simpa only [hinter, setIntegral_empty] using h

/-- Auxiliary form of the decay statement, for a filter `l` along which `|·|` tends to `atTop`
(so that `l` can be specialised to `atTop` or `atBot`). -/
theorem hcKernelDecay_aux {F : ℝ → ℝ} (hFnn : ∀ y : ℝ, 0 ≤ F y)
    (hFint : MeasureTheory.Integrable F) {δ : ℝ} (hδ : 0 < δ) {l : Filter ℝ}
    (hl : Filter.Tendsto (fun Y : ℝ => |Y|) l Filter.atTop) :
    Filter.Tendsto (fun Y : ℝ => ∫ y : ℝ, F y / Real.sqrt (δ ^ 2 + (y - Y) ^ 2)) l (nhds 0) := by
  have hGint : MeasureTheory.Integrable (fun y : ℝ => F y / δ) := hFint.div_const δ
  have hGnn : ∀ y : ℝ, 0 ≤ F y / δ := fun y => div_nonneg (hFnn y) hδ.le
  have hsqrt_ge : ∀ y Y : ℝ, δ ≤ Real.sqrt (δ ^ 2 + (y - Y) ^ 2) := by
    intro y Y
    refine (Real.le_sqrt hδ.le (by positivity)).mpr ?_
    nlinarith [sq_nonneg (y - Y)]
  have hglobal : ∀ y Y : ℝ, F y / Real.sqrt (δ ^ 2 + (y - Y) ^ 2) ≤ F y / δ := by
    intro y Y
    exact div_le_div_of_nonneg_left (hFnn y) hδ (hsqrt_ge y Y)
  have hnorm : ∀ y Y : ℝ, ‖F y / Real.sqrt (δ ^ 2 + (y - Y) ^ 2)‖ ≤ F y / δ := by
    intro y Y
    rw [Real.norm_of_nonneg (div_nonneg (hFnn y) (Real.sqrt_nonneg _))]
    exact hglobal y Y
  have hkint : ∀ Y : ℝ,
      MeasureTheory.Integrable (fun y : ℝ => F y / Real.sqrt (δ ^ 2 + (y - Y) ^ 2)) := by
    intro Y
    have haesm : MeasureTheory.AEStronglyMeasurable
        (fun y : ℝ => F y / Real.sqrt (δ ^ 2 + (y - Y) ^ 2)) volume := by
      have hcont : Continuous (fun y : ℝ => Real.sqrt (δ ^ 2 + (y - Y) ^ 2)) := by fun_prop
      have : AEMeasurable (fun y : ℝ => F y / Real.sqrt (δ ^ 2 + (y - Y) ^ 2)) volume :=
        (hFint.aestronglyMeasurable.aemeasurable).div (hcont.measurable.aemeasurable)
      exact this.aestronglyMeasurable
    exact MeasureTheory.Integrable.mono' hGint haesm
      (Filter.Eventually.of_forall (fun y => hnorm y Y))
  have hknn : ∀ Y : ℝ, 0 ≤ ∫ y : ℝ, F y / Real.sqrt (δ ^ 2 + (y - Y) ^ 2) :=
    fun Y => integral_nonneg (fun y => div_nonneg (hFnn y) (Real.sqrt_nonneg _))
  have htail : Filter.Tendsto
      (fun n : ℕ => ∫ y : ℝ in {y : ℝ | (n : ℝ) ≤ |y|}, F y / δ) Filter.atTop (nhds 0) :=
    hcKernelDecay_tail hGint
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε2 : (0 : ℝ) < ε / 2 := by linarith
  rw [Metric.tendsto_atTop] at htail
  obtain ⟨n₀, hn₀⟩ := htail (ε / 2) hε2
  have htail_lt : ∫ y : ℝ in {y : ℝ | ((n₀ : ℕ) : ℝ) ≤ |y|}, F y / δ < ε / 2 := by
    have h0 : 0 ≤ ∫ y : ℝ in {y : ℝ | ((n₀ : ℕ) : ℝ) ≤ |y|}, F y / δ :=
      integral_nonneg (fun y => hGnn y)
    have hh := hn₀ n₀ le_rfl
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg h0] at hh
  have hIFnn : 0 ≤ ∫ y : ℝ, F y := integral_nonneg hFnn
  filter_upwards [hl.eventually_ge_atTop ((n₀ : ℝ) + (∫ y : ℝ, F y) / (ε / 2) + 1)] with Y hY
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hknn Y)]
  have hcpos : 0 < |Y| - (n₀ : ℝ) := by
    have h2 : 0 ≤ (∫ y : ℝ, F y) / (ε / 2) := div_nonneg hIFnn hε2.le
    linarith
  have hcgt : (∫ y : ℝ, F y) / (ε / 2) < |Y| - (n₀ : ℝ) := by linarith
  have hcgt' : (∫ y : ℝ, F y) < (ε / 2) * (|Y| - (n₀ : ℝ)) := by
    have h := (div_lt_iff₀ hε2).mp hcgt
    nlinarith [h]
  have hinner2 : (∫ y : ℝ, F y) / (|Y| - (n₀ : ℝ)) < ε / 2 :=
    (div_lt_iff₀ hcpos).mpr hcgt'
  let A : Set ℝ := {y : ℝ | |y| < (n₀ : ℝ)}
  have hA : MeasurableSet A := measurableSet_lt continuous_abs.measurable measurable_const
  have hAeq : Aᶜ = {y : ℝ | ((n₀ : ℕ) : ℝ) ≤ |y|} := by
    ext y; simp only [A, Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt]
  have hsplit : ∫ y : ℝ, F y / Real.sqrt (δ ^ 2 + (y - Y) ^ 2)
      = (∫ y : ℝ in A, F y / Real.sqrt (δ ^ 2 + (y - Y) ^ 2))
        + (∫ y : ℝ in Aᶜ, F y / Real.sqrt (δ ^ 2 + (y - Y) ^ 2)) :=
    (integral_add_compl hA (hkint Y)).symm
  have hmonoAc : ∫ y : ℝ in Aᶜ, F y / Real.sqrt (δ ^ 2 + (y - Y) ^ 2)
      ≤ ∫ y : ℝ in Aᶜ, F y / δ := by
    apply integral_mono_ae (μ := volume.restrict Aᶜ)
    · exact (hkint Y).integrableOn
    · exact hGint.integrableOn
    · exact Filter.Eventually.of_forall (fun y => hglobal y Y)
  have hpointA : ∀ y ∈ A,
      F y / Real.sqrt (δ ^ 2 + (y - Y) ^ 2) ≤ F y / (|Y| - (n₀ : ℝ)) := by
    intro y hy
    have h1 : |Y| - (n₀ : ℝ) ≤ |y - Y| := by
      have h2 := abs_sub_abs_le_abs_sub Y y
      rw [abs_sub_comm Y y] at h2
      simp only [A, Set.mem_ofPred_eq] at hy
      linarith
    have h3 : |y - Y| ≤ Real.sqrt (δ ^ 2 + (y - Y) ^ 2) := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg δ])
    exact div_le_div_of_nonneg_left (hFnn y) hcpos (le_trans h1 h3)
  have hmonoA : ∫ y : ℝ in A, F y / Real.sqrt (δ ^ 2 + (y - Y) ^ 2)
      ≤ ∫ y : ℝ in A, F y / (|Y| - (n₀ : ℝ)) := by
    apply integral_mono_ae (μ := volume.restrict A)
    · exact (hkint Y).integrableOn
    · exact (hFint.integrableOn).div_const _
    · exact (MeasureTheory.ae_restrict_iff' hA).mpr
        (Filter.Eventually.of_forall (fun y hy => hpointA y hy))
  have hinner_eq : ∫ y : ℝ in A, F y / (|Y| - (n₀ : ℝ))
      = (|Y| - (n₀ : ℝ))⁻¹ * ∫ y : ℝ in A, F y := by
    simp_rw [div_eq_inv_mul]
    rw [MeasureTheory.integral_const_mul]
  have hsetle : ∫ y : ℝ in A, F y ≤ ∫ y : ℝ, F y :=
    MeasureTheory.setIntegral_le_integral hFint (Filter.Eventually.of_forall hFnn)
  have hA_bound : ∫ y : ℝ in A, F y / Real.sqrt (δ ^ 2 + (y - Y) ^ 2) < ε / 2 := by
    calc ∫ y : ℝ in A, F y / Real.sqrt (δ ^ 2 + (y - Y) ^ 2)
        ≤ ∫ y : ℝ in A, F y / (|Y| - (n₀ : ℝ)) := hmonoA
      _ = (|Y| - (n₀ : ℝ))⁻¹ * ∫ y : ℝ in A, F y := hinner_eq
      _ ≤ (|Y| - (n₀ : ℝ))⁻¹ * ∫ y : ℝ, F y := by
            apply mul_le_mul_of_nonneg_left hsetle
            exact inv_nonneg.mpr hcpos.le
      _ = (∫ y : ℝ, F y) / (|Y| - (n₀ : ℝ)) := by rw [div_eq_inv_mul]
      _ < ε / 2 := hinner2
  have hAc_bound : ∫ y : ℝ in Aᶜ, F y / Real.sqrt (δ ^ 2 + (y - Y) ^ 2) < ε / 2 := by
    rw [hAeq] at hmonoAc ⊢
    exact lt_of_le_of_lt hmonoAc htail_lt
  rw [hsplit]
  linarith [hA_bound, hAc_bound]

theorem hcKernelDecay {F : ℝ → ℝ} (hFnn : ∀ y : ℝ, 0 ≤ F y) (hFint : MeasureTheory.Integrable F)
    {δ : ℝ} (hδ : 0 < δ) :
    Filter.Tendsto (fun Y : ℝ => ∫ y : ℝ, F y / Real.sqrt (δ ^ 2 + (y - Y) ^ 2)) Filter.atTop (nhds 0) ∧
    Filter.Tendsto (fun Y : ℝ => ∫ y : ℝ, F y / Real.sqrt (δ ^ 2 + (y - Y) ^ 2)) Filter.atBot (nhds 0) := by
  refine ⟨?_, ?_⟩
  · exact hcKernelDecay_aux hFnn hFint hδ tendsto_abs_atTop_atTop
  · exact hcKernelDecay_aux hFnn hFint hδ tendsto_abs_atBot_atTop

end Work.FatouL1
