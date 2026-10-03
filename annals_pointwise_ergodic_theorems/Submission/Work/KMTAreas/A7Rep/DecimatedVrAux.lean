import Mathlib
import Submission.Work.KMTAreas.A7Rep.SamplingKernelDefs
import Submission.Work.Analysis.Fourier.lattice_sup_lp_sampling
import Submission.Work.BourgainPlan.IonescuWainger.lintegral_count_residue

/-!
# Auxiliary estimates for the decimated `Vʳ` sampling comparison

This module collects the three analytic estimates used by
`Work.KMTAreas.A7Rep.decimatedVrSamplingSeqBdd`:

* `rescaledBandLtQuarter`: the rescaled function `u ↦ γ (q u + r₀)` is integrable, continuous and
  band-limited to `[-1/4,1/4]` as soon as `γ` is integrable, continuous and band-limited to
  `[-β,β]` with `β q ≤ 1/4`;
* `kernelScaleSumBoundENN`: the *column* bound of the sampling kernel, i.e. the sum of `‖K‖` over the
  fine lattice `ℤ` with the sampling points `(x - r₀)/q - m` is at most a constant times `q` (the
  density of `ℤ` inside `qℤ + r₀`).  It is deduced from the *row* bound
  `samplingKernel_latticeBoundENN` by splitting `ℤ` into the `q` residue classes modulo `q`;
* `weightedHolderTsum`: the elementary Schur/weighted-Hölder step: row and column bounds on a
  `ℤ × ℤ`-matrix of `ℝ≥0∞`-weights turn `∑_x (∑_m W x m * v m)^p` into
  `A^{p-1} B * ∑_m v m^p`.
-/

namespace Work.KMTAreas.A7Rep

open MeasureTheory Finset
open scoped FourierTransform ENNReal BigOperators

noncomputable section

/-! ## 1. The rescaled family is band-limited to `[-1/4,1/4]` -/

theorem rescaledBandLtQuarter (q : ℕ) (hq : 0 < q) (r₀ : ℤ) (β : ℝ) (hβ : 0 < β)
    (hβq : β * (q : ℝ) ≤ 1 / 4)
    (γ : ℝ → ℂ) (hint : MeasureTheory.Integrable γ) (hcont : Continuous γ)
    (hbl : ∀ ξ : ℝ, ξ ∉ Set.Icc (-β) β → FourierTransform.fourier γ ξ = 0) :
    MeasureTheory.Integrable (fun u : ℝ => γ ((q : ℝ) * u + (r₀ : ℝ))) ∧
    Continuous (fun u : ℝ => γ ((q : ℝ) * u + (r₀ : ℝ))) ∧
    (∀ ξ : ℝ, ξ ∉ Set.Icc (-(1 / 4 : ℝ)) (1 / 4) →
      FourierTransform.fourier (fun u : ℝ => γ ((q : ℝ) * u + (r₀ : ℝ))) ξ = 0) := by
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hqne : ((q : ℝ)) ≠ 0 := hqpos.ne'
  refine ⟨?_, ?_, ?_⟩
  · -- integrability
    have hmp : MeasureTheory.MeasurePreserving (fun v : ℝ => v + (r₀ : ℝ)) volume volume :=
      ⟨measurable_add_const _, by rw [MeasureTheory.map_add_right_eq_self volume (r₀ : ℝ)]⟩
    have htrans : MeasureTheory.Integrable (fun v : ℝ => γ (v + (r₀ : ℝ))) :=
      hmp.integrable_comp_of_integrable hint
    have h2 := htrans.comp_mul_left' hqne
    simpa only [Function.comp_apply] using h2
  · exact hcont.comp (by fun_prop)
  · -- the band
    intro ξ hξ
    have hξabs : (1 / 4 : ℝ) < |ξ| := by
      by_contra hle
      rw [not_lt] at hle
      exact hξ (abs_le.mp hle)
    rw [show (fun u : ℝ => γ ((q : ℝ) * u + (r₀ : ℝ)))
        = (fun x : ℝ => (fun v : ℝ => γ (v + (r₀ : ℝ))) ((q : ℝ) * x)) from rfl]
    rw [Commons.Analysis.Fourier.fourier_comp_mul_left (fun v : ℝ => γ (v + (r₀ : ℝ))) hqpos ξ]
    rw [show (fun v : ℝ => γ (v + (r₀ : ℝ))) = (fun x : ℝ => γ (x - (-(r₀ : ℝ)))) from by
      funext v; congr 1; ring]
    rw [Commons.Analysis.Fourier.fourier_comp_sub γ (-(r₀ : ℝ)) (ξ / (q : ℝ))]
    have hband : FourierTransform.fourier γ (ξ / (q : ℝ)) = 0 := by
      apply hbl
      intro hmem
      have h2 : |ξ / (q : ℝ)| ≤ β := abs_le.mpr ⟨hmem.1, hmem.2⟩
      have h3 : |ξ / (q : ℝ)| = |ξ| / (q : ℝ) := by rw [abs_div, abs_of_pos hqpos]
      have hβle : β ≤ 1 / (4 * (q : ℝ)) := by
        rw [le_div_iff₀ (by positivity)]
        linarith [hβq]
      rw [h3] at h2
      have : (1 / 4 : ℝ) / (q : ℝ) < |ξ| / (q : ℝ) := by
        apply div_lt_div_of_pos_right _ hqpos
        linarith [hξabs]
      have : (1 : ℝ) / (4 * (q : ℝ)) = (1 / 4) / (q : ℝ) := by field_simp
      linarith
    rw [hband, smul_zero, mul_zero]

/-! ## 2. The column bound of the sampling kernel -/

theorem kernelScaleSumBoundENN :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) (hq : 0 < q) (r₀ m : ℤ),
      (∑' x : ℤ, ‖(samplingKernel : ℝ → ℂ) (((x : ℝ) - (r₀ : ℝ)) / (q : ℝ) - (m : ℝ))‖ₑ)
        ≤ ENNReal.ofReal (C * (q : ℝ)) := by
  obtain ⟨A, hApos, hAlat⟩ := samplingKernel_latticeBoundENN
  refine ⟨A, hApos, ?_⟩
  intro q hq r₀ m
  have hq1 : 1 ≤ q := hq
  have hsplit := Work.BourgainPlan.IonescuWainger.lintegral_count_residue (Q := q) hq1
    (fun x : ℤ => ‖(samplingKernel : ℝ → ℂ) (((x : ℝ) - (r₀ : ℝ)) / (q : ℝ) - (m : ℝ))‖ₑ)
  rw [MeasureTheory.lintegral_count] at hsplit
  rw [hsplit]
  simp only [MeasureTheory.lintegral_count]
  have hterm : ∀ r ∈ Finset.range q,
      (∑' N : ℤ, ‖(samplingKernel : ℝ → ℂ)
        ((((((q : ℤ) * N + (r : ℤ) : ℤ) : ℝ) - (r₀ : ℝ)) / (q : ℝ) - (m : ℝ)))‖ₑ)
        ≤ ENNReal.ofReal A := by
    intro r hr
    set u : ℝ := (m : ℝ) + ((r₀ : ℝ) - (r : ℝ)) / (q : ℝ) with hu
    have harg : ∀ N : ℤ, (((((q : ℤ) * N + (r : ℤ) : ℤ) : ℝ) - (r₀ : ℝ)) / (q : ℝ) - (m : ℝ))
        = (N : ℝ) - u := by
      intro N
      rw [hu]
      push_cast
      field_simp
      ring
    have hcongr : (∑' N : ℤ, ‖(samplingKernel : ℝ → ℂ)
        ((((((q : ℤ) * N + (r : ℤ) : ℤ) : ℝ) - (r₀ : ℝ)) / (q : ℝ) - (m : ℝ)))‖ₑ)
        = ∑' N : ℤ, ‖(samplingKernel : ℝ → ℂ) ((N : ℝ) - u)‖ₑ := by
      apply tsum_congr; intro N; rw [harg N]
    rw [hcongr]
    have hneg : (∑' N : ℤ, ‖(samplingKernel : ℝ → ℂ) ((N : ℝ) - u)‖ₑ)
        = ∑' j : ℤ, ‖(samplingKernel : ℝ → ℂ) ((-u) - (j : ℝ))‖ₑ := by
      rw [← Equiv.tsum_eq (Equiv.neg ℤ)
        (fun N : ℤ => ‖(samplingKernel : ℝ → ℂ) ((N : ℝ) - u)‖ₑ)]
      apply tsum_congr; intro j
      congr 2
      simp only [Equiv.neg_apply]
      push_cast
      ring
    rw [hneg]
    exact hAlat (-u)
  calc ∑ r ∈ Finset.range q, (∑' N : ℤ, ‖(samplingKernel : ℝ → ℂ)
        ((((((q : ℤ) * N + (r : ℤ) : ℤ) : ℝ) - (r₀ : ℝ)) / (q : ℝ) - (m : ℝ)))‖ₑ)
      ≤ ∑ r ∈ Finset.range q, ENNReal.ofReal A := Finset.sum_le_sum hterm
    _ = (q : ENNReal) * ENNReal.ofReal A := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ = ENNReal.ofReal (A * (q : ℝ)) := by
        rw [ENNReal.ofReal_mul hApos.le, ENNReal.ofReal_natCast, mul_comm]

/-! ## 3. The weighted-Hölder (Schur) step -/

theorem weightedHolderTsum (p : ℝ) (hp : 1 < p) {W : ℤ → ℤ → ENNReal} {v : ℤ → ENNReal}
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hrow : ∀ x : ℤ, (∑' m : ℤ, W x m) ≤ ENNReal.ofReal A)
    (hcol : ∀ m : ℤ, (∑' x : ℤ, W x m) ≤ ENNReal.ofReal B) :
    (∑' x : ℤ, (∑' m : ℤ, W x m * v m) ^ p)
      ≤ ENNReal.ofReal (A ^ (p - 1) * B) * (∑' m : ℤ, v m ^ p) := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hp1 : 0 ≤ p - 1 := by linarith
  have hstep1 : ∀ x : ℤ, (∑' m : ℤ, W x m * v m) ^ p
      ≤ ENNReal.ofReal A ^ (p - 1) * (∑' m : ℤ, W x m * v m ^ p) := by
    intro x
    have h := Commons.Analysis.Fourier.lintegral_mul_rpow_le_rpow_mul_lintegral_measure
      (Measure.count : Measure ℤ) hp (f := v) (w := fun m : ℤ => W x m)
      (measurable_of_countable _).aemeasurable (measurable_of_countable _).aemeasurable
    simp only [MeasureTheory.lintegral_count] at h
    rw [tsum_congr (fun m : ℤ => mul_comm (v m) (W x m)),
        tsum_congr (fun m : ℤ => mul_comm (v m ^ p) (W x m))] at h
    exact h.trans (mul_le_mul_of_nonneg_right (ENNReal.rpow_le_rpow (hrow x) hp1) bot_le)
  have hstep2 : (∑' x : ℤ, ENNReal.ofReal A ^ (p - 1) * (∑' m : ℤ, W x m * v m ^ p))
      ≤ ENNReal.ofReal A ^ (p - 1) * (ENNReal.ofReal B * ∑' m : ℤ, v m ^ p) := by
    rw [ENNReal.tsum_mul_left]
    refine mul_le_mul_of_nonneg_left ?_ bot_le
    rw [← ENNReal.tsum_comm]
    calc ∑' m : ℤ, ∑' x : ℤ, W x m * v m ^ p
        = ∑' m : ℤ, (∑' x : ℤ, W x m) * v m ^ p := by
          apply tsum_congr; intro m; rw [ENNReal.tsum_mul_right]
      _ ≤ ∑' m : ℤ, ENNReal.ofReal B * v m ^ p :=
          ENNReal.tsum_le_tsum (fun m => mul_le_mul_of_nonneg_right (hcol m) bot_le)
      _ = ENNReal.ofReal B * ∑' m : ℤ, v m ^ p := ENNReal.tsum_mul_left
  calc (∑' x : ℤ, (∑' m : ℤ, W x m * v m) ^ p)
      ≤ ∑' x : ℤ, ENNReal.ofReal A ^ (p - 1) * (∑' m : ℤ, W x m * v m ^ p) :=
        ENNReal.tsum_le_tsum hstep1
    _ ≤ ENNReal.ofReal A ^ (p - 1) * (ENNReal.ofReal B * ∑' m : ℤ, v m ^ p) := hstep2
    _ = ENNReal.ofReal (A ^ (p - 1) * B) * (∑' m : ℤ, v m ^ p) := by
        rw [ENNReal.ofReal_mul (Real.rpow_nonneg hA _), ENNReal.ofReal_rpow_of_nonneg hA hp1]
        ring

end

end Work.KMTAreas.A7Rep
