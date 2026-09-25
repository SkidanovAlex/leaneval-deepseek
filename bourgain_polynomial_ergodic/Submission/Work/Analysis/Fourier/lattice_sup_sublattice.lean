/-
# The sublattice sampling bound for band-limited families (`ℓ^p`, `p > 1`)

Bourgain's §7.2 samples the real-line maximal function on a *sublattice* `qℤ` of the integer
lattice `ℤ`.  This file reduces that to the published lattice comparison
`Commons.Analysis.Fourier.lattice_sup_le_integral_sup_band_limited_rpow`: the push-forward of the
counting measure under `y ↦ q y` (`q > 0`) is `≤` the counting measure (an injective map pushes a
set to a set of the same cardinality), so `lintegral_mono'` finishes.
-/

import Mathlib
import Submission.Commons.Analysis.Fourier.lattice_sup_le_integral_sup_band_limited_rpow

open MeasureTheory
open scoped ENNReal FourierTransform

namespace Commons.Analysis.Fourier

/-- **Injective push-forwards of the counting measure are `≤` the counting measure.**  For a
measurable injective `g : ℤ → ℤ`, `Measure.map g count ≤ count`: pulling back along an injection can
only lose mass. -/
theorem map_count_le_count_of_injective {g : ℤ → ℤ} (hgmeas : Measurable g)
    (hginj : Function.Injective g) :
    MeasureTheory.Measure.map g MeasureTheory.Measure.count ≤ MeasureTheory.Measure.count := by
  rw [MeasureTheory.Measure.le_iff]
  intro A hA
  rw [MeasureTheory.Measure.map_apply hgmeas hA]
  rw [MeasureTheory.Measure.count_apply (hA.preimage hgmeas),
    MeasureTheory.Measure.count_apply hA]
  have h1 : (g '' (g ⁻¹' A)).encard = (g ⁻¹' A).encard :=
    Set.InjOn.encard_image (s := g ⁻¹' A) hginj.injOn
  have h2 : (g ⁻¹' A).encard ≤ A.encard := by
    rw [← h1, Set.image_preimage_eq_inter_range]
    exact Set.encard_le_encard Set.inter_subset_left
  exact_mod_cast h2

/-- **The sublattice `ℓ^p` sup-sampling bound.**  For `p > 1`, a family `h` of integrable,
continuous, `[-1/2,1/2]`-band-limited functions satisfies
`∫⁻_{y : ℤ} (⨆_j ‖h_j (q y)‖ₑ)^p ∂count ≤ C ∫⁻_{x : ℝ} (⨆_j ‖h_j x‖ₑ)^p ∂volume`. -/
theorem lattice_sup_le_integral_sup_sublattice_rpow {p : ℝ} (hp : 1 < p) (q : ℕ) (hq : 0 < q) :
    ∃ C : ℝ, 0 < C ∧ ∀ (h : ℕ → ℝ → ℂ),
      (∀ j : ℕ, MeasureTheory.Integrable (h j)) →
      (∀ j : ℕ, Continuous (h j)) →
      (∀ (j : ℕ) (ξ : ℝ), ξ ∉ Set.Icc (-(1 / 2) : ℝ) (1 / 2) → FourierTransform.fourier (h j) ξ = 0) →
      ∫⁻ y : ℤ, (⨆ j : ℕ, ‖h j ((q : ℝ) * (y : ℝ))‖ₑ) ^ p ∂MeasureTheory.Measure.count
        ≤ ENNReal.ofReal C *
            ∫⁻ x : ℝ, (⨆ j : ℕ, ‖h j x‖ₑ) ^ p ∂MeasureTheory.volume := by
  obtain ⟨C, hC, hC'⟩ :=
    Commons.Analysis.Fourier.lattice_sup_le_integral_sup_band_limited_rpow (p := p) hp
  refine ⟨C, hC, ?_⟩
  intro h hint hcont hbl
  set g : ℤ → ℤ := fun y => (q : ℤ) * y with hgdef
  have hginj : Function.Injective g := by
    intro y z hyz
    simp only [hgdef] at hyz
    exact mul_left_cancel₀ (by exact_mod_cast (ne_of_gt hq)) hyz
  have hgmeas : Measurable g := by
    rw [hgdef]; exact measurable_const.mul measurable_id
  have hcastZ : Measurable (fun m : ℤ => (m : ℝ)) := by fun_prop
  set F : ℤ → ℝ≥0∞ := fun m => (⨆ j : ℕ, ‖h j (m : ℝ)‖ₑ) ^ p with hFdef
  have hFmeas : Measurable F := by
    rw [hFdef]
    have hbase : Measurable (fun m : ℤ => ⨆ j : ℕ, ‖h j (m : ℝ)‖ₑ) :=
      Measurable.iSup (fun j =>
        ENNReal.measurable_ofReal.comp ((hcont j).norm.measurable.comp hcastZ))
    have hrpow : Measurable (fun x : ℝ≥0∞ => x ^ p) := by fun_prop
    exact hrpow.comp hbase
  have hmap : MeasureTheory.Measure.map g MeasureTheory.Measure.count ≤ MeasureTheory.Measure.count :=
    map_count_le_count_of_injective hgmeas hginj
  calc ∫⁻ y : ℤ, (⨆ j : ℕ, ‖h j ((q : ℝ) * (y : ℝ))‖ₑ) ^ p ∂MeasureTheory.Measure.count
      = ∫⁻ y : ℤ, F (g y) ∂MeasureTheory.Measure.count := by
        refine lintegral_congr (fun y => ?_)
        simp only [hFdef, hgdef, Int.cast_mul, Int.cast_natCast]
    _ = ∫⁻ m : ℤ, F m ∂MeasureTheory.Measure.map g MeasureTheory.Measure.count :=
        (lintegral_map hFmeas hgmeas).symm
    _ ≤ ∫⁻ m : ℤ, F m ∂MeasureTheory.Measure.count := lintegral_mono' hmap le_rfl
    _ ≤ ENNReal.ofReal C * ∫⁻ x : ℝ, (⨆ j : ℕ, ‖h j x‖ₑ) ^ p ∂MeasureTheory.volume :=
        hC' h hint hcont hbl

end Commons.Analysis.Fourier
