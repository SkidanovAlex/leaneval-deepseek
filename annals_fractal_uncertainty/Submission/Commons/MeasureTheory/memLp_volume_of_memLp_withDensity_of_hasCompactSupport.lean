import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.WithDensity

open MeasureTheory
open scoped ENNReal

namespace Commons.MeasureTheory

/-- **`L²` for the Lebesgue measure from `L²` for a positive weighted measure.**
If `u ∈ L²(μ)` where `μ = volume.withDensity (fun x => ENNReal.ofReal (F x))`, `F` is continuous
and strictly positive, and `u` has compact support, then `u ∈ L²(volume)`.

The point is that on the (compact) support of `u` the density `F` is bounded below by a positive
constant `m > 0`, so `volume.restrict (tsupport u) ≤ m⁻¹ • μ`; off the support `u` vanishes. -/
theorem memLp_volume_of_memLp_withDensity_of_hasCompactSupport {d : ℕ}
    {E : Type*} [NormedAddCommGroup E]
    {F : (Fin d → ℂ) → ℝ} (hFc : Continuous F) (hFpos : ∀ x, 0 < F x)
    {u : (Fin d → ℂ) → E}
    (hu : MeasureTheory.MemLp u 2
      ((MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)).withDensity
        (fun x => ENNReal.ofReal (F x))))
    (hus : HasCompactSupport u) :
    MeasureTheory.MemLp u 2 (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)) := by
  let K : Set (Fin d → ℂ) := tsupport u
  have hK_comp : IsCompact K := hus.isCompact
  have hK_meas : MeasurableSet K := hK_comp.measurableSet
  -- `F` is bounded below by a positive constant on the compact support of `u`.
  obtain ⟨m, hmpos, hmle⟩ :=
    hK_comp.exists_forall_le' hFc.continuousOn (fun x _ => hFpos x)
  let g : (Fin d → ℂ) → ℝ≥0∞ := fun x => ENNReal.ofReal (F x)
  let cst : ℝ≥0∞ := ENNReal.ofReal m
  let C : ℝ≥0∞ := cst⁻¹
  have hcst0 : cst ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hmpos)
  have hcsttop : cst ≠ ∞ := ENNReal.ofReal_ne_top
  have hCtop : C ≠ ∞ := ENNReal.inv_ne_top.mpr hcst0
  -- On `K` the density is bounded below by `cst > 0`, hence `volume.restrict K ≤ C • μ`.
  have hle : (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)).restrict K
      ≤ C • ((MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)).withDensity g) := by
    have hpoint : (K.indicator (1 : (Fin d → ℂ) → ℝ≥0∞)) ≤ (C • g) := by
      intro x
      by_cases hx : x ∈ K
      · rw [Set.indicator_of_mem hx]
        show (1 : ℝ≥0∞) ≤ C * g x
        have hgx : cst ≤ g x := ENNReal.ofReal_le_ofReal (hmle x hx)
        calc (1 : ℝ≥0∞) = C * cst := (ENNReal.inv_mul_cancel hcst0 hcsttop).symm
          _ ≤ C * g x := by gcongr
      · rw [Set.indicator_of_notMem hx]
        exact zero_le
    have hthis := MeasureTheory.withDensity_mono
      (μ := (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)))
      (Filter.Eventually.of_forall hpoint)
    rw [MeasureTheory.withDensity_indicator_one hK_meas,
      MeasureTheory.withDensity_smul' C g hCtop] at hthis
    exact hthis
  -- Transfer `MemLp` from `μ` to `volume.restrict K`.
  have huK : MeasureTheory.MemLp u 2
      ((MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)).restrict K) :=
    MeasureTheory.MemLp.mono_measure hle (hu.smul_measure hCtop)
  -- Transfer from `volume.restrict K` back to `volume`, using `u = 0` off `K`.
  have hsupp : Function.support u ⊆ K := subset_tsupport u
  refine ⟨?_, ?_⟩
  · -- almost-everywhere strong measurability
    have h1 : AEStronglyMeasurable (K.indicator u)
        (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)) :=
      (aestronglyMeasurable_indicator_iff hK_meas).mpr huK.1
    have heq : K.indicator u =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ))] u := by
      filter_upwards with x
      by_cases hx : x ∈ K
      · rw [Set.indicator_of_mem hx]
      · rw [Set.indicator_of_notMem hx]
        exact (Function.notMem_support.mp (fun h => hx (hsupp h))).symm
    exact (aestronglyMeasurable_congr heq).mp h1
  · -- finiteness of the `L²` norm
    rw [← MeasureTheory.eLpNorm_restrict_eq_of_support_subset hsupp]
    exact huK.2

end Commons.MeasureTheory