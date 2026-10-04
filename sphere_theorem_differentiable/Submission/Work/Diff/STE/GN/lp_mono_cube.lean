import Mathlib
import Submission.Work.Diff.STE.Torus

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.style.haveILetI false

namespace Work.Diff.STE.GN

open MeasureTheory

/-- The half-open unit cube `(0,1]^ι` has total measure `1` in `ι → ℝ`. -/
lemma volume_unitCube {ι : Type*} [Fintype ι] :
    (volume : Measure (ι → ℝ)) (Work.Diff.STE.unitCube (ι := ι)) = 1 := by
  rw [Work.Diff.STE.unitCube, Real.volume_pi_Ioc]
  simp

/-- The half-open unit cube is Borel measurable. -/
lemma measurableSet_unitCube {ι : Type*} [Fintype ι] :
    MeasurableSet (Work.Diff.STE.unitCube (ι := ι)) := by
  rw [Work.Diff.STE.unitCube]
  exact MeasurableSet.univ_pi fun _ => measurableSet_Ioc

/-- Lebesgue measure restricted to the unit cube is a probability measure. -/
lemma isProbabilityMeasure_restrict_unitCube {ι : Type*} [Fintype ι] :
    IsProbabilityMeasure (volume.restrict (Work.Diff.STE.unitCube (ι := ι))) where
  measure_univ := by
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, volume_unitCube]

/-- A continuous real function is bounded on the closed unit cube `[0,1]^ι`, hence a.e. bounded
for Lebesgue measure restricted to the half-open cube. -/
lemma ae_bound_unitCube {ι : Type*} [Fintype ι] (h : (ι → ℝ) → ℝ) (hh : Continuous h) :
    ∃ C, ∀ᵐ x ∂(volume.restrict (Work.Diff.STE.unitCube (ι := ι))), ‖h x‖ ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (show ContinuousOn h (Set.Icc (0 : ι → ℝ) 1) from hh.continuousOn.mono (Set.subset_univ _))
  refine ⟨C, ?_⟩
  rw [ae_restrict_iff' measurableSet_unitCube]
  refine Filter.Eventually.of_forall fun x hx => hC x ?_
  simp only [Set.mem_Icc, Pi.le_def]
  constructor
  · intro i; exact (Set.mem_Ioc.mp (hx i (Set.mem_univ i))).1.le
  · intro i; exact (Set.mem_Ioc.mp (hx i (Set.mem_univ i))).2

/-- **Monotonicity of `L^p` norms on the unit cube** (which has measure `1`): for `0 < r ≤ s` and a
continuous nonnegative `h`, `(∫ h^r)^(1/r) ≤ (∫ h^s)^(1/s)`.  Immediate from Hölder's inequality
`∫ h^r = ∫ h^r · 1 ≤ (∫ h^s)^(r/s) (∫ 1)^(1-r/s)` on the cube of volume `1`. -/
theorem lp_mono_cube {ι : Type*} [Fintype ι] [DecidableEq ι] (r s : ℝ) (hr : 0 < r) (hrs : r ≤ s)
    (h : (ι → ℝ) → ℝ) (hh : Continuous h) (hh0 : ∀ x, 0 ≤ h x) :
    (∫ x in Work.Diff.STE.unitCube (ι := ι), h x ^ r) ^ (1 / r)
      ≤ (∫ x in Work.Diff.STE.unitCube (ι := ι), h x ^ s) ^ (1 / s) := by
  rcases eq_or_lt_of_le hrs with hEq | hlt
  · subst hEq; rfl
  set μ : Measure (ι → ℝ) := volume.restrict (Work.Diff.STE.unitCube (ι := ι)) with hμ
  haveI : IsProbabilityMeasure μ := isProbabilityMeasure_restrict_unitCube
  -- `h` is bounded (a.e.) on the cube, so all the `ℒᵖ` seminorms involved are finite.
  obtain ⟨C, hae⟩ := ae_bound_unitCube h hh
  have hmeas : AEStronglyMeasurable h μ := hh.aestronglyMeasurable
  have hMemr : MemLp h (ENNReal.ofReal r) μ := MemLp.of_bound hmeas C hae
  have hMems : MemLp h (ENNReal.ofReal s) μ := MemLp.of_bound hmeas C hae
  -- monotonicity of the `ℒᵖ` seminorm in `p` on a probability space
  have hle : lpNorm h (ENNReal.ofReal r) μ ≤ lpNorm h (ENNReal.ofReal s) μ :=
    ENNReal.toReal_mono hMems.eLpNorm_ne_top
      (eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal hrs))
  rw [lpNorm_eq_integral_norm_rpow_toReal
        (by simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hr) (by simp) hmeas,
      lpNorm_eq_integral_norm_rpow_toReal
        (by simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact lt_of_lt_of_le hr hrs)
        (by simp) hmeas] at hle
  rw [ENNReal.toReal_ofReal hr.le, ENNReal.toReal_ofReal (le_trans hr.le hrs)] at hle
  -- replace `‖h x‖` by `h x ≥ 0` and unfold the set integral
  have hconv : ∀ t : ℝ, (∫ x, ‖h x‖ ^ t ∂μ) = ∫ x in Work.Diff.STE.unitCube (ι := ι), h x ^ t := by
    intro t
    rw [hμ]
    exact integral_congr_ae
      (Filter.Eventually.of_forall fun x => by simp only [Real.norm_of_nonneg (hh0 x)])
  rw [hconv r, hconv s] at hle
  simpa [one_div] using hle

end Work.Diff.STE.GN
