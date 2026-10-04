import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.GN.lp_mono_cube

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.style.haveILetI false

namespace Work.Diff.STE.GN

open MeasureTheory

/-- **Hölder's inequality for two functions** on the unit cube, with conjugate exponents:
for `b, c : ℝ` with `1 ≤ b, c` and `1/b + 1/c = 1`, and continuous nonnegative `F, G`,
`∫ F G ≤ (∫ F^b)^(1/b) * (∫ G^c)^(1/c)`.
Derivable from `MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg` (with `MemLp` from the
a.e. boundedness of continuous functions on the cube). -/
theorem holder2_int {ι : Type*} [Fintype ι] [DecidableEq ι] (b c : ℝ) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hbc : 1 / b + 1 / c = 1) (F G : (ι → ℝ) → ℝ) (hF : Continuous F) (hG : Continuous G)
    (hF0 : ∀ x, 0 ≤ F x) (hG0 : ∀ x, 0 ≤ G x) :
    ∫ x in Work.Diff.STE.unitCube (ι := ι), F x * G x
      ≤ (∫ x in Work.Diff.STE.unitCube (ι := ι), F x ^ b) ^ (1 / b)
        * (∫ x in Work.Diff.STE.unitCube (ι := ι), G x ^ c) ^ (1 / c) := by
  have hb0 : 0 < b := by linarith
  have hc0 : 0 < c := by linarith
  -- `b` and `c` are Hölder conjugate
  have hpq : b.HolderConjugate c := ⟨by simpa [one_div] using hbc, hb0, hc0⟩
  -- the unit cube carries a probability measure
  haveI : IsProbabilityMeasure
      (volume.restrict (Work.Diff.STE.unitCube (ι := ι))) :=
    isProbabilityMeasure_restrict_unitCube
  -- continuous functions are a.e. bounded on the cube, hence in every `L^p`
  have hFmem : MemLp F (ENNReal.ofReal b)
      (volume.restrict (Work.Diff.STE.unitCube (ι := ι))) := by
    obtain ⟨C, hC⟩ := ae_bound_unitCube F hF
    exact MemLp.of_bound (μ := volume.restrict (Work.Diff.STE.unitCube (ι := ι)))
      hF.aestronglyMeasurable C hC
  have hGmem : MemLp G (ENNReal.ofReal c)
      (volume.restrict (Work.Diff.STE.unitCube (ι := ι))) := by
    obtain ⟨C, hC⟩ := ae_bound_unitCube G hG
    exact MemLp.of_bound (μ := volume.restrict (Work.Diff.STE.unitCube (ι := ι)))
      hG.aestronglyMeasurable C hC
  -- Hölder's inequality for a measure space
  exact integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := volume.restrict (Work.Diff.STE.unitCube (ι := ι))) (p := b) (q := c) hpq
    (Filter.Eventually.of_forall hF0) (Filter.Eventually.of_forall hG0) hFmem hGmem

end Work.Diff.STE.GN
