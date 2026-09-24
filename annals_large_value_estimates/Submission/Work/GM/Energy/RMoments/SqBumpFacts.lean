import Mathlib
import Submission.Work.GM.Energy.RMoments.SqDefs

/-!
# Basic facts about the rescaled flat-top bump `sqBump`

`sqBump u = psiBump (u / (2π))` equals `1` on `[0, 2π]`, is nonnegative, smooth, compactly
supported, and the complexification `sqBumpC` is integrable.  These are the only properties of
the bump used in the proof of the second-moment bound `∫_1^2 ‖R(v)‖² dv ≪ |W|`.
-/

namespace Work.GM.Energy.RMoments

open Complex Finset MeasureTheory
open scoped BigOperators FourierTransform

set_option autoImplicit false

open Work.GM.Energy.RLocal (psiBump psiBump_contDiff psiBump_hasCompactSupport
  psiBump_support_subset)

lemma sqBump_nonneg (u : ℝ) : 0 ≤ sqBump u := by
  unfold sqBump Work.GM.Energy.RLocal.psiBump
  exact Submission.LargeValues.bumpW_nonneg _

/-- The support of `sqBump` is contained in `[-2π/3, 8π/3]`. -/
lemma sqBump_support_subset :
    Function.support sqBump ⊆ Set.Icc (-(2 * Real.pi) / 3) (4 * (2 * Real.pi) / 3) := by
  intro u hu
  rw [Function.mem_support] at hu
  have hmem : u / (2 * Real.pi) ∈ Set.Icc (-(1 / 3) : ℝ) (4 / 3) := by
    apply psiBump_support_subset
    rw [Function.mem_support]
    simpa [sqBump] using hu
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  constructor
  · have h := (le_div_iff₀ hπ).mp hmem.1
    nlinarith [Real.pi_pos]
  · have h := (div_le_iff₀ hπ).mp hmem.2
    nlinarith [Real.pi_pos]

lemma sqBump_hasCompactSupport : HasCompactSupport sqBump :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc sqBump_support_subset

lemma sqBump_contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) sqBump :=
  psiBump_contDiff.comp (by fun_prop)

lemma sqBump_continuous : Continuous sqBump := sqBump_contDiff.continuous

lemma sqBumpC_contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) sqBumpC :=
  Complex.ofRealCLM.contDiff.comp sqBump_contDiff

lemma sqBumpC_continuous : Continuous sqBumpC := Complex.continuous_ofReal.comp sqBump_continuous

lemma sqBumpC_hasCompactSupport : HasCompactSupport sqBumpC :=
  sqBump_hasCompactSupport.comp_left (by simp)

lemma sqBumpC_integrable : Integrable sqBumpC :=
  sqBumpC_continuous.integrable_of_hasCompactSupport sqBumpC_hasCompactSupport

lemma sqBump_integrable : Integrable sqBump :=
  sqBump_continuous.integrable_of_hasCompactSupport sqBump_hasCompactSupport

end Work.GM.Energy.RMoments
