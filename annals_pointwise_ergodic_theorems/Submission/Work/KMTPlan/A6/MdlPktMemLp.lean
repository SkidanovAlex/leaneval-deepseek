/-
# The memory forms of the packet families

This module collects the two elementary facts about the modified bumps
`varphiNtj`/`varphitildeNtj` that the single-scale estimate for the packet families
(`Work.KMTPlan.A6.mdlPktF`, `mdlPktG`) needs:

* narrowness of the support (`varphiNtj` vanishes off the arc `2^{k - logN N}`);
* `L^∞` (hence `MemLp · ⊤`) of the periodisation.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.lowModSymbFAux

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier Work.KMTAreas.A7

/-- **Narrowness of the modified `f`-side bump.** -/
theorem varphiNtj_support_le_pkt (N k : ℕ) (j : ℤ) (t : ℝ) :
    ∀ ξ : ℝ, varphiNtj N k j t ξ ≠ 0 →
      |ξ| ≤ (2 : ℝ) ^ ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) := by
  intro ξ hξ
  have h : varphiNt N k t ξ ≠ 0 := by
    intro h0
    exact hξ (by rw [varphiNtj, h0, mul_zero])
  simpa only [varphiNt] using
    Work.KMTAreas.A7.varphiNt_support_le_all k N t ξ (by simpa only [varphiNt] using h)

/-- **`L^∞` of the periodisation of the modified `f`-side bump.** -/
theorem memLp_periodize_varphiNtj (N k : ℕ) (j : ℤ) (t : ℝ)
    (hj : j ∈ ({-1, 0, 1} : Finset ℤ)) (hk : k ≠ 0 ∨ 0 ≤ j) (hN : 1 ≤ N)
    (ht : t ∈ Set.Icc (1 / 2 : ℝ) 1) :
    MeasureTheory.MemLp (Work.Analysis.IonescuWainger.periodize (varphiNtj N k j t)) ⊤
      Work.Analysis.IonescuWainger.circleMeasure := by
  obtain ⟨S, hSnonneg, hS⟩ := varphiNtj_bounds N k j hk
  obtain ⟨hScd, hScs, -, -⟩ := hS t ht
  obtain ⟨R, hR⟩ := Work.KMTAreas.A7.exists_abs_le_of_hasCompactSupport hScs
  have hR1 : (0 : ℝ) ≤ max R 1 := le_trans zero_le_one (le_max_right R 1)
  refine Work.Analysis.IonescuWainger.memLp_periodize hScd.continuous.measurable
    (R := max R 1) (C := 8) hR1 ?_ ?_
  · intro x hx
    exact hR x (le_of_lt (lt_of_le_of_lt (le_max_left R 1) hx))
  · intro x
    exact norm_varphiNtj_le_eight N k j hj hk hN t x

end

end Work.KMTPlan.A6
