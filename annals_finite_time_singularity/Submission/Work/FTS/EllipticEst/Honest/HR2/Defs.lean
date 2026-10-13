/-
Copyright: work module for the Elgindi finite-time singularity project.

# `HR2.Defs` — admissibility of the radial cut-offs used in the honest energy inequality

This module fixes the notion of an *admissible radial cut-off* used by the truncated energy
identity of Step 1 of `prop:H2` of Elgindi, Annals **194** (2021), and records that the family
`Work.FTS.EllipticEst.cut n` is admissible (monotone increasing, tending to `1`).

A cut-off is admissible when it is `C²`, compactly supported, nonnegative, `≤ 1`, and *vanishes
on a neighbourhood of `0`*.  The last condition is what makes the boundary terms of the two
radial integrations by parts vanish at `z = 0` (the weights `w z² z²` and `w z² z` blow up there).
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.interpol_trunc_defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Honest.HR2

/-- **An admissible radial cut-off**: `C²`, compactly supported, `0 ≤ φ ≤ 1`, and vanishing on a
neighbourhood of `0`. -/
def Admissible (φ : ℝ → ℝ) : Prop :=
  ContDiff ℝ 2 φ ∧ HasCompactSupport φ ∧ (∀ z : ℝ, 0 ≤ φ z) ∧ (∀ z : ℝ, φ z ≤ 1) ∧
    ∃ ε : ℝ, 0 < ε ∧ ∀ z : ℝ, z ≤ ε → φ z = 0

/-- The effective support of an admissible cut-off is a compact interval `[ε, R]` with `ε > 0`. -/
theorem Admissible.exists_interval {φ : ℝ → ℝ} (h : Admissible φ) :
    ∃ ε R : ℝ, 0 < ε ∧ ε ≤ R ∧ ∀ z : ℝ, φ z ≠ 0 → z ∈ Set.Icc ε R := by
  obtain ⟨_, hcpt, _, _, ε, hε, hφ⟩ := h
  obtain ⟨R, hR⟩ := hcpt.isCompact.isBounded.exists_norm_le
  refine ⟨ε, max R ε, hε, le_max_right _ _, fun z hz => ⟨?_, ?_⟩⟩
  · by_contra hlt
    push_neg at hlt
    exact hz (hφ z (le_of_lt hlt))
  · have hmem : z ∈ Function.support φ := hz
    have hzc : z ∈ tsupport φ := subset_closure hmem
    have := hR z hzc
    have := abs_le.mp (by simpa [Real.norm_eq_abs] using this)
    exact le_trans this.2 (le_max_left _ _)

/-! ## The family `cut n` is admissible -/

theorem cut_contDiff_two (n : ℕ) : ContDiff ℝ 2 (Work.FTS.EllipticEst.cut n) :=
  (Work.FTS.EllipticEst.cut_contDiff n).of_le (by norm_num)

theorem cut_hasCompactSupport (n : ℕ) : HasCompactSupport (Work.FTS.EllipticEst.cut n) := by
  rw [HasCompactSupport, tsupport]
  refine (isCompact_Icc (a := (1 / (n + 1 : ℝ))) (b := 3 * (n + 1 : ℝ))).of_isClosed_subset
    isClosed_closure (closure_minimal ?_ isClosed_Icc)
  intro z hz
  by_contra hcon
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hcon
  rcases hcon with hlt | hlt
  · exact hz (Work.FTS.EllipticEst.cut_apply_zero_of_le n (le_of_lt hlt))
  · exact hz (Work.FTS.EllipticEst.cut_apply_zero_of_ge n (le_of_lt hlt))

theorem cut_admissible (n : ℕ) : Admissible (Work.FTS.EllipticEst.cut n) :=
  ⟨cut_contDiff_two n, cut_hasCompactSupport n,
    fun z => Work.FTS.EllipticEst.cut_nonneg n z,
    fun z => Work.FTS.EllipticEst.cut_le_one n z,
    1 / (n + 1 : ℝ), by positivity,
    fun z hz => Work.FTS.EllipticEst.cut_apply_zero_of_le n hz⟩

/-- The cut-off family is monotone in `n`. -/
theorem cut_mono (n : ℕ) (z : ℝ) :
    Work.FTS.EllipticEst.cut n z ≤ Work.FTS.EllipticEst.cut (n + 1) z := by
  rcases le_or_gt 0 z with hz | hz
  · have h1 : ((n : ℝ) + 1) * z - 1 ≤ ((n : ℝ) + 1 + 1) * z - 1 := by nlinarith
    have h2 : z / ((n : ℝ) + 1 + 1) - 2 ≤ z / ((n : ℝ) + 1) - 2 := by
      have h2' : (0 : ℝ) < (n : ℝ) + 1 := by linarith
      have h4 : z / ((n : ℝ) + 1 + 1) ≤ z / ((n : ℝ) + 1) :=
        div_le_div_of_nonneg_left hz h2' (by linarith)
      linarith
    have ha : Real.smoothTransition (((n : ℝ) + 1) * z - 1)
        ≤ Real.smoothTransition (((n : ℝ) + 1 + 1) * z - 1) := Real.smoothTransition.monotone h1
    have hb : (1 - Real.smoothTransition (z / ((n : ℝ) + 1) - 2)) ≤
        (1 - Real.smoothTransition (z / ((n : ℝ) + 1 + 1) - 2)) := by
      have := Real.smoothTransition.monotone h2
      linarith
    have hb0 : (0 : ℝ) ≤ 1 - Real.smoothTransition (z / ((n : ℝ) + 1) - 2) :=
      sub_nonneg.mpr (Real.smoothTransition.le_one _)
    have ha0 : (0 : ℝ) ≤ Real.smoothTransition (((n : ℝ) + 1) * z - 1) :=
      Real.smoothTransition.nonneg _
    simp only [Work.FTS.EllipticEst.cut]
    push_cast
    exact mul_le_mul ha hb hb0 (le_trans ha0 ha)
  · have h1 : ((n : ℝ) + 1) * z - 1 < 0 := by
      have : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      nlinarith
    have hzero : Real.smoothTransition (((n : ℝ) + 1) * z - 1) = 0 :=
      Real.smoothTransition.zero_of_nonpos h1.le
    have hnc : Work.FTS.EllipticEst.cut n z = 0 := by
      simp only [Work.FTS.EllipticEst.cut]
      push_cast
      rw [hzero, zero_mul]
    rw [hnc]
    exact Work.FTS.EllipticEst.cut_nonneg _ _

/-- The cut-off family tends to `1` pointwise on `(0, ∞)`. -/
theorem cut_tendsto_one {z : ℝ} (hz : 0 < z) :
    Filter.Tendsto (fun n : ℕ => Work.FTS.EllipticEst.cut n z) Filter.atTop (nhds 1) := by
  have hev : ∀ᶠ n : ℕ in Filter.atTop, (1 : ℝ) = Work.FTS.EllipticEst.cut n z := by
    refine Filter.eventually_atTop.mpr
      ⟨Nat.ceil (2 / z) + Nat.ceil (z / 2) + 2, fun n hn => ?_⟩
    have h1 : (2 : ℝ) / z ≤ (n : ℝ) + 1 := by
      have hc : (2 : ℝ) / z ≤ (Nat.ceil (2 / z) : ℝ) := Nat.le_ceil _
      have hk : Nat.ceil (2 / z) + 1 ≤ n := by omega
      have hk' : ((Nat.ceil (2 / z) + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hk
      push_cast at hk'
      linarith
    have h2 : z ≤ 2 * ((n : ℝ) + 1) := by
      have hc : z / 2 ≤ (Nat.ceil (z / 2) : ℝ) := Nat.le_ceil _
      have hk : Nat.ceil (z / 2) ≤ n := by omega
      have hk' : ((Nat.ceil (z / 2) : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hk
      linarith
    refine (Work.FTS.EllipticEst.cut_eq_one_of_mem n ?_ h2).symm
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
    have h3 : z * (2 / z) = 2 := by field_simp
    have h4 := mul_le_mul_of_nonneg_left h1 (le_of_lt hz)
    linarith [h3 ▸ h4]
  exact Filter.Tendsto.congr' hev tendsto_const_nhds

end Work.FTS.EllipticEst.Honest.HR2
