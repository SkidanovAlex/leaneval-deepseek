import Mathlib
import Submission.Work.EKLC6Core.cutHDefs
import Submission.Work.EKLC6Core.shell_borel_cantelli

/-!
# `Work.EKLC6Core.measure_iUnion_preimage_shellThin` — the exact Borel–Cantelli bound

`Work.EKLC6Core.exists_tail_iUnion_shell_lt` states that the tail visitation set of the shells
`shell (ρ λⁿ)` has *arbitrarily small* measure.  For the assembly one needs the sharp
quantitative statement of Pisa 7.31: the measure of the **full** union
`⋃_{n ≥ 0} φ⁻ⁿ (shell (D μ0ⁿ))` is at most `Cc D / (1 - μ0)`, the sum of the geometric series of
termwise bounds.  That is the content of this file.

The only point requiring care is the term `n = 0` when `D = 0` (and the terms `n ≥ 1` when
`μ0 = 0`): there the radius `D μ0ⁿ` vanishes and the linear thinness hypothesis `hthin`, which is
only available for *positive* radii, does not apply.  But the shell at radius `0` is *empty*:
`VThick 0` is the image of `V 0 = ∅`, since `V 0 = {g | ∀ i j, |g i j - 1 i j| < 0}` is empty.
Hence those terms contribute exactly `0`, which is also `ENNReal.ofReal (Cc * 0)`.
-/

open MeasureTheory Set Topology Filter
open scoped ENNReal Pointwise

set_option linter.unusedVariables false

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

variable {μ : MeasureTheory.Measure X3} {U : Subgroup SL3} {ε : ℝ}

/-- `V 0` is empty: the condition is the impossible strict inequality `|· - 1| < 0`. -/
theorem V_zero : Work.EKLContract.V (0 : ℝ) = ∅ := by
  ext g
  simp only [Work.EKLContract.V, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  intro h
  have h00 : |g 0 0 - 1| < (0 : ℝ) := by
    have := h 0 0
    simpa using this
  exact absurd h00 (not_lt.mpr (abs_nonneg _))

/-- The `0`-thickening of any set is empty. -/
theorem VThick_zero (S : Set X3) : VThick (0 : ℝ) S = ∅ := by
  rw [VThick_def, V_zero]
  simp

/-- The shell at radius `0` is empty. -/
theorem shellThin_zero (S : CutData μ U ε) : shellThin S (0 : ℝ) = ∅ := by
  rw [shellThin]
  simp only [VThick_zero, Set.iUnion_empty, Set.union_empty]

theorem measure_iUnion_preimage_shellThin {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ] {U : Subgroup Work.EKLContract.SL3} {ε : ℝ}
    (S : Work.EKLC6Core.CutData μ U ε) {t : Fin 3 → ℝ}
    (hmp : MeasureTheory.MeasurePreserving
      (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) μ μ)
    {Cc : ℝ} (hCc : 0 < Cc)
    (hthin : ∀ s : ℝ, 0 < s →
      μ (Work.EKLC6Core.shellThin S s) ≤ ENNReal.ofReal (Cc * s))
    {D μ0 : ℝ} (hD : 0 ≤ D) (hμ00 : 0 ≤ μ0) (hμ01 : μ0 < 1) :
    μ (⋃ n : ℕ, ((fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x)^[n]) ⁻¹'
        Work.EKLC6Core.shellThin S (D * μ0 ^ n))
      ≤ ENNReal.ofReal (Cc * D / (1 - μ0)) := by
  -- The thinness estimate, extended to the (empty) shell of radius `0`.
  have hshell : ∀ s : ℝ, 0 ≤ s → μ (shellThin S s) ≤ ENNReal.ofReal (Cc * s) := by
    intro s hs
    rcases eq_or_lt_of_le hs with h | h
    · rw [← h, shellThin_zero]; simp
    · exact hthin s h
  -- Termwise bound: the `n`-th preimage is bounded by `Cc * (D μ0ⁿ)`.
  have hbound : ∀ n : ℕ,
      μ (((fun x : X3 => aDiag t • x)^[n]) ⁻¹' shellThin S (D * μ0 ^ n))
        ≤ ENNReal.ofReal (Cc * D * μ0 ^ n) := by
    intro n
    have hs : 0 ≤ D * μ0 ^ n := by positivity
    have hle := Measure.le_map_apply (μ := μ)
      ((hmp.iterate n).measurable).aemeasurable (shellThin S (D * μ0 ^ n))
    rw [(hmp.iterate n).map_eq] at hle
    calc μ (((fun x : X3 => aDiag t • x)^[n]) ⁻¹' shellThin S (D * μ0 ^ n))
        ≤ μ (shellThin S (D * μ0 ^ n)) := hle
      _ ≤ ENNReal.ofReal (Cc * (D * μ0 ^ n)) := hshell _ hs
      _ = ENNReal.ofReal (Cc * D * μ0 ^ n) := by congr 1; ring
  -- Sum the termwise bounds and evaluate the geometric series.
  calc μ (⋃ n : ℕ, ((fun x : X3 => aDiag t • x)^[n]) ⁻¹' shellThin S (D * μ0 ^ n))
      ≤ ∑' n : ℕ, μ (((fun x : X3 => aDiag t • x)^[n]) ⁻¹' shellThin S (D * μ0 ^ n)) :=
        measure_iUnion_le _
    _ ≤ ∑' n : ℕ, ENNReal.ofReal (Cc * D * μ0 ^ n) := ENNReal.tsum_le_tsum hbound
    _ = ENNReal.ofReal (Cc * D / (1 - μ0)) := by
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)
              ((summable_geometric_of_lt_one hμ00 hμ01).mul_left (Cc * D))]
        congr 1
        rw [tsum_mul_left, tsum_geometric_of_lt_one hμ00 hμ01, div_eq_mul_inv]

end Work.EKLC6Core
