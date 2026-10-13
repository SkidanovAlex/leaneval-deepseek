import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS_RegExport.RXA1w.Helpers
import Submission.Work.FTS.StrongEps.EComparison.EllPkgClsSliceAux
import Submission.Work.FTS.H2.LinfQ

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.HkMinPrep`

Elementary preparation for the pointwise bound `hkMem_pointwise_min`: the weight `w` is
nonnegative, the a.e. transfer from the open angular interval `(0,π/2)` to `Iθ`, the algebraic
comparison `(a b)² ≤ (a c)²` for `0 ≤ b ≤ c`, the notion of an *admissible slot* of
`HkIntegrand α 4`, and the pointwise domination of an admissible slot by the integrand.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXT

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- `w ≥ 0` everywhere. -/
theorem w_nonneg (z : ℝ) : 0 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w]; positivity

/-- `volume.restrict Iθ = volume.restrict (Ioo 0 (π/2))`. -/
theorem restrict_Iθ_eq_restrict_Ioo :
    MeasureTheory.volume.restrict Work.Spaces.Iθ
      = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  rw [Work.Spaces.Iθ]
  exact (Measure.restrict_congr_set
    (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
      (b := Real.pi / 2))).symm

/-- An a.e. statement on `Iθ` holds if it holds at every interior angle. -/
theorem ae_restrict_Iθ_of_Ioo {p : ℝ → Prop}
    (h : ∀ σ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), p σ) :
    ∀ᵐ σ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), p σ := by
  rw [restrict_Iθ_eq_restrict_Ioo]
  exact ae_restrict_of_forall_mem measurableSet_Ioo h

/-- A function continuous on the open angular interval is a.e. strongly measurable for
`volume.restrict Iθ`. -/
theorem aestrongly_Iθ_of_continuousOn {u : ℝ → ℝ}
    (h : ContinuousOn u (Set.Ioo (0 : ℝ) (Real.pi / 2))) :
    MeasureTheory.AEStronglyMeasurable u (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  rw [restrict_Iθ_eq_restrict_Ioo]
  exact h.aestronglyMeasurable measurableSet_Ioo

/-- The interval integral over `Ioi 0` is the set integral over `Iz = Ici 0`. -/
theorem integral_Ioi_eq_integral_Iz (f : ℝ → ℝ) :
    (∫ x in Set.Ioi (0 : ℝ), f x) = ∫ x in Work.Spaces.Iz, f x := by
  rw [Work.Spaces.Iz, MeasureTheory.restrict_Ioi_eq_restrict_Ici]

/-- `(a b)² ≤ (a c)²` for `0 ≤ b ≤ c`. -/
theorem sq_mul_le_sq_mul {a b c : ℝ} (hb : 0 ≤ b) (hbc : b ≤ c) : (a * b) ^ 2 ≤ (a * c) ^ 2 := by
  have h1 : b ^ 2 ≤ c ^ 2 := by nlinarith
  calc (a * b) ^ 2 = a ^ 2 * b ^ 2 := by ring
    _ ≤ a ^ 2 * c ^ 2 := mul_le_mul_of_nonneg_left h1 (sq_nonneg a)
    _ = (a * c) ^ 2 := by ring

/-- The slots of `HkIntegrand α 4`: the mixed ones (`1 ≤ i`, `i + j ≤ 4`) and the pure radial
ones (`i = 0`, `j ≤ 4`). -/
def FTSAdm (j i : ℕ) : Prop := (1 ≤ i ∧ i + j ≤ 4) ∨ (i = 0 ∧ j ≤ 4)

/-- At an interior angle, the plain-`w`-weighted square of an admissible slot is dominated by
the `ℋ⁴`-integrand. -/
theorem slot_pointwise_le {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ} (j i : ℕ) (hadm : FTSAdm j i)
    (x : ℝ) {σ : ℝ} (hσ : σ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    (Work.Spaces.mixed j i f x σ) ^ 2 * (Work.Spaces.w x) ^ 2
      ≤ Work.Spaces.HkIntegrand α 4 f x σ := by
  have hsin0 : 0 < Real.sin (2 * σ) := Work.FTS.H2.sin_two_pos_of_mem_Ioo hσ
  have hsinle : Real.sin (2 * σ) ≤ 1 := Real.sin_le_one _
  rcases hadm with ⟨hi1, hij⟩ | ⟨hi0, hj4⟩
  · -- mixed slot: compare with the `Wt`-weighted slot
    have hbase := Work.Spaces.sq_le_HkIntegrand_mixed α 4 f x σ i j hi1 hij
    have hle : (Work.Spaces.mixed j i f x σ * Work.Spaces.w x) ^ 2
        ≤ (Work.Spaces.mixed j i f x σ * Work.Spaces.Wt α x σ) ^ 2 := by
      refine sq_mul_le_sq_mul (a := Work.Spaces.mixed j i f x σ) (w_nonneg x) ?_
      have hspos : 0 < (Real.sin (2 * σ)) ^ (Work.Spaces.gam α / 2) :=
        Real.rpow_pos_of_pos hsin0 _
      have hsle : (Real.sin (2 * σ)) ^ (Work.Spaces.gam α / 2) ≤ 1 :=
        Real.rpow_le_one hsin0.le hsinle (by have := Work.Spaces.gam_pos hα; linarith)
      have hone : (1 : ℝ) ≤ (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α / 2)) := by
        rw [Real.rpow_neg hsin0.le]
        simpa [one_div] using one_le_one_div hspos hsle
      calc Work.Spaces.w x = Work.Spaces.w x * 1 := (mul_one _).symm
        _ ≤ Work.Spaces.w x * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α / 2)) :=
            mul_le_mul_of_nonneg_left hone (w_nonneg x)
        _ = Work.Spaces.w x * Work.Spaces.wTheta α σ := rfl
    calc (Work.Spaces.mixed j i f x σ) ^ 2 * (Work.Spaces.w x) ^ 2
        = (Work.Spaces.mixed j i f x σ * Work.Spaces.w x) ^ 2 := by ring
      _ ≤ (Work.Spaces.mixed j i f x σ * Work.Spaces.Wt α x σ) ^ 2 := hle
      _ ≤ Work.Spaces.HkIntegrand α 4 f x σ := hbase
  · -- pure radial slot
    subst hi0
    have hbase := Work.Spaces.sq_le_HkIntegrand_z α 4 f x σ j (by omega)
    have hle : (Work.Spaces.DzIter j f x σ * Work.Spaces.w x) ^ 2
        ≤ (Work.Spaces.DzIter j f x σ
            * (Work.Spaces.w x / (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
      refine sq_mul_le_sq_mul (a := Work.Spaces.DzIter j f x σ) (w_nonneg x) ?_
      have hspos : 0 < (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2) :=
        Real.rpow_pos_of_pos hsin0 _
      have hsle : (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2) ≤ 1 :=
        Real.rpow_le_one hsin0.le hsinle (by have := Work.Spaces.eta_pos; linarith)
      calc Work.Spaces.w x = Work.Spaces.w x * 1 := (mul_one _).symm
        _ ≤ Work.Spaces.w x * (1 / (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2)) :=
            mul_le_mul_of_nonneg_left (one_le_one_div hspos hsle) (w_nonneg x)
        _ = Work.Spaces.w x / (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2) := by ring
    calc (Work.Spaces.mixed j 0 f x σ) ^ 2 * (Work.Spaces.w x) ^ 2
        = (Work.Spaces.DzIter j f x σ * Work.Spaces.w x) ^ 2 := by
          rw [Work.Spaces.mixed_zero_right]; ring
      _ ≤ _ := hle
      _ ≤ Work.Spaces.HkIntegrand α 4 f x σ := hbase

end Work.FTS_RegExport.RXT
