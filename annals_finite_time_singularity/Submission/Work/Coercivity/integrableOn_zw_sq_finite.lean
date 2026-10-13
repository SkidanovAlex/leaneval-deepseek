import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.Interval.Basic
import Submission.Work.Coercivity.Defs
import Submission.Work.Spaces.HardyZ

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.Coercivity

/-- A function which is bounded and continuous on the open interval `(0,R)` is integrable
on the closed interval `[0,R]`.  The two endpoints are null sets, so neither the bound nor
the continuity needs to extend to them. -/
private lemma integrableOn_Icc_of_bounded_continuousOn_Ioo {f : ℝ → ℝ} {R C : ℝ}
    (hf : ContinuousOn f (Set.Ioo 0 R)) (hC : ∀ z ∈ Set.Ioo 0 R, ‖f z‖ ≤ C) :
    IntegrableOn f (Set.Icc 0 R) := by
  have hfin : volume (Set.Ioo 0 R) < ⊤ := by
    rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top
  have hbdd : ∀ᵐ z ∂volume.restrict (Set.Ioo 0 R), ‖f z‖ ≤ C := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with z hz
    exact hC z hz
  have hInt : IntegrableOn f (Set.Ioo 0 R) :=
    IntegrableOn.of_bound hfin (hf.aestronglyMeasurable measurableSet_Ioo) C hbdd
  simpa only [IntegrableOn, MeasureTheory.restrict_Ioo_eq_restrict_Icc] using hInt

theorem integrableOn_zw_sq_finite {u : ℝ → ℝ → ℝ} (hsm : Work.Spaces.SmoothNbhd u) {R : ℝ} (hR : 0 < R)
    {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ)
    (hb1 : ∃ C : ℝ, ∀ z ∈ Set.Ioo 0 R, |u z θ * Work.Spaces.w z| ≤ C)
    (hb2 : ∃ C : ℝ, ∀ z ∈ Set.Ioo 0 R, |Work.Coercivity.L u z θ * u z θ * Work.Spaces.w z ^ 2| ≤ C) :
    MeasureTheory.IntegrableOn (fun z => (u z θ * Work.Spaces.w z) ^ 2) (Set.Icc 0 R) ∧
    MeasureTheory.IntegrableOn (fun z => Work.Coercivity.L u z θ * u z θ * Work.Spaces.w z ^ 2) (Set.Icc 0 R) := by
  obtain ⟨C1, hC1⟩ := hb1
  obtain ⟨C2, hC2⟩ := hb2
  -- The `θ`-slice `z ↦ u z θ` and its `z`-derivative are continuous on `(-1,∞)`.
  have hslice : ContinuousOn (fun z => u z θ) (Set.Ioi (-1)) :=
    (Work.Spaces.hardyZ_contDiffOn_slice u hsm hθ).continuousOn
  have hsub : Set.Ioo 0 R ⊆ Set.Ioi (-1) := by
    intro z hz; simp only [Set.mem_Ioo] at hz; simp only [Set.mem_Ioi]; linarith [hz.1]
  have hslice' : ContinuousOn (fun z => u z θ) (Set.Ioo 0 R) := hslice.mono hsub
  have hpz : ContinuousOn (fun z => Work.Spaces.pz u z θ) (Set.Ioo 0 R) :=
    (Work.Spaces.hardyZ_continuousOn_pz_slice u hsm hθ).mono hsub
  -- The weight `w` is continuous away from `0`.
  have hw : ContinuousOn (fun z : ℝ => Work.Spaces.w z) (Set.Ioo 0 R) := by
    simp only [Work.Spaces.w]
    exact ContinuousOn.div (by fun_prop) (by fun_prop) (fun z hz => by
      have hz0 : z ≠ 0 := by simp only [Set.mem_Ioo] at hz; linarith [hz.1]
      exact pow_ne_zero 2 hz0)
  have hw2 : ContinuousOn (fun z : ℝ => Work.Spaces.w z ^ 2) (Set.Ioo 0 R) := hw.pow 2
  -- Continuity of the two integrands.
  have hcont1 : ContinuousOn (fun z => (u z θ * Work.Spaces.w z) ^ 2) (Set.Ioo 0 R) :=
    (hslice'.mul hw).pow 2
  have hDz : ContinuousOn (fun z => Work.Spaces.Dz u z θ) (Set.Ioo 0 R) := by
    simp only [Work.Spaces.Dz]
    exact continuousOn_id.mul hpz
  have hthird : ContinuousOn (fun z => 2 * u z θ / (1 + z)) (Set.Ioo 0 R) := by
    apply ContinuousOn.div
    · exact continuousOn_const.mul hslice'
    · exact continuousOn_const.add continuousOn_id
    · intro z hz; simp only [Set.mem_Ioo] at hz; linarith [hz.1]
  have hLu : ContinuousOn (fun z => Work.Coercivity.L u z θ) (Set.Ioo 0 R) := by
    have heq : (fun z => Work.Coercivity.L u z θ) =
        fun z => (u z θ + Work.Spaces.Dz u z θ) - 2 * u z θ / (1 + z) := rfl
    rw [heq]
    exact (hslice'.add hDz).sub hthird
  have hcont2 : ContinuousOn (fun z => Work.Coercivity.L u z θ * u z θ * Work.Spaces.w z ^ 2)
      (Set.Ioo 0 R) := (hLu.mul hslice').mul hw2
  -- Boundedness of the two integrands on `(0,R)`, from `hb1` and `hb2`.
  have hbdd1 : ∀ z ∈ Set.Ioo 0 R, ‖(u z θ * Work.Spaces.w z) ^ 2‖ ≤ C1 ^ 2 := by
    intro z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs (u z θ * Work.Spaces.w z)]
    exact pow_le_pow_left₀ (abs_nonneg _) (hC1 z hz) 2
  have hbdd2 : ∀ z ∈ Set.Ioo 0 R,
      ‖Work.Coercivity.L u z θ * u z θ * Work.Spaces.w z ^ 2‖ ≤ C2 := by
    intro z hz
    rw [Real.norm_eq_abs]
    exact hC2 z hz
  exact ⟨integrableOn_Icc_of_bounded_continuousOn_Ioo hcont1 hbdd1,
    integrableOn_Icc_of_bounded_continuousOn_Ioo hcont2 hbdd2⟩

end Work.Coercivity
