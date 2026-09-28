import Mathlib
import Submission.Work.HP.MMDefs
import Submission.Work.HP.BallVolIntrinsic

/-!
# `ConeSliceVolBound`

`Work.HP.coneSliceVol L v w γ` is the volume of
`span_ℝ(L) ∩ B(1) ∩ 𝒞_v^{(γ)} ∩ 𝒞_w^{(γ)}`, where the cone conditions are the two
`|⟪·,t⟫| ≤ ‖·‖‖t‖ / (2γ)` inequalities.  The defining set always contains the conjunct
`‖t‖ ≤ 1`, so it is a subset of the closed unit ball of `spanE L = span_ℝ(L)`, whatever the
values of `v`, `w` and `γ` (in particular for the degenerate `γ ≤ 0`, where Lean's division
makes the cone conditions as strong as possible).  The closed unit ball of a finite dimensional
real inner product space `V` has volume `ballVol (finrank ℝ V)` (`Work.HP.BallVolIntrinsic`) and
finite measure (`MeasureTheory.measure_closedBall_lt_top`), and
`finrank ℝ (spanE L) ≤ finrank ℝ (EuclideanSpace ℝ ι) = card ι`.  Hence `coneSliceVol` is
bounded by a constant depending only on the index type `ι`.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Finset

namespace Work.HP.MM2

/-- The cone slice volume is at most the volume of the unit ball of the real span of `L`. -/
theorem coneSliceVol_le_ballVol {ι : Type} [Fintype ι] (L : Submodule ℤ (ι → ℤ))
    (v w : ι → ℝ) (γ : ℝ) :
    Work.HP.coneSliceVol L v w γ ≤ Work.HP.ballVol (Module.finrank ℝ ↥(Work.HP.spanE L)) := by
  set S : Set (EuclideanSpace ℝ ι) :=
    {t : EuclideanSpace ℝ ι |
      |inner ℝ (Work.HP.toE v) t| ≤ ‖Work.HP.toE v‖ * ‖t‖ / (2 * γ) ∧
      |inner ℝ (Work.HP.toE w) t| ≤ ‖Work.HP.toE w‖ * ‖t‖ / (2 * γ) ∧ ‖t‖ ≤ 1} with hS
  have hdef : Work.HP.coneSliceVol L v w γ
      = (volume {t : ↥(Work.HP.spanE L) | (t : EuclideanSpace ℝ ι) ∈ S}).toReal := by
    rw [Work.HP.coneSliceVol, Work.HP.subVol, hS]
  rw [hdef]
  have hA : {t : ↥(Work.HP.spanE L) | (t : EuclideanSpace ℝ ι) ∈ S} ⊆
      Metric.closedBall (0 : ↥(Work.HP.spanE L)) 1 := by
    rintro t ht
    simp only [Metric.mem_closedBall, dist_zero_right]
    exact ht.2.2
  have hfin : (volume : Measure ↥(Work.HP.spanE L))
      (Metric.closedBall (0 : ↥(Work.HP.spanE L)) 1) ≠ ⊤ :=
    (measure_closedBall_lt_top (x := (0 : ↥(Work.HP.spanE L))) (r := (1 : ℝ))).ne
  calc (volume {t : ↥(Work.HP.spanE L) | (t : EuclideanSpace ℝ ι) ∈ S}).toReal
      ≤ (volume (Metric.closedBall (0 : ↥(Work.HP.spanE L)) 1)).toReal :=
        ENNReal.toReal_mono hfin (measure_mono hA)
    _ = Work.HP.ballVol (Module.finrank ℝ ↥(Work.HP.spanE L)) := Work.HP.BallVolIntrinsic

theorem ConeSliceVolBound {ι : Type} [Fintype ι] :
    ∃ K : ℝ, 0 < K ∧ ∀ (L : Submodule ℤ (ι → ℤ)) (v w : ι → ℝ) (γ : ℝ),
      Work.HP.coneSliceVol L v w γ ≤ K := by
  refine ⟨1 + ∑ r ∈ Finset.range (Fintype.card ι + 1), |Work.HP.ballVol r|, ?_, ?_⟩
  · have h : 0 ≤ ∑ r ∈ Finset.range (Fintype.card ι + 1), |Work.HP.ballVol r| :=
      Finset.sum_nonneg fun r _ => abs_nonneg _
    linarith
  · intro L v w γ
    refine (coneSliceVol_le_ballVol L v w γ).trans ?_
    have hfl : Module.finrank ℝ ↥(Work.HP.spanE L) ≤ Fintype.card ι :=
      (Submodule.finrank_le (Work.HP.spanE L)).trans
        (le_of_eq (finrank_euclideanSpace (𝕜 := ℝ) (ι := ι)))
    have hm : Module.finrank ℝ ↥(Work.HP.spanE L) ∈ Finset.range (Fintype.card ι + 1) :=
      Finset.mem_range.mpr (by omega)
    have h2 : Work.HP.ballVol (Module.finrank ℝ ↥(Work.HP.spanE L)) ≤
        |Work.HP.ballVol (Module.finrank ℝ ↥(Work.HP.spanE L))| := le_abs_self _
    have h3 : |Work.HP.ballVol (Module.finrank ℝ ↥(Work.HP.spanE L))| ≤
        ∑ r ∈ Finset.range (Fintype.card ι + 1), |Work.HP.ballVol r| :=
      Finset.single_le_sum (s := Finset.range (Fintype.card ι + 1))
        (f := fun r => |Work.HP.ballVol r|) (fun r _ => abs_nonneg (Work.HP.ballVol r)) hm
    have h4 : (∑ r ∈ Finset.range (Fintype.card ι + 1), |Work.HP.ballVol r|) ≤
        1 + ∑ r ∈ Finset.range (Fintype.card ι + 1), |Work.HP.ballVol r| := by
      linarith
    linarith

end Work.HP.MM2
