import ChallengeDeps
import Submission.FUP.Porosity
import Submission.FUP.LineRestriction
import Submission.FUP.SegmentMeasure

open FractalUncertainty
open MeasureTheory FourierTransform Metric
open scoped ENNReal

set_option autoImplicit false
variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

namespace Submission.FUP

/-- The closed `r`-neighbourhood of `Y`, presented as the closure of the Minkowski sum with a
closed ball, so that it is closed (hence Borel measurable) by construction. -/
noncomputable def nbhd (Y : Set ℝᵈ) (r : ℝ) : Set ℝᵈ :=
  closure (addSet Y (closedBall 0 r))

lemma isClosed_nbhd (Y : Set ℝᵈ) (r : ℝ) : IsClosed (nbhd Y r) := isClosed_closure

lemma measurableSet_nbhd (Y : Set ℝᵈ) (r : ℝ) : MeasurableSet (nbhd Y r) :=
  (isClosed_nbhd Y r).measurableSet

lemma subset_nbhd (Y : Set ℝᵈ) {r : ℝ} (hr : 0 ≤ r) : Y ⊆ nbhd Y r := by
  intro y hy
  exact subset_closure ⟨y, hy, 0, by simpa using hr, by abel⟩

/-- The closure of a line-porous set is line-porous, with a slightly weakened porosity
parameter: a ball avoiding `X` also avoids `closure X` (after shrinking slightly). -/
lemma PorousOnLines.closure {ν ν' α₀ α₁ : ℝ} {X : Set ℝᵈ} (hα₀ : 0 < α₀) (hν' : ν' < ν)
    (hX : PorousOnLines ν α₀ α₁ X) : PorousOnLines ν' α₀ α₁ (closure X) := by
  intro R hR y₁ y₂ hd
  have hRpos : 0 < R := lt_trans hα₀ (Set.mem_Ioo.mp hR).1
  rcases hX R hR y₁ y₂ hd with ⟨x, hx, hxempty⟩
  refine ⟨x, hx, ?_⟩
  apply Set.subset_empty_iff.mp
  rintro z ⟨hzball, hzclos⟩
  have hpos : 0 < (ν - ν') * R := mul_pos (sub_pos.mpr hν') hRpos
  obtain ⟨w, hwX, hwdist⟩ := Metric.mem_closure_iff.mp hzclos ((ν - ν') * R) hpos
  have hzx : dist z x ≤ ν' * R := Metric.mem_closedBall.mp hzball
  have hwx : dist w x < ν * R := by
    calc dist w x ≤ dist w z + dist z x := dist_triangle w z x
      _ = dist z w + dist z x := by rw [dist_comm w z]
      _ < (ν - ν') * R + ν' * R := by linarith
      _ = ν * R := by ring
  have hw : w ∈ closedBall x (ν * R) ∩ X := ⟨Metric.mem_closedBall.mpr (le_of_lt hwx), hwX⟩
  simpa [hxempty] using hw

/-- A closed neighbourhood of a line-porous set is line-porous (with porosity parameter
halved and lower scale raised to `4r/ν`). -/
lemma PorousOnLines_nbhd {ν α₀ α₁ r : ℝ} {Y : Set ℝᵈ} (hα₀ : 0 < α₀) (hν : 0 < ν)
    (hα : α₀ ≤ 4 * r / ν) (hY : PorousOnLines ν α₀ α₁ Y) :
    PorousOnLines (ν / 2) (4 * r / ν) α₁ (nbhd Y r) := by
  have hν4pos : 0 < 3 * ν / 4 := by positivity
  have hlt : 3 * ν / 4 < ν := by linarith
  have hsub : ν - 3 * ν / 4 = ν / 4 := by ring
  have h4r : 0 < 4 * r / ν := lt_of_lt_of_le hα₀ hα
  have hZ : PorousOnLines (3 * ν / 4) (4 * r / ν) α₁ (addSet Y (closedBall 0 r)) := by
    have h := PorousOnLines_add_ball (ν := ν) (ν' := 3 * ν / 4) (α₀ := α₀) (α₁ := α₁)
      (r := r) (Y := Y) hν4pos hlt ?_ hY
    · rwa [hsub, show r / (ν / 4) = 4 * r / ν by ring] at h
    · rw [hsub]
      have : r / (ν / 4) = 4 * r / ν := by ring
      rw [this]; exact hα
  exact PorousOnLines.closure h4r (ν' := ν / 2) (by linarith) hZ

/-- Quantitative intersection of a closed neighbourhood of a line-porous set with a unit-speed
segment: this is the estimate used in §6.1 of Cohen's paper. -/
lemma nbhd_segment_measure {ν α₀ α₁ r : ℝ} {Y : Set ℝᵈ} (hα₀ : 0 < α₀) (hν : 0 < ν)
    (hα : α₀ ≤ 4 * r / ν) (hY : PorousOnLines ν α₀ α₁ Y)
    (p v : ℝᵈ) (hv : ‖v‖ = 1) {R : ℝ} (hR : R ∈ Set.Ioo (4 * r / ν) α₁) :
    ∃ γ C : ℝ, 0 < γ ∧ 0 < C ∧
      (volume ((fun t : ℝ => p + t • v) ⁻¹' nbhd Y r ∩ Set.Icc 0 R) : ℝ≥0∞) ≤
        ENNReal.ofReal (C * R * ((4 * r / ν) / R) ^ γ) := by
  have h4r : 0 < 4 * r / ν := lt_of_lt_of_le hα₀ hα
  have hZ : PorousOnLines (ν / 2) (4 * r / ν) α₁ (nbhd Y r) :=
    PorousOnLines_nbhd hα₀ hν hα hY
  exact line_porous_segment_measure (ν := ν / 2) (α₀ := 4 * r / ν) (α₁ := α₁)
    (by positivity) h4r (measurableSet_nbhd Y r) hZ p v hv hR

end Submission.FUP
