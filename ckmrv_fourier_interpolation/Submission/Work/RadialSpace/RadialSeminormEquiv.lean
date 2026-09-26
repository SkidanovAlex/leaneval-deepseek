import Mathlib
import Submission.Work.RadialSpace.RadialSeminorm
import Submission.Work.RadialSpace.radialSeminorm_le_seminorm
import Submission.Work.RadialSpace.tail_seminorm_le_radialSeminorm

/-!
# The radial-seminorm characterisation of radial Schwartz functions

A smooth radial function on `R^n` is a Schwartz function if and only if all of
its radial seminorms are finite, and the two families of seminorms bound each
other:

* `Work.RadialSpace.radialSeminorm_le_seminorm`: every radial seminorm of a
  Schwartz function is bounded by the corresponding Schwartz seminorm;
* `Work.RadialSpace.tail_seminorm_le_radialSeminorm`: outside the unit ball, the
  full Schwartz seminorm `‖x‖ ^ k ‖D^l F x‖` is bounded by the explicit finite
  combination `radialSeminormSum k l F` of radial seminorms;
* on the unit ball the seminorms are bounded by compactness
  (`Work.RadialSpace.exists_bound_on_unit_ball`).

## Main results

* `Work.RadialSpace.exists_schwartz_iff_radialSeminorm_lt_top`
-/

open Filter Topology
open scoped SchwartzMap Topology ContDiff ENNReal

namespace Work.RadialSpace

open LeanEval.Analysis.CKMRVInterpolation

variable {n : ℕ} [NeZero n]

/-- **The radial-seminorm characterisation.** A smooth radial function on `R^n` is
a Schwartz function iff all its radial seminorms are finite. -/
theorem exists_schwartz_iff_radialSeminorm_lt_top (F : EuclideanSpace ℝ (Fin n) → ℂ)
    (hF : ContDiff ℝ Smooth F) (hr : Radial F) :
    (∃ G : 𝓢(EuclideanSpace ℝ (Fin n), ℂ), ⇑G = F) ↔
      ∀ k l, radialSeminorm k l F < ⊤ := by
  constructor
  · rintro ⟨G, rfl⟩ k l
    exact lt_of_le_of_lt (radialSeminorm_le_seminorm G k l) ENNReal.ofReal_lt_top
  · intro h
    have hdec : ∀ k l : ℕ, ∃ C : ℝ, ∀ x : EuclideanSpace ℝ (Fin n),
        ‖x‖ ^ k * ‖iteratedFDeriv ℝ l F x‖ ≤ C := by
      intro k l
      obtain ⟨C₁, hC₁, htail⟩ := tail_seminorm_le_radialSeminorm F hF hr k l
      obtain ⟨C₂, hC₂⟩ := exists_bound_on_unit_ball F hF k l
      have hsum' : radialSeminormSum k l F < ⊤ := by
        rw [radialSeminormSum]
        exact ENNReal.sum_lt_top.mpr fun j _ => ENNReal.sum_lt_top.mpr fun m _ => h m j
      have hT : (ENNReal.ofReal C₁ * (radialSeminormSum k l F + 1)) ≠ ⊤ := by
        refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_
        rw [Ne, ENNReal.add_eq_top]
        exact not_or.mpr ⟨ne_of_lt hsum', ENNReal.one_ne_top⟩
      refine ⟨max C₂ (C₁ * ((radialSeminormSum k l F).toReal + 1)), fun x => ?_⟩
      rcases le_total ‖x‖ 1 with hx | hx
      · exact le_trans (hC₂ x hx) (le_max_left _ _)
      · have h2 := htail x hx
        have h3 : (ENNReal.ofReal (‖x‖ ^ k * ‖iteratedFDeriv ℝ l F x‖)).toReal ≤
            (ENNReal.ofReal C₁ * (radialSeminormSum k l F + 1)).toReal :=
          ENNReal.toReal_mono hT h2
        rw [ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_mul, ENNReal.toReal_ofReal hC₁,
          ENNReal.toReal_add (ne_of_lt hsum') ENNReal.one_ne_top, ENNReal.toReal_one] at h3
        exact le_trans h3 (le_max_right _ _)
    exact ⟨SchwartzMap.mk F hF hdec, rfl⟩

end Work.RadialSpace
