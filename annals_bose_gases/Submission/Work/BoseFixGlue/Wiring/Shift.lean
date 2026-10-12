import ChallengeDeps
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BoseFixGlue.EΛBound
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixGlue.Wiring.Shift` — corner box ↔ centred box

The corpus states its finite-volume energies on the *corner* box `box N L = [0,L]^{3N}`
(`ChallengeDeps.lean`), while FS's localisation comparison
`Work.BoseKinLoc.Compare.compare_box_energy_v2` lives on the *centred* box
`abox N L = [-L/2,L/2]^{3N}` (`Submission/CentreBox.lean`).  This module provides the
change of variables that carries a state of the corner box to the centred box, and the
elementary translation invariance of the Lebesgue integral behind it.

The shift is `cellShift N c w = w - c` (`Submission/GridSubadd.lean`) with the centre
`cubeC L = (L/2,L/2,L/2)`, so that

* `cellShift N (cubeC L) '' box N L = abox N L` (`cellShift_cubeC_mem_abox_iff`), and
* `cellShift N (-(cubeC L)) = (· + c)` is the inverse shift, which carries the corner box
  *into* the centred one (`tsupport_shift_inv_subset_abox`).

Everything is a direct application of `Submission.BoseGases.cellShift_sub`,
`partialLaplacian_cellShift` and the measure preservation
`Submission.BoseGases.integral_cellShift`.
-/

noncomputable section

open scoped Real Topology BigOperators
open MeasureTheory Filter Metric

namespace Work.BoseFixGlue

open _root_.BoseGases Submission.BoseGases Work.UBB Work.UBBInputs3 Work.BoseBox Work.BoseKinLoc
open Work.BoseBoxFix

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. The shift and its interaction with the two boxes -/

lemma cellShift_apply (N : ℕ) (c : ℝ³) (w : X N) (i : Fin N) (m : Fin 3) :
    (cellShift N c w i).ofLp m = (w i).ofLp m - c.ofLp m := by
  simp [cellShift, sub_eq_add_neg]

lemma cellShift_cubeC_neg_cubeC (N : ℕ) (L : ℝ) (w : X N) :
    cellShift N (cubeC L) (cellShift N (-(cubeC L)) w) = w := by
  ext i m
  rw [cellShift_apply, cellShift_apply]
  simp [cubeC]

lemma cellShift_neg_cubeC_cubeC (N : ℕ) (L : ℝ) (w : X N) :
    cellShift N (-(cubeC L)) (cellShift N (cubeC L) w) = w := by
  ext i m
  rw [cellShift_apply, cellShift_apply]
  simp [cubeC]

/-- `cellShift N (cubeC L)` maps the corner box `box N L` onto the centred box `abox N L`. -/
lemma cellShift_cubeC_mem_abox_iff {N : ℕ} {L : ℝ} {w : X N} :
    cellShift N (cubeC L) w ∈ abox N L ↔ w ∈ box N L := by
  rw [Submission.BoseGases.mem_abox_iff_coord, box]
  constructor
  · intro h i m
    have h' := h i m
    rw [Set.mem_Icc] at h' ⊢
    rw [cellShift_apply] at h'
    simp only [cubeC, WithLp.ofLp_toLp] at h'
    exact ⟨by linarith [h'.1], by linarith [h'.2]⟩
  · intro h i m
    have h' := h i m
    rw [Set.mem_Icc] at h' ⊢
    rw [cellShift_apply]
    simp only [cubeC, WithLp.ofLp_toLp]
    exact ⟨by linarith [h'.1], by linarith [h'.2]⟩

/-- The shifted state `x ↦ Ψ (x + c)` of a corner-box state is supported in the centred box. -/
lemma tsupport_shift_neg_cubeC_subset_abox {N : ℕ} {L : ℝ} {Ψ : X N → ℝ}
    (hsupp : tsupport Ψ ⊆ box N L) :
    tsupport (fun x : X N => Ψ (cellShift N (-(cubeC L)) x)) ⊆ abox N L := by
  intro x hx
  have hx' : x ∈ (cellShift N (-(cubeC L))) ⁻¹' tsupport Ψ :=
    Submission.BoseGases.tsupport_comp_preimage (f := Ψ) (T := cellShift N (-(cubeC L)))
      (Submission.BoseGases.cellShift_continuous N (-(cubeC L)))
      (by simpa [Function.comp_def] using hx)
  have hbox : cellShift N (-(cubeC L)) x ∈ box N L := hsupp hx'
  have h := (cellShift_cubeC_mem_abox_iff (N := N) (L := L)
    (w := cellShift N (-(cubeC L)) x)).mpr hbox
  rwa [cellShift_cubeC_neg_cubeC] at h

/-- Smoothness is preserved by the shift. -/
lemma contDiff_shift_neg_cubeC {N : ℕ} {L : ℝ} {Ψ : X N → ℝ}
    (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : X N => Ψ (cellShift N (-(cubeC L)) x)) :=
  hΨ.comp (Submission.BoseGases.cellShift_contDiff N (-(cubeC L)))

/-- Bosonic symmetry is preserved by the (diagonal) shift. -/
lemma permInvariant_shift_neg_cubeC {N : ℕ} {L : ℝ} {Ψ : X N → ℝ}
    (hΨ : PermInvariant N Ψ) :
    PermInvariant N (fun x : X N => Ψ (cellShift N (-(cubeC L)) x)) := by
  intro σ x
  have hcomm : cellShift N (-(cubeC L)) (actPerm N σ x)
      = actPerm N σ (cellShift N (-(cubeC L)) x) := by
    ext i
    rfl
  show Ψ (cellShift N (-(cubeC L)) (actPerm N σ x)) = Ψ (cellShift N (-(cubeC L)) x)
  rw [hcomm]
  exact hΨ σ _

/-! ## 2. Change of variables -/

/-- **Change of variables `box → abox`.**  For `0 < L` and a function `F` of compact support,
`∫_{abox N L} F = ∫_{box N L} F(· - c)`, i.e. the corner box integral transported to the centred
box by the shift `cellShift N (cubeC L) = (· - c)`. -/
theorem setIntegral_box_shift_self {N : ℕ} {L : ℝ} (hL : 0 < L) (F : X N → ℝ)
    (hF : HasCompactSupport F) :
    (∫ w in box N L, F (cellShift N (cubeC L) w)) = ∫ x in abox N L, F x := by
  have hbox_meas : MeasurableSet (box N L) := Submission.BoseGases.box_measurable N L
  have habox_meas : MeasurableSet (abox N L) := Submission.BoseGases.abox_measurable N L
  have hpt : ∀ w : X N, (box N L).indicator (fun w => F (cellShift N (cubeC L) w)) w
      = (abox N L).indicator F (cellShift N (cubeC L) w) := by
    intro w
    by_cases hw : w ∈ box N L
    · rw [Set.indicator_of_mem hw,
        Set.indicator_of_mem ((cellShift_cubeC_mem_abox_iff (N := N) (L := L)).mpr hw)]
    · rw [Set.indicator_of_notMem hw,
        Set.indicator_of_notMem (fun h => hw ((cellShift_cubeC_mem_abox_iff (N := N) (L := L)).mp h))]
  have key : (∫ w : X N, (box N L).indicator (fun w => F (cellShift N (cubeC L) w)) w)
      = ∫ x : X N, (abox N L).indicator F x := by
    rw [show (∫ w : X N, (box N L).indicator (fun w => F (cellShift N (cubeC L) w)) w)
        = ∫ w : X N, (abox N L).indicator F (cellShift N (cubeC L) w) from
        integral_congr_ae (Filter.Eventually.of_forall hpt)]
    exact integral_cellShift (N := N) (cubeC L) (fun x : X N => (abox N L).indicator F x)
  rw [← MeasureTheory.integral_indicator hbox_meas, ← MeasureTheory.integral_indicator habox_meas]
  exact key

end Work.BoseFixGlue
