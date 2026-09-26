import Mathlib
import Submission.Work.BoxShrink.PinchOff.Basic

/-!
# The closure of the slice, off the slice, lies on the box sphere

The slice `Σ = F ∩ PBox s c σ ∩ {y (σ 2) = c (σ 2) + u}` of the pinch-off configuration is open in
the trace of the cutting plane inside the surface.  Consequently a point of the closure of `Σ`
which does not itself lie in `Σ` cannot lie in the *interior* of the box: it must lie on the
boundary sphere `∂PBox s c σ = {boxNorm = s}` of the box, i.e. in `SphereTrace s c σ`.

This is the elementary set-theoretic half of the "gate" description of the slice: limit points of
the slice off the slice are exactly controlled by the box sphere.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.PinchOff

noncomputable section

/-- The closure of Pardon's open box is contained in the closed box `{boxNorm ≤ s}`. -/
theorem closure_PBox_subset_boxNorm_le (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) :
    closure (Submission.PBox s c σ) ⊆ {y : R3 | Submission.boxNorm c σ y ≤ s} := by
  intro y hy
  have hi : ∀ i : Fin 3, |y (σ i) - c (σ i)| ≤ Submission.boxSide i * s := by
    intro i
    have h1 : closure (Submission.PBox s c σ) ⊆
        closure {z : R3 | |z (σ i) - c (σ i)| < Submission.boxSide i * s} :=
      closure_mono (fun z hz => (Submission.mem_PBox.mp hz) i)
    have h2 : closure {z : R3 | |z (σ i) - c (σ i)| < Submission.boxSide i * s} ⊆
        {z : R3 | |z (σ i) - c (σ i)| ≤ Submission.boxSide i * s} :=
      closure_lt_subset_le (f := fun z : R3 => |z (σ i) - c (σ i)|)
        (g := fun _ : R3 => Submission.boxSide i * s) (by fun_prop) continuous_const
    exact h2 (h1 hy)
  show max (max (|y (σ 0) - c (σ 0)| / Submission.boxSide 0)
      (|y (σ 1) - c (σ 1)| / Submission.boxSide 1))
      (|y (σ 2) - c (σ 2)| / Submission.boxSide 2) ≤ s
  rw [max_le_iff, max_le_iff, div_le_iff₀ (Submission.boxSide_pos 0),
    div_le_iff₀ (Submission.boxSide_pos 1), div_le_iff₀ (Submission.boxSide_pos 2)]
  exact ⟨⟨by simpa [mul_comm] using hi 0, by simpa [mul_comm] using hi 1⟩,
    by simpa [mul_comm] using hi 2⟩

/-- The cutting plane is closed. -/
theorem isClosed_cutPlane (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    IsClosed (Work.BoxShrink.Core.cutPlane c σ u) := by
  have hset : Work.BoxShrink.Core.cutPlane c σ u = {z : R3 | z (σ 2) = c (σ 2) + u} := rfl
  rw [hset]
  exact isClosed_eq (f := fun z : R3 => z (σ 2)) (g := fun _ => c (σ 2) + u)
    (by fun_prop) continuous_const

theorem closure_Sigma_sdiff_Sigma_subset_sphereTrace (ψ : Submission.Diffeo) (s : ℝ)
    (c : LeanEval.KnotTheory.PardonDistortion.R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    closure (Work.BoxShrink.PinchOff.Sigma ψ s c σ u) \ Work.BoxShrink.PinchOff.Sigma ψ s c σ u ⊆
      Work.BoxShrink.PinchOff.SphereTrace s c σ := by
  intro y hy
  obtain ⟨hycl, hynot⟩ := hy
  -- `Σ` is a triple intersection: carrier ∩ PBox ∩ cutPlane, so the closure separates.
  have hclAB := (closure_inter_subset hycl).1
  have hclA : y ∈ closure (surface ψ).carrier := (closure_inter_subset hclAB).1
  have hclB : y ∈ closure (Submission.PBox s c σ) := (closure_inter_subset hclAB).2
  have hclC : y ∈ closure (Work.BoxShrink.Core.cutPlane c σ u) :=
    (closure_inter_subset hycl).2
  -- the surface and the cutting plane are closed
  have hycar : y ∈ (surface ψ).carrier := by
    rwa [IsClosed.closure_eq ((Work.Smooth.Morse.Surface.isCompact_torus ψ).isClosed)] at hclA
  have hycut : y ∈ Work.BoxShrink.Core.cutPlane c σ u := by
    rwa [(isClosed_cutPlane c σ u).closure_eq] at hclC
  -- a limit point of the slice off the slice is not in the open box
  have hnotP : y ∉ Submission.PBox s c σ := by
    intro hP
    exact hynot ⟨⟨hycar, hP⟩, hycut⟩
  -- hence its box norm is exactly `s`
  have hle : Submission.boxNorm c σ y ≤ s := closure_PBox_subset_boxNorm_le s c σ hclB
  have hge : s ≤ Submission.boxNorm c σ y := by
    have h := (Submission.mem_PBox_iff s c σ y).not.mp hnotP
    exact le_of_not_gt h
  show y ∈ SphereTrace s c σ
  exact le_antisymm hle hge

end

end Work.BoxShrink.PinchOff
