import Mathlib
import Submission.Work.Drive.Mono.FiberModel.Defs
import Submission.Work.Drive.Mono.FiberModel.pair_facts

/-!
# The shadow of the box and the planar image of the removed level

The shadow `W = π '' closure (PBox s c σ)` of the closed box is the closure of the shadow of the
open box, and the latter is the *interior* of the former (convexity + `π` open).  Consequently the
planar image `Z` of the removed level is `interior W ∩ chamber`: the removal condition depends on
`π y` alone.
-/

open LeanEval.KnotTheory.PardonDistortion Set

namespace Work.Drive.Mono.FiberModel

noncomputable section

/-- The box is nonempty for positive radius. -/
theorem PBox_nonempty {s : ℝ} (hs : 0 < s) (c : R3) (σ : Equiv.Perm (Fin 3)) :
    (Submission.PBox s c σ).Nonempty :=
  ⟨c, fun i => by
    rw [sub_self, abs_zero]
    exact mul_pos (Submission.boxSide_pos i) hs⟩

/-- The box is empty for nonpositive radius. -/
theorem PBox_eq_empty_of_nonpos {s : ℝ} (hs : s ≤ 0) (c : R3) (σ : Equiv.Perm (Fin 3)) :
    Submission.PBox s c σ = ∅ := by
  ext y
  simp only [Submission.mem_PBox, Set.mem_empty_iff_false, iff_false, not_forall]
  refine ⟨0, ?_⟩
  have hb : Submission.boxSide 0 * s ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (Submission.boxSide_pos 0).le hs
  intro h
  have h0 : 0 ≤ |y (σ 0) - c (σ 0)| := abs_nonneg _
  linarith

/-- The box is bounded. -/
theorem isBounded_PBox (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) :
    Bornology.IsBounded (Submission.PBox s c σ) := by
  by_cases hs : s ≤ 0
  · rw [PBox_eq_empty_of_nonpos hs]; exact Bornology.isBounded_empty
  · exact (Metric.isBounded_ball (x := c) (r := (5 / 2) * s)).subset
      (Submission.PBox_subset_ball s (not_le.mp hs).le c σ)

/-- The shadow of the closed box is the closure of the shadow of the open box. -/
theorem boxShadow_eq_closure_image (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (v : R3)
    (ℓ : R3 →L[ℝ] ℝ) :
    boxShadow s c σ v ℓ = closure (levPair v ℓ '' Submission.PBox s c σ) := by
  rw [boxShadow, ClBox, shadow]
  refine Subset.antisymm ?_ ?_
  · intro X hX
    obtain ⟨y, hy, rfl⟩ := hX
    simpa only [levPair_eq_levPairCLM] using
      image_closure_subset_closure_image (f := levPairCLM v ℓ)
        (s := Submission.PBox s c σ) (map_continuous (levPairCLM v ℓ)) ⟨y, hy, rfl⟩
  · have hcompact : IsCompact (closure (Submission.PBox s c σ)) :=
      (isBounded_PBox s c σ).isCompact_closure
    have hclosed : IsClosed ((levPairCLM v ℓ) '' closure (Submission.PBox s c σ)) :=
      (hcompact.image (map_continuous _)).isClosed
    exact closure_minimal (Set.image_mono subset_closure) hclosed

/-- The shadow of the *open* box is the interior of the shadow of the closed box. -/
theorem image_PBox_eq_interior_boxShadow {s : ℝ} (c : R3) (σ : Equiv.Perm (Fin 3)) {v : R3}
    {ℓ : R3 →L[ℝ] ℝ} (hv : v ≠ 0) (hℓv : ℓ v = 0) (hℓne : ℓ ≠ 0) :
    levPair v ℓ '' Submission.PBox s c σ = interior (boxShadow s c σ v ℓ) := by
  by_cases hs : s ≤ 0
  · rw [PBox_eq_empty_of_nonpos hs, Set.image_empty, boxShadow, ClBox, shadow,
      PBox_eq_empty_of_nonpos hs, closure_empty, Set.image_empty]
    simp
  · have hs' : 0 < s := not_le.mp hs
    have hconv : Convex ℝ (levPair v ℓ '' Submission.PBox s c σ) := by
      change Convex ℝ ((levPairCLM v ℓ).toLinearMap '' Submission.PBox s c σ)
      exact (Work.Topology.SphereSlicing.convex_PBox s c σ).linear_image
        (levPairCLM v ℓ).toLinearMap
    have hopen : IsOpen (levPair v ℓ '' Submission.PBox s c σ) := by
      rw [levPair_eq_levPairCLM]
      exact levPairCLM_isOpenMap hv hℓv hℓne _
        (Work.Topology.SphereSlicing.isOpen_PBox s c σ)
    have hne : (interior (levPair v ℓ '' Submission.PBox s c σ)).Nonempty := by
      rw [hopen.interior_eq]
      exact (PBox_nonempty hs' c σ).image _
    have h1 := Convex.interior_closure_eq_interior_of_nonempty_interior hconv hne
    have h2 : interior (levPair v ℓ '' Submission.PBox s c σ)
        = levPair v ℓ '' Submission.PBox s c σ := hopen.interior_eq
    rw [boxShadow_eq_closure_image, h1, h2]

end

end Work.Drive.Mono.FiberModel
