import Mathlib
import Submission.Work.ThomBordism.RelDuality.interiorPushDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The collar family of a compact manifold with boundary

This file sets up the family of maps which is used to build a collar of a compact `C¹`
`9`-manifold with boundary, out of the local inward pushes of
`Submission/Work/ThomBordism/RelDuality/interiorPushDefs.lean` (`PushDatum`, `localMap`).

* `Work.ThomBordism.RelDuality.bnd` — the boundary of `M`;
* `Work.ThomBordism.RelDuality.fam` — the composite of the local pushes of a list of push data,
  all with the *same* time parameter `t`;
* `fam_zero`, `fam_continuous`, `fam_interior` — the basic API;
* `CoversBnd` — the hypothesis that the regions of the data cover the boundary (this is what makes
  the family push *strictly* inwards at every boundary point).
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

open scoped Topology Manifold
open Function Set

namespace Work.ThomBordism.RelDuality

noncomputable section

variable {M : Type} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanHalfSpace 9) M]

/-- The boundary of the `9`-manifold with boundary `M`. -/
abbrev bnd (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 9) M] : Set M :=
  (modelWithCornersEuclideanHalfSpace 9).boundary M

/-- The composite of the local pushes of a list of push data, all with the same time parameter
`t`.  (The list is applied left to right: the first datum of the list is the innermost push.) -/
def fam (L : List (PushDatum M)) (t : ℝ) (y : M) : M :=
  L.foldl (fun z D => D.localMap t z) y

@[simp] theorem fam_nil (t : ℝ) (y : M) : fam ([] : List (PushDatum M)) t y = y := rfl

theorem fam_cons (D : PushDatum M) (L : List (PushDatum M)) (t : ℝ) (y : M) :
    fam (D :: L) t y = fam L t (D.localMap t y) := by
  simp [fam, List.foldl_cons]

/-- The family at time `0` is the identity (every local push is the identity at `t = 0`). -/
theorem fam_zero (L : List (PushDatum M)) (y : M) : fam L 0 y = y := by
  induction L generalizing y with
  | nil => rfl
  | cons D L ih =>
      rw [fam_cons, D.localMap_zero]
      exact ih y

/-- The family is jointly continuous in the point and the time. -/
theorem fam_continuous (L : List (PushDatum M)) :
    Continuous fun p : M × ℝ => fam L p.2 p.1 := by
  induction L with
  | nil => simpa [fam] using continuous_fst
  | cons D L ih =>
      have h : (fun p : M × ℝ => fam (D :: L) p.2 p.1)
          = fun p : M × ℝ => fam L p.2 (D.localMap p.2 p.1) := by
        funext p
        rw [fam_cons]
      rw [h]
      exact ih.comp (D.continuous_localMap_uncurry.prodMk continuous_snd)

/-- **The family preserves the interior.** -/
theorem fam_interior [IsManifold (modelWithCornersEuclideanHalfSpace 9) 1 M]
    (L : List (PushDatum M)) {y : M} (hy : (modelWithCornersEuclideanHalfSpace 9).IsInteriorPoint y)
    (t : ℝ) : (modelWithCornersEuclideanHalfSpace 9).IsInteriorPoint (fam L t y) := by
  induction L generalizing y with
  | nil => exact hy
  | cons D L ih =>
      rw [fam_cons]
      exact ih (D.isInteriorPoint_localMap_of_isInteriorPoint hy t)

/-- **The regions of the data cover the boundary.** -/
def CoversBnd (L : List (PushDatum M)) : Prop :=
  ∀ y : M, y ∈ bnd M → ∃ D ∈ L, y ∈ D.region

/-- **The family pushes every boundary point covered by a datum strictly into the interior**, at
every positive time. -/
theorem fam_isInteriorPoint_of_mem_bnd
    [IsManifold (modelWithCornersEuclideanHalfSpace 9) 1 M]
    (L : List (PushDatum M)) {y : M} (hL : ∃ D ∈ L, y ∈ D.region) {t : ℝ} (ht0 : 0 < t) :
    (modelWithCornersEuclideanHalfSpace 9).IsInteriorPoint (fam L t y) := by
  induction L generalizing y with
  | nil => simp at hL
  | cons D L ih =>
      rw [fam_cons]
      by_cases hreg : y ∈ D.region
      · exact fam_interior L (D.isInteriorPoint_localMap hreg ht0) t
      · rw [D.localMap_eq_self_of_not_mem hreg t]
        refine ih ?_
        obtain ⟨D', hD', hy'⟩ := hL
        rcases List.mem_cons.mp hD' with rfl | hmem
        · exact absurd hy' hreg
        · exact ⟨D', hmem, hy'⟩

end

end Work.ThomBordism.RelDuality
