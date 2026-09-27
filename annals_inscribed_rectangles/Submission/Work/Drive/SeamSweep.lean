import Mathlib
import Submission.Work.Drive.SeamMeetDefs
import Submission.Work.Drive.scaleSweep

/-!
# The sweep of a seam-invariant plane is seam-invariant

`Submission/Work/Drive/SeamMeetDefs.lean` fixes the vocabulary of the *seam* faces of the three
parameter cubes of the triple-intersection parity, and `Work.Drive.manifold_triple_seam_cancel` (the
delegated lemma) shows that the seam contributions cancel whenever each chain is invariant under the
antipodal involution `seamInv` on the seam.  This file supplies that invariance for the chains the
chain route actually uses: the **sweeps** of planes.

A plane of the capped family is presented by a map `P : ℝ² → CappingSpace` from the parameter square
(the disk presentation `Work.Drive.diskPt` of
`Submission/Work/Drive/cappedPlaneCharts.lean`, composed with a square-to-disk map), and the seam
identification is exactly the antipodal identification of the square's boundary, so that
`P y = P (seamInv₂ y)` for `y` on the boundary of the square
(`Work.Drive.cappedPlane_diskPresentation`: two disk points have the same image iff they are equal or
antipodal on the boundary circle).  The sweep `Work.Drive.sweepChain a ha P` of such a `P` then also
satisfies the seam invariance, because the sweep parameter depends only on the third coordinate.
-/

namespace Work.Drive

open scoped Topology

noncomputable section

/-- The antipodal involution of the parameter square: `(y 0, y 1) ↦ (1 - y 0, 1 - y 1)`. -/
def seamInv2 (y : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  mk2 (1 - y 0) (1 - y 1)

@[simp] lemma seamInv2_apply_zero (y : EuclideanSpace ℝ (Fin 2)) : seamInv2 y 0 = 1 - y 0 := by
  simp [seamInv2]

@[simp] lemma seamInv2_apply_one (y : EuclideanSpace ℝ (Fin 2)) : seamInv2 y 1 = 1 - y 1 := by
  simp [seamInv2]

/-- A point of the parameter square lies on its boundary. -/
def onSeam2 (y : EuclideanSpace ℝ (Fin 2)) : Prop :=
  y 0 = 0 ∨ y 0 = 1 ∨ y 1 = 0 ∨ y 1 = 1

lemma onSeam2_of_onSeam (x : EuclideanSpace ℝ (Fin 3)) (h : onSeam x) :
    onSeam2 (mk2 (x 0) (x 1)) := h

lemma mk2_seamInv (x : EuclideanSpace ℝ (Fin 3)) :
    mk2 ((seamInv x) 0) ((seamInv x) 1) = seamInv2 (mk2 (x 0) (x 1)) := by
  ext i
  fin_cases i <;> simp [seamInv, seamInv2]

/-- **The sweep of a seam-invariant plane is seam-invariant.**  If the `2`-chain `P` presenting the
plane agrees with itself under the antipodal involution of the parameter square on the boundary of the
square (the disk presentation of the capped plane, whose boundary circle is identified antipodally with
the cut of the surface), then the sweep `Work.Drive.sweepChain a ha P` agrees with itself under the
corresponding involution `Work.Drive.seamInv` of the three cube parameters — because the sweep
parameter depends only on the third coordinate.  This is the hypothesis `hseam` of
`Work.Drive.manifold_triple_seam_cancel`. -/
theorem sweepChain_seamInv (a : ℝ) (ha : 0 < a) (P : EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (hP : ∀ y : EuclideanSpace ℝ (Fin 2), onSeam2 y → P y = P (seamInv2 y))
    (x : EuclideanSpace ℝ (Fin 3)) (hx : onSeam x) :
    sweepChain a ha P x = sweepChain a ha P (seamInv x) := by
  have hp : sweepParam a (seamInv x) = sweepParam a x := by
    refine Subtype.ext ?_
    rw [sweepParam_val, sweepParam_val, seamInv_apply_two]
  rw [sweepChain_apply, sweepChain_apply, hp, mk2_seamInv]
  exact congrArg (scaleCapping (sweepParam a x)) (hP (mk2 (x 0) (x 1)) (onSeam2_of_onSeam x hx))

/-- The same statement in the form of the `hseam` hypothesis of
`Work.Drive.manifold_triple_seam_cancel`, for a triple of planes presented by seam-invariant box
maps: every chain of the triple is seam-invariant. -/
theorem triple_seamInv_of_plane_seamInv
    (a : Fin 3 → ℝ) (ha : ∀ k, 0 < a k)
    (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (hP : ∀ k, ∀ y : EuclideanSpace ℝ (Fin 2), onSeam2 y → P k y = P k (seamInv2 y)) :
    ∀ (k : Fin 3) (x : EuclideanSpace ℝ (Fin 3)), onSeam x →
      sweepChain (a k) (ha k) (P k) x = sweepChain (a k) (ha k) (P k) (seamInv x) :=
  fun k x hx => sweepChain_seamInv (a k) (ha k) (P k) (hP k) x hx

end

end Work.Drive
