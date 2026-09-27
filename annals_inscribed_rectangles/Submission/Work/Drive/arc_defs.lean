import Mathlib
import Submission.Work.Drive.Surf.Model
import Submission.Work.Surf.chordFamily

/-!
# Arcs of the disk: the general `1`-chains of the disk model of `ℝP²`

`Work.Drive.IsChord` (`Submission/Work/Drive/Surf/Model.lean`) models the *lifts of essential loops*
of the disk model of `ℝP²`: arcs from `z` to the antipodal point `-z`.  A general `1`-chain
transverse to the projective line lifts instead to a finite system of arcs with *arbitrary* endpoints
on the circle, and the mod-2 intersection of two such systems is computed from the *interlacing*
pattern of the endpoints (`Work.Drive.chordMeet` counts the crossings).

This file provides the vocabulary for that general case:

* `Work.Drive.IsArc a` — `a` is a `C¹` arc with both endpoints on the unit circle and its interior in
  the disk (the endpoints may be any two distinct circle points);
* `Work.Drive.straightArc z w` — the straight segment from `z` to `w`, the "straightened" model arc;
* `Work.Drive.straightArc_isArc` — a straight segment between two distinct circle points is an arc
  (strict convexity of the disk, `Work.Surf.eq_of_combo_norm_eq_one`).

The base case of the general `(SURF)` is then: two arcs cross oddly exactly when their endpoints
interlace — which for straight arcs is the statement that the two segments meet in the interior.
-/

namespace Work.Drive

open scoped Manifold ContDiff Topology

noncomputable section

/-- **An arc of the disk model**: a `C¹` arc with its two endpoints on the unit circle and its
interior in the disk.  These are the lifts of the `1`-chains of `ℝP²` transverse to the projective
line (`Work.Drive.IsChord` is the special case of *antipodal* endpoints, i.e. the lifts of essential
loops). -/
def IsArc (a : ℝ → EuclideanSpace ℝ (Fin 2)) : Prop :=
  ContDiff ℝ 1 a ∧ a 0 ∈ unitCircle ∧ a 1 ∈ unitCircle ∧
    ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) 1 → a t ∈ unitDisk

lemma IsArc.contDiff {a : ℝ → EuclideanSpace ℝ (Fin 2)} (h : IsArc a) : ContDiff ℝ 1 a := h.1

lemma IsArc.start {a : ℝ → EuclideanSpace ℝ (Fin 2)} (h : IsArc a) : a 0 ∈ unitCircle := h.2.1

lemma IsArc.end {a : ℝ → EuclideanSpace ℝ (Fin 2)} (h : IsArc a) : a 1 ∈ unitCircle := h.2.2.1

lemma IsArc.inside {a : ℝ → EuclideanSpace ℝ (Fin 2)} (h : IsArc a) :
    ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) 1 → a t ∈ unitDisk := h.2.2.2

/-- The **straight arc** from `z` to `w`: the affine segment, parametrised on `[0,1]`. -/
def straightArc (z w : EuclideanSpace ℝ (Fin 2)) : ℝ → EuclideanSpace ℝ (Fin 2) :=
  fun t => (1 - t) • z + t • w

@[simp] lemma straightArc_zero (z w : EuclideanSpace ℝ (Fin 2)) : straightArc z w 0 = z := by
  simp [straightArc]

@[simp] lemma straightArc_one (z w : EuclideanSpace ℝ (Fin 2)) : straightArc z w 1 = w := by
  simp [straightArc]

@[simp] lemma straightArc_apply (z w : EuclideanSpace ℝ (Fin 2)) (t : ℝ) :
    straightArc z w t = (1 - t) • z + t • w := rfl

lemma contDiff_straightArc (z w : EuclideanSpace ℝ (Fin 2)) :
    ContDiff ℝ 1 (straightArc z w) := by
  unfold straightArc
  fun_prop

/-- A point of the straight arc between two points of the closed unit disk lies in the closed unit
disk. -/
lemma straightArc_mem_unitDisk {z w : EuclideanSpace ℝ (Fin 2)} (hz : z ∈ unitDisk)
    (hw : w ∈ unitDisk) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) : straightArc z w t ∈ unitDisk := by
  have hz' : ‖z‖ ≤ 1 := hz
  have hw' : ‖w‖ ≤ 1 := hw
  have ht0 : 0 ≤ t := ht.1
  have ht1 : t ≤ 1 := ht.2
  rw [straightArc, unitDisk, Set.mem_ofPred_eq]
  have h1 : ‖(1 - t) • z‖ = (1 - t) * ‖z‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  have h2 : ‖t • w‖ = t * ‖w‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
  calc ‖(1 - t) • z + t • w‖ ≤ ‖(1 - t) • z‖ + ‖t • w‖ := norm_add_le _ _
    _ = (1 - t) * ‖z‖ + t * ‖w‖ := by rw [h1, h2]
    _ ≤ 1 := by nlinarith

/-- **A straight segment between two distinct points of the unit circle is an arc of the disk
model.**  Its interior is strictly inside the disk by the strict convexity of the disk: a convex
combination with strictly positive weights of two unit vectors of norm `1` has norm `< 1`
(`Work.Surf.eq_of_combo_norm_eq_one`). -/
lemma straightArc_isArc {z w : EuclideanSpace ℝ (Fin 2)} (hz : z ∈ unitCircle)
    (hw : w ∈ unitCircle) (hne : z ≠ w) : IsArc (straightArc z w) := by
  have hz1 : ‖z‖ = 1 := hz
  have hw1 : ‖w‖ = 1 := hw
  refine ⟨contDiff_straightArc z w, ?_, ?_, ?_⟩
  · simpa only [straightArc_zero] using hz
  · simpa only [straightArc_one] using hw
  · intro t ht
    have hmem : straightArc z w t ∈ unitDisk :=
      straightArc_mem_unitDisk (show z ∈ unitDisk from le_of_eq hz1)
        (show w ∈ unitDisk from le_of_eq hw1) ⟨ht.1.le, ht.2.le⟩
    have hmem' : ‖straightArc z w t‖ ≤ 1 := hmem
    suffices h : ‖straightArc z w t‖ < 1 from le_of_lt h
    refine lt_of_le_of_ne hmem' (fun hcon => ?_)
    have heq : z = w :=
      Work.Surf.eq_of_combo_norm_eq_one ht.1 ht.2 (le_of_eq hz1) (le_of_eq hw1)
        (straightArc_apply z w t).symm hcon
    exact hne heq

/-! ## Systems of arcs, and the interlacing of two arcs -/

/-- A **`σ`-invariant system of arcs**: a family of arcs of the disk closed under the antipodal map
through an involution `ac` of the index set.  The arcs fixed by `ac` are the *chords* (their endpoints
are antipodal, so the antipodal image of the arc is the same arc, traversed backwards); the others
come in antipodal pairs and represent the trivial loops.  This is the disk-model presentation of a
`1`-chain of `ℝP²`. -/
def IsArcSystem {ι : Type*} (A : ι → ℝ → EuclideanSpace ℝ (Fin 2)) (ac : ι → ι) : Prop :=
  Function.Involutive ac ∧
    (∀ i, ac i ≠ i → A (ac i) = fun t => - A i t) ∧
    (∀ i, ac i = i → A i 1 = - A i 0) ∧
    (∀ i, IsArc (A i))

/-- **The straightened arcs interlace**: the straight segments from the endpoints of `a` and of `b`
meet in exactly one point, with both parameters interior.  In the disk model this is the criterion
which decides the parity of the number of interior crossings of the two arcs (the two parity lemmas
`Work.Surf.odd_ncard_chordMeet_of_interlacing` and
`Work.Surf.even_ncard_chordMeet_of_not_interlacing`). -/
def Interlaces (a b : ℝ → EuclideanSpace ℝ (Fin 2)) : Prop :=
  ∃! p : ℝ × ℝ, p.1 ∈ Set.Ioo (0 : ℝ) 1 ∧ p.2 ∈ Set.Ioo (0 : ℝ) 1 ∧
    straightArc (a 0) (a 1) p.1 = straightArc (b 0) (b 1) p.2

end

end Work.Drive
