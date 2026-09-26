import Mathlib
import Submission.Work.Drive.Mono.TiltedTraceData
import Submission.Work.Drive.Mono.SlabCaps
import Submission.Work.Drive.EpsForm.sweepThrough
import Submission.Work.Drive.Mono.FrontierCorner_holds
import Submission.Work.Drive.Mono.exists_mem_PBox_abs_inner_gt_near
import Submission.Work.Drive.Mono.exists_mem_PBox_gt_level_near
import Submission.Work.Drive.Mono.frontier_eq_caps_of_closure_interior

/-!
# The frontier of a level of the tilted sweep, as a union of caps

`Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam` is Pardon's open box with the closed tilted
slab `{|⟪v,·⟫ - (⟪v,c⟫ + u)| ≤ h}` cut away on the side `{ℓ < lam}`.  This module computes its
frontier exactly, under the two "poking" hypotheses

* `hcut : SlabCutsBox s c σ (⟪v,c⟫+u) h v` — the box pokes out of the slab on **both** sides, and
* `habove : ∃ y ∈ PBox s c σ, lam < ℓ y` — the box pokes strictly **above** the level.

Both are necessary (`_cex_ftlrec.lean` refutes the identity without `hcut`,
`_ftlrec_hcut_cex.lean` refutes it without `habove`).  With them the frontier is

`(∂B \ (B ∩ S ∩ T)) ∪ ((B ∩ S ∩ T) ∩ (∂S ∪ ∂T))`

where `B = closure (PBox s c σ)`, `S = {|⟪v,·⟫ - (⟪v,c⟫+u)| ≤ h}` and `T = {ℓ ≤ lam}`.

The proof has three elementary parts, all of them point-set:

1. `closure R = B \ (S° ∩ T°)` where `S° = {|⟪v,·⟫-a| < h}` and `T° = {ℓ < lam}`.  The inclusion
   `⊆` is immediate; for `⊇` one must produce, near a point `z ∈ B` which is *not* in `S° ∩ T°`,
   points of the open box outside the removed region.  If `z` is off the slab in the strict sense
   (or strictly above the level) continuity gives them; on the slab faces (`h ≤ |⟪v,z⟫-a|` with
   equality) one uses `hcut` and the convexity of the box, and on the level (`ℓ z = lam`, `z ∈ S°`)
   one uses `habove` and convexity again: if a whole neighbourhood of `z` in the box were removed,
   then by convexity the whole box would be removed, contradicting `hcut`/`habove`.
2. `interior R = PBox \ (S ∩ T)`, which is `interior (P \ G) = P \ closure G` for the open box `P`
   and `closure (S ∩ T°) = S ∩ T` (`closure_closedSlab_inter`, where `ℓ v = 0` and `ℓ ≠ 0` make `ℓ`
   non-parallel to `⟪v,·⟫`).
3. The resulting pure set identity (`frontier_eq_caps_of_closure_interior`).

The two approximation lemmas of step 1 are the delegated modules
`Work.Drive.Mono.exists_mem_PBox_abs_inner_gt_near` and
`Work.Drive.Mono.exists_mem_PBox_gt_level_near`, and step 3 is the delegated module
`Work.Drive.Mono.frontier_eq_caps_of_closure_interior` (all three proved in this directory).
-/

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion MeasureTheory Set
open scoped ENNReal

noncomputable section

/-! ## Elementary helpers -/

/-- `ℓ` is not a multiple of `⟪v,·⟫` when `ℓ ≠ 0`, `ℓ v = 0` and `v ≠ 0`. -/
private lemma ne_smul_innerSL {v : R3} {ℓ : R3 →L[ℝ] ℝ} (hv : v ≠ 0) (hℓ : ℓ ≠ 0)
    (hℓv : ℓ v = 0) : ∀ t : ℝ, ℓ ≠ t • (innerSL ℝ) v := by
  intro t ht
  have h1 : (t • (innerSL ℝ) v) v = 0 := by rw [← ht]; exact hℓv
  rw [smul_apply, innerSL_apply_apply, real_inner_self_eq_norm_sq, smul_eq_mul] at h1
  have h2 : t = 0 := by
    rcases mul_eq_zero.mp h1 with h | h
    · exact h
    · exact absurd h (pow_ne_zero 2 (norm_ne_zero_iff.mpr hv))
  rw [ht, h2, zero_smul] at hℓ
  exact hℓ rfl

/-- The function `y ↦ |⟪v,y⟫ - a|` is continuous. -/
private lemma continuous_abs_inner_sub (v : R3) (a : ℝ) :
    Continuous fun y : R3 => |inner ℝ v y - a| :=
  continuous_abs.comp (((continuous_const : Continuous fun _ : R3 => v).inner continuous_id).sub
    (continuous_const : Continuous fun _ : R3 => a))

private lemma isOpen_abs_inner_lt (v : R3) (a h : ℝ) :
    IsOpen {y : R3 | |inner ℝ v y - a| < h} :=
  isOpen_lt (continuous_abs_inner_sub v a) (continuous_const : Continuous fun _ : R3 => h)

private lemma isOpen_abs_inner_gt (v : R3) (a h : ℝ) :
    IsOpen {y : R3 | h < |inner ℝ v y - a|} :=
  isOpen_lt (continuous_const : Continuous fun _ : R3 => h) (continuous_abs_inner_sub v a)

private lemma isOpen_level_lt (ℓ : R3 →L[ℝ] ℝ) (lam : ℝ) : IsOpen {y : R3 | ℓ y < lam} :=
  isOpen_lt ℓ.continuous (continuous_const : Continuous fun _ : R3 => lam)

private lemma isOpen_level_gt (ℓ : R3 →L[ℝ] ℝ) (lam : ℝ) : IsOpen {y : R3 | lam < ℓ y} :=
  isOpen_lt (continuous_const : Continuous fun _ : R3 => lam) ℓ.continuous

/-- The slab face is the slab minus the open slab. -/
private lemma slab_sdiff_openSlab (a h : ℝ) (v : R3) :
    ({y : R3 | |inner ℝ v y - a| = h} : Set R3) =
      {y : R3 | |inner ℝ v y - a| ≤ h} \ {y : R3 | |inner ℝ v y - a| < h} := by
  ext y
  rw [Set.mem_sdiff]
  simp only [Set.mem_ofPred_eq]
  constructor
  · intro hy
    exact ⟨le_of_eq hy, by rw [hy]; exact lt_irrefl h⟩
  · rintro ⟨h1, h2⟩
    exact le_antisymm h1 (not_lt.mp h2)

/-- The level wall is the closed level set minus the open level set. -/
private lemma level_sdiff (ℓ : R3 →L[ℝ] ℝ) (lam : ℝ) :
    ({y : R3 | ℓ y = lam} : Set R3) =
      {y : R3 | ℓ y ≤ lam} \ {y : R3 | ℓ y < lam} := by
  ext y
  rw [Set.mem_sdiff]
  simp only [Set.mem_ofPred_eq]
  constructor
  · intro hy
    exact ⟨le_of_eq hy, by rw [hy]; exact lt_irrefl lam⟩
  · rintro ⟨h1, h2⟩
    exact le_antisymm h1 (not_lt.mp h2)

/-- The interior of the closure of the box is the box itself (the box is open, convex and
nonempty). -/
private lemma interior_closure_PBox {s : ℝ} (hs : 0 < s) (c : R3) (σ : Equiv.Perm (Fin 3)) :
    interior (closure (Submission.PBox s c σ)) = Submission.PBox s c σ := by
  have hcv : Convex ℝ (Submission.PBox s c σ) := Work.Topology.SphereSlicing.convex_PBox s c σ
  have hopen : IsOpen (Submission.PBox s c σ) := Work.Topology.SphereSlicing.isOpen_PBox s c σ
  have hc : c ∈ interior (Submission.PBox s c σ) := by
    rw [hopen.interior_eq, Submission.mem_PBox]
    intro i
    rw [sub_self, abs_zero]
    exact mul_pos (Submission.boxSide_pos i) hs
  rw [hcv.interior_closure_eq_interior_of_nonempty_interior ⟨c, hc⟩, hopen.interior_eq]

/-- The frontier of the closed box is the closed box minus the box. -/
private lemma frontier_closure_PBox {s : ℝ} (hs : 0 < s) (c : R3) (σ : Equiv.Perm (Fin 3)) :
    frontier (closure (Submission.PBox s c σ)) =
      closure (Submission.PBox s c σ) \ Submission.PBox s c σ := by
  rw [frontier, closure_closure, interior_closure_PBox hs c σ]

/-! ## The closure and the interior of a level of the tilted sweep -/

/-- **The closure of the removed set of a level.** -/
theorem closure_tiltedLevelRemoved (s u h lam : ℝ) (c v : R3) (σ : Equiv.Perm (Fin 3))
    (ℓ : R3 →L[ℝ] ℝ)
    (hcut : SlabCutsBox s c σ (inner ℝ v c + u) h v)
    (habove : ∃ y : R3, y ∈ Submission.PBox s c σ ∧ lam < ℓ y) :
    closure (tiltedLevelRemoved s c σ u v h ℓ lam) =
      closure (Submission.PBox s c σ) \
        ({y : R3 | |inner ℝ v y - (inner ℝ v c + u)| < h} ∩ {y : R3 | ℓ y < lam}) := by
  set S' : Set R3 := {y : R3 | |inner ℝ v y - (inner ℝ v c + u)| < h} with hS'
  set T' : Set R3 := {y : R3 | ℓ y < lam} with hT'
  have hopen : IsOpen (S' ∩ T') := by
    rw [hS', hT']
    exact (isOpen_abs_inner_lt v (inner ℝ v c + u) h).inter (isOpen_level_lt ℓ lam)
  have hsub : tiltedLevelRemoved s c σ u v h ℓ lam ⊆ (S' ∩ T')ᶜ := by
    intro w hw
    rw [Set.mem_compl_iff]
    rintro ⟨hw1, hw2⟩
    rw [hS'] at hw1
    rw [hT'] at hw2
    have hw1' : |inner ℝ v w - (inner ℝ v c + u)| < h := hw1
    have hw2' : ℓ w < lam := hw2
    rw [tiltedLevelRemoved, Set.mem_sdiff] at hw
    exact hw.2 ⟨le_of_lt hw1', hw2'⟩
  refine Subset.antisymm ?_ ?_
  · intro z hz
    refine ⟨?_, ?_⟩
    · have hle : tiltedLevelRemoved s c σ u v h ℓ lam ⊆ Submission.PBox s c σ := by
        intro w hw
        rw [tiltedLevelRemoved, Set.mem_sdiff] at hw
        exact hw.1
      exact closure_mono hle hz
    · exact closure_minimal hsub hopen.isClosed_compl hz
  · intro z hz
    obtain ⟨hzB, hznot⟩ := hz
    rw [Metric.mem_closure_iff]
    intro ε hε
    by_cases hS : |inner ℝ v z - (inner ℝ v c + u)| < h
    · have hzlam : lam ≤ ℓ z := by
        by_contra hcon
        push_neg at hcon
        exact hznot ⟨by rw [hS']; exact hS, by rw [hT']; exact hcon⟩
      rcases lt_or_eq_of_le hzlam with hlt | heq
      · obtain ⟨δ, hδpos, hδ⟩ := Metric.isOpen_iff.mp (isOpen_level_gt ℓ lam) z hlt
        obtain ⟨w, hwP, hwd⟩ := Metric.mem_closure_iff.mp hzB (min δ ε) (lt_min hδpos hε)
        have hball : dist w z < min δ ε := by rw [dist_comm]; exact hwd
        refine ⟨w, ⟨hwP, ?_⟩, lt_of_lt_of_le hwd (min_le_right _ _)⟩
        rintro ⟨-, hwT'⟩
        have hwT'' : ℓ w < lam := hwT'
        exact absurd (hδ (Metric.mem_ball.mpr (lt_of_lt_of_le hball (min_le_left _ _))))
          (not_lt.mpr (le_of_lt hwT''))
      · obtain ⟨w, hwP, hwd, hwgt⟩ :=
          exists_mem_PBox_gt_level_near habove hzB (le_of_eq heq) hε
        have hzw : dist z w < ε := by rw [dist_comm]; exact hwd
        refine ⟨w, ⟨hwP, ?_⟩, hzw⟩
        rintro ⟨-, hwT'⟩
        have hwT'' : ℓ w < lam := hwT'
        exact absurd hwgt (not_lt.mpr (le_of_lt hwT''))
    · push_neg at hS
      rcases lt_or_eq_of_le hS with hlt | heq
      · obtain ⟨δ, hδpos, hδ⟩ :=
          Metric.isOpen_iff.mp (isOpen_abs_inner_gt v (inner ℝ v c + u) h) z hlt
        obtain ⟨w, hwP, hwd⟩ := Metric.mem_closure_iff.mp hzB (min δ ε) (lt_min hδpos hε)
        have hball : dist w z < min δ ε := by rw [dist_comm]; exact hwd
        refine ⟨w, ⟨hwP, ?_⟩, lt_of_lt_of_le hwd (min_le_right _ _)⟩
        rintro ⟨hwS, -⟩
        have hwS' : |inner ℝ v w - (inner ℝ v c + u)| ≤ h := hwS
        exact absurd (hδ (Metric.mem_ball.mpr (lt_of_lt_of_le hball (min_le_left _ _))))
          (not_lt.mpr hwS')
      · obtain ⟨w, hwP, hwd, hwgt⟩ :=
          exists_mem_PBox_abs_inner_gt_near hcut hzB heq.le hε
        have hzw : dist z w < ε := by rw [dist_comm]; exact hwd
        refine ⟨w, ⟨hwP, ?_⟩, hzw⟩
        rintro ⟨hwS, -⟩
        have hwS' : |inner ℝ v w - (inner ℝ v c + u)| ≤ h := hwS
        exact absurd hwgt (not_lt.mpr hwS')

/-- **The interior of the removed set of a level.** -/
theorem interior_tiltedLevelRemoved (s u h lam : ℝ) (c v : R3) (σ : Equiv.Perm (Fin 3))
    (ℓ : R3 →L[ℝ] ℝ) (hv : v ≠ 0) (hℓ : ℓ ≠ 0) (hℓv : ℓ v = 0) :
    interior (tiltedLevelRemoved s c σ u v h ℓ lam) =
      Submission.PBox s c σ \
        ({y : R3 | |inner ℝ v y - (inner ℝ v c + u)| ≤ h} ∩ {y : R3 | ℓ y ≤ lam}) := by
  have hanti := ne_smul_innerSL hv hℓ hℓv
  have hopen : IsOpen (Submission.PBox s c σ) := Work.Topology.SphereSlicing.isOpen_PBox s c σ
  have hcl : closure ({y : R3 | |inner ℝ v y - (inner ℝ v c + u)| ≤ h} ∩ {y : R3 | ℓ y < lam}) =
      {y : R3 | |inner ℝ v y - (inner ℝ v c + u)| ≤ h} ∩ {y : R3 | ℓ y ≤ lam} :=
    closure_closedSlab_inter hv hanti (inner ℝ v c + u) h lam
  rw [tiltedLevelRemoved, Work.Drive.EpsForm.tiltedSlabClosed, Set.sdiff_eq, Set.sdiff_eq,
    interior_inter, hopen.interior_eq, interior_compl, hcl]

/-! ## The target -/

open LeanEval.KnotTheory.PardonDistortion MeasureTheory Set in
open scoped ENNReal Topology in
theorem frontier_tiltedLevelRemoved_eq_caps
    (s u h lam : ℝ) (c v : R3) (σ : Equiv.Perm (Fin 3)) (ℓ : R3 →L[ℝ] ℝ)
    (hs : 0 < s) (hh : 0 < h) (hv : v ≠ 0) (hℓv : ℓ v = 0) (hℓ : ℓ ≠ 0)
    (hcut : Work.Drive.Mono.SlabCutsBox s c σ (inner ℝ v c + u) h v)
    (habove : ∃ y : R3, y ∈ Submission.PBox s c σ ∧ lam < ℓ y) :
    frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam) =
      (frontier (closure (Submission.PBox s c σ)) \
          (closure (Submission.PBox s c σ) ∩
            {y : R3 | |inner ℝ v y - (inner ℝ v c + u)| ≤ h} ∩ {y : R3 | ℓ y ≤ lam}))
      ∪ ((closure (Submission.PBox s c σ) ∩
            {y : R3 | |inner ℝ v y - (inner ℝ v c + u)| ≤ h} ∩ {y : R3 | ℓ y ≤ lam}) ∩
          ({y : R3 | |inner ℝ v y - (inner ℝ v c + u)| = h} ∪ {y : R3 | ℓ y = lam})) := by
  refine frontier_eq_caps_of_closure_interior
    (closure_tiltedLevelRemoved s u h lam c v σ ℓ hcut habove)
    (interior_tiltedLevelRemoved s u h lam c v σ ℓ hv hℓ hℓv) (frontier_closure_PBox hs c σ) rfl
    ?_ ?_ (slab_sdiff_openSlab (inner ℝ v c + u) h v) (level_sdiff ℓ lam)
  · intro x hx
    exact le_of_lt (show |inner ℝ v x - (inner ℝ v c + u)| < h from hx)
  · intro x hx
    exact le_of_lt (show ℓ x < lam from hx)

end

end Work.Drive.Mono
