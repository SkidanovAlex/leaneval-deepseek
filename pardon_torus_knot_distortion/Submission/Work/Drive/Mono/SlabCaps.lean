import Mathlib
import Submission.Work.Topology.SphereSlicing.frontier_PBox
import Submission.Work.Drive.EpsFormSphere.encard_frontier_tiltedSweptBall_lt_min

/-!
# The two caps of Pardon's box cut by the tilted slab

The definitions and the elementary frontier facts about the two **caps** into which the tilted slab
cuts Pardon's box.  They live in this *low* module (below the deliverable's file) so that lemmas
about them can be proved in modules below the deliverable and *used* in its proof:
`Submission/Work/Drive/Mono/frontier_PBox_sdiff_slab_eq_caps.lean` (the frontier of the box minus
the slab is the union of the two cap frontiers) and
`Submission/Work/Drive/Mono/isEmbeddedSphere_frontier_slabCaps.lean` (each cap frontier is an
embedded sphere) both import this module only.

* `slabCapPlus s c σ a h v = PBox s c σ ∩ {a + h ≤ ⟪v,·⟫}`, `slabCapMinus` the mirror;
* `SlabCutsBox` — both caps are nonempty (strictly beyond the two faces);
* `facePlanePlus`, `facePlaneMinus` — the two faces of the slab;
* `disjoint_frontier_slabCaps` — the two cap frontiers are disjoint (`0 < h`);
* `frontier_sdiff_slab_subset_sphereSet_union_faces` — the frontier of the box minus the slab is
  contained in the box sphere together with the two faces.
-/

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped RealInnerProductSpace

noncomputable section

/-- The **upper cap** of the box cut by the tilted slab. -/
def slabCapPlus (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (a h : ℝ) (v : R3) : Set R3 :=
  {y : R3 | y ∈ Submission.PBox s c σ ∧ a + h ≤ inner ℝ v y}

/-- The **lower cap** of the box cut by the tilted slab. -/
def slabCapMinus (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (a h : ℝ) (v : R3) : Set R3 :=
  {y : R3 | y ∈ Submission.PBox s c σ ∧ inner ℝ v y ≤ a - h}


/-- **The slab cuts the box**: both caps of the box cut by the slab are nonempty (strictly, in the
direction of the slab's normal). -/
def SlabCutsBox (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (a h : ℝ) (v : R3) : Prop :=
  (∃ y : R3, y ∈ Submission.PBox s c σ ∧ a + h < inner ℝ v y) ∧
    (∃ y : R3, y ∈ Submission.PBox s c σ ∧ inner ℝ v y < a - h)

/-- The **upper face** of the tilted slab: the plane `{⟪v,·⟫ = ⟪v,c⟫ + u + h}`. -/
def facePlanePlus (c : R3) (u h : ℝ) (v : R3) : Set R3 :=
  {y : R3 | inner ℝ v y = inner ℝ v c + u + h}

/-- The **lower face** of the tilted slab: the plane `{⟪v,·⟫ = ⟪v,c⟫ + u - h}`. -/
def facePlaneMinus (c : R3) (u h : ℝ) (v : R3) : Set R3 :=
  {y : R3 | inner ℝ v y = inner ℝ v c + u - h}

/-- **The frontier of the box minus the slab is contained in the box sphere together with the two
faces.** -/
theorem frontier_sdiff_slab_subset_sphereSet_union_faces {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u h : ℝ} {v : R3} (hs : 0 < s) (hh : 0 < h) :
    frontier (Submission.PBox s c σ \
        Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h) ⊆
      Work.BoxShrink.Core.sphereSet c σ s ∪ facePlanePlus c u h v ∪ facePlaneMinus c u h v := by
  have hfrPBox : frontier (Submission.PBox s c σ) = Work.BoxShrink.Core.sphereSet c σ s := by
    rw [Work.Topology.SphereSlicing.frontier_PBox hs c σ,
      Work.BoxShrink.Core.sphereSet_eq_BoxSphere]
  intro y hy
  rcases Work.Drive.EpsFormSphere.frontier_sdiff_subset (Submission.PBox s c σ)
      (Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h) hy with hb | hs'
  · exact Or.inl (Or.inl (by rw [← hfrPBox]; exact hb))
  · have h2 : |inner ℝ v y - (inner ℝ v c + u)| = h :=
      Work.Drive.EpsFormSphere.frontier_tiltedSlabClosed_subset (inner ℝ v c + u) v h hs'
    rcases (abs_eq (le_of_lt hh)).mp h2 with h3 | h3
    · refine Or.inl (Or.inr ?_)
      show inner ℝ v y = inner ℝ v c + u + h
      linarith
    · refine Or.inr ?_
      show inner ℝ v y = inner ℝ v c + u - h
      linarith

/-- **The frontiers of the two caps are disjoint** (for `0 < h`): the frontier of a cap is
contained in the closed half-space defining it. -/
theorem disjoint_frontier_slabCaps {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {a h : ℝ} {v : R3}
    (hh : 0 < h) :
    Disjoint (frontier (slabCapPlus s c σ a h v)) (frontier (slabCapMinus s c σ a h v)) := by
  rw [Set.disjoint_left]
  intro y hy hy'
  have hcl : Continuous fun z : R3 => inner ℝ v z := continuous_const.inner continuous_id
  have h1 : a + h ≤ inner ℝ v y := by
    have hsub : frontier (slabCapPlus s c σ a h v) ⊆ {z : R3 | a + h ≤ inner ℝ v z} :=
      subset_trans frontier_subset_closure
        (closure_minimal (fun z hz => hz.2) (isClosed_le continuous_const hcl))
    exact hsub hy
  have h2 : inner ℝ v y ≤ a - h := by
    have hsub : frontier (slabCapMinus s c σ a h v) ⊆ {z : R3 | inner ℝ v z ≤ a - h} :=
      subset_trans frontier_subset_closure
        (closure_minimal (fun z hz => hz.2) (isClosed_le hcl continuous_const))
    exact hsub hy'
  linarith


end

end Work.Drive.Mono
