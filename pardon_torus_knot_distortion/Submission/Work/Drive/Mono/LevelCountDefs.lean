import Mathlib
import Submission.Work.Drive.Mono.TiltedTraceData
import Submission.Work.Drive.Mono.inbox_frontier_subset
import Submission.Work.Drive.EpsForm.encard_inter_sphereSet_lt_min

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion MeasureTheory Set
open scoped ENNReal Topology

noncomputable section

/-!
## Definitions and basic lemmas for the level count of the tilted sweep

The definitions of the level count of `Work.Drive.Mono.ae_levelCount_lt_min`: the three functions
`boxA`, `cutG`, `wallW` of the parameter, the parameter sets `slabVisit` (the visits),
`trenchSet`, `cutCross`, `facePts`, `wallPts`, `inboxPts`, and the visit `visit Y c`.  The lemmas
are the continuity, periodicity, derivative and openness facts used by the level count, the
characterisation `inboxPts ⊆ facePts ∪ wallPts` of the in-box trace parameters, and the periodicity
of the visits.

The hero statement `Work.Drive.Mono.ae_levelCount_lt_min` lives in
`Submission/Work/Drive/Mono/ae_levelCount_lt_min.lean`, which imports this module together with the
delegated visit lemmas; the delegated lemmas import *this* module only, so that the dependency graph
is acyclic.

## The level count at every level of the sweep, from the non-grazing hypotheses

The hypotheses of `Work.Drive.Mono.ae_levelCount_lt_min` are the "no grazing visit" conditions:

* `hboxsph`: on the box sphere the knot is outside the open slab;
* `hgraze`: at a critical point of the sweep height inside the box, the knot is outside the open
  slab;
* `hwall`: inside the box and the closed slab, the level `lam` is a regular value of the wall
  functional along the knot;
* `hface`: at a point of the knot in the box on a slab face, the face is crossed transversally;
* `hcorner`: a point of the knot in the box at a slab face and on the wall belongs to `exc`.

Together they say that the knot's visits to the box-and-slab are never *grazing*: every visit
crosses the cutting plane exactly once, so the number of visits is at most the number of crossings,
and the whole in-box part of the level's trace costs at most twice that number.
-/

/-- The box-norm deviation of the knot, `boxNorm c σ (K.curve t) - s`: negative exactly at the
parameters at which the knot lies in the open box `PBox s c σ`. -/
def boxA (K : Knot) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (t : ℝ) : ℝ :=
  Submission.boxNorm c σ (K.curve t) - s

/-- The tilted cutting height of the knot, `⟪v, K.curve t⟫ - (⟪v, c⟫ + u)`. -/
def cutG (K : Knot) (c : R3) (u : ℝ) (v : R3) (t : ℝ) : ℝ :=
  inner ℝ v (K.curve t) - (inner ℝ v c + u)

/-- The wall functional along the knot, `ℓ (K.curve t)`. -/
def wallW (K : Knot) (ℓ : R3 →L[ℝ] ℝ) (t : ℝ) : ℝ :=
  ℓ (K.curve t)

/-- The **slab visit set**: the knot in the open box and in the *open* tilted slab.  Its connected
components are the *visits* of the knot to the box-and-slab. -/
def slabVisit (K : Knot) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) (v : R3)
    (h : ℝ) : Set ℝ :=
  {t : ℝ | boxA K s c σ t < 0 ∧ |cutG K c u v t| < h}

/-- The **trench parameter set** of the level `lam`: the knot in the open box, in the open tilted
slab, strictly below the level. -/
def trenchSet (K : Knot) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) (v : R3) (h : ℝ)
    (ℓ : R3 →L[ℝ] ℝ) (lam : ℝ) : Set ℝ :=
  {t : ℝ | boxA K s c σ t < 0 ∧ |cutG K c u v t| < h ∧ wallW K ℓ t < lam}

/-- The **crossing parameters** of the cutting plane: the knot in the open box and on the plane
`{⟪v, ·⟫ = ⟪v, c⟫ + u}`. -/
def cutCross (K : Knot) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) (v : R3) : Set ℝ :=
  {t : ℝ | boxA K s c σ t < 0 ∧ cutG K c u v t = 0}

/-- The **face parameters** of the in-box trace: the knot in the open box, on a face of the tilted
slab and strictly below the level. -/
def facePts (K : Knot) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) (v : R3) (h : ℝ)
    (ℓ : R3 →L[ℝ] ℝ) (lam : ℝ) : Set ℝ :=
  {t : ℝ | boxA K s c σ t < 0 ∧ |cutG K c u v t| = h ∧ wallW K ℓ t < lam}

/-- The **wall parameters** of the in-box trace: the knot in the open box, in the open slab and on
the level wall `{ℓ = lam}`. -/
def wallPts (K : Knot) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) (v : R3) (h : ℝ)
    (ℓ : R3 →L[ℝ] ℝ) (lam : ℝ) : Set ℝ :=
  {t : ℝ | boxA K s c σ t < 0 ∧ |cutG K c u v t| < h ∧ wallW K ℓ t = lam}

/-- The **in-box parameters** of the level count: the knot in the open box and on the frontier of the
level's removed set.  This is the part of `#(range K.curve ∩ frontier (tiltedLevelRemoved …))` which
is not on the box sphere. -/
def inboxPts (K : Knot) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) (v : R3) (h : ℝ)
    (ℓ : R3 →L[ℝ] ℝ) (lam : ℝ) : Set ℝ :=
  {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧ K.curve t ∈ Submission.PBox s c σ ∧
    K.curve t ∈ frontier (tiltedLevelRemoved s c σ u v h ℓ lam)}

/-- A **visit** of the knot to a set `Y` of parameters: the connected component of `Y` containing
`c`. -/
def visit (Y : Set ℝ) (c : ℝ) : Set ℝ :=
  connectedComponentIn Y c

section Basic

variable {K : Knot} {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ} {v : R3} {h : ℝ}
variable {ℓ : R3 →L[ℝ] ℝ} {lam : ℝ} {exc : Finset ℝ}

theorem continuous_boxNorm_comp :
    Continuous (fun t : ℝ => Submission.boxNorm c σ (K.curve t)) := by
  have h : Continuous (fun y : R3 => Submission.boxNorm c σ y) := by
    unfold Submission.boxNorm
    fun_prop
  exact h.comp K.smooth.continuous

theorem continuous_boxA : Continuous (boxA K s c σ) := by
  unfold boxA
  exact continuous_boxNorm_comp.sub continuous_const

theorem boxA_lt_zero_iff (t : ℝ) : boxA K s c σ t < 0 ↔ K.curve t ∈ Submission.PBox s c σ := by
  rw [boxA, sub_neg, Submission.mem_PBox_iff]

theorem periodic_boxA (t : ℝ) : boxA K s c σ (t + 2 * Real.pi) = boxA K s c σ t := by
  simp [boxA, K.periodic]

theorem continuous_cutG : Continuous (cutG K c u v) := by
  unfold cutG
  exact (continuous_const.inner K.smooth.continuous).sub continuous_const

theorem contDiff_cutG : ContDiff ℝ (⊤ : ℕ∞) (cutG K c u v) := by
  unfold cutG
  exact ((ContinuousLinearMap.contDiff ((innerSL ℝ) v)).comp K.smooth).sub contDiff_const

theorem periodic_cutG (t : ℝ) : cutG K c u v (t + 2 * Real.pi) = cutG K c u v t := by
  simp [cutG, K.periodic]

theorem deriv_cutG_eq (t : ℝ) :
    deriv (cutG K c u v) t = deriv (fun r : ℝ => inner ℝ v (K.curve r)) t := by
  unfold cutG
  rw [deriv_sub_const]

theorem wallW_apply (t : ℝ) : wallW K ℓ t = ℓ (K.curve t) := rfl

theorem deriv_wallW_eq (t : ℝ) :
    deriv (wallW K ℓ) t = deriv (fun r : ℝ => ℓ (K.curve r)) t := rfl

theorem continuous_wallW : Continuous (wallW K ℓ) :=
  ℓ.continuous.comp K.smooth.continuous

theorem periodic_wallW (t : ℝ) : wallW K ℓ (t + 2 * Real.pi) = wallW K ℓ t := by
  simp [wallW, K.periodic]

theorem isOpen_slabVisit : IsOpen (slabVisit K s c σ u v h) := by
  unfold slabVisit
  exact (isOpen_lt continuous_boxA continuous_const).inter
    (isOpen_lt continuous_cutG.abs continuous_const)

theorem isOpen_trenchSet : IsOpen (trenchSet K s c σ u v h ℓ lam) := by
  unfold trenchSet
  exact (isOpen_lt continuous_boxA continuous_const).inter
    ((isOpen_lt continuous_cutG.abs continuous_const).inter
      (isOpen_lt continuous_wallW continuous_const))

theorem slabVisit_periodic (t : ℝ) :
    (t + 2 * Real.pi ∈ slabVisit K s c σ u v h ↔ t ∈ slabVisit K s c σ u v h) := by
  simp only [slabVisit, Set.mem_ofPred_eq]
  rw [periodic_boxA, periodic_cutG]

theorem trenchSet_eq_raw :
    trenchSet K s c σ u v h ℓ lam =
      {t : ℝ | K.curve t ∈ Submission.PBox s c σ ∧
        |inner ℝ v (K.curve t) - (inner ℝ v c + u)| < h ∧ ℓ (K.curve t) < lam} := by
  ext t
  simp only [trenchSet, Set.mem_ofPred_eq, cutG, wallW]
  rw [boxA_lt_zero_iff]

theorem cutCross_subset_slabVisit (hh : 0 < h) :
    cutCross K s c σ u v ⊆ slabVisit K s c σ u v h := by
  intro t ht
  exact ⟨ht.1, by rw [ht.2, abs_zero]; exact hh⟩

theorem facePts_periodic (t : ℝ) :
    (t + 2 * Real.pi ∈ facePts K s c σ u v h ℓ lam ↔ t ∈ facePts K s c σ u v h ℓ lam) := by
  simp only [facePts, Set.mem_ofPred_eq]
  rw [periodic_boxA, periodic_cutG, periodic_wallW]

theorem wallPts_periodic (t : ℝ) :
    (t + 2 * Real.pi ∈ wallPts K s c σ u v h ℓ lam ↔ t ∈ wallPts K s c σ u v h ℓ lam) := by
  simp only [wallPts, Set.mem_ofPred_eq]
  rw [periodic_boxA, periodic_cutG, periodic_wallW]

theorem cornerPts_periodic (t : ℝ) :
    (t + 2 * Real.pi ∈ facePts K s c σ u v h ℓ lam ∪ wallPts K s c σ u v h ℓ lam ↔
      t ∈ facePts K s c σ u v h ℓ lam ∪ wallPts K s c σ u v h ℓ lam) := by
  rw [Set.mem_union, Set.mem_union, facePts_periodic, wallPts_periodic]


theorem cutCross_periodic (t : ℝ) :
    (t + 2 * Real.pi ∈ cutCross K s c σ u v ↔ t ∈ cutCross K s c σ u v) := by
  simp only [cutCross, Set.mem_ofPred_eq]
  rw [periodic_boxA, periodic_cutG]

/-- **The visits of a periodic set are periodic**: the connected component of `Y` containing
`c + 2π` is the translate by `2π` of the component containing `c`. -/
theorem connectedComponentIn_add_period {Y : Set ℝ}
    (hYper : ∀ t : ℝ, t + 2 * Real.pi ∈ Y ↔ t ∈ Y) {c : ℝ} (hc : c ∈ Y) :
    connectedComponentIn Y (c + 2 * Real.pi) =
      (fun x : ℝ => x + 2 * Real.pi) '' connectedComponentIn Y c := by
  have hYper' : ∀ t : ℝ, t ∈ Y ↔ t - 2 * Real.pi ∈ Y := by
    intro t
    have h := hYper (t - 2 * Real.pi)
    simpa using h
  have hcc : c + 2 * Real.pi ∈ Y := (hYper c).mpr hc
  have h1 : (fun x : ℝ => x + 2 * Real.pi) '' connectedComponentIn Y c ⊆
      connectedComponentIn Y (c + 2 * Real.pi) := by
    refine IsPreconnected.subset_connectedComponentIn ?_ ?_ ?_
    · exact isPreconnected_connectedComponentIn.image _
        (continuous_add_const (2 * Real.pi)).continuousOn
    · exact ⟨c, mem_connectedComponentIn hc, rfl⟩
    · rintro x ⟨y, hy, rfl⟩
      exact (hYper y).mpr (connectedComponentIn_subset Y c hy)
  have h2 : connectedComponentIn Y (c + 2 * Real.pi) ⊆
      (fun x : ℝ => x + 2 * Real.pi) '' connectedComponentIn Y c := by
    have himg : (fun x : ℝ => x - 2 * Real.pi) '' connectedComponentIn Y (c + 2 * Real.pi) ⊆
        connectedComponentIn Y c := by
      refine IsPreconnected.subset_connectedComponentIn ?_ ?_ ?_
      · exact isPreconnected_connectedComponentIn.image _
          (continuous_id.sub continuous_const).continuousOn
      · exact ⟨c + 2 * Real.pi, mem_connectedComponentIn hcc, by ring⟩
      · rintro x ⟨y, hy, rfl⟩
        exact (hYper' y).mp (connectedComponentIn_subset Y (c + 2 * Real.pi) hy)
    rintro x hx
    exact ⟨x - 2 * Real.pi, himg ⟨x, hx, rfl⟩, by ring⟩
  exact le_antisymm h2 h1

theorem deriv_cutG_ne_zero_of_mem_slabVisit
    (hgraze : ∀ t : ℝ, K.curve t ∈ Submission.PBox s c σ →
      deriv (fun r : ℝ => inner ℝ v (K.curve r)) t = 0 → h ≤ |cutG K c u v t|)
    {t : ℝ} (ht : t ∈ slabVisit K s c σ u v h) : deriv (cutG K c u v) t ≠ 0 := fun hzero =>
  absurd (hgraze t ((boxA_lt_zero_iff t).mp ht.1) (by rw [← deriv_cutG_eq]; exact hzero))
    (not_le.mpr ht.2)

theorem deriv_wallW_ne_zero_of_mem_slabVisit
    (hwall : ∀ t : ℝ, K.curve t ∈ Submission.PBox s c σ → |cutG K c u v t| ≤ h →
      deriv (wallW K ℓ) t ≠ 0)
    {t : ℝ} (ht : t ∈ slabVisit K s c σ u v h) : deriv (wallW K ℓ) t ≠ 0 :=
  hwall t ((boxA_lt_zero_iff t).mp ht.1) (le_of_lt ht.2)

theorem slabVisit_ne_univ
    (hgraze : ∀ t : ℝ, K.curve t ∈ Submission.PBox s c σ →
      deriv (fun r : ℝ => inner ℝ v (K.curve r)) t = 0 → h ≤ |cutG K c u v t|) :
    ∃ t : ℝ, t ∉ slabVisit K s c σ u v h := by
  by_contra hcon
  push Not at hcon
  have hderiv : ∀ t : ℝ, deriv (cutG K c u v) t ≠ 0 := fun t =>
    deriv_cutG_ne_zero_of_mem_slabVisit hgraze (hcon t)
  have hdcont : Continuous (deriv (cutG K c u v)) :=
    (contDiff_cutG (K := K) (c := c) (u := u) (v := v)).continuous_deriv (by simp)
  have hsign : (∀ x : ℝ, 0 < deriv (cutG K c u v) x) ∨
      (∀ x : ℝ, deriv (cutG K c u v) x < 0) := by
    by_contra hc
    push Not at hc
    obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := hc
    have hx' : deriv (cutG K c u v) x < 0 := lt_of_le_of_ne hx (hderiv x)
    have hy' : 0 < deriv (cutG K c u v) y := lt_of_le_of_ne hy (Ne.symm (hderiv y))
    rcases le_total x y with hxy | hyx
    · have hmem : (0 : ℝ) ∈ Set.Icc (deriv (cutG K c u v) x) (deriv (cutG K c u v) y) :=
        ⟨hx'.le, hy'.le⟩
      obtain ⟨z, -, hz⟩ := intermediate_value_Icc hxy hdcont.continuousOn hmem
      exact hderiv z hz
    · have hmem : (0 : ℝ) ∈ Set.Icc (deriv (cutG K c u v) x) (deriv (cutG K c u v) y) :=
        ⟨hx'.le, hy'.le⟩
      obtain ⟨z, -, hz⟩ := intermediate_value_Icc' hyx hdcont.continuousOn hmem
      exact hderiv z hz
  have hper : cutG K c u v (2 * Real.pi) = cutG K c u v 0 := by
    simpa using periodic_cutG (K := K) (c := c) (u := u) (v := v) 0
  rcases hsign with hs | hs
  · have hmono : StrictMonoOn (cutG K c u v) Set.univ :=
      strictMonoOn_of_deriv_pos convex_univ
        (continuous_cutG (K := K) (c := c) (u := u) (v := v)).continuousOn
        (fun x _ => hs x)
    have hlt := hmono (Set.mem_univ 0) (Set.mem_univ (2 * Real.pi)) (by positivity)
    rw [hper] at hlt
    exact absurd hlt (lt_irrefl _)
  · have hmono : StrictAntiOn (cutG K c u v) Set.univ :=
      strictAntiOn_of_deriv_neg convex_univ
        (continuous_cutG (K := K) (c := c) (u := u) (v := v)).continuousOn
        (fun x _ => hs x)
    have hlt := hmono (Set.mem_univ 0) (Set.mem_univ (2 * Real.pi)) (by positivity)
    rw [hper] at hlt
    exact absurd hlt (lt_irrefl _)

theorem closure_trenchSet_le {t : ℝ} (ht : t ∈ closure (trenchSet K s c σ u v h ℓ lam)) :
    boxA K s c σ t ≤ 0 ∧ |cutG K c u v t| ≤ h ∧ wallW K ℓ t ≤ lam := by
  refine ⟨?_, ?_, ?_⟩
  · exact closure_minimal (fun y hy => hy.1.le)
      (isClosed_le continuous_boxA continuous_const) ht
  · exact closure_minimal (fun y hy => hy.2.1.le)
      (isClosed_le continuous_cutG.abs continuous_const) ht
  · exact closure_minimal (fun y hy => hy.2.2.le)
      (isClosed_le continuous_wallW continuous_const) ht

/-! ## The split of the level count (local copies)

The level count of the sweep splits into the count on the box sphere and the count of the trace
inside the box; the two lemmas below are local copies of
`Work.Drive.Mono.encard_frontier_lt_min_of_parts` and its ingredients (which live in a module that
is still under construction by another agent), so that this development depends only on modules
that are stable. -/

theorem levelCount_range_inter_le_paramSet (K : Knot) (A : Set R3) :
    Set.encard (Set.range K.curve ∩ A) ≤
      Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧ K.curve t ∈ A} := by
  have h1 : Set.range K.curve ∩ A =
      K.curve '' {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧ K.curve t ∈ A} := by
    rw [Work.Drive.EpsForm.range_knot_eq_image_Ico K]
    ext y
    constructor
    · rintro ⟨⟨t, ht, rfl⟩, hyA⟩
      exact ⟨t, ⟨ht, hyA⟩, rfl⟩
    · rintro ⟨t, ⟨ht, htA⟩, rfl⟩
      exact ⟨⟨t, ht, rfl⟩, htA⟩
  rw [h1]
  exact Set.encard_image_le K.curve _

/-- **The level count splits into the box-sphere part and the in-box part.** -/
theorem levelCount_frontier_le_boxSphere_add_inbox (K : Knot) {s u : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {v : R3} {h : ℝ} {ℓ : R3 →L[ℝ] ℝ} {lam : ℝ} (hs : 0 < s) :
    Set.encard (Set.range K.curve ∩ frontier (tiltedLevelRemoved s c σ u v h ℓ lam)) ≤
      Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
          Submission.boxNorm c σ (K.curve t) = s} +
      Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
          K.curve t ∈ Submission.PBox s c σ ∧
          K.curve t ∈ frontier (tiltedLevelRemoved s c σ u v h ℓ lam)} := by
  have hfrPBox : frontier (Submission.PBox s c σ) = Work.BoxShrink.Core.sphereSet c σ s := by
    rw [Work.Topology.SphereSlicing.frontier_PBox hs c σ,
      Work.BoxShrink.Core.sphereSet_eq_BoxSphere]
  have hsub : Set.range K.curve ∩ frontier (tiltedLevelRemoved s c σ u v h ℓ lam) ⊆
      (Set.range K.curve ∩ Work.BoxShrink.Core.sphereSet c σ s) ∪
        (Set.range K.curve ∩ (Submission.PBox s c σ ∩
          frontier (tiltedLevelRemoved s c σ u v h ℓ lam))) := by
    rintro y ⟨hyK, hyF⟩
    have hcl : y ∈ closure (Submission.PBox s c σ) :=
      closure_mono (show tiltedLevelRemoved s c σ u v h ℓ lam ⊆ Submission.PBox s c σ from
        fun z hz => hz.1) (frontier_subset_closure hyF)
    rw [closure_eq_self_union_frontier, hfrPBox] at hcl
    rcases hcl with hybox | hysph
    · exact Or.inr ⟨hyK, hybox, hyF⟩
    · exact Or.inl ⟨hyK, hysph⟩
  refine le_trans (Set.encard_le_encard hsub) (le_trans (Set.encard_union_le _ _) ?_)
  refine add_le_add ?_ ?_
  · exact levelCount_range_inter_le_paramSet K (Work.BoxShrink.Core.sphereSet c σ s)
  · exact levelCount_range_inter_le_paramSet K
      (Submission.PBox s c σ ∩ frontier (tiltedLevelRemoved s c σ u v h ℓ lam))

/-- **The level count from the two parts.** -/
theorem levelCount_lt_min_of_parts (p q : ℕ) (K : Knot) {s u : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {v : R3} {h : ℝ} {ℓ : R3 →L[ℝ] ℝ} {lam : ℝ} {A B : ℕ∞}
    (hs : 0 < s)
    (hS : Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        Submission.boxNorm c σ (K.curve t) = s} ≤ A)
    (hin : Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        K.curve t ∈ Submission.PBox s c σ ∧
        K.curve t ∈ frontier (tiltedLevelRemoved s c σ u v h ℓ lam)} ≤ B)
    (hAB : A + B < (Nat.min p q : ℕ∞)) :
    Set.encard (Set.range K.curve ∩ frontier (tiltedLevelRemoved s c σ u v h ℓ lam)) <
      (Nat.min p q : ℕ∞) :=
  lt_of_le_of_lt
    (le_trans (levelCount_frontier_le_boxSphere_add_inbox (K := K) (s := s) (u := u) (c := c)
      (σ := σ) (v := v) (h := h) (ℓ := ℓ) (lam := lam) hs) (add_le_add hS hin)) hAB

/-- **A frontier point of the removed set inside the box lies in the closed slab.** -/
theorem levelCount_abs_le_of_mem_inbox {s u : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {v : R3}
    {h : ℝ} {ℓ : R3 →L[ℝ] ℝ} {lam : ℝ} {y : R3}
    (hybox : y ∈ Submission.PBox s c σ)
    (hyfr : y ∈ frontier (tiltedLevelRemoved s c σ u v h ℓ lam)) :
    |inner ℝ v y - (inner ℝ v c + u)| ≤ h := by
  have hfr := Work.Drive.EpsFormSphere.frontier_tiltedSwept_subset s (inner ℝ v c + u) h lam c v
    σ ℓ hyfr
  rcases hfr with hf | hf
  · have hmem : y ∈ interior (Submission.PBox s c σ) := by
      rw [(Work.Topology.SphereSlicing.isOpen_PBox s c σ).interior_eq]
      exact hybox
    exact absurd hmem hf.2
  · rcases hf with hf | hf
    · exact le_of_eq hf
    · exact le_of_lt hf.1


/-! ## The in-box trace parameters are face or wall parameters

The trace of the level inside the box is the frontier of the *slab chunk*
`slabClosed ∩ {ℓ < lam}`: a point of it either lies on a face of the slab (and strictly below the
level, the corner `{|⟪v,·⟫-a| = h ∧ ℓ = lam}` being exceptional) or lies in the open slab on the wall
`{ℓ = lam}`.  This is the split which makes the level count spendable against the crossings of the
knot with the *cutting plane*. -/

theorem inboxPts_subset_corner (hh : 0 < h)
    (hwall : ∀ t : ℝ, K.curve t ∈ Submission.PBox s c σ →
      |cutG K c u v t| ≤ h → deriv (wallW K ℓ) t ≠ 0)
    (hface : ∀ t : ℝ, K.curve t ∈ Submission.PBox s c σ →
      |cutG K c u v t| = h → deriv (fun r : ℝ => inner ℝ v (K.curve r)) t ≠ 0)
    (hcorner : ∀ t : ℝ, K.curve t ∈ Submission.PBox s c σ →
      |cutG K c u v t| = h → wallW K ℓ t ∈ (exc : Set ℝ))
    (hne : lam ∉ (exc : Set ℝ)) :
    inboxPts K s c σ u v h ℓ lam ⊆
      facePts K s c σ u v h ℓ lam ∪ wallPts K s c σ u v h ℓ lam := by
  intro t ht
  obtain ⟨htIco, htbox, htfr⟩ := ht
  have htboxA : boxA K s c σ t < 0 := (boxA_lt_zero_iff t).mpr htbox
  have h1 := Work.Drive.Mono.inbox_frontier_subset (K := K) (s := s) (u := u) (c := c) (σ := σ)
    (v := v) (h := h) (ℓ := ℓ) (lam := lam) hh ⟨htIco, htbox, htfr⟩
  have hle : |cutG K c u v t| ≤ h :=
    levelCount_abs_le_of_mem_inbox htbox htfr
  rcases h1 with h12 | hD
  · rcases h12 with hAB | hC
    · rcases hAB with hfr | hB
      · -- `t` is on the frontier of the trench: its level is `|g| = h` (below `lam`) or `ℓ = lam`
        have hfr' : t ∈ frontier (trenchSet K s c σ u v h ℓ lam) := by
          rwa [trenchSet_eq_raw]
        have hcl := closure_trenchSet_le (K := K) (s := s) (c := c) (σ := σ) (u := u) (v := v)
          (h := h) (ℓ := ℓ) (lam := lam) (frontier_subset_closure hfr')
        have hfr'' := hfr'
        rw [frontier, Set.mem_sdiff] at hfr''
        have hnotX : t ∉ trenchSet K s c σ u v h ℓ lam := by
          intro hX
          have : t ∈ interior (trenchSet K s c σ u v h ℓ lam) := by
            rwa [isOpen_trenchSet.interior_eq]
          exact hfr''.2 this
        have hcases : |cutG K c u v t| = h ∨ wallW K ℓ t = lam := by
          by_cases hlt : |cutG K c u v t| < h
          · right
            by_contra hw
            exact hnotX ⟨htboxA, hlt, lt_of_le_of_ne hcl.2.2 hw⟩
          · left
            exact le_antisymm hcl.2.1 (not_lt.mp hlt)
        rcases hcases with hg | hw
        · left
          refine ⟨htboxA, hg, ?_⟩
          by_contra hwlt
          have hwlam : wallW K ℓ t = lam := le_antisymm hcl.2.2 (not_lt.mp hwlt)
          have hexc : wallW K ℓ t ∈ (exc : Set ℝ) := hcorner t htbox hg
          rw [hwlam] at hexc
          exact hne hexc
        · right
          refine ⟨htboxA, ?_, hw⟩
          refine lt_of_le_of_ne hcl.2.1 ?_
          intro hge
          have hexc : wallW K ℓ t ∈ (exc : Set ℝ) := hcorner t htbox hge
          rw [hw] at hexc
          exact hne hexc
      · -- the wall functional has a critical point inside the box and the slab: excluded
        have hB' : deriv (wallW K ℓ) t = 0 := by
          rw [deriv_wallW_eq]
          exact hB
        exact absurd hB' (hwall t htbox hle)
    · -- `|g| = h` with critical height: excluded by `hface`
      have hg : |cutG K c u v t| = h := by simpa [cutG] using hC.1
      have hne0 : deriv (cutG K c u v) t ≠ 0 := by
        rw [deriv_cutG_eq]
        exact hface t htbox hg
      exact absurd (by rw [deriv_cutG_eq]; exact hC.2) hne0
  · -- `|g| = h` and on the wall: the corner, which is exceptional
    have hg : |cutG K c u v t| = h := by simpa [cutG] using hD.1
    have hexc : wallW K ℓ t ∈ (exc : Set ℝ) := hcorner t htbox hg
    have hexc' : lam ∈ (exc : Set ℝ) := by
      rw [wallW_apply, hD.2] at hexc
      exact hexc
    exact absurd hexc' hne



end Basic

end

end Work.Drive.Mono
