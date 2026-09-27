import Mathlib
import Submission.Work.Drive.sideAntisymmetry
import Submission.Work.Drive.cutDichotomy

/-!
# The cut dichotomy with an **arbitrary** class image (no linear plane needed)

`Submission/Work/Drive/cutDichotomy.lean` and `Submission/Work/Drive/sideAntisymmetry.lean` prove that
the cut of a plane presentation by a clamped radial sweep is *rigid*: it is either the whole
**class-cut** or empty.  As stated there, the class-cut is the pullback of a **linear** projective plane
`projLine (ker φ)` — i.e. of the projectivisation of a hyperplane of `ℝ⁴`.  That description is
available for the *linear* model planes of the end contribution (`linPlaneChart`), but it is **not**
available for the plane chart of a curve: the class image of that chart is the image of the chord
family under
`chord ↦ (halved chord direction, midpoint/radius)`, which is a *knotted* `ℝP² ⊂ ℝP³` and is contained
in a linear projective plane only for curves lying in a circle centred at the origin (see
`CLASS_IMAGE_OBSTRUCTION.md`; numerically, four chords of the circle of radius `2` about `(2,0)` give
four linearly independent class vectors, so no non-zero functional can vanish on all of them).

This file therefore restates the rigidity *without* any functional: the class-cut is the pullback of an
**arbitrary** set of classes `Y`, and in the intended application `Y` is the *class image of the swept
plane's box*, which is connected **for free** (it is the continuous image of the connected box
`unitBox 1`).  Nothing in the argument uses linearity; the four branch lemmas are copies of the
linear-plane ones with `classCut Q φ` replaced by `classCutSet Q Y` and the hypothesis `hPcls`
(classes of the sweep in `projLine (ker φ)`) replaced by its set form `classes of the sweep in Y`.

## Contents

* `Work.Drive.classCutSet` — the class-cut of a chart by a set of classes;
* `Work.Drive.classImage` — the class image of a plane presentation (the canonical `Y`);
* `Work.Drive.diskCut_subset_classCutSet` — the cut is contained in the class-cut;
* the four *branch* lemmas (disk and class-line forms), with the sign of the profile difference as an
  explicit hypothesis (exactly as in `sideAntisymmetry.lean`, but with `Y` in place of
  `projLine (ker φ)`);
* `Work.Drive.isPreconnected_classImage_of_continuous` — the class image of a continuous presentation is
  **preconnected** (the box is connected), so the class-line form's `hLpre` is free in the application;
* `Work.Drive.ProfilesSeparate` — the *residual geometric input* in the linearity-free formulation: the
  two level profiles have opposite order on the whole class image of the swept plane (weaker statements
  are available: see the two `diskCut_eq_classCutSet_or_empty_of_*` forms below);
* `Work.Drive.diskCut_eq_classCutSet_or_empty_of_profilesSeparate` and
  `Work.Drive.diskCut_eq_classCutSet_or_empty_of_separated` — the packaged dichotomy.

All declarations are `sorry`-free and rest only on `propext`, `Classical.choice` and `Quot.sound`.
-/

namespace Work.Drive

open scoped Topology Manifold ContDiff
open Set

noncomputable section

/-! ## The class-cut by an arbitrary set of classes -/

/-- **The class-cut of a chart by a set of classes.**  The parameters of the closed disk — read in the
parameter plane through `Work.Drive.cplxOf` — whose chart point has its class in `Y`.  For
`Y = projLine (ker φ)` this is `Work.Drive.classCut Q φ`; for the design it is the pullback of the
class image of the swept plane, which is connected without any hypothesis. -/
def classCutSet (Q : ℂ → CappingSpace) (Y : Set (Projectivization ℝ (Eucl 3))) :
    Set (EuclideanSpace ℝ (Fin 2)) :=
  {x | ‖cplxOf x‖ ≤ 1 ∧ (cappingSpaceHomeoProj (Q (cplxOf x))).2 ∈ Y}

theorem mem_classCutSet {Q : ℂ → CappingSpace} {Y : Set (Projectivization ℝ (Eucl 3))}
    {x : EuclideanSpace ℝ (Fin 2)} :
    x ∈ classCutSet Q Y ↔ ‖cplxOf x‖ ≤ 1 ∧
      (cappingSpaceHomeoProj (Q (cplxOf x))).2 ∈ Y := Iff.rfl

/-- **The class-cut of the linear-plane description is the set form at `Y = projLine (ker φ)`.**  (The
two definitions agree definitionally; the lemma records the dictionary.) -/
theorem classCut_eq_classCutSet (Q : ℂ → CappingSpace) (φ : Eucl 3 →L[ℝ] ℝ) :
    classCut Q φ = classCutSet Q (projLine (LinearMap.ker (φ : Eucl 3 →ₗ[ℝ] ℝ))) := rfl

/-- **The class image of a plane presentation**: the set of classes of the box parameters.  This is the
canonical choice of `Y`: the swept plane's classes, and (for a *plane chart*) the chart's own class
image.  It is preconnected whenever the presentation is continuous
(`Work.Drive.isPreconnected_classImage_of_continuous`) — this is the replacement for the
connectedness of a projective line. -/
def classImage (P : EuclideanSpace ℝ (Fin 2) → CappingSpace) :
    Set (Projectivization ℝ (Eucl 3)) :=
  (fun y => (cappingSpaceHomeoProj (P y)).2) '' Submission.Drive.unitBox 1

theorem mem_classImage {P : EuclideanSpace ℝ (Fin 2) → CappingSpace}
    {q : Projectivization ℝ (Eucl 3)} :
    q ∈ classImage P ↔ ∃ y ∈ Submission.Drive.unitBox 1,
      (cappingSpaceHomeoProj (P y)).2 = q := Iff.rfl

/-! ## The cut lies in the class-cut -/

/-- **The cut of a clamped sweep lies in the class-cut of the sweep's class image.**  The class of a
point of the sweep is the class of the plane at the corresponding box point (`cls_clampedSweep`), and
that class lies in the class image `Y` by definition when `Y` is chosen as `classImage P`. -/
theorem diskCut_subset_classCutSet (Q : ℂ → CappingSpace) (c : ℝ) (ψ : ℝ → ℝ)
    (P : EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (Y : Set (Projectivization ℝ (Eucl 3)))
    (hPcls : ∀ y ∈ Submission.Drive.unitBox 1, (cappingSpaceHomeoProj (P y)).2 ∈ Y) :
    diskCut Q (clampedSweep c ψ P) ⊆ classCutSet Q Y := by
  intro x hx
  refine ⟨hx.1, ?_⟩
  obtain ⟨y, hy, hxy⟩ := hx.2
  rw [show (cappingSpaceHomeoProj (Q (cplxOf x))).2
      = (cappingSpaceHomeoProj (clampedSweep c ψ P y)).2 from by rw [hxy],
    cls_clampedSweep]
  exact hPcls _ (mk2_mem_unitBox (hy 0) (hy 1))

/-! ## The four branch lemmas (set form of the class-cut) -/

/-- **The cut is empty when the chart's profile dominates the swept plane's** — the first branch of the
rigidity, in the set form, with the sign of the profile difference as an explicit hypothesis.  This is
`Work.Drive.diskCut_eq_empty_of_lt_profile` with `projLine (ker φ)` replaced by an arbitrary set `Y` of
classes (the linear-plane version is not applicable to the plane chart of a curve). -/
theorem diskCut_eq_empty_of_lt_profile_set (Q : ℂ → CappingSpace) (c : ℝ) (hc : 0 < c)
    (ψ : ℝ → ℝ) (hψ0 : ψ 0 = 1) (hψ1 : ψ 1 = 0)
    (hψ01 : ∀ t ∈ Set.Icc (0 : ℝ) 1, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hcont : ContinuousOn ψ (Set.Icc (0 : ℝ) 1))
    (P : EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (hr : ∀ y ∈ Submission.Drive.unitBox 1, c ≤ levelOf (P y))
    (Y : Set (Projectivization ℝ (Eucl 3)))
    (hPcls : ∀ y ∈ Submission.Drive.unitBox 1, (cappingSpaceHomeoProj (P y)).2 ∈ Y)
    (g : EuclideanSpace ℝ (Fin 2) → ℝ)
    (hgmax : ∀ x y : EuclideanSpace ℝ (Fin 2), ‖cplxOf x‖ ≤ 1 →
      y ∈ Submission.Drive.unitBox 1 →
      (cappingSpaceHomeoProj (Q (cplxOf x))).2 = (cappingSpaceHomeoProj (P y)).2 →
        levelOf (P y) ≤ g x)
    (hgt : ∀ x ∈ classCutSet Q Y, g x < levelOf (Q (cplxOf x))) :
    diskCut Q (clampedSweep c ψ P) = ∅ := by
  have hsub := diskCut_subset_classCutSet Q c ψ P Y hPcls
  have himg := image_clampedSweep c hc ψ hψ0 hψ1 hψ01 hcont P hr
  rw [Set.eq_empty_iff_forall_notMem]
  intro x hx
  have hxS : x ∈ classCutSet Q Y := hsub hx
  obtain ⟨-, hx2⟩ := hx
  rw [himg] at hx2
  obtain ⟨y, hy, hcls, _hcle, hle⟩ := hx2
  have hle' : levelOf (P y) ≤ g x := hgmax x y hxS.1 hy hcls
  have hlt := hgt x hxS
  linarith

/-- **The cut is the whole class-cut when the swept plane's profile dominates the chart's** — the
second branch of the rigidity in the set form, again with the sign as an explicit hypothesis. -/
theorem diskCut_eq_classCutSet_of_lt_profile_set (Q : ℂ → CappingSpace) (c : ℝ) (hc : 0 < c)
    (ψ : ℝ → ℝ) (hψ0 : ψ 0 = 1) (hψ1 : ψ 1 = 0)
    (hψ01 : ∀ t ∈ Set.Icc (0 : ℝ) 1, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hcont : ContinuousOn ψ (Set.Icc (0 : ℝ) 1))
    (P : EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (hr : ∀ y ∈ Submission.Drive.unitBox 1, c ≤ levelOf (P y))
    (Y : Set (Projectivization ℝ (Eucl 3)))
    (hPcls : ∀ y ∈ Submission.Drive.unitBox 1, (cappingSpaceHomeoProj (P y)).2 ∈ Y)
    (g : EuclideanSpace ℝ (Fin 2) → ℝ)
    (hgatt : ∀ x ∈ classCutSet Q Y, ∃ y ∈ Submission.Drive.unitBox 1,
      (cappingSpaceHomeoProj (Q (cplxOf x))).2 = (cappingSpaceHomeoProj (P y)).2 ∧
        g x = levelOf (P y))
    (hclow : ∀ x ∈ classCutSet Q Y, c ≤ levelOf (Q (cplxOf x)))
    (hlt : ∀ x ∈ classCutSet Q Y, levelOf (Q (cplxOf x)) < g x) :
    diskCut Q (clampedSweep c ψ P) = classCutSet Q Y := by
  have hsub := diskCut_subset_classCutSet Q c ψ P Y hPcls
  have himg := image_clampedSweep c hc ψ hψ0 hψ1 hψ01 hcont P hr
  refine Set.Subset.antisymm hsub ?_
  intro x hxS
  obtain ⟨y, hy, hcls, hgy⟩ := hgatt x hxS
  have hlt' : levelOf (Q (cplxOf x)) < levelOf (P y) := by
    rw [← hgy]
    exact hlt x hxS
  refine ⟨hxS.1, ?_⟩
  rw [himg]
  exact ⟨y, hy, hcls, hclow x hxS, hlt'.le⟩

/-- **The class-line form of the empty branch** (set form).  The sign hypothesis is stated on an
arbitrary set `L` of classes containing the classes of the class-cut; in the application `L` is the
class image of the swept plane, whose preconnectedness is free
(`Work.Drive.isPreconnected_classImage_of_continuous`). -/
theorem diskCut_eq_empty_of_lt_profile_classLine_set
    (Q : ℂ → CappingSpace) (c : ℝ) (hc : 0 < c) (ψ : ℝ → ℝ) (hψ0 : ψ 0 = 1) (hψ1 : ψ 1 = 0)
    (hψ01 : ∀ t ∈ Set.Icc (0 : ℝ) 1, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hcont : ContinuousOn ψ (Set.Icc (0 : ℝ) 1))
    (P : EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (hr : ∀ y ∈ Submission.Drive.unitBox 1, c ≤ levelOf (P y))
    (Y : Set (Projectivization ℝ (Eucl 3)))
    (hPcls : ∀ y ∈ Submission.Drive.unitBox 1, (cappingSpaceHomeoProj (P y)).2 ∈ Y)
    (L : Set (Projectivization ℝ (Eucl 3)))
    (hLmem : ∀ x ∈ classCutSet Q Y, (cappingSpaceHomeoProj (Q (cplxOf x))).2 ∈ L)
    (FQ G : Projectivization ℝ (Eucl 3) → ℝ)
    (hFQval : ∀ x ∈ classCutSet Q Y,
      FQ ((cappingSpaceHomeoProj (Q (cplxOf x))).2) = levelOf (Q (cplxOf x)))
    (hGmax : ∀ x ∈ classCutSet Q Y, ∀ y ∈ Submission.Drive.unitBox 1,
      (cappingSpaceHomeoProj (Q (cplxOf x))).2 = (cappingSpaceHomeoProj (P y)).2 →
        levelOf (P y) ≤ G ((cappingSpaceHomeoProj (Q (cplxOf x))).2))
    (hgt : ∀ q ∈ L, G q < FQ q) :
    diskCut Q (clampedSweep c ψ P) = ∅ := by
  have hsub := diskCut_subset_classCutSet Q c ψ P Y hPcls
  have himg := image_clampedSweep c hc ψ hψ0 hψ1 hψ01 hcont P hr
  rw [Set.eq_empty_iff_forall_notMem]
  intro x hx
  have hxS : x ∈ classCutSet Q Y := hsub hx
  obtain ⟨-, hx2⟩ := hx
  rw [himg] at hx2
  obtain ⟨y, hy, hcls, _hcle, hle⟩ := hx2
  have hle' : levelOf (P y) ≤ G ((cappingSpaceHomeoProj (Q (cplxOf x))).2) :=
    hGmax x hxS y hy hcls
  have h2 : G ((cappingSpaceHomeoProj (Q (cplxOf x))).2)
      < levelOf (Q (cplxOf x)) := by
    have hh := hgt _ (hLmem x hxS)
    rwa [hFQval x hxS] at hh
  linarith

/-- **The class-line form of the class-cut branch** (set form). -/
theorem diskCut_eq_classCutSet_of_lt_profile_classLine_set
    (Q : ℂ → CappingSpace) (c : ℝ) (hc : 0 < c) (ψ : ℝ → ℝ) (hψ0 : ψ 0 = 1) (hψ1 : ψ 1 = 0)
    (hψ01 : ∀ t ∈ Set.Icc (0 : ℝ) 1, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hcont : ContinuousOn ψ (Set.Icc (0 : ℝ) 1))
    (P : EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (hr : ∀ y ∈ Submission.Drive.unitBox 1, c ≤ levelOf (P y))
    (Y : Set (Projectivization ℝ (Eucl 3)))
    (hPcls : ∀ y ∈ Submission.Drive.unitBox 1, (cappingSpaceHomeoProj (P y)).2 ∈ Y)
    (L : Set (Projectivization ℝ (Eucl 3)))
    (hLmem : ∀ x ∈ classCutSet Q Y, (cappingSpaceHomeoProj (Q (cplxOf x))).2 ∈ L)
    (G : Projectivization ℝ (Eucl 3) → ℝ)
    (hGatt : ∀ x ∈ classCutSet Q Y, ∃ y ∈ Submission.Drive.unitBox 1,
      (cappingSpaceHomeoProj (Q (cplxOf x))).2 = (cappingSpaceHomeoProj (P y)).2 ∧
        G ((cappingSpaceHomeoProj (Q (cplxOf x))).2) = levelOf (P y))
    (hclow : ∀ x ∈ classCutSet Q Y, c ≤ levelOf (Q (cplxOf x)))
    (FQ : Projectivization ℝ (Eucl 3) → ℝ)
    (hFQval : ∀ x ∈ classCutSet Q Y,
      FQ ((cappingSpaceHomeoProj (Q (cplxOf x))).2) = levelOf (Q (cplxOf x)))
    (hlt : ∀ q ∈ L, FQ q < G q) :
    diskCut Q (clampedSweep c ψ P) = classCutSet Q Y := by
  have hsub := diskCut_subset_classCutSet Q c ψ P Y hPcls
  have himg := image_clampedSweep c hc ψ hψ0 hψ1 hψ01 hcont P hr
  refine Set.Subset.antisymm hsub ?_
  intro x hxS
  obtain ⟨y, hy, hcls, hgy⟩ := hGatt x hxS
  have hlt' : levelOf (Q (cplxOf x)) < levelOf (P y) := by
    have hh := hlt _ (hLmem x hxS)
    rw [hFQval x hxS, hgy] at hh
    exact hh
  refine ⟨hxS.1, ?_⟩
  rw [himg]
  exact ⟨y, hy, hcls, hclow x hxS, hlt'.le⟩

/-- **The bridge in the set form: the cut is non-empty exactly when the chart's profile lies below the
swept plane's along the class set `L`.**  This is the linearity-free analogue of
`Work.Drive.diskCut_ne_empty_iff_profile` (whose `L` is a projective line): the sign of the profile
difference is constant on the preconnected `L` and nowhere zero there, so the two branches of the
rigidity are complementary.  In the intended application `L` is the class image of the swept plane,
whose preconnectedness is free (`Work.Drive.isPreconnected_classImage_of_continuous`). -/
theorem diskCut_ne_empty_iff_profile_set
    (Q : ℂ → CappingSpace) (c : ℝ) (hc : 0 < c) (ψ : ℝ → ℝ)
    (hψ0 : ψ 0 = 1) (hψ1 : ψ 1 = 0)
    (hψ01 : ∀ t ∈ Set.Icc (0 : ℝ) 1, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hcont : ContinuousOn ψ (Set.Icc (0 : ℝ) 1))
    (P : EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (hr : ∀ y ∈ Submission.Drive.unitBox 1, c ≤ levelOf (P y))
    (Y : Set (Projectivization ℝ (Eucl 3)))
    (hPcls : ∀ y ∈ Submission.Drive.unitBox 1, (cappingSpaceHomeoProj (P y)).2 ∈ Y)
    (L : Set (Projectivization ℝ (Eucl 3)))
    (hLmem : ∀ x ∈ classCutSet Q Y, (cappingSpaceHomeoProj (Q (cplxOf x))).2 ∈ L)
    (FQ G : Projectivization ℝ (Eucl 3) → ℝ)
    (hFQval : ∀ x ∈ classCutSet Q Y,
      FQ ((cappingSpaceHomeoProj (Q (cplxOf x))).2) = levelOf (Q (cplxOf x)))
    (hGmax : ∀ x ∈ classCutSet Q Y, ∀ y ∈ Submission.Drive.unitBox 1,
      (cappingSpaceHomeoProj (Q (cplxOf x))).2 = (cappingSpaceHomeoProj (P y)).2 →
        levelOf (P y) ≤ G ((cappingSpaceHomeoProj (Q (cplxOf x))).2))
    (hGatt : ∀ x ∈ classCutSet Q Y, ∃ y ∈ Submission.Drive.unitBox 1,
      (cappingSpaceHomeoProj (Q (cplxOf x))).2 = (cappingSpaceHomeoProj (P y)).2 ∧
        G ((cappingSpaceHomeoProj (Q (cplxOf x))).2) = levelOf (P y))
    (hclow : ∀ x ∈ classCutSet Q Y, c ≤ levelOf (Q (cplxOf x)))
    (hLpre : IsPreconnected L)
    (hcontFG : ContinuousOn (fun q => FQ q - G q) L)
    (hccne : classCutSet Q Y ≠ ∅)
    (hne : ∀ q ∈ L, G q ≠ FQ q) :
    diskCut Q (clampedSweep c ψ P) ≠ ∅ ↔ ∀ q ∈ L, FQ q < G q := by
  constructor
  · intro hcut
    rcases preconnected_forall_pos_or_neg hLpre hcontFG
        (fun q hq => sub_ne_zero.mpr (Ne.symm (hne q hq))) with hpos | hneg
    · exfalso
      refine hcut (diskCut_eq_empty_of_lt_profile_classLine_set Q c hc ψ hψ0 hψ1 hψ01 hcont P hr
        Y hPcls L hLmem FQ G hFQval hGmax ?_)
      intro q hq
      have h := hpos q hq
      change 0 < FQ q - G q at h
      linarith
    · intro q hq
      have h := hneg q hq
      change FQ q - G q < 0 at h
      linarith
  · intro hlt
    rw [diskCut_eq_classCutSet_of_lt_profile_classLine_set Q c hc ψ hψ0 hψ1 hψ01 hcont P hr
      Y hPcls L hLmem G hGatt hclow FQ hFQval hlt]
    exact hccne

/-! ## The preconnectedness of the class image is free -/

/-- The unit box `[0,1]²` is preconnected (it is convex). -/
theorem isPreconnected_unitBox_one : IsPreconnected (Submission.Drive.unitBox 1) := by
  have hconv : Convex ℝ (Submission.Drive.unitBox 1) := by
    intro x hx y hy a b _ha _hb _hab i
    have hxi : x i ∈ Set.Icc (0 : ℝ) 1 := hx i
    have hyi : y i ∈ Set.Icc (0 : ℝ) 1 := hy i
    have hcoe : (a • x + b • y) i = a * x i + b * y i := by simp [smul_eq_mul]
    rw [hcoe]
    exact ⟨by nlinarith [hxi.1, hyi.1, hxi.2, hyi.2],
      by nlinarith [hxi.1, hyi.1, hxi.2, hyi.2]⟩
  exact hconv.isPreconnected

/-- **The class image of a continuous plane presentation is preconnected.**  This is what replaces the
connectedness of a projective line in the linear-plane version of the rigidity: it needs no
hypothesis on the curve, only that the presentation is continuous on the (connected) box. -/
theorem isPreconnected_classImage_of_continuous
    (P : EuclideanSpace ℝ (Fin 2) → CappingSpace) (hP : Continuous P) :
    IsPreconnected (classImage P) :=
  isPreconnected_unitBox_one.image _
    ((continuous_snd.comp cappingSpaceHomeoProj.continuous).comp hP).continuousOn

/-! ## The packaged dichotomy -/

/-- **The residual geometric input of the rigidity, in the linearity-free form.**  The two level
profiles of the chart and of the swept plane are ordered in the *same* way on the whole class image of
the swept plane.  On the classes common to the two planes this is the *disjointness* of the planes
(proved for the rotation family as `Work.Drive.cappedPlaneDisjoint`); on the remaining classes of the
swept plane it is a statement about the chosen extension of the chart's profile (see
`CLASS_IMAGE_OBSTRUCTION.md` §"what is left"), and it is what the rigidity consumes. -/
def ProfilesSeparate (FQ G : Projectivization ℝ (Eucl 3) → ℝ)
    (Y : Set (Projectivization ℝ (Eucl 3))) : Prop :=
  (∀ q ∈ Y, G q < FQ q) ∨ (∀ q ∈ Y, FQ q < G q)

/-- **The rigidity dichotomy in the set form, with the sign of the profile difference as a
hypothesis.**  The cut of a clamped sweep is the whole class-cut (of the swept plane's class image) or
empty. -/
theorem diskCut_eq_classCutSet_or_empty_of_profilesSeparate
    (Q : ℂ → CappingSpace) (c : ℝ) (hc : 0 < c) (ψ : ℝ → ℝ)
    (hψ0 : ψ 0 = 1) (hψ1 : ψ 1 = 0)
    (hψ01 : ∀ t ∈ Set.Icc (0 : ℝ) 1, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hcont : ContinuousOn ψ (Set.Icc (0 : ℝ) 1))
    (P : EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (hr : ∀ y ∈ Submission.Drive.unitBox 1, c ≤ levelOf (P y))
    (Y : Set (Projectivization ℝ (Eucl 3)))
    (hPcls : ∀ y ∈ Submission.Drive.unitBox 1, (cappingSpaceHomeoProj (P y)).2 ∈ Y)
    (FQ G : Projectivization ℝ (Eucl 3) → ℝ)
    (hFQval : ∀ x ∈ classCutSet Q Y,
      FQ ((cappingSpaceHomeoProj (Q (cplxOf x))).2) = levelOf (Q (cplxOf x)))
    (hGmax : ∀ x ∈ classCutSet Q Y, ∀ y ∈ Submission.Drive.unitBox 1,
      (cappingSpaceHomeoProj (Q (cplxOf x))).2 = (cappingSpaceHomeoProj (P y)).2 →
        levelOf (P y) ≤ G ((cappingSpaceHomeoProj (Q (cplxOf x))).2))
    (hGatt : ∀ x ∈ classCutSet Q Y, ∃ y ∈ Submission.Drive.unitBox 1,
      (cappingSpaceHomeoProj (Q (cplxOf x))).2 = (cappingSpaceHomeoProj (P y)).2 ∧
        G ((cappingSpaceHomeoProj (Q (cplxOf x))).2) = levelOf (P y))
    (hclow : ∀ x ∈ classCutSet Q Y, c ≤ levelOf (Q (cplxOf x)))
    (hsep : ProfilesSeparate FQ G Y) :
    diskCut Q (clampedSweep c ψ P) = classCutSet Q Y ∨
      diskCut Q (clampedSweep c ψ P) = ∅ := by
  rcases hsep with hsep | hsep
  · right
    exact diskCut_eq_empty_of_lt_profile_classLine_set Q c hc ψ hψ0 hψ1 hψ01 hcont P hr Y hPcls
      Y (fun x hx => hx.2) FQ G hFQval hGmax hsep
  · left
    exact diskCut_eq_classCutSet_of_lt_profile_classLine_set Q c hc ψ hψ0 hψ1 hψ01 hcont P hr Y
      hPcls Y (fun x hx => hx.2) G hGatt hclow FQ hFQval hsep

/-- **The rigidity dichotomy from continuity and non-vanishing of the profile difference on the class
image of the swept plane.**  The class image is preconnected for free
(`Work.Drive.isPreconnected_classImage_of_continuous`), so a continuous nowhere-zero profile
difference has a *definite* sign there and
`Work.Drive.diskCut_eq_classCutSet_or_empty_of_profilesSeparate` applies.  This is the form in which
the rigidity is reduced to its single geometric input. -/
theorem diskCut_eq_classCutSet_or_empty_of_separated
    (Q : ℂ → CappingSpace) (c : ℝ) (hc : 0 < c) (ψ : ℝ → ℝ)
    (hψ0 : ψ 0 = 1) (hψ1 : ψ 1 = 0)
    (hψ01 : ∀ t ∈ Set.Icc (0 : ℝ) 1, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hcont : ContinuousOn ψ (Set.Icc (0 : ℝ) 1))
    (P : EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (hr : ∀ y ∈ Submission.Drive.unitBox 1, c ≤ levelOf (P y))
    (hP : Continuous P)
    (hPcls : ∀ y ∈ Submission.Drive.unitBox 1, (cappingSpaceHomeoProj (P y)).2 ∈ classImage P)
    (FQ G : Projectivization ℝ (Eucl 3) → ℝ)
    (hFQval : ∀ x ∈ classCutSet Q (classImage P),
      FQ ((cappingSpaceHomeoProj (Q (cplxOf x))).2) = levelOf (Q (cplxOf x)))
    (hGmax : ∀ x ∈ classCutSet Q (classImage P), ∀ y ∈ Submission.Drive.unitBox 1,
      (cappingSpaceHomeoProj (Q (cplxOf x))).2 = (cappingSpaceHomeoProj (P y)).2 →
        levelOf (P y) ≤ G ((cappingSpaceHomeoProj (Q (cplxOf x))).2))
    (hGatt : ∀ x ∈ classCutSet Q (classImage P), ∃ y ∈ Submission.Drive.unitBox 1,
      (cappingSpaceHomeoProj (Q (cplxOf x))).2 = (cappingSpaceHomeoProj (P y)).2 ∧
        G ((cappingSpaceHomeoProj (Q (cplxOf x))).2) = levelOf (P y))
    (hclow : ∀ x ∈ classCutSet Q (classImage P), c ≤ levelOf (Q (cplxOf x)))
    (hcontFG : ContinuousOn (fun q => FQ q - G q) (classImage P))
    (hne : ∀ q ∈ classImage P, FQ q ≠ G q) :
    diskCut Q (clampedSweep c ψ P) = classCutSet Q (classImage P) ∨
      diskCut Q (clampedSweep c ψ P) = ∅ := by
  refine diskCut_eq_classCutSet_or_empty_of_profilesSeparate Q c hc ψ hψ0 hψ1 hψ01 hcont P hr
    (classImage P) hPcls FQ G hFQval hGmax hGatt hclow ?_
  rcases preconnected_forall_pos_or_neg (isPreconnected_classImage_of_continuous P hP) hcontFG
    (fun q hq => sub_ne_zero.mpr (hne q hq)) with hpos | hneg
  · refine Or.inl fun q hq => ?_
    have h := hpos q hq
    change 0 < FQ q - G q at h
    linarith
  · refine Or.inr fun q hq => ?_
    have h := hneg q hq
    change FQ q - G q < 0 at h
    linarith

end

end Work.Drive
