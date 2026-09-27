import Mathlib
import Submission.Work.Drive.clampedSweepLevel
import Submission.Work.Drive.exists_radial_level_eq_of_lt_level
import Submission.Work.Drive.cutTransport
import Submission.Work.Drive.cutTranslate
import Submission.Work.Drive.BoxParityDefs
import Submission.Work.Drive.haReduction

/-!
# The image of a clamped radial sweep: classes and levels

`Work.Drive.clampedSweep c ψ P` is the radial `3`-chain of a plane presentation `P`: at `x = (y, t)`
its projective class is that of `P y`, and its level interpolates between the truncation level `c`
(at `t = 0`, `ψ 0 = 1`) and the plane's own level `levelOf (P y)` (at `t = 1`, `ψ 1 = 0`).  This file
records the **exact image** of the sweep over the parameter box:

> `clampedSweep c ψ P '' unitBox 2 = {p | ∃ y ∈ unitBox 1, class p = class (P y) ∧
>    c ≤ level p ≤ level (P y)}`

— "the set of points whose class is attained by the plane and whose level lies between the truncation
level and the plane's level at that class".  This is the *level analysis* of the design's cut: the
transport's `hVcut : diskCut Q V = SmoothArc.Zset h` asks for the cut (the set of disk parameters
`x` with `Q x ∈ clampedSweep c ψ P '' unitBox 2`) to be the zero set of a profile, and with the
dictionary of `Submission/Work/Drive/projPlaneCut.lean` (the class half) the only remaining
ingredient is exactly this description of the sweep's image.

The two inclusions are the two level bounds already proved for the sweep
(`Work.Drive.le_levelOf_clampedSweep_local`, `Work.Drive.levelOf_clampedSweep_le_local`) and the
existence of a radial parameter at a prescribed level
(`Work.Drive.exists_radial_level_eq_of_lt_level`, an intermediate-value argument), plus the fact that a
point of the capping space is determined by its level and its class
(`Work.Drive.eq_of_levelOf_eq_of_class_eq`).
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff
open Submission.Drive

noncomputable section

/-- **A point of the capping space is determined by its level and its class.** -/
theorem eq_of_levelOf_eq_of_class_eq {a b : CappingSpace}
    (h1 : levelOf a = levelOf b)
    (h2 : (cappingSpaceHomeoProj a).2 = (cappingSpaceHomeoProj b).2) : a = b := by
  refine cappingSpaceHomeoProj.injective ?_
  refine Prod.ext ?_ h2
  exact Subtype.ext h1

/-- The two-parameter point of the plane's box lies in the box. -/
lemma mk2_mem_unitBox {a b : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1) (hb : b ∈ Set.Icc (0 : ℝ) 1) :
    mk2 a b ∈ unitBox 1 := by
  intro i
  fin_cases i
  · simpa using ha
  · simpa using hb

/-- The radial vector over a box point is in the parameter box.  (Kept `private`: the name is
already taken by `Work.Drive.radVec_mem_unitBox` in `endDistinctLevelDesign.lean`.) -/
private lemma radVec_mem_unitBox {y : EuclideanSpace ℝ (Fin 2)} (hy : y ∈ unitBox 1) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) : radVec y t ∈ unitBox 2 := by
  intro i
  fin_cases i
  · simpa using hy 0
  · simpa using hy 1
  · simpa using ht

/-- **The image of a clamped radial sweep.**  The sweep over the parameter box is exactly the set of
points whose class is the class of a plane point of the box and whose level lies between the
truncation level `c` and the plane's level at that point. -/
theorem image_clampedSweep (c : ℝ) (hc : 0 < c) (ψ : ℝ → ℝ)
    (hψ0 : ψ 0 = 1) (hψ1 : ψ 1 = 0)
    (hψ01 : ∀ t ∈ Set.Icc (0 : ℝ) 1, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hcont : ContinuousOn ψ (Set.Icc (0 : ℝ) 1))
    (P : EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (hr : ∀ y ∈ unitBox 1, c ≤ levelOf (P y)) :
    clampedSweep c ψ P '' unitBox 2
      = {p : CappingSpace | ∃ y ∈ unitBox 1,
          (cappingSpaceHomeoProj p).2 = (cappingSpaceHomeoProj (P y)).2 ∧
          c ≤ levelOf p ∧ levelOf p ≤ levelOf (P y)} := by
  ext p
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨mk2 (x 0) (x 1), mk2_mem_unitBox (hx 0) (hx 1), cls_clampedSweep c ψ P x, ?_, ?_⟩
    · exact le_levelOf_clampedSweep_local hc hψ01 P x (hx 2) (hr _ (mk2_mem_unitBox (hx 0) (hx 1)))
    · exact levelOf_clampedSweep_le_local hc hψ01 P x (hx 2) (hr _ (mk2_mem_unitBox (hx 0) (hx 1)))
  · rintro ⟨y, hy, hcls, hcle, hler⟩
    have hcr : c ≤ levelOf (P y) := le_trans hcle hler
    have hrpos : 0 < levelOf (P y) := levelOf_pos _
    -- the class of the sweep point at `radVec y t` is `class (P y)`
    have hcls' : ∀ t : ℝ, (cappingSpaceHomeoProj (clampedSweep c ψ P (radVec y t))).2
        = (cappingSpaceHomeoProj (P y)).2 := by
      intro t
      rw [cls_clampedSweep]
      simp only [radVec_apply_zero, radVec_apply_one, mk2_eta]
    -- the level of the sweep at `radVec y t` is `exp (ψ t (log c − log r)) * r`
    have hlev' : ∀ t : ℝ, levelOf (clampedSweep c ψ P (radVec y t))
        = Real.exp (ψ t * (Real.log c - Real.log (levelOf (P y)))) * levelOf (P y) := by
      intro t
      rw [levelOf_clampedSweep, clampScale]
      simp only [radVec_apply_zero, radVec_apply_one, radVec_apply_two, mk2_eta]
    -- the three cases `level p = c`, `c < level p = level (P y)`, `c < level p < level (P y)`
    rcases eq_or_lt_of_le hcle with h_eq | h_lt
    · -- `level p = c`: the bottom face
      have hlev0 : levelOf (clampedSweep c ψ P (radVec y 0)) = levelOf p := by
        rw [hlev' 0, hψ0, one_mul, Real.exp_sub, Real.exp_log hc, Real.exp_log hrpos,
          div_mul_cancel₀ c (ne_of_gt hrpos)]
        exact h_eq
      exact ⟨radVec y 0, radVec_mem_unitBox hy (by norm_num),
        eq_of_levelOf_eq_of_class_eq hlev0 ((hcls' 0).trans hcls.symm)⟩
    · rcases eq_or_lt_of_le hler with h_eq | h_lt'
      · -- `level p = level (P y)`: the top face
        have hlev1 : levelOf (clampedSweep c ψ P (radVec y 1)) = levelOf p := by
          rw [hlev' 1, hψ1, zero_mul, Real.exp_zero, one_mul]
          exact h_eq.symm
        exact ⟨radVec y 1, radVec_mem_unitBox hy (by norm_num),
          eq_of_levelOf_eq_of_class_eq hlev1 ((hcls' 1).trans hcls.symm)⟩
      · -- the interior: the intermediate value theorem
        obtain ⟨t, ht, hlevt⟩ :=
          exists_radial_level_eq_of_lt_level (levelOf p) c hc h_lt ψ hψ0 hψ1 hcont P y h_lt'
        exact ⟨radVec y t, radVec_mem_unitBox hy ⟨le_of_lt ht.1, le_of_lt ht.2⟩,
          eq_of_levelOf_eq_of_class_eq hlevt ((hcls' t).trans hcls.symm)⟩

/-- **The cut of a clamped sweep, in the plane's own data.**  Combining the image description with the
definition of `Work.Drive.diskCut`: the cut of the chart `Q` of a plane by the sweep of the plane
presentation `P` is

> `{x | ‖x‖ ≤ 1 and the class of Q x is the class of some box point of P and the level of Q x lies
>    between the truncation level c and the level of P at that point}`.

This is the exact form the design has to compare with a level set: with the class dictionary of
`Submission/Work/Drive/projPlaneCut.lean` (`φ ∘ V'` vanishes exactly on the classes of `projLine φ`),
the design's `hVcut : diskCut Q V = SmoothArc.Zset h` needs only that, for every `x` of the disk whose
class is attained by the swept plane, the *level inequality* `levelOf (Q x) ≤ levelOf (P y)` holds for
the box point `y` with that class. -/
theorem diskCut_clampedSweep_eq (Q : ℂ → CappingSpace) (c : ℝ) (hc : 0 < c) (ψ : ℝ → ℝ)
    (hψ0 : ψ 0 = 1) (hψ1 : ψ 1 = 0)
    (hψ01 : ∀ t ∈ Set.Icc (0 : ℝ) 1, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hcont : ContinuousOn ψ (Set.Icc (0 : ℝ) 1))
    (P : EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (hr : ∀ y ∈ unitBox 1, c ≤ levelOf (P y)) :
    diskCut Q (clampedSweep c ψ P)
      = {x : EuclideanSpace ℝ (Fin 2) | ‖cplxOf x‖ ≤ 1 ∧ ∃ y ∈ unitBox 1,
          (cappingSpaceHomeoProj (Q (cplxOf x))).2 = (cappingSpaceHomeoProj (P y)).2 ∧
          c ≤ levelOf (Q (cplxOf x)) ∧ levelOf (Q (cplxOf x)) ≤ levelOf (P y)} := by
  ext x
  simp only [diskCut, Set.mem_setOf_eq,
    image_clampedSweep c hc ψ hψ0 hψ1 hψ01 hcont P hr]

/-- **The fibre hypothesis `hfibV` of the transport, from injectivity at the class.**  The cut of a
clamped radial sweep is a *graph* over the plane's parameter box: the fibre over a box point `u` is the
single parameter `pad3 u = (u 0, u 1, 1)`.  Indeed, if `y` is any parameter of `unitBox 2` with
`clampedSweep c ψ P y = P u`, then the class of the sweep is the class of `P (mk2 (y 0) (y 1))`, so the
class-injectivity at `u` gives `mk2 (y 0) (y 1) = u`; the level equation then reads
`exp (ψ (y 2) (log c − log r)) · r = r` with `r = level (P u) > c`, whence `ψ (y 2) = 0` and (by
strictness of `ψ`) `y 2 = 1`.

The only geometric input is `hcls`: the class map of the plane's own presentation is injective at the
class of `P u` (in the design this holds off the seam of the disk model). -/
theorem ncard_cutFibreBox_clampedSweep_eq_one
    (P : EuclideanSpace ℝ (Fin 2) → CappingSpace) (c : ℝ) (hc : 0 < c) (ψ : ℝ → ℝ)
    (hψ1 : ψ 1 = 0) (hψstr : ∀ t ∈ Set.Icc (0 : ℝ) 1, ψ t = 0 → t = 1)
    (u : EuclideanSpace ℝ (Fin 2)) (hu : u ∈ unitBox 1)
    (hcls : ∀ y ∈ unitBox 1,
      (cappingSpaceHomeoProj (P y)).2 = (cappingSpaceHomeoProj (P u)).2 → y = u)
    (hlev : c < levelOf (P u)) :
    (cutFibreBox P (clampedSweep c ψ P) u).ncard = 1 := by
  have hrpos : 0 < levelOf (P u) := levelOf_pos _
  have hset : cutFibreBox P (clampedSweep c ψ P) u = {pad3 u} := by
    ext y
    constructor
    · rintro ⟨hy, hyu⟩
      -- the class of `P (mk2 (y 0) (y 1))` is the class of `P u`
      have hcls_eq : (cappingSpaceHomeoProj (P (mk2 (y 0) (y 1)))).2
          = (cappingSpaceHomeoProj (P u)).2 := by
        rw [← cls_clampedSweep c ψ P y]
        have h2 : (cappingSpaceHomeoProj (clampedSweep c ψ P y)).2
            = (cappingSpaceHomeoProj (P u)).2 := by rw [hyu]
        exact h2
      have hy1 : mk2 (y 0) (y 1) = u :=
        hcls _ (mk2_mem_unitBox (hy 0) (hy 1)) hcls_eq
      -- the level equation
      have hlevel : levelOf (clampedSweep c ψ P y) = levelOf (P u) := by rw [hyu]
      rw [levelOf_clampedSweep, clampScale, hy1] at hlevel
      -- hence `ψ (y 2) = 0`
      have hexp1 : Real.exp (ψ (y 2) * (Real.log c - Real.log (levelOf (P u)))) = 1 := by
        refine mul_right_cancel₀ (ne_of_gt hrpos) ?_
        rw [hlevel, one_mul]
      have hlog : Real.log c - Real.log (levelOf (P u)) ≠ 0 := by
        intro h0
        have h1 : Real.log c = Real.log (levelOf (P u)) := by linarith
        have h2 : c = levelOf (P u) := by
          have := congrArg Real.exp h1
          rwa [Real.exp_log hc, Real.exp_log hrpos] at this
        exact absurd h2 (ne_of_lt hlev)
      have hx0 : ψ (y 2) * (Real.log c - Real.log (levelOf (P u))) = 0 := by
        have := congrArg Real.log hexp1
        rwa [Real.log_exp, Real.log_one] at this
      have hψy : ψ (y 2) = 0 := by
        rcases mul_eq_zero.mp hx0 with h | h
        · exact h
        · exact absurd h hlog
      have hy2 : y 2 = 1 := hψstr (y 2) (hy 2) hψy
      -- conclude `y = pad3 u`
      have : y = pad3 u := by
        have h1 : y = radVec (mk2 (y 0) (y 1)) (y 2) := (mk3_eta y).symm
        rw [h1, hy1, hy2]
        rfl
      exact this
    · rintro rfl
      refine ⟨pad3_mem_unitBox hu, ?_⟩
      show P u = clampedSweep c ψ P (pad3 u)
      rw [clampedSweep_face_one c ψ P hψ1 (pad3 u) (pad3_apply_two u)]
      simp only [pad3_apply_zero, pad3_apply_one, mk2_eta]
  rw [hset, Set.ncard_singleton]

/-- **Class-injectivity of the design's plane presentation at an interior point.**  If the chart's
class map is injective off the *seam* of the disk (`hQinj`, the standard disk model of `ℝP² = D²/{x ∼ -x}`)
and a box point `u` corresponds to an *interior* point of the disk, then no other box point shares the
class of `diskPlane Q u`.  This is the `hcls` hypothesis of
`Work.Drive.ncard_cutFibreBox_clampedSweep_eq_one`, so the design's graph condition is reduced to those
two chart facts (the chart's injectivity off the seam, and the base point being off the seam). -/
theorem class_injective_diskPlane_of_interior {Q : ℂ → CappingSpace}
    (hQinj : ∀ z w : ℂ, (cappingSpaceHomeoProj (Q z)).2 = (cappingSpaceHomeoProj (Q w)).2 →
      z = w ∨ (‖z‖ = 1 ∧ w = -z))
    {u : EuclideanSpace ℝ (Fin 2)} (hu : u ∈ unitBox 1) (hint : ‖sqDisk (foldBox u)‖ < 1)
    {y : EuclideanSpace ℝ (Fin 2)} (hy : y ∈ unitBox 1)
    (hcls : (cappingSpaceHomeoProj (diskPlane Q y)).2
      = (cappingSpaceHomeoProj (diskPlane Q u)).2) :
    y = u := by
  rw [diskPlane_apply, diskPlane_apply] at hcls
  rcases hQinj _ _ hcls with h | ⟨h1, h2⟩
  · obtain ⟨w, ⟨-, hwz⟩, hwuniq⟩ :=
      sqDisk_foldBox_existsUnique (sqDisk (foldBox u)) (le_of_lt hint)
    have huw : u = w := hwuniq u ⟨hu, rfl⟩
    have hyw : y = w := hwuniq y ⟨hy, h⟩
    rw [hyw, huw]
  · exfalso
    have h1' : ‖sqDisk (foldBox u)‖ = 1 := by rw [h2, norm_neg]; exact h1
    exact absurd h1' (ne_of_lt hint)

/-- **A truncation level strictly below a continuous plane presentation's levels.**  For a continuous
`P : ℝ² → CappingSpace` the level function is positive everywhere and continuous, so on the compact
parameter box it has a positive lower bound.  This is the constant the design's sweeps need
(`hr` below, and the engine's `hlev`). -/
theorem exists_truncationLevel (P : EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (hP : Continuous P) :
    ∃ c : ℝ, 0 < c ∧ ∀ y ∈ unitBox 1, c < levelOf (P y) := by
  obtain ⟨c, hc, hmin⟩ := (isCompact_unitBox 1).exists_forall_le'
    (f := fun y => levelOf (P y)) (continuous_levelOf.comp hP).continuousOn
    (a := 0) (fun b _ => levelOf_pos (P b))
  exact ⟨c / 2, by positivity, fun y hy => lt_of_lt_of_le (by linarith) (hmin y hy)⟩

/-- **The cut of a clamped sweep is the class-cut of the swept plane's projective plane exactly when the
level condition holds.**  Let `Q` be the chart of a plane, `φ` the normal functional of the *swept*
plane's projective plane and `P` a presentation of that swept plane whose box-image lies in the plane
(`hPcls`).  Then

> `diskCut Q (clampedSweep c ψ P) = {x | ‖x‖ ≤ 1 and class (Q x) ∈ projLine (ker φ)}`

if and only if every disk point whose class lies in the plane has a *box point of `P` with that class*
whose level is at least the level of `Q` there (and the truncation level `c` is below it).  With
`Work.Drive.image_clampedSweep` (the exact image of the sweep) this is a formal equivalence, so the
design's `hVcut : diskCut Q V = SmoothArc.Zset h` is *exactly* this level condition on top of the class
dictionary of `projPlaneCut.lean` — the sharp form of the risk recorded in
`CHAIN_INTERFACE_CONSUMERS.md` §7. -/
theorem diskCut_eq_classCut_iff (Q : ℂ → CappingSpace) (c : ℝ) (hc : 0 < c) (ψ : ℝ → ℝ)
    (hψ0 : ψ 0 = 1) (hψ1 : ψ 1 = 0)
    (hψ01 : ∀ t ∈ Set.Icc (0 : ℝ) 1, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hcont : ContinuousOn ψ (Set.Icc (0 : ℝ) 1))
    (P : EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (hr : ∀ y ∈ unitBox 1, c ≤ levelOf (P y))
    (φ : Eucl 3 →L[ℝ] ℝ)
    (hPcls : ∀ y ∈ unitBox 1,
      (cappingSpaceHomeoProj (P y)).2 ∈ projLine (LinearMap.ker (φ : Eucl 3 →ₗ[ℝ] ℝ))) :
    diskCut Q (clampedSweep c ψ P)
        = {x : EuclideanSpace ℝ (Fin 2) | ‖cplxOf x‖ ≤ 1 ∧
            (cappingSpaceHomeoProj (Q (cplxOf x))).2
              ∈ projLine (LinearMap.ker (φ : Eucl 3 →ₗ[ℝ] ℝ))}
      ↔ (∀ x : EuclideanSpace ℝ (Fin 2), ‖cplxOf x‖ ≤ 1 →
          (cappingSpaceHomeoProj (Q (cplxOf x))).2
            ∈ projLine (LinearMap.ker (φ : Eucl 3 →ₗ[ℝ] ℝ)) →
          ∃ y ∈ unitBox 1,
            (cappingSpaceHomeoProj (Q (cplxOf x))).2 = (cappingSpaceHomeoProj (P y)).2 ∧
            c ≤ levelOf (Q (cplxOf x)) ∧ levelOf (Q (cplxOf x)) ≤ levelOf (P y)) := by
  have himg := image_clampedSweep c hc ψ hψ0 hψ1 hψ01 hcont P hr
  constructor
  · intro h x hx1 hxmem
    have hxcut : x ∈ diskCut Q (clampedSweep c ψ P) := by
      rw [h]; exact ⟨hx1, hxmem⟩
    obtain ⟨-, hmem⟩ := hxcut
    rw [himg] at hmem
    simpa only [Set.mem_setOf_eq] using hmem
  · intro hlevel
    ext x
    rw [diskCut]
    constructor
    · rintro ⟨hx1, hmem⟩
      rw [himg] at hmem
      obtain ⟨y, hybox, hcls, -, -⟩ := hmem
      refine ⟨hx1, ?_⟩
      rw [hcls]
      exact hPcls y hybox
    · rintro ⟨hx1, hxmem⟩
      obtain ⟨y, hybox, hcls, hcle, hler⟩ := hlevel x hx1 hxmem
      refine ⟨hx1, ?_⟩
      rw [himg]
      exact ⟨y, hybox, hcls, hcle, hler⟩

end

end Work.Drive
