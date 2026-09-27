import Mathlib
import Submission.Work.Drive.collapseTransport
import Submission.Work.Drive.clampedSweep
import Submission.Work.Drive.planeChain

/-!
# The level-face avoidances of the radial-collapse pair count

`Submission/Work/Drive/TRANSPORT_COLLAPSE_STATUS.md` §7.7(ii) records that the two *level-face
avoidances* `havY`/`havZ` of the pair engine `Work.Drive.even_ncard_pairMeetBdry` (T1/T3 of the
radial-collapse transport of Hugelmeyer's Lemma 2) are geometric: at a meet of the collapsed plane
with a clamped sweep, the *level* coordinate of the sweep parameter can be neither `1` (the top face,
where the sweep degenerates to the plane `Pᵢ` itself) nor `0` (the floor, where it degenerates to the
shadow at the level `c`).

This file discharges the two *implications*, in the honest `CappingSpace`-valued vocabulary:

* **top face** (`clampedSweep_face_one`, `ψ 1 = 0`): the collapsed plane's value at `u` is
  `Q z` with `‖z‖ ≤ 1` (`norm_colMap_le_one`), while the top face is `P y'`; so a meet there would be
  a point of `Q '' (closed disk)` meeting the plane `P` — excluded by the two *cap-disjointness*
  hypotheses `hcap` (open disk vs open disk: `P`'s cap misses `Q`'s cap) and `hcirc` (the boundary
  circle of `Q` misses `P`'s cap), **provided** the sweep's own point `sqDisk (foldBox y')` is *off*
  the seam of the square (`‖·‖ < 1`), i.e. provided the meet is not a corner of the parameter box —
  that corner exclusion is exactly the "exactly one face coordinate" clause of the engine's `hface`.
* **floor** (`clampedSweep_face_zero`, `ψ 0 = 1`): the floor lies in the level `c`
  (`levelOf_shadow`), while the collapsed plane's level is *above* `c` (`hlev` — the design's "the
  floors lie below the levels", a consequence of `IsPlaneChart` alone,
  `Work.Drive.exists_levelData_of_isPlaneChart`); so a meet there is impossible with **no** disjointness
  hypothesis at all.

Both are stated for a single chain; the combined form `colMeet_level_face_avoid` is the shape in which
the design consumes them (T1's `havY`/`havZ` after the chart bridge of
`Submission/Work/Drive/collapseChartBridge.lean`).

## The corner cases, recorded so that they are not resdiscovered

The top-face implication is **not** true without the "off the seam" hypothesis on the sweep's point:
if both `u` (through `sqDisk ∘ foldBox`) and `y'` lie on the respective seams of the parameter boxes,
then both sides of the equation lie on the *curve* `Q '' {‖z‖ = 1} = P '' {seam}`, and the equation does
hold for the matching points.  Those configurations are precisely the corner zeros (two face
coordinates at once) which the engine's `hface` excludes, so the design's `havY` must be supplied for
the *one-face* zeros only — this is why the statement below carries `‖sqDisk (foldBox y')‖ < 1`
explicitly, and why the helper `norm_sqDisk_foldBox_lt_one_of_ne_one` is what turns the engine's
one-face clause into it.
-/

set_option autoImplicit false

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff Topology

noncomputable section

/-! ## 1. The collapsed plane's values and their chart preimages -/

/-- The collapsed plane at `u` is the chart evaluated at the collapse of the square-to-disk point. -/
lemma colPlane_apply (β : ℝ → ℝ) (Q : ℂ → CappingSpace) (s : ℝ)
    (u : EuclideanSpace ℝ (Fin 2)) :
    colPlane β Q s u = Q (colMap β s (sqDisk (foldBox u))) := rfl

/-- **The collapsed plane lands in the chart's image of the closed disk.** -/
lemma colPlane_mem_image_closedDisk {β : ℝ → ℝ} (hβpos : ∀ t : ℝ, 0 < β t)
    (hβ : ∀ t : ℝ, Real.sqrt t ≤ β t) (Q : ℂ → CappingSpace) (s : ℝ)
    (u : EuclideanSpace ℝ (Fin 2)) :
    colPlane β Q s u ∈ Q '' {z : ℂ | ‖z‖ ≤ 1} :=
  ⟨colMap β s (sqDisk (foldBox u)),
    norm_colMap_le_one hβpos hβ s _ (norm_sqDisk_le_one _ (foldBox_mem_unitBox u)),
    colPlane_apply β Q s u⟩

/-- A point of the square whose image under `sqDisk (foldBox ·)` is off the unit circle is a point off
the seam.  This is the conversion of the engine's one-face clause into the "off the seam" hypothesis of
the top-face avoidance. -/
lemma norm_sqDisk_foldBox_lt_one_of_ne_one {y : EuclideanSpace ℝ (Fin 2)}
    (h : ‖sqDisk (foldBox y)‖ ≠ 1) : ‖sqDisk (foldBox y)‖ < 1 :=
  lt_of_le_of_ne (norm_sqDisk_le_one _ (foldBox_mem_unitBox y)) h

/-! ## 1bis. The fold of an interior point of the square is off the seam

`foldFun z = (1 - cos (π z)) / 2` vanishes exactly at the even integers and equals `1` exactly at the
odd ones; so on `(0,1)` the fold takes neither value, and a square point whose two coordinates are
*strictly* interior has its `sqDisk`-image in the *open* disk.  This is the conversion of the engine's
one-face clause (`x j ∈ Ioo 0 1` for `j ≠ i`) into the "off the seam" hypotheses of the top-face
avoidance. -/

/-- The half-cosine fold does not vanish on the open interval `(0,1)`. -/
lemma foldFun_ne_zero_of_mem_Ioo {z : ℝ} (hz : z ∈ Set.Ioo 0 1) : foldFun z ≠ 0 := by
  intro h
  have h' : (1 - Real.cos (Real.pi * z)) / 2 = 0 := h
  have hc : Real.cos (Real.pi * z) = 1 := by linarith
  have hx : Real.pi * z = 0 := by
    refine (Real.cos_eq_one_iff_of_lt_of_lt ?_ ?_).mp hc
    · nlinarith [Real.pi_pos, hz.1]
    · nlinarith [Real.pi_pos, hz.2]
  nlinarith [Real.pi_pos, hz.1]

/-- The half-cosine fold does not equal `1` on the open interval `(0,1)`. -/
lemma foldFun_ne_one_of_mem_Ioo {z : ℝ} (hz : z ∈ Set.Ioo 0 1) : foldFun z ≠ 1 := by
  intro h
  have h' : (1 - Real.cos (Real.pi * z)) / 2 = 1 := h
  have hc : Real.cos (Real.pi * z) = -1 := by linarith
  have h1 : Real.cos (Real.pi - Real.pi * z) = 1 := by
    rw [Real.cos_pi_sub, hc]
    ring
  have hx : Real.pi - Real.pi * z = 0 := by
    refine (Real.cos_eq_one_iff_of_lt_of_lt ?_ ?_).mp h1
    · nlinarith [Real.pi_pos, hz.2]
    · nlinarith [Real.pi_pos, hz.1]
  nlinarith [Real.pi_pos, hz.2]

/-- A square point with both coordinates strictly interior is off the seam after folding. -/
lemma not_onSeam2_foldBox_of_mem_Ioo {y : EuclideanSpace ℝ (Fin 2)}
    (h0 : y 0 ∈ Set.Ioo 0 1) (h1 : y 1 ∈ Set.Ioo 0 1) : ¬ onSeam2 (foldBox y) := by
  rw [onSeam2, foldBox_apply_zero, foldBox_apply_one]
  rintro (h | h | h | h)
  · exact foldFun_ne_zero_of_mem_Ioo h0 h
  · exact foldFun_ne_one_of_mem_Ioo h0 h
  · exact foldFun_ne_zero_of_mem_Ioo h1 h
  · exact foldFun_ne_one_of_mem_Ioo h1 h

/-- **A square point with both coordinates strictly interior has its `sqDisk`-image in the open
disk.** -/
lemma norm_sqDisk_foldBox_lt_one_of_mem_Ioo {y : EuclideanSpace ℝ (Fin 2)}
    (h0 : y 0 ∈ Set.Ioo 0 1) (h1 : y 1 ∈ Set.Ioo 0 1) :
    ‖sqDisk (foldBox y)‖ < 1 := by
  refine lt_of_le_of_ne (norm_sqDisk_le_one _ (foldBox_mem_unitBox y)) ?_
  intro hEq
  exact not_onSeam2_foldBox_of_mem_Ioo h0 h1
    ((norm_sqDisk_eq_one_iff _ (foldBox_mem_unitBox y)).mp hEq)

/-! ## 2. The two level faces -/

/-- **The top face of a clamped sweep does not meet the collapsed plane.**  At `y 2 = 1` the sweep is
the plane `P (mk2 (y 0) (y 1))` (`clampedSweep_face_one`), the collapsed plane's value is `Q z` with
`‖z‖ ≤ 1`, and the two cap-disjointness hypotheses (`hcap` on the open disks, `hcirc` for the chart's
boundary circle against the open disk) exclude the equation — provided the sweep's own point is off the
seam of its square. -/
theorem colPlane_ne_clampedSweep_top {β : ℝ → ℝ} (hβpos : ∀ t : ℝ, 0 < β t)
    (hβ : ∀ t : ℝ, Real.sqrt t ≤ β t) {c : ℝ} {ψ : ℝ → ℝ} (hψ1 : ψ 1 = 0)
    {Q : ℂ → CappingSpace} {P : EuclideanSpace ℝ (Fin 2) → CappingSpace}
    (hcap : ∀ (z : ℂ) (y : EuclideanSpace ℝ (Fin 2)),
      ‖z‖ < 1 → ‖sqDisk (foldBox y)‖ < 1 → Q z ≠ P y)
    (hcirc : ∀ (z : ℂ) (y : EuclideanSpace ℝ (Fin 2)),
      ‖z‖ = 1 → ‖sqDisk (foldBox y)‖ < 1 → Q z ≠ P y)
    (s : ℝ) (u : EuclideanSpace ℝ (Fin 2)) (y : EuclideanSpace ℝ (Fin 3))
    (hy2 : y 2 = 1) (hwy : ‖sqDisk (foldBox (mk2 (y 0) (y 1)))‖ < 1) :
    colPlane β Q s u ≠ clampedSweep c ψ P y := by
  intro h
  rw [clampedSweep_face_one c ψ P hψ1 y hy2] at h
  rw [colPlane_apply] at h
  have hz : ‖colMap β s (sqDisk (foldBox u))‖ ≤ 1 :=
    norm_colMap_le_one hβpos hβ s _ (norm_sqDisk_le_one _ (foldBox_mem_unitBox u))
  rcases lt_or_eq_of_le hz with hlt | heq
  · exact hcap _ _ hlt hwy h
  · exact hcirc _ _ heq hwy h

/-- **The floor of a clamped sweep does not meet the collapsed plane.**  At `y 2 = 0` the sweep is the
shadow of the plane on the level `c` (`clampedSweep_face_zero`), whose level is `c` (`levelOf_shadow`),
while the collapsed plane's level is the level of `Q` at a point of the closed disk, which is `≠ c` by
the truncation bound `hlev` ("the floors lie below the levels").  No disjointness hypothesis is
needed. -/
theorem colPlane_ne_clampedSweep_floor {β : ℝ → ℝ} (hβpos : ∀ t : ℝ, 0 < β t)
    (hβ : ∀ t : ℝ, Real.sqrt t ≤ β t) {c : ℝ} (hc : 0 < c) {ψ : ℝ → ℝ} (hψ0 : ψ 0 = 1)
    {Q : ℂ → CappingSpace} {P : EuclideanSpace ℝ (Fin 2) → CappingSpace}
    (hlev : ∀ z : ℂ, ‖z‖ ≤ 1 → levelOf (Q z) ≠ c)
    (s : ℝ) (u : EuclideanSpace ℝ (Fin 2)) (y : EuclideanSpace ℝ (Fin 3)) (hy2 : y 2 = 0) :
    colPlane β Q s u ≠ clampedSweep c ψ P y := by
  intro h
  rw [clampedSweep_face_zero c hc ψ P hψ0 y hy2] at h
  have hlv : levelOf (colPlane β Q s u) = c := by rw [h, levelOf_shadow c hc]
  rw [colPlane_apply] at hlv
  exact hlev _ (norm_colMap_le_one hβpos hβ s _
    (norm_sqDisk_le_one _ (foldBox_mem_unitBox u))) hlv

/-- **The top face of a clamped sweep does not meet the uncollapsed plane.**  The same statement as
`colPlane_ne_clampedSweep_top` for the *second* block of the pair count (the plane `diskPlane Q`), whose
chart preimage is `sqDisk (foldBox u)` with `‖·‖ ≤ 1` — so only the closed-disk form of the cap
disjointness is needed. -/
theorem diskPlane_ne_clampedSweep_top {c : ℝ} {ψ : ℝ → ℝ} (hψ1 : ψ 1 = 0)
    {Q : ℂ → CappingSpace} {P : EuclideanSpace ℝ (Fin 2) → CappingSpace}
    (hcap : ∀ (z : ℂ) (y : EuclideanSpace ℝ (Fin 2)),
      ‖z‖ ≤ 1 → ‖sqDisk (foldBox y)‖ < 1 → Q z ≠ P y)
    (u : EuclideanSpace ℝ (Fin 2)) (y : EuclideanSpace ℝ (Fin 3))
    (hy2 : y 2 = 1) (hwy : ‖sqDisk (foldBox (mk2 (y 0) (y 1)))‖ < 1) :
    diskPlane Q u ≠ clampedSweep c ψ P y := by
  intro h
  rw [clampedSweep_face_one c ψ P hψ1 y hy2] at h
  rw [diskPlane_apply] at h
  exact hcap _ _ (norm_sqDisk_le_one _ (foldBox_mem_unitBox u)) hwy h

/-- **The floor of a clamped sweep does not meet the uncollapsed plane**: the second block's version of
`colPlane_ne_clampedSweep_floor`. -/
theorem diskPlane_ne_clampedSweep_floor {c : ℝ} (hc : 0 < c) {ψ : ℝ → ℝ} (hψ0 : ψ 0 = 1)
    {Q : ℂ → CappingSpace} {P : EuclideanSpace ℝ (Fin 2) → CappingSpace}
    (hlev : ∀ z : ℂ, ‖z‖ ≤ 1 → levelOf (Q z) ≠ c)
    (u : EuclideanSpace ℝ (Fin 2)) (y : EuclideanSpace ℝ (Fin 3)) (hy2 : y 2 = 0) :
    diskPlane Q u ≠ clampedSweep c ψ P y := by
  intro h
  rw [clampedSweep_face_zero c hc ψ P hψ0 y hy2] at h
  have hlv : levelOf (diskPlane Q u) = c := by rw [h, levelOf_shadow c hc]
  rw [diskPlane_apply] at hlv
  exact hlev _ (norm_sqDisk_le_one _ (foldBox_mem_unitBox u)) hlv

/-! ## 3. The avoidances in the form the pair count consumes -/

/-- **`havY` and `havZ` of the collapse pair count.**  At a meet of the collapse pair — the collapsed
plane meeting the sweep `V = clampedSweep c ψ P₁` and the uncollapsed plane meeting the sweep
`W = clampedSweep c ψ P₂` — neither sweep sits on its level faces, provided the two cap-disjointness
hypotheses for `P₁` and the level bound hold, and provided the meets are not at corners (the two "off
the seam" hypotheses `hwy`, `hwz`, which the engine's one-face clause supplies). -/
theorem colMeet_level_face_avoid {β : ℝ → ℝ} (hβpos : ∀ t : ℝ, 0 < β t)
    (hβ : ∀ t : ℝ, Real.sqrt t ≤ β t) {c : ℝ} (hc : 0 < c) {ψ : ℝ → ℝ}
    (hψ0 : ψ 0 = 1) (hψ1 : ψ 1 = 0) {Q : ℂ → CappingSpace}
    {P₁ P₂ : EuclideanSpace ℝ (Fin 2) → CappingSpace}
    (hcap₁ : ∀ (z : ℂ) (y : EuclideanSpace ℝ (Fin 2)),
      ‖z‖ < 1 → ‖sqDisk (foldBox y)‖ < 1 → Q z ≠ P₁ y)
    (hcirc₁ : ∀ (z : ℂ) (y : EuclideanSpace ℝ (Fin 2)),
      ‖z‖ = 1 → ‖sqDisk (foldBox y)‖ < 1 → Q z ≠ P₁ y)
    (hcap₂ : ∀ (z : ℂ) (y : EuclideanSpace ℝ (Fin 2)),
      ‖z‖ ≤ 1 → ‖sqDisk (foldBox y)‖ < 1 → Q z ≠ P₂ y)
    (hlev : ∀ z : ℂ, ‖z‖ ≤ 1 → levelOf (Q z) ≠ c)
    (s : ℝ) (p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 3) ×
      EuclideanSpace ℝ (Fin 3))
    (hp : p ∈ colMeet β Q (clampedSweep c ψ P₁) (clampedSweep c ψ P₂) s)
    (hwy : ‖sqDisk (foldBox (mk2 (p.2.1 0) (p.2.1 1)))‖ < 1)
    (hwz : ‖sqDisk (foldBox (mk2 (p.2.2 0) (p.2.2 1)))‖ < 1) :
    p.2.1 2 ≠ 0 ∧ p.2.1 2 ≠ 1 ∧ p.2.2 2 ≠ 0 ∧ p.2.2 2 ≠ 1 := by
  obtain ⟨_hp1, hp2, hp3, hpV, hpW⟩ := hp
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    exact (colPlane_ne_clampedSweep_floor hβpos hβ hc hψ0 hlev s p.1 p.2.1 h) hpV
  · intro h
    exact (colPlane_ne_clampedSweep_top hβpos hβ hψ1 hcap₁ hcirc₁ s p.1 p.2.1 h hwy) hpV
  · intro h
    exact (diskPlane_ne_clampedSweep_floor hc hψ0 hlev p.1 p.2.2 h) hpW
  · intro h
    exact (diskPlane_ne_clampedSweep_top hψ1 hcap₂ p.1 p.2.2 h hwz) hpW

end

end Work.Drive
