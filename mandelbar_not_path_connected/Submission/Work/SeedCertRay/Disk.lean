/-
# SeedCertRay — disk (centre + radius) certificate layer

The chain certificate of `chain_sound` is phrased for arbitrary closed sets, but the boxes of
`Basic.lean` are a poor enclosure of a *radial* piece of a ray: the level-0 piece is the segment
`[ρ 1 · d, ρ 0 · d]`, whose axis-parallel bounding box is fat for a diagonal direction, and the
fatness only halves per level, so the box chain stalls (see `NOTES.md` §2).  A **disk** enclosure
is tight for a segment (radius = half the length) and the disk-to-disk preimage estimate is
sharp; the pieces are then covered by a *finite union* of disks (one per sub-piece), which is
what this module provides.

* `Work.SeedCertRay.Disk` : centre `(cx, cy) ∈ ℚ²` and radius `r ∈ ℚ`; `Disk.mem`, `Disk.toSet`,
  `Disk.neg`, `Disk.center`, `Disk.rad`.
* `Work.SeedCertRay.diskUnion` : the union of a `Fin N`-indexed family of disks (the sets
  `C k j` of the chain).
* `Work.SeedCertRay.segSubdisks` : the standard covering of a radial piece by `N` sub-disks,
  used in (D0).
-/
import Mathlib
import Submission.Work.SeedCertRay.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

namespace Work.SeedCertRay

open Classical Set Function Filter
open scoped Topology ComplexConjugate

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-- A closed disk with rational centre and radius. -/
structure Disk where
  cx : ℚ
  cy : ℚ
  r : ℚ

namespace Disk

/-- The centre of a disk as a complex number. -/
def center (D : Disk) : ℂ := ((D.cx : ℝ) : ℂ) + ((D.cy : ℝ) : ℂ) * Complex.I

/-- Membership. -/
def mem (D : Disk) (z : ℂ) : Prop := ‖z - D.center‖ ≤ (D.r : ℝ)

/-- The underlying closed set. -/
def toSet (D : Disk) : Set ℂ := {z | D.mem z}

@[simp] theorem mem_toSet {D : Disk} {z : ℂ} : z ∈ D.toSet ↔ D.mem z := Iff.rfl

/-- The reflection of a disk. -/
def neg (D : Disk) : Disk := ⟨-D.cx, -D.cy, D.r⟩

@[simp] theorem neg_center (D : Disk) : D.neg.center = -D.center := by
  simp [neg, center, Complex.ext_iff]

theorem mem_neg {D : Disk} {z : ℂ} : D.neg.mem z ↔ D.mem (-z) := by
  rw [mem, mem, neg_center]
  have h : z - -D.center = -(-z - D.center) := by ring
  rw [h, norm_neg]
  simp only [Disk.neg]

theorem neg_toSet (D : Disk) : D.neg.toSet = -D.toSet := by
  ext z
  rw [mem_toSet, Set.mem_neg, mem_neg]
  exact mem_toSet.symm

end Disk

/-- **Condition (D1) with disk enclosures**: the two-valued preimage of the disk `D` under
`T_c`, with the parameter `c` running over the box `X`, is covered by `E` and `-E`. -/
def DiskCover (D : Disk) (X : Box) (E : Disk) : Prop :=
  ∀ z c u : ℂ, D.mem z → X.mem c → Tantibar c u = z → E.mem u ∨ E.mem (-u)

/-- The open half-plane of direction `v`. -/
def halfplane (v : ℚ × ℚ) : Set ℂ := {z : ℂ | 0 < (v.1 : ℝ) * z.re + (v.2 : ℝ) * z.im}

/-- The union of a finite (`Fin N`-indexed) family of disks: the sets `C k j` of the chain. -/
def diskUnion {N : ℕ} (D : Fin N → Disk) : Set ℂ := ⋃ i, (D i).toSet

@[simp] theorem mem_diskUnion {N : ℕ} {D : Fin N → Disk} {z : ℂ} :
    z ∈ diskUnion D ↔ ∃ i, (D i).mem z := by
  simp [diskUnion]

/-- **The `N`-fold sub-disks of a radial piece.**  For a direction `d ∈ ℚ²`, the radial range
`[a, b]` (`0 ≤ a ≤ b`) and a tolerance `ε`, this is the family of disks centred on the midpoints
of `N` equal sub-intervals of `[a, b]` along the direction `d`, each of radius half the
sub-interval plus `ε`.  This is the (D0) covering: the piece of the ray at level 0 lies in the
union of these disks. -/
def segSubdisks (N : ℕ) (d : ℚ × ℚ) (a b ε : ℚ) : Fin N → Disk := fun i =>
  let t1 : ℚ := a + (b - a) * (i : ℕ) / N
  let t2 : ℚ := a + (b - a) * ((i : ℕ) + 1) / N
  ⟨d.1 * (t1 + t2) / 2, d.2 * (t1 + t2) / 2, (t2 - t1) / 2 + ε⟩

end Work.SeedCertRay
