import Submission.Work.PinchFamily.Defs

/-!
# The pinching family from the push-off

This module **builds the family of `Work.PinchCounted.CountedPinch`** from the push-off residual
`Work.PinchFamily.RegionPushOff` — the simplest of the three geometric inputs of `Defs.lean`.

The construction is Pardon's pinch in its crudest coordinates: the region is the region inside the
box for `t < 1`, and the two half-regions for `t ≥ 1`.  Every local move is then a transport of the
loop content (case 1 of `Work.PinchCounted.CountedStep`), provided by the push-off alone; in
particular the family has **no surgery**: the whole content of Pardon's Step 2 is in the single
statement that the two endpoint regions are `RegionEquivalent`.

Geometrically this is the right reading of Pardon's proof: the region `F ∩ int(S_t)` of the
intermediate spheres is a *continuous* deformation of the region inside the box, so its loop content
never changes; the only thing that changes is that the slice trace is pushed off onto the two
half-regions — which is exactly the push-off. -/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.PinchFamily

noncomputable section

variable {P : Work.CoreTopology.ParamTorus}

/-! ## The two-piece family -/

/-- **The crudest pinching family**: the region inside the box up to time `1`, and the two
half-regions from time `1` on. -/
def twoRegion (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (u : ℝ) : ℝ → Set R3 :=
  fun t => if t < 1 then box P s c σ else halves P s c σ u

theorem twoRegion_of_lt {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u t : ℝ} (ht : t < 1) :
    twoRegion P s c σ u t = box P s c σ := if_pos ht

theorem twoRegion_of_le {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u t : ℝ} (ht : 1 ≤ t) :
    twoRegion P s c σ u t = halves P s c σ u := if_neg (not_lt.mpr ht)

@[simp] theorem twoRegion_zero {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ} :
    twoRegion P s c σ u 0 = box P s c σ := twoRegion_of_lt zero_lt_one

@[simp] theorem twoRegion_one {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ} :
    twoRegion P s c σ u 1 = halves P s c σ u := twoRegion_of_le le_rfl

/-- **Every pair of values of the two-piece family is related by the push-off**, hence by
`RegionEquivalent`. -/
theorem regionEquivalent_twoRegion {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (h : RegionPushOff P s c σ u) (t r : ℝ) :
    Work.SurgeryInvariance.RegionEquivalent P (twoRegion P s c σ u t) (twoRegion P s c σ u r) := by
  rw [twoRegion, twoRegion]
  by_cases ht : t < 1
  · rw [if_pos ht]
    by_cases hr : r < 1
    · rw [if_pos hr]; exact Work.SurgeryInvariance.RegionEquivalent.refl (P := P) _
    · rw [if_neg hr]; exact h.symm
  · rw [if_neg ht]
    by_cases hr : r < 1
    · rw [if_pos hr]; exact h
    · rw [if_neg hr]; exact Work.SurgeryInvariance.RegionEquivalent.refl (P := P) _

/-- **Every local move of the two-piece family is a `CountedStep`** (case 1: a transport of the loop
content). -/
theorem countedStep_twoRegion {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (h : RegionPushOff P s c σ u) (β : Work.CoreTopology.ClosedCurve P) (t r : ℝ) :
    Work.PinchCounted.CountedStep P β (twoRegion P s c σ u t) (twoRegion P s c σ u r) :=
  Work.PinchCounted.CountedStep.of_regionEquivalent (regionEquivalent_twoRegion h t r)

/-- **The local moves of the two-piece family**, in the ε-form consumed by `CountedPinch`. -/
theorem twoRegion_localMoves {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (h : RegionPushOff P s c σ u) (β : Work.CoreTopology.ClosedCurve P) (t : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ r : ℝ, |r - t| < ε →
      Work.PinchCounted.CountedStep P β (twoRegion P s c σ u t) (twoRegion P s c σ u r) :=
  ⟨1, one_pos, fun r _ => countedStep_twoRegion h β t r⟩

/-! ## The family exists whenever the push-off does -/

/-- **The push-off gives the local family of `CountedPinch`.**  The two-piece family starts at the
box region, ends at the two half-regions (with the empty extra piece), and all its local moves are
`CountedStep`s. -/
theorem exists_region_of_regionPushOff {P : Work.CoreTopology.ParamTorus}
    (β : Work.CoreTopology.ClosedCurve P) {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (h : RegionPushOff P s c σ u) : LocalFamilyBody P β s c σ u :=
  ⟨twoRegion P s c σ u, twoRegion_zero,
    ⟨∅, Work.BoxShrink.Pinch.isOpenInCarrier_empty P, Work.BoxShrink.Pinch.windingSpan_empty P,
      by simp, by rw [twoRegion_one, Set.union_empty]⟩,
    fun t => twoRegion_localMoves h β t⟩

/-- The push-off gives the local family (the name used by the cross-links of this area). -/
theorem localFamilyBody_of_regionPushOff {P : Work.CoreTopology.ParamTorus}
    (β : Work.CoreTopology.ClosedCurve P) {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (h : RegionPushOff P s c σ u) : LocalFamilyBody P β s c σ u :=
  exists_region_of_regionPushOff β h

end

end Work.PinchFamily
