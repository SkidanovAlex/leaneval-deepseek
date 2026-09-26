import Submission.Work.CoreTopology.Disk
import Submission.Work.CoreTopology.meridianCurve_boundsDisk
import Submission.Work.CoreTopology.longitudeCurve_boundsDisk
import Submission.Work.CoreTopology.encard_meridian_inter_standardCurve
import Submission.Work.CoreTopology.encard_longitude_inter_standardCurve
import Submission.Work.CoreTopology.Simplicity

/-!
# Pardon's invariant `I(F, β)` for the standard torus and the standard `(p,q)`-curve

For the standard torus of revolution with major radius `2` and minor radius `1` and the
standard `(p,q)`-curve `β`, Pardon's invariant `I(F, β)` — the minimum, over simple closed
curves `α` of `F` that bound an embedded disc whose interior is disjoint from `F`, of the
number of intersections of `α` with `β` — equals `min p q`.

The two ingredients of the computation are:

* the meridian circle and the longitude circle of the standard torus each bound an embedded
  disc lying in the complement of the torus (`meridianCurve_boundsDisk`,
  `longitudeCurve_boundsDisk`), and the meridian meets `β` in exactly `p` points while the
  longitude meets it in exactly `q` points (`encard_meridian_inter_standardCurve`,
  `encard_longitude_inter_standardCurve`).  Hence `I(F, β) ≤ min p q`;
* conversely, every compressing essential loop of the standard torus is homotopic in `F` to
  the meridian or to the longitude, and of the two classes the meridian has intersection
  number `p` and the longitude `q` with `β`; hence every such loop meets `β` at least
  `min p q` times, i.e. `min p q ≤ I(F, β)`.

The second ingredient is the geometric input; it is packaged below as the predicate
`CompressingLoopsMeetOften` (with its two named parts).  The first ingredient, and the
deductions, are proved outright.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.CoreTopology

noncomputable section

/-- The geometric input for the *lower* bound of `I(F, β)`: every compressing essential loop
of the standard torus meets the standard `(p,q)`-curve at least `min p q` times. -/
def CompressingLoopsMeetOften (p q : ℕ) : Prop :=
  ∀ α : ClosedCurve standard, IsSimple standard α → IsEssential standard α →
    BoundsDiskInComplement standard α →
    (Nat.min p q : ℕ∞) ≤ Set.encard (Set.range α.γ ∩ Set.range (standardCurve p q).γ)

/-- First part of the geometric input: every essential loop of the standard torus bounding a
disc in the complement of the torus has winding vector `(a, 0)` or `(0, b)`, i.e. is
homotopic in `F` to a multiple of the longitude or of the meridian. -/
def CompressingLoopsAreMeridianOrLongitude : Prop :=
  ∀ α : ClosedCurve standard, IsEssential standard α → BoundsDiskInComplement standard α →
    (∀ L : LiftOf standard α, (L.winding).2 = 0) ∨
      (∀ L : LiftOf standard α, (L.winding).1 = 0)

/-- Second part of the geometric input: an essential curve of the torus whose winding vector
is `(a, 0)` or `(0, b)` meets the standard `(p,q)`-curve at least `min p q` times (the
algebraic intersection number being `|a| q` resp. `|b| p`, and the geometric intersection
number being at least its absolute value). -/
def IntersectionLowerBound (p q : ℕ) : Prop :=
  ∀ α : ClosedCurve standard, IsSimple standard α → IsEssential standard α →
    ((∀ L : LiftOf standard α, (L.winding).2 = 0) ∨
      (∀ L : LiftOf standard α, (L.winding).1 = 0)) →
    (Nat.min p q : ℕ∞) ≤ Set.encard (Set.range α.γ ∩ Set.range (standardCurve p q).γ)

/-- The two parts of the geometric input combine to give `CompressingLoopsMeetOften`. -/
theorem compressingLoopsMeetOften_of (p q : ℕ)
    (h1 : CompressingLoopsAreMeridianOrLongitude) (h2 : IntersectionLowerBound p q) :
    CompressingLoopsMeetOften p q :=
  fun α hsimple hess hb => h2 α hsimple hess (h1 α hess hb)

/-- The meridian circle of the standard torus is a compressing essential loop meeting the
standard `(p,q)`-curve in exactly `p` points, whence `I(F, β) ≤ p`. -/
theorem pardonsI_le_p (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q) :
    pardonsI standard (standardCurve p q) ≤ (p : ℕ∞) := by
  have h := pardonsI_le (P := standard) (β := standardCurve p q)
    (meridianCurve_simple standard 0) (meridianCurve_essential standard 0)
    (meridianCurve_boundsDisk 0)
  rw [Set.inter_comm] at h
  rwa [encard_meridian_inter_standardCurve p q hp hq hc 0] at h

/-- The longitude circle of the standard torus is a compressing essential loop meeting the
standard `(p,q)`-curve in exactly `q` points, whence `I(F, β) ≤ q`. -/
theorem pardonsI_le_q (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q) :
    pardonsI standard (standardCurve p q) ≤ (q : ℕ∞) := by
  have h := pardonsI_le (P := standard) (β := standardCurve p q)
    (longitudeCurve_simple standard 0) (longitudeCurve_essential standard 0)
    (longitudeCurve_boundsDisk)
  rw [Set.inter_comm] at h
  rwa [encard_longitude_inter_standardCurve p q hp hq hc 0] at h

/-- **Pardon's invariant is at most `min p q` for the standard torus and the standard
`(p,q)`-curve**: the meridian and the longitude bound discs in the complement of the torus
and meet the curve in `p` resp. `q` points. -/
theorem pardonsI_le_min (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q) :
    pardonsI standard (standardCurve p q) ≤ (Nat.min p q : ℕ∞) := by
  rcases le_total p q with hpq | hpq
  · rw [show (Nat.min p q : ℕ∞) = (p : ℕ∞) by simp [Nat.min_eq_left hpq]]
    exact pardonsI_le_p p q hp hq hc
  · rw [show (Nat.min p q : ℕ∞) = (q : ℕ∞) by simp [Nat.min_eq_right hpq]]
    exact pardonsI_le_q p q hp hq hc

/-- The lower bound `min p q ≤ I(F, β)` follows from the geometric input
`CompressingLoopsMeetOften`. -/
theorem pardonsI_ge_min (p q : ℕ) (h : CompressingLoopsMeetOften p q) :
    (Nat.min p q : ℕ∞) ≤ pardonsI standard (standardCurve p q) :=
  le_pardonsI fun α hsimple hess hb => h α hsimple hess hb

/-- **Pardon's invariant for the standard torus and the standard `(p,q)`-curve.**
Assuming the geometric input `CompressingLoopsMeetOften` (every compressing essential loop
meets the standard `(p,q)`-curve at least `min p q` times), we have `I(F, β) = min p q`. -/
theorem pardonsI_standard_of_input (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q)
    (h : CompressingLoopsMeetOften p q) :
    pardonsI standard (standardCurve p q) = (Nat.min p q : ℕ∞) :=
  le_antisymm (pardonsI_le_min p q hp hq hc) (pardonsI_ge_min p q h)

/-- `pardonsI_standard`, with the geometric input split into its two named parts. -/
theorem pardonsI_standard_of (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q)
    (h1 : CompressingLoopsAreMeridianOrLongitude) (h2 : IntersectionLowerBound p q) :
    pardonsI standard (standardCurve p q) = (Nat.min p q : ℕ∞) :=
  pardonsI_standard_of_input p q hp hq hc (compressingLoopsMeetOften_of p q h1 h2)

/-- If the classification of compressing loops is available, the only remaining input for
`I(F, β) = min p q` is the intersection-number inequality `IntersectionLowerBound`. -/
theorem pardonsI_standard_of_classification (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hc : Nat.Coprime p q) (hclass : CompressingLoopsAreMeridianOrLongitude)
    (hint : IntersectionLowerBound p q) :
    pardonsI standard (standardCurve p q) = (Nat.min p q : ℕ∞) :=
  pardonsI_standard_of p q hp hq hc hclass hint

end

end Work.CoreTopology
