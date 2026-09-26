import Submission.Work.PinchCounted.Counted
import Submission.Work.BoxShrink.counting

/-!
# The counting bridge

Pardon's Lemma 2 (`mustbeinessential`): *if a sphere transverse to `F` meets the knot `β` in fewer
than `I(F,β)` points, then every curve of its trace is inessential in `F`.*  This module records it
in the three shapes in which the counted form of Pardon's Lemma 3 consumes it.

## 1. The engine

```
Work.PinchCounted.windingSpan_eq_bot_of_subset_of_count
```
**Any piece of the surface contained in a low-count sphere has vanishing winding span.**  This is the
lemma which turns Pardon's count `|S_t ∩ β| ≤ |S ∩ β| + 2|D ∩ β| < I(F,β)` at the intermediate
spheres of the pinching family into the span-preserving local models of
`Work.PinchCounted.PinchSweep`: every *changed piece* of the pinch is contained in an intermediate
trace, hence in a low-count sphere, hence carries no essential loop.

It is stated with two inputs: the innermost-disc input for the sphere (`CleansInSphere`, which the
workspace obtains from a slicing of the sphere and the cut-and-paste,
`Work.PinchCounted.not_containsEssentialLoop_of_slicing`), and the count.

## 2. The endpoints

* `Work.PinchCounted.sphereTrace_inessential_of_counts` — the box sphere `∂PBox s c σ` carries no
  essential loop, from the crux's sphere count and the general position of the sphere
  (`SlicedSphere`) and the cut-and-paste (`CleansDiscs`).  This is Pardon's Lemma 4.2 at the sphere
  (the sibling `Work.BoxShrink.Core.not_containsEssentialLoop_sphereSet_of_slicing`, re-exported
  with the vocabulary of this chapter);
* `Work.PinchCounted.sliceTrace_inessential_of_counts` — the flat slicing disc carries no essential
  loop, from the crux's plane count and the planar innermost input
  (`CleansInSphere (cutDisc s c σ u)`).

**Caveat (important for anyone re-using these).**  The planar innermost input
`CleansInSphere P (cutDisc s c σ u)` is *not* available at every plane level: the slice of the
**open** box is not transverse in the sense of `Work.Smooth.Plane.TransversePlane`
(`Work.PlaneSlice.not_ae_transversePlane_pardonSlice`), and the workspace proves the cleaning for
*almost every* level only (`Work.PlaneSlice.aeCleansPardonSlice`).  The counted form of Pardon's
Lemma 3 does **not** need it: Pardon's proof applies Lemma 2 to the intermediate *spheres*, never to
the slicing disc.  This is the precise sense in which
`Work.BoxShrink.Pinch.CountingHalf` is strictly more than
`Work.BoxShrink.Pinch.SmoothHalfS`; see `Main.lean`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

namespace Work.PinchCounted

noncomputable section

variable {P : Work.CoreTopology.ParamTorus}

/-! ## The engine -/

/-- **Pardon's Lemma 2 (`mustbeinessential`), in the form the counted pinch consumes.**

If `S` is a set of `ℝ³` whose trace with `F` can be cleaned (Pardon's innermost-disc input
`CleansInSphere`, obtained from a slicing of `S` together with the cut-and-paste) and which meets the
knot `β` in fewer than `I(F,β)` points, then `S` contains no essential loop of `F`. -/
theorem not_containsEssentialLoop_of_count (β : Work.CoreTopology.ClosedCurve P) (S : Set R3)
    (hclean : Work.InnermostDisk.CleansInSphere P S)
    (hcount : Set.encard (Set.range β.γ ∩ S) < Work.CoreTopology.pardonsI P β) :
    ¬ P.ContainsEssentialLoop S :=
  fun ⟨γ, hess, hγ⟩ =>
    Work.InnermostDisk.mustbeinessential_of_cleansInSphere P β S hclean hcount γ hγ hess

/-- **The innermost-disc input from a slicing of the sphere and the cut-and-paste.** -/
theorem cleansInSphere_of_slicing {S : Set R3} (hslice : Nonempty (Work.InnermostDisk.SphereSlicing P S))
    (hcl : Work.InnermostDisk.CleansDiscs P) : Work.InnermostDisk.CleansInSphere P S :=
  Work.InnermostDisk.cleansInSphere_of_inputs
    (Work.InnermostDisk.SphereSlicing.innermostDiscInput_of_slicing hslice.some) hcl

/-- **Pardon's Lemma 2 from a slicing.**  The same as `not_containsEssentialLoop_of_count`, with the
innermost-disc input *derived* from a general position datum for the sphere (a finiteness, nesting
and covering datum for `S ∩ F`) together with Pardon's cut-and-paste `CleansDiscs`. -/
theorem not_containsEssentialLoop_of_slicing (β : Work.CoreTopology.ClosedCurve P) {S : Set R3}
    (hslice : Nonempty (Work.InnermostDisk.SphereSlicing P S))
    (hcl : Work.InnermostDisk.CleansDiscs P)
    (hcount : Set.encard (Set.range β.γ ∩ S) < Work.CoreTopology.pardonsI P β) :
    ¬ P.ContainsEssentialLoop S :=
  not_containsEssentialLoop_of_count β S (cleansInSphere_of_slicing (P := P) hslice hcl) hcount

/-- **The engine in span form: every piece of the surface inside a low-count sphere is
inessential.**  This is what turns Pardon's inequality `|S_t ∩ β| ≤ |S ∩ β| + 2|D ∩ β| < I(F,β)` at
the intermediate spheres of the pinching family into the span-preserving local models of
`Work.PinchCounted.PinchSweep`: each changed piece `Y` of the pinch is contained in the trace of the
intermediate sphere, which is inessential, so `WindingSpan P Y = ⊥`. -/
theorem windingSpan_eq_bot_of_subset_of_count (β : Work.CoreTopology.ClosedCurve P) {S Y : Set R3}
    (hclean : Work.InnermostDisk.CleansInSphere P S)
    (hcount : Set.encard (Set.range β.γ ∩ S) < Work.CoreTopology.pardonsI P β) (hYS : Y ⊆ S) :
    Work.SurgeryInvariance.WindingSpan P Y = ⊥ := by
  have hbot : Work.SurgeryInvariance.WindingSpan P S = ⊥ :=
    (Work.SurgeryInvariance.WindingSpan_eq_bot_iff P S).mpr
      (not_containsEssentialLoop_of_count β S hclean hcount)
  exact le_antisymm (hbot ▸ Work.SurgeryInvariance.WindingSpan_mono P hYS) bot_le

/-- **The number of intersection points only decreases when the set shrinks** — the elementary step
by which Pardon's inequality at a sphere is transferred to a piece of that sphere. -/
theorem encard_inter_le_of_subset {β : Work.CoreTopology.ClosedCurve P} {Y S : Set R3}
    (h : Y ⊆ S) : Set.encard (Set.range β.γ ∩ Y) ≤ Set.encard (Set.range β.γ ∩ S) :=
  Set.encard_mono (Set.inter_subset_inter_right _ h)

/-- **The count transfers to subsets.**  A subset of a low-count sphere satisfies the count
hypothesis whenever the sphere does. -/
theorem count_of_subset_of_count {β : Work.CoreTopology.ClosedCurve P} {Y S : Set R3}
    (hcount : Set.encard (Set.range β.γ ∩ S) < Work.CoreTopology.pardonsI P β) (h : Y ⊆ S) :
    Set.encard (Set.range β.γ ∩ Y) < Work.CoreTopology.pardonsI P β :=
  lt_of_le_of_lt (encard_inter_le_of_subset h) hcount

/-! ## The two endpoints of the counted configuration -/

/-- **The box sphere carries no essential loop**, from the crux's sphere count, the general position
of the sphere and Pardon's cut-and-paste.  (`Work.BoxShrink.Core.not_containsEssentialLoop_sphereSet_of_slicing`
with `torus ψ = ParamTorus.mapHomeomorph ψ.toHomeomorph`.) -/
theorem sphereTrace_inessential_of_counts (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hc : Nat.Coprime p q) (ψ : Submission.Diffeo) (K : Knot) {d : ℝ} (hd : 0 ≤ d)
    (himg : Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ)
    (hsmall : Submission.countConst * d < (Nat.min p q : ℝ))
    {s : ℝ} (hs : 0 < s) (c : R3) (σ : Equiv.Perm (Fin 3))
    (hslice : Work.BoxShrink.SlicedSphere (Work.Smooth.Morse.torus ψ)
      {y : R3 | Submission.boxNorm c σ y = s})
    (hcl : Work.InnermostDisk.CleansDiscs (Work.Smooth.Morse.torus ψ))
    (hcount : ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        Submission.boxNorm c σ (K.curve t) = s}) : ENNReal)
      ≤ ENNReal.ofReal (10 * (1 + Submission.eps) / Submission.eps * d))) :
    ¬ (Work.Smooth.Morse.torus ψ).ContainsEssentialLoop (Work.BoxShrink.Core.sphereSet c σ s) :=
  Work.BoxShrink.Core.not_containsEssentialLoop_sphereSet_of_slicing p q hp hq hc ψ K hd himg
    hsmall hs c σ hslice hcl hcount

/-- **The flat slicing disc carries no essential loop**, from the crux's plane count and the planar
innermost input at that disc. -/
theorem sliceTrace_inessential_of_counts (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hc : Nat.Coprime p q) (ψ : Submission.Diffeo) (K : Knot) {d : ℝ} (hd : 0 ≤ d)
    (himg : Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ)
    (hsmall : Submission.countConst * d < (Nat.min p q : ℝ))
    {s : ℝ} (hs : 0 < s) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    (hclean : Work.InnermostDisk.CleansInSphere (Work.Smooth.Morse.torus ψ)
      (Work.BoxShrink.Core.cutDisc s c σ u))
    (hcount : ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        K.curve t ∈ Submission.PBox s c σ ∧ (K.curve t) (σ 2) = c (σ 2) + u}) : ENNReal)
      ≤ ENNReal.ofReal (5 * (1 + Submission.eps) / Submission.eps * d))) :
    ¬ (Work.Smooth.Morse.torus ψ).ContainsEssentialLoop
      (Work.BoxShrink.Core.sliceRegion (Work.Smooth.Morse.torus ψ) s c σ u) :=
  Work.BoxShrink.Core.not_containsEssentialLoop_sliceRegion p q hp hq hc ψ K hd himg hsmall hs
    c σ u hclean hcount

/-! ## The counting bookkeeping of the crux

The two counts of the swept box sphere and of the plane level, together with
`countConst · d < min p q = I(F,β)`, give *Pardon's inequality*
`|S ∩ β| + 2|D ∩ β| < I(F,β)` — the numerical content of Pardon's Step 2.  These are the sibling
chapter's `Work.BoxShrink.count_add_two_mul_lt` and its consequences, re-exported. -/

variable {p q : ℕ}

/-- **Pardon's inequality at the two endpoints**: the sphere count plus twice the plane count is
below `min p q = I(F,β)`. -/
theorem counts_add_two_mul_lt (hp : 0 < p) (hq : 0 < q) {K : Knot} {d : ℝ} (hd : 0 ≤ d)
    (hsmall : Submission.countConst * d < (Nat.min p q : ℝ)) {c : R3} {σ : Equiv.Perm (Fin 3)}
    {s u : ℝ}
    (hS : (Work.BoxShrink.sphCount K c σ s : ENNReal) ≤
      ENNReal.ofReal (10 * (1 + Submission.eps) / Submission.eps * d))
    (hD : (Work.BoxShrink.planeCount K c σ s u : ENNReal) ≤
      ENNReal.ofReal (5 * (1 + Submission.eps) / Submission.eps * d)) :
    (Work.BoxShrink.sphCount K c σ s : ENNReal) + 2 * (Work.BoxShrink.planeCount K c σ s u : ENNReal)
      < (Nat.min p q : ENNReal) :=
  Work.BoxShrink.count_add_two_mul_lt (lt_min hp hq) hd hsmall hS hD

/-- **The sphere count is below `I(F,β) = min p q`.** -/
theorem sphCount_lt_min (hp : 0 < p) (hq : 0 < q) {K : Knot} {d : ℝ} (hd : 0 ≤ d)
    (hsmall : Submission.countConst * d < (Nat.min p q : ℝ)) {c : R3} {σ : Equiv.Perm (Fin 3)}
    {s : ℝ}
    (hS : (Work.BoxShrink.sphCount K c σ s : ENNReal) ≤
      ENNReal.ofReal (10 * (1 + Submission.eps) / Submission.eps * d)) :
    Work.BoxShrink.sphCount K c σ s < (Nat.min p q : ℕ∞) :=
  Work.BoxShrink.sphCount_lt (lt_min hp hq) hd hsmall hS

/-- **The plane count is below `I(F,β) = min p q`.** -/
theorem planeCount_lt_min (hp : 0 < p) (hq : 0 < q) {K : Knot} {d : ℝ} (hd : 0 ≤ d)
    (hsmall : Submission.countConst * d < (Nat.min p q : ℝ)) {c : R3} {σ : Equiv.Perm (Fin 3)}
    {s u : ℝ}
    (hD : (Work.BoxShrink.planeCount K c σ s u : ENNReal) ≤
      ENNReal.ofReal (5 * (1 + Submission.eps) / Submission.eps * d)) :
    Work.BoxShrink.planeCount K c σ s u < (Nat.min p q : ℕ∞) :=
  Work.BoxShrink.planeCount_lt (lt_min hp hq) hd hsmall hD

end

end Work.PinchCounted
