import Submission.Work.BoxShrink.Bubble.PardonLocalModel
import Submission.Work.SurgeryInvariance.WindingSpan.carrier_eq_top
import Submission.Work.BoxShrink.Bubble.cex_windingSpan_boxRegion_eq_top

/-!
# The API of Pardon's dichotomy

`Work.BoxShrink.Bubble.PardonDichotomy P X` (`WindingSpan P X = ⊥ ∨ WindingSpan P X = ⊤`) is the
geometric input that Pardon's counting hypothesis supplies at every intermediate sphere of the
pinching family, and it is the only hypothesis of the corrected input
`Work.BoxShrink.Bubble.PardonPinchInput` beyond the shape of the family
(`Work.BoxShrink.Bubble.PinchDatum`).  This file collects the elementary closure properties of the
dichotomy, which are what a caller needs to assemble it sphere by sphere:

* `Work.BoxShrink.Bubble.pardonDichotomy_empty`, `…_carrier` — the two basic cases;
* `Work.BoxShrink.Bubble.pardonDichotomy_union` — **the dichotomy is preserved by unions of disjoint
  open pieces of the surface** (because the winding span of a union of disjoint open pieces is the
  supremum of the spans, `Work.SurgeryInvariance.Span.union_eq_sup`, and a supremum of two elements
  of `{⊥, ⊤}` lies in `{⊥, ⊤}`); this is the step that turns the dichotomy of the two members of a
  double bubble into the dichotomy of its inside;
* `Work.BoxShrink.Bubble.pardonDichotomy_of_subset_of_span_eq_top` — if a piece of the region already
  carries the whole of `H₁(F; ℚ)`, so does the region (monotonicity);
* `Work.BoxShrink.Bubble.pardonDichotomy_congr` — the dichotomy is a property of the region only;
* `Work.BoxShrink.Bubble.pardonDichotomy_boxRegion_of_carrier_subset` — **Pardon's dichotomy at the
  initial sphere `∂PBox` when the box contains the whole surface** (then the region inside the box is
  the whole surface and its winding span is `⊤`): a configuration where the hypothesis `hS` of the
  field holds and the dichotomy is a theorem;
* `Work.BoxShrink.Bubble.pardonDichotomy_boxRegion_of_disjoint` — the degenerate case in which the
  box misses the surface entirely;
* `Work.BoxShrink.Bubble.pardonDichotomy_boxRegion_of_empty_sphereTrace` — the dichotomy at the
  initial sphere whenever the box boundary misses the surface (`F ∩ sphereSet c σ s = ∅`), which
  covers both of the previous cases at once and is the case of the first sub-target of `PLAN.md` in
  which the hypothesis `hS` holds trivially; its proof uses the new
  `Work.BoxShrink.Bubble.isPreconnected_carrier` (the surface of a parametrised torus is connected,
  being the continuous image of the parameter plane), `Work.BoxShrink.Bubble.isOpen_PBox` and
  `Work.BoxShrink.Bubble.continuous_boxNorm`.

The remaining content — the dichotomy for an arbitrary sphere `S` transverse to `F` with `F ∩ S` a
union of inessential curves — is the surface-theoretic input discussed in `README.md`/`PLAN.md`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.Bubble

noncomputable section

variable {P : Work.CoreTopology.ParamTorus}

/-- The empty region satisfies the dichotomy (it realises no winding vector). -/
theorem pardonDichotomy_empty : PardonDichotomy P (∅ : Set R3) :=
  Or.inl windingSpan_empty

/-- The whole surface satisfies the dichotomy (`Work.SurgeryInvariance.WindingSpan.carrier_eq_top`):
its two basic curves exhibit the generators `(1,0)`, `(0,1)` of `H₁(T²; ℚ)`. -/
theorem pardonDichotomy_carrier : PardonDichotomy P P.carrier :=
  Or.inr (Work.SurgeryInvariance.WindingSpan.carrier_eq_top P)

/-- **The dichotomy is preserved by unions of disjoint open pieces of the surface.**  The winding
span of such a union is the supremum of the two spans
(`Work.SurgeryInvariance.Span.union_eq_sup`), and a supremum of two elements of `{⊥, ⊤}` is again
`⊥` or `⊤`. -/
theorem pardonDichotomy_union {X Y : Set R3}
    (hXo : Work.SurgeryInvariance.IsOpenInCarrier P X)
    (hYo : Work.SurgeryInvariance.IsOpenInCarrier P Y) (hd : Disjoint X Y)
    (hX : PardonDichotomy P X) (hY : PardonDichotomy P Y) :
    PardonDichotomy P (X ∪ Y) := by
  unfold PardonDichotomy
  rw [Work.SurgeryInvariance.Span.union_eq_sup hXo hYo hd]
  rcases hX with h | h <;> rcases hY with h' | h' <;> rw [h, h'] <;> simp

/-- The dichotomy is invariant under replacing the region by an equal set. -/
theorem pardonDichotomy_congr {X Y : Set R3} (h : X = Y) (hX : PardonDichotomy P X) :
    PardonDichotomy P Y :=
  h ▸ hX

/-- If a piece of a region already realises the whole of `H₁(F; ℚ)`, so does the region
(monotonicity of the winding span). -/
theorem pardonDichotomy_of_subset_of_span_eq_top {X Y : Set R3} (hXY : X ⊆ Y)
    (hX : Work.SurgeryInvariance.WindingSpan P X = ⊤) : PardonDichotomy P Y :=
  Or.inr (top_le_iff.mp (hX ▸ Work.SurgeryInvariance.WindingSpan_mono P hXY))

/-- **Pardon's dichotomy at the initial sphere, when the box contains the whole surface**: the
region inside the box is then the whole surface. -/
theorem pardonDichotomy_boxRegion_of_carrier_subset {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)}
    (h : P.carrier ⊆ Submission.PBox s c σ) :
    PardonDichotomy P (Work.BoxShrink.Core.boxRegion P s c σ) := by
  unfold PardonDichotomy
  have hbox : Work.BoxShrink.Core.boxRegion P s c σ = P.carrier := by
    rw [Work.BoxShrink.Core.boxRegion]
    exact Set.inter_eq_left.mpr h
  rw [hbox]
  exact Or.inr (Work.SurgeryInvariance.WindingSpan.carrier_eq_top P)

/-- Pardon's dichotomy at the initial sphere, in the degenerate case in which the box misses the
surface. -/
theorem pardonDichotomy_boxRegion_of_disjoint {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)}
    (h : Disjoint P.carrier (Submission.PBox s c σ)) :
    PardonDichotomy P (Work.BoxShrink.Core.boxRegion P s c σ) := by
  unfold PardonDichotomy
  rw [Work.BoxShrink.Core.boxRegion, Set.disjoint_iff_inter_eq_empty.mp h]
  exact Or.inl windingSpan_empty

/-- **At the counterexample configuration the region inside the box satisfies Pardon's dichotomy**
(on the `⊤` side): its winding span is all of `H₁(F; ℚ)`, spanned by the longitude `{z = -1}` of
winding `(1,0)` and the meridian `{p.1 = π/2}` of winding `(0,1)`
(`Work.BoxShrink.Bubble.cex_windingSpan_boxRegion_eq_top`).

Together with `Work.BoxShrink.Bubble.cex_not_slicePushOffSpan` — which shows that the union of the
two half-regions has winding span at most `ℚ·(0,1)` at the same configuration — this completes the
span picture of the counterexample: the dichotomy of the *initial* region is a theorem, as Pardon's
counting hypothesis gives it, while the push-off fails because the *intermediate* spheres of the
pinch cut an essential meridian of the torus. -/
theorem cex_pardonDichotomy_boxRegion :
    PardonDichotomy Work.CoreTopology.standard
      (Work.BoxShrink.Core.boxRegion Work.CoreTopology.standard (5 / 2) 0
        (Equiv.swap (1 : Fin 3) 2)) :=
  Or.inr cex_windingSpan_boxRegion_eq_top

/-- **Pardon's dichotomy at the initial sphere in an intermediate range of box sizes.**  For
`σ = Equiv.swap 1 2`, `c = 0` and every `s ≥ 5/2` the region inside the box
`PBox s 0 (swap 1 2)` still contains both witness loops of the counterexample — the longitude
`{z = -1}` (winding `(1,0)`) and the meridian `{p.1 = π/2}` (winding `(0,1)`) — because the box
grows with `s`; hence its winding span is `⊤` and the dichotomy holds.

This is the regime in which the box genuinely cuts the surface (`|x| ≤ 3`, `|y| ≤ 3`, `|z| ≤ 1`),
i.e. the configuration of Pardon's pinch, as opposed to the degenerate case of
`pardonDichotomy_boxRegion_of_carrier_subset`.  It is the `⊤` branch of the first of the two
sub-targets of `PLAN.md` (the dichotomy at the initial sphere), verified in a whole family of
genuine configurations. -/
theorem pardonDichotomy_boxRegion_swap (s : ℝ) (hs : 5 / 2 ≤ s) :
    PardonDichotomy Work.CoreTopology.standard
      (Work.BoxShrink.Core.boxRegion Work.CoreTopology.standard s 0
        (Equiv.swap (1 : Fin 3) 2)) :=
  pardonDichotomy_of_subset_of_span_eq_top
    (X := Work.BoxShrink.Core.boxRegion Work.CoreTopology.standard (5 / 2) 0
      (Equiv.swap (1 : Fin 3) 2))
    (fun y hy => by
      obtain ⟨hc, hbox⟩ := Work.BoxShrink.Core.mem_boxRegion.mp hy
      refine ⟨hc, ?_⟩
      rw [Submission.mem_PBox_iff] at hbox ⊢
      exact lt_of_lt_of_le hbox hs)
    cex_windingSpan_boxRegion_eq_top

/-- **The surface of a parametrised torus is connected**: it is the continuous image of the
connected parameter plane `ℝ × ℝ`. -/
theorem isPreconnected_carrier (P : Work.CoreTopology.ParamTorus) :
    IsPreconnected P.carrier := by
  rw [Work.CoreTopology.ParamTorus.carrier]
  exact isPreconnected_range (f := fun p : ℝ × ℝ => P.psi p.1 p.2) P.cont

/-- The box norm is continuous. -/
theorem continuous_boxNorm (c : R3) (σ : Equiv.Perm (Fin 3)) :
    Continuous (Submission.boxNorm c σ) := by
  unfold Submission.boxNorm
  fun_prop

/-- Pardon's box is open. -/
theorem isOpen_PBox (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) :
    IsOpen (Submission.PBox s c σ) := by
  have h : Submission.PBox s c σ = {y : R3 | Submission.boxNorm c σ y < s} := by
    ext y; exact Submission.mem_PBox_iff s c σ y
  rw [h]
  exact isOpen_lt (continuous_boxNorm c σ) continuous_const

/-- **Pardon's dichotomy at the initial sphere when the box boundary misses the surface.**  If
`F ∩ sphereSet c σ s = ∅`, then the whole box lies on one side of `F`: either the box contains the
surface (and the region inside it is the whole surface, of winding span `⊤`) or it misses it
entirely (and the region is empty, of span `⊥`).  This is the connectedness of the torus, and it
generalises both `pardonDichotomy_boxRegion_of_carrier_subset` and
`pardonDichotomy_boxRegion_of_disjoint`; it is the case of the first sub-target of `PLAN.md` in which
the hypothesis `hS` holds with an empty trace. -/
theorem pardonDichotomy_boxRegion_of_empty_sphereTrace {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)}
    (h : P.carrier ∩ Work.BoxShrink.Core.sphereSet c σ s = ∅) :
    PardonDichotomy P (Work.BoxShrink.Core.boxRegion P s c σ) := by
  have hcont : Continuous (Submission.boxNorm c σ) := continuous_boxNorm c σ
  have hdisj : Disjoint (Submission.PBox s c σ) {y : R3 | Submission.boxNorm c σ y ≤ s}ᶜ := by
    rw [Set.disjoint_left]
    intro y hy hy'
    rw [Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hy'
    exact absurd ((Submission.mem_PBox_iff s c σ y).mp hy) (not_lt.mpr (le_of_lt hy'))
  have hcover : P.carrier ⊆
      Submission.PBox s c σ ∪ {y : R3 | Submission.boxNorm c σ y ≤ s}ᶜ := by
    intro y hy
    rcases lt_or_ge (Submission.boxNorm c σ y) s with hlt | hge
    · exact Or.inl ((Submission.mem_PBox_iff s c σ y).mpr hlt)
    · refine Or.inr ?_
      rw [Set.mem_compl_iff, Set.mem_setOf_eq, not_le]
      by_contra hle
      exact (Set.eq_empty_iff_forall_notMem.mp h) _
        ⟨hy, by
          rw [Work.BoxShrink.Core.mem_sphereSet]
          exact le_antisymm (le_of_not_gt hle) hge⟩
  rcases (isPreconnected_carrier P).subset_or_subset (isOpen_PBox s c σ)
      (isClosed_le hcont continuous_const).isOpen_compl hdisj hcover with hcase | hcase
  · exact pardonDichotomy_boxRegion_of_carrier_subset hcase
  · left
    have hbox : Work.BoxShrink.Core.boxRegion P s c σ = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro y hy
      obtain ⟨hyc, hyb⟩ := Work.BoxShrink.Core.mem_boxRegion.mp hy
      rw [Submission.mem_PBox_iff s c σ y] at hyb
      have hgt : s < Submission.boxNorm c σ y := by
        simpa [Set.mem_compl_iff, Set.mem_setOf_eq, not_le] using hcase hyc
      exact absurd hyb (not_lt.mpr (le_of_lt hgt))
    rw [hbox]
    exact windingSpan_empty

end

end Work.BoxShrink.Bubble
