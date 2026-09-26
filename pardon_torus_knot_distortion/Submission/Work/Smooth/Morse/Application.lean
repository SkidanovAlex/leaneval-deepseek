import Mathlib
import Submission.Work.Smooth.Morse.Defs
import Submission.Work.Smooth.Morse.Banded
import Submission.Work.Smooth.Morse.Sweep
import Submission.Box
import Submission.Work.SurgeryInvariance.API

/-!
# Application: Pardon's two families (item 5)

This file records how the level-set machinery of this chapter feeds Pardon's argument, in the two
forms in which the paper uses it.  Both are *banded*: Pardon sweeps and pinches only within a
bounded band of scales and levels, and the global forms of these statements (with the hypotheses on
all of `ℝ`) are vacuous — see the module `Work.Smooth.Morse.Banded` and the README of the chapter.

## Pardon's box sweep

Pardon sweeps the self-similar family of boxes `PBox(t)` (`Submission.PBox`) through the surface and
shrinks the box.  To satisfy the smoothness hypotheses of the sweep one uses a *rounded* box: a
`C^∞` gauge `g` whose sublevel sets are smooth convex bodies sandwiched between Pardon's boxes,

`PBox(t) ⊆ {g < t} ⊆ PBox((1+δ) t)`

for a small room `δ > 0` (about `2%`, absorbed by the constants of the argument).  The regions of
the sweep are then exactly the sublevel sets `F ∩ {g < t}`, and

* `Work.Smooth.Morse.boxSweep_containsEssentialLoop_on` and
  `Work.Smooth.Morse.boxSweep_containsEssentialLoop_of_crossing_on` are Pardon's sweeping step
  **on the band `[a,b]` of scales actually swept**: if the box `PBox(t)` meets `F` in an essential
  loop, then so does `PBox((1+δ) s)` for every `s` in the band.

An explicit gauge with the sandwich exists: `Work.Smooth.Morse.boxGauge` (the `ℓ^{2k}` gauge of
Pardon's box) satisfies `PBox t ⊆ {boxGauge < 3^{1/(2k)} t}` and
`{boxGauge < t} ⊆ PBox t`, so the *renormalised* gauge `boxGauge / 3^{1/(2k)}` satisfies the
sandwich exactly, with the room `δ = 3^{1/(2k)} - 1 → 0`
(`Work.Smooth.Morse.Gauge.gaugeSandwich`).  The smoothing of `boxGauge` at the centre of the box
(which lies off the surface) is `Work.Smooth.Morse.Gauge.exists_smooth_gauge_of_not_mem_centre`, and
the two together are packaged as `Work.Smooth.Morse.Gauge.exists_smooth_gauge_with_sandwich`: a
`C^∞` gauge with `PBox(t) ⊆ {g < t} ⊆ PBox((1+δ) t)` for every `t`.

## Pardon's double bubble

`Work.SurgeryInvariance.double_bubble_persistence` is Pardon's Lemma 3 once the region inside the
original sphere is decomposed as the two half-boxes together with the piece cut out by the cutting
disc; `Work.Smooth.Morse.doubleBubble_containsEssentialLoop` states it in this chapter's vocabulary,
and `Work.Smooth.Morse.doubleBubble_containsEssentialLoop_of_split` /
`Work.Smooth.Morse.doubleBubble_containsEssentialLoop_of_regionEquivalent` state the two forms of
the decomposition which Pardon's geometry actually supplies (see the docstrings: the piece cut out
by the *plane* is a curve of the surface, not the interior of a disc of the surface, so the honest
input is a `RegionEquivalent` — the `SlicePushOff` of the sibling subproject
`Work.BoxShrink.Bubble`).

## Sharpness: the level family alone is not enough

`Work.Smooth.Morse.Application.levelSweep_span_not_const` shows that the persistence statement is
**false** for a raw level family: for the standard torus and a height coordinate the winding span of
`F ∩ {g < t}` jumps from `⊥` (empty region) to `⊤` (the whole torus), while `g` is smooth and has
locally finitely many critical values.  Consequently the hypotheses of the theorems above (the
crossing data, or a single `2`-surgery at each critical value) are not cosmetic: they encode exactly
what Pardon's family of spheres put in general position supplies, and where the change of the region
is by an *embedded disc of `F`* — the input `Work.SurgeryInvariance.SurgeryShape` of the sibling
subproject.  See the README of this chapter.

## What is *not* proved here

The existence of the gauge `g` together with the sandwich `PBox(t) ⊆ {g < t} ⊆ PBox((1+δ)t)`
(smoothing the corners of a box while keeping the constants) is pure convex geometry and is not
proved in this chapter, nor is the decomposition of the region inside the double bubble by the
cutting plane; both are recorded as hypotheses here and in the README.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.Smooth.Morse

noncomputable section

variable {a b : ℝ}

/-! ## Pardon's box sweep -/

/-- **Pardon's shrinking step for the box sweep, up to the room of the rounding, on a band.**

Let `g` be a gauge whose sublevel sets sandwich Pardon's boxes *on the swept band*
`[a,b] ∋ t ↦ PBox(t)`.  If the sweep data of the level family of `g` is available *on that band* —
the Morse/Sard input `LocallyFiniteCriticalValues`, the transport `RegularEquivalent` across
regular intervals, and the local model `DiscModel` at the critical values of the band — then an
essential loop in `F ∩ PBox(t)` produces one in `F ∩ PBox((1+δ) s)` for every `s ∈ [a,b]` with
`s ≤ t`.

The band is essential: with the sandwich and the local models imposed on all of `ℝ` the hypotheses
are contradictory (the span of the region would be both `⊥`, below the range of `g|_F`, and `⊤`,
above it).  Pardon sweeps only a bounded range of scales, and the general position of his family of
spheres is only controlled there. -/
theorem boxSweep_containsEssentialLoop_on (ψ : Submission.Diffeo) {c : R3} {σ : Equiv.Perm (Fin 3)}
    {g : R3 → ℝ} (hg : Continuous g)
    (hcrit : LocallyFiniteCriticalValues ψ g) (hreg : RegularEquivalent ψ g)
    (hdisc : ∀ t₀ ∈ criticalValues ψ g ∩ Set.Icc a b, DiscModel ψ g t₀) {δ : ℝ}
    (hlow : ∀ t ∈ Set.Icc a b, Submission.PBox t c σ ∩ (torus ψ).carrier ⊆ region ψ g t)
    (hup : ∀ t ∈ Set.Icc a b, region ψ g t ⊆ Submission.PBox ((1 + δ) * t) c σ)
    {s t : ℝ} (hs : s ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b) (_hst : s ≤ t)
    (h : (torus ψ).ContainsEssentialLoop (Submission.PBox t c σ ∩ (torus ψ).carrier)) :
    (torus ψ).ContainsEssentialLoop (Submission.PBox ((1 + δ) * s) c σ ∩ (torus ψ).carrier) := by
  have hgene : (torus ψ).ContainsEssentialLoop (region ψ g t) :=
    (torus ψ).containsEssentialLoop_mono (hlow t ht) h
  have hs' : (torus ψ).ContainsEssentialLoop (region ψ g s) :=
    (containsEssentialLoop_iff_of_levelSweep_on ψ hg hcrit hreg hdisc hs ht).mpr hgene
  obtain ⟨γ, hess, hmem⟩ := hs'
  exact ⟨γ, hess, fun u => ⟨hup s hs (hmem u), γ.mem u⟩⟩

/-- **Pardon's shrinking step for the box sweep, with the transport input discharged, on a band.**

For a `C^∞` gauge `g` the transport input of `Work.Smooth.Morse.boxSweep_containsEssentialLoop_on`
is supplied by the normalised gradient flow
(`Work.Smooth.Morse.regularEquivalent_of_contDiff`, item 3), so the only hypotheses left are the
Morse/Sard input, the local model at the critical values of the band, and the sandwich on the band.

This is the form of the sweeping step which is *not* vacuous: restricting the sandwich and the
local model to the swept band `Set.Icc a b` is exactly what Pardon's argument supplies. -/
theorem boxSweep_containsEssentialLoop_of_crossing_on (ψ : Submission.Diffeo) {c : R3}
    {σ : Equiv.Perm (Fin 3)} {g : R3 → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hcrit : LocallyFiniteCriticalValues ψ g)
    (hcross : ∀ t₀ ∈ criticalValues ψ g ∩ Set.Icc a b, ∃ ε : ℝ, 0 < ε ∧
      Work.SurgeryInvariance.WindingSpan (torus ψ) (region ψ g (t₀ - ε)) =
        Work.SurgeryInvariance.WindingSpan (torus ψ) (region ψ g (t₀ + ε))) {δ : ℝ}
    (hlow : ∀ t ∈ Set.Icc a b, Submission.PBox t c σ ∩ (torus ψ).carrier ⊆ region ψ g t)
    (hup : ∀ t ∈ Set.Icc a b, region ψ g t ⊆ Submission.PBox ((1 + δ) * t) c σ)
    {s t : ℝ} (hs : s ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b) (hst : s ≤ t)
    (h : (torus ψ).ContainsEssentialLoop (Submission.PBox t c σ ∩ (torus ψ).carrier)) :
    (torus ψ).ContainsEssentialLoop (Submission.PBox ((1 + δ) * s) c σ ∩ (torus ψ).carrier) := by
  have hgene : (torus ψ).ContainsEssentialLoop (region ψ g t) :=
    (torus ψ).containsEssentialLoop_mono (hlow t ht) h
  have hs' : (torus ψ).ContainsEssentialLoop (region ψ g s) :=
    containsEssentialLoop_of_levelSweep_of_crossing_on ψ hg hcrit hcross hs ht hst hgene
  obtain ⟨γ, hess, hmem⟩ := hs'
  exact ⟨γ, hess, fun u => ⟨hup s hs (hmem u), γ.mem u⟩⟩

/-! ## Pardon's double bubble -/

/-- **If a region splits into two disjoint open pieces, an essential loop lies in one of them.**

The winding span of `X ∪ Y` is the supremum of the two spans as soon as `X` and `Y` are open and
disjoint in the surface: a loop of the union cannot cross between the two pieces
(`Work.SurgeryInvariance.Span.union_eq_sup`).  This is the last step of Pardon's double bubble:
after the `2`-surgery the region inside the pinched sphere is the disjoint union of the two
half-regions, and an essential loop must lie in one of them. -/
theorem containsEssentialLoop_of_union (ψ : Submission.Diffeo) {Z₁ Z₂ : Set R3}
    (hopen₁ : Work.SurgeryInvariance.IsOpenInCarrier (torus ψ) Z₁)
    (hopen₂ : Work.SurgeryInvariance.IsOpenInCarrier (torus ψ) Z₂) (hdisj : Disjoint Z₁ Z₂)
    (h : (torus ψ).ContainsEssentialLoop (Z₁ ∪ Z₂)) :
    (torus ψ).ContainsEssentialLoop Z₁ ∨ (torus ψ).ContainsEssentialLoop Z₂ := by
  by_contra hcon
  rw [not_or] at hcon
  have hb₁ : Work.SurgeryInvariance.WindingSpan (torus ψ) Z₁ = ⊥ :=
    (Work.SurgeryInvariance.WindingSpan_eq_bot_iff (torus ψ) Z₁).mpr hcon.1
  have hb₂ : Work.SurgeryInvariance.WindingSpan (torus ψ) Z₂ = ⊥ :=
    (Work.SurgeryInvariance.WindingSpan_eq_bot_iff (torus ψ) Z₂).mpr hcon.2
  have hbot : Work.SurgeryInvariance.WindingSpan (torus ψ) (Z₁ ∪ Z₂) = ⊥ := by
    rw [Work.SurgeryInvariance.Span.union_eq_sup hopen₁ hopen₂ hdisj, hb₁, hb₂, sup_bot_eq]
  exact (Work.SurgeryInvariance.WindingSpan_eq_bot_iff (torus ψ) (Z₁ ∪ Z₂)).mp hbot h

/-- **The double bubble, with the region split exactly into the two halves.**

`A = F ∩ int(S)` is the region inside the original sphere and `H₁`, `H₂` are the two half-regions
(the regions inside the two spheres `H₁`, `H₂` into which the `2`-surgery of the double bubble cuts
`S`); the two halves are open and disjoint in the surface and their union is `A`.  If `A` contains
an essential loop, so does one of the two halves.

This is the shape of the conclusion of Pardon's Lemma 3 for the *pinched* family, where the region
inside `S_t` is literally the disjoint union of the two pieces. -/
theorem doubleBubble_containsEssentialLoop_of_split (ψ : Submission.Diffeo) {A H₁ H₂ : Set R3}
    (hopen₁ : Work.SurgeryInvariance.IsOpenInCarrier (torus ψ) H₁)
    (hopen₂ : Work.SurgeryInvariance.IsOpenInCarrier (torus ψ) H₂) (hdisj : Disjoint H₁ H₂)
    (hcover : A = H₁ ∪ H₂) (h0 : (torus ψ).ContainsEssentialLoop A) :
    (torus ψ).ContainsEssentialLoop H₁ ∨ (torus ψ).ContainsEssentialLoop H₂ := by
  rw [hcover] at h0
  exact containsEssentialLoop_of_union ψ hopen₁ hopen₂ hdisj h0

/-- **The double bubble from a `Sweep` whose final region is the union of the two halves.**

This is the form in which the sibling subproject `Work.SurgeryInvariance` states Pardon's Lemma 3
(`Work.SurgeryInvariance.Sweep.double_bubble`): a family of spheres whose last member cuts out the
two half-regions gives the conclusion, by the invariance of the essential-piece invariant along the
sweep (`Work.SurgeryInvariance.Sweep.containsEssentialLoop_iff`, which is
`Work.SurgeryInvariance.Sweep.spherefamily` in the `0 → 1` direction) together with
`Work.Smooth.Morse.containsEssentialLoop_of_union`. -/
theorem doubleBubble_containsEssentialLoop_of_sweep (ψ : Submission.Diffeo)
    {S : Work.SurgeryInvariance.Sweep (torus ψ)} {H₁ H₂ : Set R3}
    (hopen₁ : Work.SurgeryInvariance.IsOpenInCarrier (torus ψ) H₁)
    (hopen₂ : Work.SurgeryInvariance.IsOpenInCarrier (torus ψ) H₂) (hdisj : Disjoint H₁ H₂)
    (hsplit : S.region 1 = H₁ ∪ H₂) (h0 : (torus ψ).ContainsEssentialLoop (S.region 0)) :
    (torus ψ).ContainsEssentialLoop H₁ ∨ (torus ψ).ContainsEssentialLoop H₂ := by
  have h1 : (torus ψ).ContainsEssentialLoop (S.region 1) := (S.containsEssentialLoop_iff 1).mpr h0
  rw [hsplit] at h1
  exact containsEssentialLoop_of_union ψ hopen₁ hopen₂ hdisj h1

/-- **The double bubble, with the decomposition supplied as a `RegionEquivalent`.**

This is the *honest* hypothesis for Pardon's family of spheres: the region `A = F ∩ int(S)` inside
the original sphere is the union of the two half-regions `H₁`, `H₂` together with the slice
`F ∩ D` cut out by the cutting *plane* `D`, and that slice is a `1`-dimensional curve of the
surface, not the interior of a disc of the surface.  What is needed is therefore not the equality
`A = H₁ ∪ H₂` but only that `A` and `H₁ ∪ H₂` have the same loop content
(`Work.SurgeryInvariance.RegionEquivalent`), i.e. that the slice can be pushed off without changing
the winding content — the input `Work.BoxShrink.Bubble.SlicePushOff` of the sibling subproject.
The genuine `2`-surgery piece is accounted for by
`Work.SurgeryInvariance.SurgeryStepZero.windingSpan_eq`. -/
theorem doubleBubble_containsEssentialLoop_of_regionEquivalent (ψ : Submission.Diffeo)
    {A H₁ H₂ : Set R3}
    (hopen₁ : Work.SurgeryInvariance.IsOpenInCarrier (torus ψ) H₁)
    (hopen₂ : Work.SurgeryInvariance.IsOpenInCarrier (torus ψ) H₂) (hdisj : Disjoint H₁ H₂)
    (hRE : Work.SurgeryInvariance.RegionEquivalent (torus ψ) A (H₁ ∪ H₂))
    (h0 : (torus ψ).ContainsEssentialLoop A) :
    (torus ψ).ContainsEssentialLoop H₁ ∨ (torus ψ).ContainsEssentialLoop H₂ := by
  have hne : Work.SurgeryInvariance.WindingSpan (torus ψ) (H₁ ∪ H₂) ≠ ⊥ := by
    rw [← Work.SurgeryInvariance.RegionEquivalent.windingSpan_eq hRE]
    exact (Work.SurgeryInvariance.windingSpan_ne_bot_iff (torus ψ) A).mpr h0
  by_contra hcon
  rw [not_or] at hcon
  refine hne ?_
  rw [Work.SurgeryInvariance.Span.union_eq_sup hopen₁ hopen₂ hdisj,
    (Work.SurgeryInvariance.WindingSpan_eq_bot_iff (torus ψ) H₁).mpr hcon.1,
    (Work.SurgeryInvariance.WindingSpan_eq_bot_iff (torus ψ) H₂).mpr hcon.2, sup_bot_eq]

/-- **Pardon's Lemma 3 (double bubble) in the vocabulary of this chapter.**

`A = F ∩ int(S)` is the region inside the original sphere; the cutting plane decomposes it into
the two half-box regions `H₁`, `H₂` and the disc `D` cut out by the sweep, all open in `F` and
pairwise disjoint.  If `A` contains an essential loop then so does one of the two halves.

This is `Work.SurgeryInvariance.double_bubble_persistence` for the torus `torus ψ`, whose hypothesis
`A = (H₁ ∪ H₂) ∪ D.interior` describes a region of the surface obtained from `H₁ ∪ H₂` by adjoining
the interior of an **embedded disc of the surface** (the local model of a single `2`-surgery).  The
trace of a disc of *space* on the surface is a curve, not the interior of a disc of the surface, so
this hypothesis is not literally Pardon's geometry for a closed slice; see
`Work.BoxShrink.Bubble.Obstruction` and `Work.Smooth.Morse.doubleBubble_containsEssentialLoop_of_regionEquivalent`
for the honest input.  The statement is kept because it is exactly what the sibling subproject
`Work.SurgeryInvariance` proves and what a caller who has the `2`-surgery model must consume. -/
theorem doubleBubble_containsEssentialLoop (ψ : Submission.Diffeo) {A H₁ H₂ : Set R3}
    {D : Work.SurgeryInvariance.DiscRegion (torus ψ)}
    (hopen₁ : Work.SurgeryInvariance.IsOpenInCarrier (torus ψ) H₁)
    (hopen₂ : Work.SurgeryInvariance.IsOpenInCarrier (torus ψ) H₂)
    (hdisj : Disjoint H₁ H₂) (hdisjZ : Disjoint (H₁ ∪ H₂) D.interior)
    (hcover : A = (H₁ ∪ H₂) ∪ D.interior)
    (h0 : (torus ψ).ContainsEssentialLoop A) :
    (torus ψ).ContainsEssentialLoop H₁ ∨ (torus ψ).ContainsEssentialLoop H₂ :=
  Work.SurgeryInvariance.double_bubble_persistence hopen₁ hopen₂ hdisj hdisjZ hcover h0

end

end Work.Smooth.Morse
