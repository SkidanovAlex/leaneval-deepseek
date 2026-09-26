import Submission.Work.BoxShrink.Core.Basic
import Submission.Work.SurgeryInvariance.Span.union_eq_sup
import Submission.Work.SurgeryInvariance.Abstract

/-!
# The corrected interface of the box/plane double bubble: definitions and local models

**The field `bubble` of `Work.BoxShrink.Core.BubbleInput` is false**
(`Work.BoxShrink.Bubble.standard_counterexample`, `Work.BoxShrink.Bubble.no_bubble_field`).  This
module contains *only the definitions* of the corrected interface, with a deliberately small
dependency footprint (`Work.BoxShrink.Core.Basic` plus two modules of `Work.SurgeryInvariance`), so
that the files that still name the false field can import it **without a cycle**:

* `Work.BoxShrink.Bubble.BubbleHalf` — Pardon's Lemma 3 conclusion at the loop level (the statement
  the shrinking step consumes);
* `Work.BoxShrink.Bubble.PushOffHalf`, `Work.BoxShrink.Bubble.SmoothHalf` — the corrected field,
  for all parametrised tori resp. for the smooth tori of the challenge;
* `Work.BoxShrink.Bubble.BubbleInputHalf` — `Work.BoxShrink.Core.BubbleInput` with the field's
  *conclusion* weakened to `BubbleHalf` (a drop-in replacement);
* `Work.BoxShrink.Bubble.PardonDichotomy`, `Work.BoxShrink.Bubble.SurgeryStepSmall`,
  `Work.BoxShrink.Bubble.SweepLoopsSmall`, `Work.BoxShrink.Bubble.PinchDatum` and
  `Work.BoxShrink.Bubble.PardonPinchInput` — Pardon's own local model and his dichotomy (the
  isolated input that a proof of the corrected interface must supply);
* `Work.BoxShrink.Bubble.BubbleInputPardon` — `Work.BoxShrink.Core.BubbleInput` with the field
  replaced by Pardon's datum `PinchDatum` (the other drop-in replacement).

Everything *about* these definitions (the instances, the implications from the old interface, the
crux replays) is in `Work.BoxShrink.Bubble.Corrected` and
`Work.BoxShrink.Bubble.PardonLocalModel`; see `MIGRATION.md` for how to switch the rest of the
workspace over.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.Bubble

noncomputable section

variable {P : Work.CoreTopology.ParamTorus}

/-! ## The corrected conclusion -/

/-- **Pardon's Lemma 3 conclusion, at the loop level**: if the region of the surface inside the
sphere `∂PBox s c σ` carries an essential loop, then so does one of the two half-regions cut out by
the plane `{y (σ 2) = c (σ 2) + u}`.

This is the exact statement the shrinking step consumes (`Work.BoxShrink.Core.CruxCore`), and it is
strictly weaker than the push-off `Work.BoxShrink.Bubble.SlicePushOff` (which would give it for the
union and hence, by `Work.SurgeryInvariance.Span.union_eq_sup`, for one of the halves). -/
def BubbleHalf (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (u : ℝ) : Prop :=
  P.ContainsEssentialLoop (Work.BoxShrink.Core.boxRegion P s c σ) →
    P.ContainsEssentialLoop (Work.BoxShrink.Core.upperRegion P s c σ u) ∨
      P.ContainsEssentialLoop (Work.BoxShrink.Core.lowerRegion P s c σ u)

/-- **The corrected field.**  Pardon's double bubble, in the form his proof actually delivers:
for every box/plane configuration whose two cuts carry no essential loop, an essential loop of the
region inside the box survives to one of the two half-regions.

Like the field it corrects, this is quantified over *all* parametrised tori (only continuous
parametrisations, and `Work.CoreTopology.ParamTorus` allows wild embeddings of `T²`), which is the
form the caller's structure uses.  For the challenge itself only the smooth tori of the challenge
occur, and Pardon's proof — in particular his counting hypothesis, which is what supplies the
dichotomy of `Work.BoxShrink.Bubble.PardonPinchInput` — applies to those; see
`Work.BoxShrink.Bubble.SmoothHalf` for the restricted form (and
`Work.BoxShrink.Bubble.cruxCore_of_smoothHalf`, whose conclusion is the crux). -/
def PushOffHalf : Prop :=
  ∀ (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
    ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sphereSet c σ s) →
    ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sliceRegion P s c σ u) →
    BubbleHalf P s c σ u

/-- **The corrected field for the smooth tori of the challenge only** (the form in which the crux
needs it, cf. `Work.BoxShrink.Bubble.RestrictedInput`). -/
def SmoothHalf : Prop :=
  ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
    ¬ (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph).ContainsEssentialLoop
      (Work.BoxShrink.Core.sliceRegion
        (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph) s c σ u) →
    BubbleHalf (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph) s c σ u


/-! ## Drop-in replacements for `Work.BoxShrink.Core.BubbleInput`

The caller's structure has two fields: the planar innermost-disc input `cleansInDisc` (unchanged) and
the double-bubble field `bubble`.  The two structures below are the same structure with `bubble`
replaced by the corrected datum — the minimal change (`BubbleInputHalf`: only the *conclusion*
changes, from `BubbleSweep` to `BubbleHalf`) and the Pardon-faithful one (`BubbleInputPardon`: the
field becomes the pinch datum of `Work.BoxShrink.Bubble.PardonPinchInput`).  Both give
`Work.BoxShrink.CruxStatement` for all `p, q` with the same two classical inputs as
`Work.BoxShrink.Core.crux_of_bubbleInput`. -/

/-- **`Work.BoxShrink.Core.BubbleInput` with the double-bubble conclusion weakened to Pardon's
Lemma 3 conclusion.**  The `bubble` field asks only what the shrinking step consumes. -/
structure BubbleInputHalf where
  /-- the classical (planar) innermost-disc input at every flat disc cut out of a box by a plane -/
  cleansInDisc : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
    Work.InnermostDisk.CleansInSphere
      (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph)
      (Work.BoxShrink.Core.cutDisc s c σ u)
  /-- Pardon's Lemma 3 conclusion, for every box/plane configuration whose two cuts are inessential -/
  bubble : ∀ (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (u : ℝ),
    ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sphereSet c σ s) →
    ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sliceRegion P s c σ u) → BubbleHalf P s c σ u

/-! ## Pardon's local move and his dichotomy -/

/-- **Pardon's local move of a sphere family.**  The region `A'` is obtained from the region `A` by
adding or removing an *open* piece `Z` of the surface whose winding span is not the whole of
`H₁(F; ℚ) = ℚ²` — i.e. a piece of dimension at most one.  This is Pardon's "a single surgery
changes `dim im(H₁(F ∩ int S_t) → H₁(F))` by at most one", in the loop-level vocabulary of this
development.

(`Work.SurgeryInvariance.SurgeryStepZero` is the special case in which `Z` has vanishing span; it is
*not* enough, see `Work.BoxShrink.Bubble.standard_counterexample`.) -/
def SurgeryStepSmall (P : Work.CoreTopology.ParamTorus) (A A' : Set R3) : Prop :=
  ∃ Z : Set R3, Work.SurgeryInvariance.WindingSpan P Z ≠ ⊤ ∧
    Work.SurgeryInvariance.IsOpenInCarrier P A ∧ Work.SurgeryInvariance.IsOpenInCarrier P A' ∧
    Work.SurgeryInvariance.IsOpenInCarrier P Z ∧
    ((A = A' ∪ Z ∧ Disjoint A' Z) ∨ (A' = A ∪ Z ∧ Disjoint A Z))

/-- **Pardon's dichotomy** (equation (1) of the paper, loop-level form): the region `X = F ∩ int(S)`
of a sphere `S` which is transverse to `F` and meets it in inessential curves either carries no
essential loop (`WindingSpan P X = ⊥`) or carries the whole of `H₁(F; ℚ)` (`WindingSpan P X = ⊤`,
because its genus-`g` component maps onto `H₁(F)`).

This is the geometric input that the counting hypothesis supplies and that the vanishing of winding
spans cannot supply on its own. -/
def PardonDichotomy (P : Work.CoreTopology.ParamTorus) (X : Set R3) : Prop :=
  Work.SurgeryInvariance.WindingSpan P X = ⊥ ∨ Work.SurgeryInvariance.WindingSpan P X = ⊤

/-- `⊥ ≠ ⊤` for the winding span of a region of the torus. -/
theorem submodule_bot_ne_top : (⊥ : Submodule ℚ (ℚ × ℚ)) ≠ ⊤ := by
  intro h
  have hmem : ((1, 0) : ℚ × ℚ) ∈ (⊥ : Submodule ℚ (ℚ × ℚ)) := by
    rw [h]; exact Submodule.mem_top
  simpa using hmem

/-- A `2`-surgery of the library (`Work.SurgeryInvariance.SurgeryStepZero`) is a small step: a piece
of vanishing winding span is in particular not the whole of `H₁(F; ℚ)`. -/
theorem surgeryStepSmall_of_surgeryStepZero {A A' : Set R3}
    (h : Work.SurgeryInvariance.SurgeryStepZero P A A') : SurgeryStepSmall P A A' := by
  obtain ⟨Z, hZ, hA, hA', hZo, hcase⟩ := h
  exact ⟨Z, by rw [hZ]; exact submodule_bot_ne_top, hA, hA', hZo, hcase⟩

/-- **A small step preserves the vanishing of the winding span, in the presence of Pardon's
dichotomy.**  If `A'` is a small step from `A` and both spans lie in `{⊥, ⊤}`, then
`WindingSpan P A = ⊥ ↔ WindingSpan P A' = ⊥`.

This is Pardon's argument: a single surgery changes the dimension by at most one, and the dimension
takes only the two values `0` and `2g`, so it cannot change at all. -/
theorem bot_iff_of_surgeryStepSmall {A A' : Set R3} (h : SurgeryStepSmall P A A')
    (hA : PardonDichotomy P A) (hA' : PardonDichotomy P A') :
    (Work.SurgeryInvariance.WindingSpan P A = ⊥ ↔ Work.SurgeryInvariance.WindingSpan P A' = ⊥) := by
  obtain ⟨Z, hZtop, hAo, hA'o, hZo, hcase⟩ := h
  constructor
  · intro hbot
    rcases hcase with ⟨hc, hd⟩ | ⟨hc, hd⟩
    · rw [hc, Work.SurgeryInvariance.Span.union_eq_sup hA'o hZo hd] at hbot
      exact (sup_eq_bot_iff.mp hbot).1
    · have hAZ : Work.SurgeryInvariance.WindingSpan P A' =
          Work.SurgeryInvariance.WindingSpan P Z := by
        rw [hc, Work.SurgeryInvariance.Span.union_eq_sup hAo hZo hd, hbot, bot_sup_eq]
      rcases hA' with h | h
      · exact h
      · rw [hAZ] at h; exact absurd h hZtop
  · intro hbot
    rcases hcase with ⟨hc, hd⟩ | ⟨hc, hd⟩
    · have hAZ : Work.SurgeryInvariance.WindingSpan P A =
          Work.SurgeryInvariance.WindingSpan P Z := by
        rw [hc, Work.SurgeryInvariance.Span.union_eq_sup hA'o hZo hd, hbot, bot_sup_eq]
      rcases hA with h | h
      · exact h
      · rw [hAZ] at h; exact absurd h hZtop
    · rw [hc, Work.SurgeryInvariance.Span.union_eq_sup hAo hZo hd] at hbot
      exact (sup_eq_bot_iff.mp hbot).1

/-! ## The sweep with Pardon's local models -/

/-- **A one-parameter family of regions of `F` with Pardon's local models.**  This is
`Work.SurgeryInvariance.SweepLoops` with `SurgeryStepZero` relaxed to
`Work.BoxShrink.Bubble.SurgeryStepSmall` (Pardon's "changes by at most one"), and with Pardon's
dichotomy assumed at every parameter.

The dichotomy is what makes the argument work: without it a small step can change `⊥` into a line,
which is exactly the counterexample. -/
structure SweepLoopsSmall (P : Work.CoreTopology.ParamTorus) where
  /-- the region `F ∩ int(S_t)` -/
  region : ℝ → Set R3
  /-- the exceptional (surgery) parameters -/
  exc : Finset ℝ
  /-- away from the exceptional parameters the loop content is transported -/
  regular : ∀ t : ℝ, t ∉ exc → ∃ ε : ℝ, 0 < ε ∧ (∀ s : ℝ, |s - t| < ε → s ∉ exc) ∧
    ∀ s : ℝ, |s - t| < ε → Work.SurgeryInvariance.RegionEquivalent P (region t) (region s)
  /-- at an exceptional parameter the region changes by a piece of dimension at most one, or is
  transported -/
  surgery : ∀ t : ℝ, t ∈ exc → ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, |s - t| < ε →
    SurgeryStepSmall P (region t) (region s) ∨
      Work.SurgeryInvariance.RegionEquivalent P (region t) (region s)
  /-- **Pardon's dichotomy** (equation (1)) at every parameter *before the pinching parameter*.

  The restriction to `t < 1` is essential and is exactly what Pardon's proof uses: the dichotomy is
  applied to the genuine spheres `S_t` of the family, for which `S_t ∩ F` consists of inessential
  curves; at the pinching parameter `t = 1` the "sphere" is the double bubble (a disjoint union of
  two spheres), and Pardon's last step is an *inclusion* argument, not the dichotomy.  (With the
  dichotomy at `t = 1` the datum would be false: at the counterexample configuration the final
  region is `upperRegion ∪ lowerRegion`, whose winding span is a line — neither `⊥` nor `⊤`.)  The
  endgame is the field `Work.BoxShrink.Bubble.PinchDatum.pinch`. -/
  dichotomy : ∀ t : ℝ, t < 1 → PardonDichotomy P (region t)

/-- **A quantity which is locally constant on `(-∞, 1)` is constant there.**  The restriction of
`Work.SurgeryInvariance.eq_of_locally_const` to the preconnected set `Set.Iio 1`. -/
theorem eq_of_locally_const_lt_one {α : Type*} {f : ℝ → α}
    (h : ∀ t : ℝ, t < 1 → ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, s < 1 → |s - t| < ε → f s = f t)
    {x y : ℝ} (hx : x < 1) (hy : y < 1) : f x = f y := by
  have hlc : IsLocallyConstant (fun t : Set.Iio (1 : ℝ) => f (t : ℝ)) := by
    intro u
    rw [isOpen_iff_forall_mem_open]
    intro t ht
    obtain ⟨ε, hε, hc⟩ := h (t : ℝ) t.2
    refine ⟨{s : Set.Iio (1 : ℝ) | |(s : ℝ) - (t : ℝ)| < ε}, ?_,
      isOpen_lt (continuous_subtype_val.sub continuous_const).abs continuous_const, ?_⟩
    · intro s hs
      change f (s : ℝ) ∈ u
      rw [hc (s : ℝ) s.2 hs]
      exact ht
    · simpa using hε
  haveI : PreconnectedSpace (Set.Iio (1 : ℝ)) :=
    isPreconnected_iff_preconnectedSpace.mp (isPreconnected_Iio (a := (1 : ℝ)))
  exact hlc.apply_eq_of_isPreconnected (s := Set.univ) isPreconnected_univ
    (x := ⟨x, hx⟩) (y := ⟨y, hy⟩) trivial trivial

/-- **The vanishing of the winding span is constant along a sweep with Pardon's local models**, for
every parameter before the pinching parameter. -/
theorem SweepLoopsSmall.bot_iff (S : SweepLoopsSmall P) {t : ℝ} (ht : t < 1) :
    (Work.SurgeryInvariance.WindingSpan P (S.region t) = ⊥ ↔
      Work.SurgeryInvariance.WindingSpan P (S.region 0) = ⊥) := by
  refine Iff.of_eq (eq_of_locally_const_lt_one
    (f := fun u : ℝ => Work.SurgeryInvariance.WindingSpan P (S.region u) = ⊥) ?_ ht
    (by norm_num))
  intro u hu
  have h2 : 0 < (1 - u) / 2 := by linarith
  by_cases hc : u ∈ S.exc
  · obtain ⟨ε, hε, hstep⟩ := S.surgery u hc
    refine ⟨min ε ((1 - u) / 2), lt_min hε h2, fun s _ hs => ?_⟩
    have hs1 : s < 1 := by
      have hlt : |s - u| < (1 - u) / 2 := lt_of_lt_of_le hs (min_le_right _ _)
      rw [abs_lt] at hlt
      linarith [hlt.2]
    rcases hstep s (lt_of_lt_of_le hs (min_le_left _ _)) with hsmall | hequiv
    · exact (propext (bot_iff_of_surgeryStepSmall hsmall (S.dichotomy u hu)
        (S.dichotomy s hs1))).symm
    · rw [Work.SurgeryInvariance.RegionEquivalent.windingSpan_eq hequiv]
  · obtain ⟨ε, hε, -, hequiv⟩ := S.regular u hc
    exact ⟨ε, hε, fun s _ hs => by
      rw [Work.SurgeryInvariance.RegionEquivalent.windingSpan_eq (hequiv s hs)]⟩

/-- **The essential-piece invariant is constant along a sweep with Pardon's local models**, up to
the pinching parameter. -/
theorem SweepLoopsSmall.containsEssentialLoop_iff (S : SweepLoopsSmall P) {t : ℝ} (ht : t < 1) :
    P.ContainsEssentialLoop (S.region t) ↔ P.ContainsEssentialLoop (S.region 0) := by
  rw [← Work.SurgeryInvariance.windingSpan_ne_bot_iff,
    ← Work.SurgeryInvariance.windingSpan_ne_bot_iff]
  exact Iff.not (S.bot_iff ht)

/-- **Pardon's Lemma `spherefamily` with his own local models, before the pinching parameter.**  If
the family starts with an essential loop then it has one at every parameter `t < 1`; the passage to
the two halves at `t = 1` is the endgame field of
`Work.BoxShrink.Bubble.PinchDatum`. -/
theorem SweepLoopsSmall.containsEssentialLoop_of_lt_one (S : SweepLoopsSmall P) (t : ℝ)
    (ht : t < 1) (h : P.ContainsEssentialLoop (S.region 0)) :
    P.ContainsEssentialLoop (S.region t) :=
  (S.containsEssentialLoop_iff ht).mpr h

/-- **Pardon's pinch is not invisible.**  If `A'` is a small step from `A` (they differ by an open
piece of winding span `≠ ⊤`, i.e. of dimension at most one) and `A'` realises the whole of
`H₁(F; ℚ)`, then `A` realises a nonzero class.  This is the endgame step at the pinching parameter:
the pinch removes the trace of the neck of the pinching sphere, a piece of dimension at most one, so
the region just after the pinch is still essential. -/
theorem not_bot_of_surgeryStepSmall_of_top {A A' : Set R3} (h : SurgeryStepSmall P A A')
    (hA' : Work.SurgeryInvariance.WindingSpan P A' = ⊤) :
    Work.SurgeryInvariance.WindingSpan P A ≠ ⊥ := by
  obtain ⟨Z, hZtop, hAo, hA'o, hZo, hcase⟩ := h
  rcases hcase with ⟨hc, hd⟩ | ⟨hc, hd⟩
  · intro hbot
    have h1 : Work.SurgeryInvariance.WindingSpan P A =
        Work.SurgeryInvariance.WindingSpan P A' ⊔ Work.SurgeryInvariance.WindingSpan P Z := by
      rw [hc, Work.SurgeryInvariance.Span.union_eq_sup hA'o hZo hd]
    rw [h1, hA', top_sup_eq] at hbot
    exact submodule_bot_ne_top hbot.symm
  · intro hbot
    have h1 : Work.SurgeryInvariance.WindingSpan P A' =
        Work.SurgeryInvariance.WindingSpan P A ⊔ Work.SurgeryInvariance.WindingSpan P Z := by
      rw [hc, Work.SurgeryInvariance.Span.union_eq_sup hAo hZo hd]
    rw [h1, hbot, bot_sup_eq] at hA'
    exact hZtop hA'

/-- **A small step cannot destroy the essential loop.**  If the region `A'` is obtained from `A` by
adding or removing a piece of dimension at most one and `A'` carries an essential loop (which, by the
dichotomy at `A'`, means that `A'` realises the whole of `H₁(F; ℚ)`), then so does `A`.  This is the
local-model form of the endgame at the pinching parameter. -/
theorem containsEssentialLoop_of_surgeryStepSmall {A A' : Set R3} (h : SurgeryStepSmall P A A')
    (hdich : PardonDichotomy P A') (hA : P.ContainsEssentialLoop A') :
    P.ContainsEssentialLoop A := by
  have htop : Work.SurgeryInvariance.WindingSpan P A' = ⊤ := by
    rcases hdich with h' | h'
    · exact absurd h' ((Work.SurgeryInvariance.windingSpan_ne_bot_iff P A').mpr hA)
    · exact h'
  exact (Work.SurgeryInvariance.windingSpan_ne_bot_iff P A).mp
    (not_bot_of_surgeryStepSmall_of_top h htop)

/-! ## The isolated input of the pinch, with Pardon's local models -/

/-- **The pinch datum of the box/plane configuration**: the one-parameter family of regions of `F`
pinching the sphere `∂PBox s c σ` along the flat disc `cutDisc s c σ u`, with Pardon's local models
(`Work.BoxShrink.Bubble.SurgeryStepSmall`), Pardon's dichotomy at every parameter, and the two
endpoint regions `boxRegion` and `upperRegion ∪ lowerRegion`.

This is the isolated input that should replace the field `bubble` of
`Work.BoxShrink.Core.BubbleInput`: it is what Pardon's Lemma 3 actually constructs (from the counting
hypothesis, applied to *every* intermediate sphere), and it is not refuted by the counterexample
(`Work.BoxShrink.Bubble.standard_counterexample`), which only shows that the local models of
`Work.SurgeryInvariance.SweepLoops` are too strong.

The dichotomy field is where the counting hypothesis enters, and Pardon's argument for it (equation
(1) of the paper: the region is `F ∩ int(S_t)`, the sphere `S_t` is transverse to `F`, and `F ∩ S_t`
consists of inessential curves, so `F ∖ S_t` has a component of genus `g` whose homology surjects onto
`H₁(F)`) uses the topology of the *PL/smooth* embedded surface; the challenge only needs the smooth
tori `P = ParamTorus.mapHomeomorph ψ.toHomeomorph`.  Compare `Work.BoxShrink.Bubble.Dichotomy.lean`
for the closure properties of the dichotomy and the configurations where it is a theorem. -/
structure PinchDatum (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) where
  /-- the one-parameter family of regions, with Pardon's local models and dichotomy -/
  sweep : SweepLoopsSmall P
  /-- at time `0` the family is the region inside the sphere `∂PBox s c σ` -/
  zero : sweep.region 0 = Work.BoxShrink.Core.boxRegion P s c σ
  /-- at time `1` the family is the union of the two half-regions -/
  one : sweep.region 1 =
    Work.BoxShrink.Core.upperRegion P s c σ u ∪ Work.BoxShrink.Core.lowerRegion P s c σ u
  /-- **The endgame at the pinching parameter**: the essential loop of some region strictly before
  the pinch survives to the final region (the union of the two halves).

  This is Pardon's last step of the proof of Lemma `doublebubble`: just before the pinch the sphere
  is an arbitrarily small perturbation of the double bubble, and "since `F ∩ int(S)` is an open
  surface, the property of it having a connected component of genus `g` is preserved under
  sufficiently small perturbations of `S`".  It is *not* a consequence of the local models alone:
  the pinch removes the trace of the neck of the pinching sphere, and that piece touches both
  half-regions along the slice (`region 1 = region t ∩ {y (σ 2) ≠ c (σ 2) + u}` for `t` close to
  `1`), so it cannot be decomposed into a piece disjoint from the final region in the way
  `Work.BoxShrink.Bubble.SurgeryStepSmall` requires.  (`Work.BoxShrink.Bubble.SurgeryStepSmall`
  steps — a `2`-surgery whose changed piece may have dimension one — *do* imply this field:
  `Work.BoxShrink.Bubble.containsEssentialLoop_of_surgeryStepSmall`.) -/
  pinch : ∃ t : ℝ, t < 1 ∧ (P.ContainsEssentialLoop (sweep.region t) →
    P.ContainsEssentialLoop (sweep.region 1))

/-- **Pardon's Lemma 3 (`doublebubble`) from the pinch datum.**  An essential loop of the region
inside the sphere survives, along the family, to every parameter before the pinch (constancy of the
vanishing of the winding span, using the dichotomy at those parameters), and the endgame field
carries it to the final region, the union of the two halves; those are disjoint open pieces of the
surface, so one of them carries the loop (`Span.union_eq_sup`). -/
theorem bubbleHalf_of_pinchDatum {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (D : PinchDatum P s c σ u) : BubbleHalf P s c σ u := by
  intro hbox
  have h0 : P.ContainsEssentialLoop (D.sweep.region 0) := by
    rw [D.zero]; exact hbox
  obtain ⟨t, ht1, hsurv⟩ := D.pinch
  have ht : P.ContainsEssentialLoop (D.sweep.region t) :=
    D.sweep.containsEssentialLoop_of_lt_one t ht1 h0
  have h1 : P.ContainsEssentialLoop (D.sweep.region 1) := hsurv ht
  rw [D.one] at h1
  have hsplit := Work.SurgeryInvariance.Span.union_eq_sup (P := P)
    (Work.BoxShrink.Core.isOpenInCarrier_upperRegion P s c σ u)
    (Work.BoxShrink.Core.isOpenInCarrier_lowerRegion P s c σ u)
    (Work.BoxShrink.Core.disjoint_upperRegion_lowerRegion P s c σ u)
  have hne : Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.upperRegion P s c σ u) ⊔
      Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.lowerRegion P s c σ u) ≠ ⊥ := by
    rw [← hsplit]
    exact (Work.SurgeryInvariance.windingSpan_ne_bot_iff P _).mpr h1
  rcases not_and_or.mp (fun hh : Work.SurgeryInvariance.WindingSpan P
      (Work.BoxShrink.Core.upperRegion P s c σ u) = ⊥ ∧
      Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.lowerRegion P s c σ u) = ⊥ =>
      hne (by rw [hh.1, hh.2, sup_bot_eq])) with hup | hlo
  · exact Or.inl ((Work.SurgeryInvariance.windingSpan_ne_bot_iff P _).mp hup)
  · exact Or.inr ((Work.SurgeryInvariance.windingSpan_ne_bot_iff P _).mp hlo)

/-- **The corrected (Pardon-faithful) input**: the pinch datum for every box/plane configuration
whose two cuts carry no essential loop. -/
def PardonPinchInput : Type :=
  ∀ (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
    ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sphereSet c σ s) →
    ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sliceRegion P s c σ u) →
    PinchDatum P s c σ u

/-- The corrected input gives the corrected field, hence (by
`Work.BoxShrink.Bubble.crux_of_pushOffHalf`) the whole shrinking step. -/
theorem pushOffHalf_of_pardonPinchInput (h : PardonPinchInput) : PushOffHalf :=
  fun P s c σ u hS hZ => bubbleHalf_of_pinchDatum (h P s c σ u hS hZ)

/-! ## A drop-in replacement for `Work.BoxShrink.Core.BubbleInput`

`Work.BoxShrink.Bubble.BubbleInputPardon` is the caller's structure with the field `bubble` replaced
by Pardon's own datum (`PinchDatum`); `crux_of_bubbleInputPardon` is the analogue of
`Work.BoxShrink.Core.crux_of_bubbleInput`.  (The weakened drop-in
`Work.BoxShrink.Bubble.BubbleInputHalf`, whose field is only `BubbleHalf`, is in `Corrected.lean`.) -/

/-- **`Work.BoxShrink.Core.BubbleInput` with the double-bubble field replaced by Pardon's own
datum** (`Work.BoxShrink.Bubble.PardonPinchInput`): the pinching family with his local models and
his dichotomy. -/
structure BubbleInputPardon where
  /-- the classical (planar) innermost-disc input at every flat disc cut out of a box by a plane -/
  cleansInDisc : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
    Work.InnermostDisk.CleansInSphere
      (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph)
      (Work.BoxShrink.Core.cutDisc s c σ u)
  /-- the pinch datum, for every box/plane configuration whose two cuts are inessential -/
  bubble : ∀ (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (u : ℝ),
    ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sphereSet c σ s) →
    ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sliceRegion P s c σ u) →
    PinchDatum P s c σ u

/-- A `PinchDatum` gives the corrected conclusion, so the Pardon-faithful structure implies the
weakened one. -/
theorem bubbleInputHalf_of_bubbleInputPardon (hin : BubbleInputPardon) : BubbleInputHalf where
  cleansInDisc := hin.cleansInDisc
  bubble := pushOffHalf_of_pardonPinchInput hin.bubble
end

end Work.BoxShrink.Bubble
