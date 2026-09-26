import Mathlib
import Submission.Work.Smooth.Morse.Defs
import Submission.Work.Smooth.Morse.Transport
import Submission.Work.Smooth.Morse.MorseModel
import Submission.Work.Smooth.Morse.Span
import Submission.Work.Smooth.Morse.MorseModel.windingSpan_locally_const
import Submission.Work.Smooth.Morse.MorseModel.windingSpan_locally_const_of_span_eq
import Submission.Work.Smooth.Morse.Sweep.windingSpan_locally_const_of_regularValue
import Submission.Work.Smooth.Morse.Flow
import Submission.Work.SurgeryInvariance.API

/-!
# The sweep of the level family (item 5)

This file assembles the local models of the chapter into the persistence statement for the level
family of a smooth function on the torus:

* at a regular level, the winding span is locally constant because nearby regions are transported
  (`Work.Smooth.Morse.RegularEquivalent`, item 3);
* at a critical level whose local model is `DiscModel`, the winding span is locally constant by the
  one-sided span bound `Work.Smooth.Morse.WindingSpan.le_of_subset_union` and the disc lemma
  (item 4);

hence, by `Work.SurgeryInvariance.eq_of_locally_const`, the winding span of `F ∩ {g < t}` is
*independent of `t`*, and so is the property "the region contains an essential loop of the torus".

The statement is conditional on the two analytic inputs `RegularEquivalent ψ g` (the transport
across regular intervals, produced by the normalised gradient flow) and `DiscModel ψ g t₀` at the
critical values (the local model of the critical point), and on the Morse/Sard input
`LocallyFiniteCriticalValues ψ g` (which is what makes the set of regular values open).

## Main results

* `Work.Smooth.Morse.windingSpan_eq_of_levelSweep` — the winding span is independent of the level;
* `Work.Smooth.Morse.containsEssentialLoop_iff_of_levelSweep` — Pardon's persistence for the level
  family;
* `Work.Smooth.Morse.LevelFamily.windingSpan_eq` and
  `Work.Smooth.Morse.LevelFamily.containsEssentialLoop_iff` — the same for the abstract local model
  `LevelFamily`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.Smooth.Morse

noncomputable section

variable {ψ : Submission.Diffeo} {g : R3 → ℝ}

/-! ## The abstract local model -/

/-- **The winding span is constant along a level family.**  At every parameter the span is locally
constant: at a regular parameter because the neighbouring regions are transported
(`RegionEquivalent.windingSpan_eq`), at an exceptional one by the local model. -/
theorem LevelFamily.windingSpan_eq (P : Work.CoreTopology.ParamTorus) (S : LevelFamily P) (t : ℝ) :
    Work.SurgeryInvariance.WindingSpan P (S.region t) =
      Work.SurgeryInvariance.WindingSpan P (S.region 0) :=
  Work.SurgeryInvariance.eq_of_locally_const
    (f := fun u : ℝ => Work.SurgeryInvariance.WindingSpan P (S.region u)) (by
      intro u
      by_cases hu : u ∈ S.exc
      · obtain ⟨ε, hε, hc⟩ := S.crossing u hu
        exact ⟨ε, hε, fun s hs => hc s hs⟩
      · obtain ⟨ε, hε, -, heq⟩ := S.regular u hu
        exact ⟨ε, hε, fun s hs =>
          (Work.SurgeryInvariance.RegionEquivalent.windingSpan_eq (heq s hs)).symm⟩) t 0

/-- The essential-piece invariant is constant along a level family. -/
theorem LevelFamily.containsEssentialLoop_iff (P : Work.CoreTopology.ParamTorus)
    (S : LevelFamily P) (t : ℝ) :
    P.ContainsEssentialLoop (S.region t) ↔ P.ContainsEssentialLoop (S.region 0) := by
  rw [← Work.SurgeryInvariance.windingSpan_ne_bot_iff P (S.region t),
    ← Work.SurgeryInvariance.windingSpan_ne_bot_iff P (S.region 0), S.windingSpan_eq P t]

/-! ## The level family of a smooth function -/

/-- **The local model at every level.**  At a regular value the span is locally constant by the
transport, at a critical value by `DiscModel`. -/
theorem windingSpan_locally_const_of_level (ψ : Submission.Diffeo) {g : R3 → ℝ}
    (hg : Continuous g) (hcrit : LocallyFiniteCriticalValues ψ g)
    (hreg : RegularEquivalent ψ g) (hdisc : ∀ t₀ ∈ criticalValues ψ g, DiscModel ψ g t₀) (t : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, |s - t| < ε →
      Work.SurgeryInvariance.WindingSpan (torus ψ) (region ψ g s) =
        Work.SurgeryInvariance.WindingSpan (torus ψ) (region ψ g t) := by
  by_cases ht : IsRegularValue ψ g t
  · exact Work.Smooth.Morse.Sweep.windingSpan_locally_const_of_regularValue ψ hcrit hreg ht
  · have hmem : t ∈ criticalValues ψ g := not_not.mp ht
    exact Work.Smooth.Morse.MorseModel.windingSpan_locally_const ψ hg (hdisc t hmem)

/-- **Item 5, level form: the winding span is independent of the level.**

The hypotheses are the three inputs of the chapter: the Morse/Sard input
`LocallyFiniteCriticalValues ψ g` (finitely many critical values on every bounded interval), the
transport across regular intervals `RegularEquivalent ψ g` (item 3, produced by the normalised
gradient flow), and the local model `DiscModel ψ g t₀` at every critical value (item 4). -/
theorem windingSpan_eq_of_levelSweep (ψ : Submission.Diffeo) {g : R3 → ℝ} (hg : Continuous g)
    (hcrit : LocallyFiniteCriticalValues ψ g) (hreg : RegularEquivalent ψ g)
    (hdisc : ∀ t₀ ∈ criticalValues ψ g, DiscModel ψ g t₀) (a b : ℝ) :
    Work.SurgeryInvariance.WindingSpan (torus ψ) (region ψ g a) =
      Work.SurgeryInvariance.WindingSpan (torus ψ) (region ψ g b) :=
  Work.SurgeryInvariance.eq_of_locally_const
    (f := fun u : ℝ => Work.SurgeryInvariance.WindingSpan (torus ψ) (region ψ g u))
    (windingSpan_locally_const_of_level ψ hg hcrit hreg hdisc) a b

/-- **The general level-sweep theorem, with the local model expressed as the equality of the two
sides' winding spans.**  This is the weakest form of the local model at a critical value which
still gives the persistence: `region(t₀-ε) ⊆ region t₀ ⊆ region(t₀+ε)`, so equality of the spans of
the two outer regions forces equality on the whole neighbourhood
(`Work.Smooth.Morse.MorseModel.windingSpan_locally_const_of_span_eq`). -/
theorem windingSpan_eq_of_levelSweep_of_span (ψ : Submission.Diffeo) {g : R3 → ℝ}
    (hcrit : LocallyFiniteCriticalValues ψ g) (hreg : RegularEquivalent ψ g)
    (hcross : ∀ t₀ ∈ criticalValues ψ g, ∃ ε : ℝ, 0 < ε ∧
      Work.SurgeryInvariance.WindingSpan (torus ψ) (region ψ g (t₀ - ε)) =
        Work.SurgeryInvariance.WindingSpan (torus ψ) (region ψ g (t₀ + ε)))
    (a b : ℝ) :
    Work.SurgeryInvariance.WindingSpan (torus ψ) (region ψ g a) =
      Work.SurgeryInvariance.WindingSpan (torus ψ) (region ψ g b) :=
  Work.SurgeryInvariance.eq_of_locally_const
    (f := fun u : ℝ => Work.SurgeryInvariance.WindingSpan (torus ψ) (region ψ g u))
    (by
      intro t
      by_cases ht : IsRegularValue ψ g t
      · exact Work.Smooth.Morse.Sweep.windingSpan_locally_const_of_regularValue ψ hcrit hreg ht
      · exact Work.Smooth.Morse.MorseModel.windingSpan_locally_const_of_span_eq ψ
          (hcross t (not_not.mp ht))) a b

/-- **The level-sweep theorem with the local model expressed as a single `2`-surgery.**
At each critical value the passage from `region (t₀-ε)` to `region (t₀+ε)` is a single `2`-surgery
in the sense of `Work.SurgeryInvariance` (its change is an embedded disc of the surface, with the
usual openness and disjointness certificates).  This is the form in which the hypotheses of Pardon's
argument are most naturally supplied by a family of spheres put in general position. -/
theorem windingSpan_eq_of_levelSweep_of_surgeryStepZero (ψ : Submission.Diffeo) {g : R3 → ℝ}
    (hcrit : LocallyFiniteCriticalValues ψ g) (hreg : RegularEquivalent ψ g)
    (hstep : ∀ t₀ ∈ criticalValues ψ g, ∃ ε : ℝ, 0 < ε ∧
      Work.SurgeryInvariance.SurgeryStepZero (torus ψ) (region ψ g (t₀ - ε)) (region ψ g (t₀ + ε)))
    (a b : ℝ) :
    Work.SurgeryInvariance.WindingSpan (torus ψ) (region ψ g a) =
      Work.SurgeryInvariance.WindingSpan (torus ψ) (region ψ g b) :=
  windingSpan_eq_of_levelSweep_of_span ψ hcrit hreg
    (fun t₀ ht₀ => by
      obtain ⟨ε, hε, hst⟩ := hstep t₀ ht₀
      exact ⟨ε, hε, hst.windingSpan_eq⟩) a b

/-- **Item 5 in the satisfiable form, with the transport input discharged.**  For a `C^∞` function,
*if* the change of the region across every critical value preserves the winding span — the local
model which a family of spheres in general position provides, and which is *not* automatic for a raw
level family (see `Submission.Work.Smooth.Morse.MorseModel`) — *then* the winding span of
`F ∩ {g < t}` is independent of `t`.

This is the non-vacuous form of the sweep theorem: the hypothesis holds, for instance, at the first
tangency of a growing convex body with `F`
(`Work.Smooth.Morse.DiscGrowth.windingSpan_eq`), and it is vacuous on every interval without critical
values (so the theorem specialises to the transport statement of item 3). -/
theorem windingSpan_eq_of_levelSweep_of_crossing (ψ : Submission.Diffeo) {g : R3 → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hcrit : LocallyFiniteCriticalValues ψ g)
    (hcross : ∀ t₀ ∈ criticalValues ψ g, ∃ ε : ℝ, 0 < ε ∧
      Work.SurgeryInvariance.WindingSpan (torus ψ) (region ψ g (t₀ - ε)) =
        Work.SurgeryInvariance.WindingSpan (torus ψ) (region ψ g (t₀ + ε)))
    (a b : ℝ) :
    Work.SurgeryInvariance.WindingSpan (torus ψ) (region ψ g a) =
      Work.SurgeryInvariance.WindingSpan (torus ψ) (region ψ g b) :=
  windingSpan_eq_of_levelSweep_of_span ψ hcrit (regularEquivalent_of_contDiff ψ hg) hcross a b

/-- The same, with the local model stated as a single `2`-surgery (the form supplied by a family of
spheres in general position). -/
theorem windingSpan_eq_of_levelSweep_of_surgeryStepZero' (ψ : Submission.Diffeo) {g : R3 → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hcrit : LocallyFiniteCriticalValues ψ g)
    (hstep : ∀ t₀ ∈ criticalValues ψ g, ∃ ε : ℝ, 0 < ε ∧
      Work.SurgeryInvariance.SurgeryStepZero (torus ψ) (region ψ g (t₀ - ε)) (region ψ g (t₀ + ε)))
    (a b : ℝ) :
    Work.SurgeryInvariance.WindingSpan (torus ψ) (region ψ g a) =
      Work.SurgeryInvariance.WindingSpan (torus ψ) (region ψ g b) :=
  windingSpan_eq_of_levelSweep_of_surgeryStepZero ψ hcrit (regularEquivalent_of_contDiff ψ hg)
    hstep a b

/-- Pardon's persistence for the level family of a `C^∞` function, with the transport discharged
and the local model at the critical values in the satisfiable "crossing" form. -/
theorem containsEssentialLoop_iff_of_levelSweep_of_crossing (ψ : Submission.Diffeo) {g : R3 → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hcrit : LocallyFiniteCriticalValues ψ g)
    (hcross : ∀ t₀ ∈ criticalValues ψ g, ∃ ε : ℝ, 0 < ε ∧
      Work.SurgeryInvariance.WindingSpan (torus ψ) (region ψ g (t₀ - ε)) =
        Work.SurgeryInvariance.WindingSpan (torus ψ) (region ψ g (t₀ + ε)))
    (a b : ℝ) :
    (torus ψ).ContainsEssentialLoop (region ψ g a) ↔
      (torus ψ).ContainsEssentialLoop (region ψ g b) := by
  rw [← Work.SurgeryInvariance.windingSpan_ne_bot_iff (torus ψ) (region ψ g a),
    ← Work.SurgeryInvariance.windingSpan_ne_bot_iff (torus ψ) (region ψ g b),
    windingSpan_eq_of_levelSweep_of_crossing ψ hg hcrit hcross a b]

/-- **Item 5 with the transport input discharged**, stated with the local model `DiscModel` at every
critical value.  The transport across the critical-value-free intervals is supplied by the normalised
gradient flow (`Work.Smooth.Morse.regularEquivalent_of_contDiff`, item 3).

Use `Work.Smooth.Morse.windingSpan_eq_of_levelSweep_of_crossing` instead when the interest is in a
non-vacuous statement: `DiscModel ψ g t₀` is satisfiable only at a critical value at the bottom of
the range of `g|_F` (`Work.Smooth.Morse.MorseModel.not_discModel_of_lt`), so the hypothesis
`∀ t₀ ∈ criticalValues ψ g, DiscModel ψ g t₀` cannot be met by a nonconstant `g`. -/
theorem windingSpan_eq_of_levelSweep_of_contDiff (ψ : Submission.Diffeo) {g : R3 → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hcrit : LocallyFiniteCriticalValues ψ g)
    (hdisc : ∀ t₀ ∈ criticalValues ψ g, DiscModel ψ g t₀) (a b : ℝ) :
    Work.SurgeryInvariance.WindingSpan (torus ψ) (region ψ g a) =
      Work.SurgeryInvariance.WindingSpan (torus ψ) (region ψ g b) :=
  windingSpan_eq_of_levelSweep ψ hg.continuous hcrit
    (regularEquivalent_of_contDiff ψ hg) hdisc a b

/-- Pardon's persistence for the level family of a `C^∞` function, with the transport input
discharged. -/
theorem containsEssentialLoop_iff_of_levelSweep_of_contDiff (ψ : Submission.Diffeo) {g : R3 → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hcrit : LocallyFiniteCriticalValues ψ g)
    (hdisc : ∀ t₀ ∈ criticalValues ψ g, DiscModel ψ g t₀) (a b : ℝ) :
    (torus ψ).ContainsEssentialLoop (region ψ g a) ↔
      (torus ψ).ContainsEssentialLoop (region ψ g b) := by
  rw [← Work.SurgeryInvariance.windingSpan_ne_bot_iff (torus ψ) (region ψ g a),
    ← Work.SurgeryInvariance.windingSpan_ne_bot_iff (torus ψ) (region ψ g b),
    windingSpan_eq_of_levelSweep_of_contDiff ψ hg hcrit hdisc a b]

/-- The `DiscModel` form of the general theorem, by `DiscModel.windingSpan_eq`. -/
theorem windingSpan_eq_of_levelSweep' (ψ : Submission.Diffeo) {g : R3 → ℝ} (hg : Continuous g)
    (hcrit : LocallyFiniteCriticalValues ψ g) (hreg : RegularEquivalent ψ g)
    (hdisc : ∀ t₀ ∈ criticalValues ψ g, DiscModel ψ g t₀) (a b : ℝ) :
    Work.SurgeryInvariance.WindingSpan (torus ψ) (region ψ g a) =
      Work.SurgeryInvariance.WindingSpan (torus ψ) (region ψ g b) :=
  windingSpan_eq_of_levelSweep ψ hg hcrit hreg hdisc a b

/-- **Pardon's persistence for the level family.**  If the region `F ∩ {g < a}` contains a loop
which is essential in the torus then so does `F ∩ {g < b}`. -/
theorem containsEssentialLoop_iff_of_levelSweep (ψ : Submission.Diffeo) {g : R3 → ℝ}
    (hg : Continuous g) (hcrit : LocallyFiniteCriticalValues ψ g) (hreg : RegularEquivalent ψ g)
    (hdisc : ∀ t₀ ∈ criticalValues ψ g, DiscModel ψ g t₀) (a b : ℝ) :
    (torus ψ).ContainsEssentialLoop (region ψ g a) ↔
      (torus ψ).ContainsEssentialLoop (region ψ g b) := by
  rw [← Work.SurgeryInvariance.windingSpan_ne_bot_iff (torus ψ) (region ψ g a),
    ← Work.SurgeryInvariance.windingSpan_ne_bot_iff (torus ψ) (region ψ g b),
    windingSpan_eq_of_levelSweep ψ hg hcrit hreg hdisc a b]

/-- The one-directional form of the persistence theorem. -/
theorem containsEssentialLoop_of_levelSweep (ψ : Submission.Diffeo) {g : R3 → ℝ}
    (hg : Continuous g) (hcrit : LocallyFiniteCriticalValues ψ g) (hreg : RegularEquivalent ψ g)
    (hdisc : ∀ t₀ ∈ criticalValues ψ g, DiscModel ψ g t₀) {a b : ℝ}
    (h : (torus ψ).ContainsEssentialLoop (region ψ g a)) :
    (torus ψ).ContainsEssentialLoop (region ψ g b) :=
  (containsEssentialLoop_iff_of_levelSweep ψ hg hcrit hreg hdisc a b).mp h

end

end Work.Smooth.Morse
