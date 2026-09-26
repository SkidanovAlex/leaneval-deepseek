import Mathlib
import Submission.Work.Smooth.Morse.Defs
import Submission.Work.SurgeryInvariance.API

/-!
# Regular level intervals move the region by a transport (item 3)

If `[a,b]` contains no critical value of `g|_F`, the normalised gradient flow of `g|_F` moves every
point of the surface down to the level `a` and therefore pushes the larger region `F ∩ {g < b}`
into the smaller one `F ∩ {g < a}`.  The flow is a homotopy of the surface starting at the
identity, so it transports loops of the torus with their winding vectors
(`Work.SurgeryInvariance.windingOf_map_eq`), and the loop level content of the pair of regions is
exactly `Work.SurgeryInvariance.RegionEquivalent`.

This file proves that reduction: the *analytic* input is the structure `SublevelTransport` of
`Submission.Work.Smooth.Morse.Defs` (the existence of the flow), and its *topological* consequence
is `Work.SurgeryInvariance.RegionEquivalent`, which is what the persistence proofs of
`Work.SurgeryInvariance` consume.  The existence of the transport from the ODE theory is the one
piece that is not proved here; it is documented in the module
`Submission.Work.Smooth.Morse.Regular` and in the README of this chapter.

## Main results

* `Work.Smooth.Morse.SublevelTransport.continuous_φ` — the time-one map is continuous;
* `Work.Smooth.Morse.SublevelTransport.toRegionEquivalent` — a transport gives the loop-level
  equivalence of the two sublevel regions;
* `Work.Smooth.Morse.regularEquivalent_of_transport` — a family of transports across every regular
  interval gives `RegularEquivalent`;
* `Work.Smooth.Morse.RegularEquivalent.windingSpan_eq` and
  `Work.Smooth.Morse.RegularEquivalent.containsEssentialLoop_iff` — consequently the winding span
  is constant across a regular interval.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.Smooth.Morse

noncomputable section

variable {ψ : Submission.Diffeo} {g : R3 → ℝ} {a b : ℝ}

/-- The time-one map of a `SublevelTransport` is continuous. -/
theorem SublevelTransport.continuous_φ (T : SublevelTransport ψ g a b) : Continuous T.φ := by
  have h1 : Continuous (fun x : R3 => Function.uncurry T.H (1, x)) :=
    T.cont.comp (continuous_const.prodMk continuous_id)
  have h2 : T.φ = fun x : R3 => Function.uncurry T.H (1, x) := by
    funext x
    exact (T.one x).symm
  rw [h2]
  exact h1

/-- The time-one map of a transport preserves the surface. -/
theorem SublevelTransport.mapsTo_carrier (T : SublevelTransport ψ g a b) :
    ∀ x : R3, x ∈ (torus ψ).carrier → T.φ x ∈ (torus ψ).carrier := by
  intro x hx
  have h := T.mem 1 x hx
  rwa [T.one] at h

/-- **Item 3, loop level.**  A transport across the level interval `[a,b]` (with `a ≤ b`) gives the
loop-level equivalence of the two sublevel regions `F ∩ {g < a}` and `F ∩ {g < b}`.

The forward direction is monotonicity: a loop below `a` is also below `b`, and it is its own
transport (same winding vector).  The backward direction is the transport: a loop `γ` below `b`
is sent to the loop `T.φ ∘ γ` below `a`, which is homotopic to `γ` through the closed curves
`u ↦ T.H u ∘ γ` and therefore has the same winding vector
(`Work.SurgeryInvariance.windingOf_map_eq`). -/
theorem SublevelTransport.toRegionEquivalent (T : SublevelTransport ψ g a b) (hab : a ≤ b) :
    Work.SurgeryInvariance.RegionEquivalent (torus ψ) (region ψ g a) (region ψ g b) := by
  refine ⟨?_, ?_⟩
  · intro γ hγ
    exact ⟨γ, fun t => region_mono ψ g hab (hγ t), rfl⟩
  · intro γ hγ
    refine ⟨Work.SurgeryInvariance.curveMap γ T.φ T.continuous_φ T.mapsTo_carrier, ?_, ?_⟩
    · intro t
      exact T.maps (γ t) (hγ t)
    · exact Work.SurgeryInvariance.windingOf_map_eq γ T.continuous_φ T.mapsTo_carrier
        T.H T.cont (fun x => T.zero x) (fun x => T.one x) T.mem

/-- **A family of transports across every regular interval gives the loop-level
`RegularEquivalent`.**  This is the analytic input of the sweep in the form consumed by the
assembly of `Submission.Work.Smooth.Morse.Sweep`. -/
theorem regularEquivalent_of_transport
    (h : ∀ a b : ℝ, a ≤ b → (∀ t ∈ Set.Icc a b, IsRegularValue ψ g t) →
      Nonempty (SublevelTransport ψ g a b)) :
    RegularEquivalent ψ g :=
  fun a b hab hreg => (Classical.choice (h a b hab hreg)).toRegionEquivalent hab

/-- Across a regular interval the winding span is constant. -/
theorem RegularEquivalent.windingSpan_eq {a b : ℝ}
    (h : Work.SurgeryInvariance.RegionEquivalent (torus ψ) (region ψ g a) (region ψ g b)) :
    Work.SurgeryInvariance.WindingSpan (torus ψ) (region ψ g a) =
      Work.SurgeryInvariance.WindingSpan (torus ψ) (region ψ g b) :=
  Work.SurgeryInvariance.RegionEquivalent.windingSpan_eq h

/-- Across a regular interval the essential-piece invariant is constant. -/
theorem RegularEquivalent.containsEssentialLoop_iff {a b : ℝ}
    (h : Work.SurgeryInvariance.RegionEquivalent (torus ψ) (region ψ g a) (region ψ g b)) :
    (torus ψ).ContainsEssentialLoop (region ψ g a) ↔
      (torus ψ).ContainsEssentialLoop (region ψ g b) := by
  rw [← Work.SurgeryInvariance.windingSpan_ne_bot_iff (torus ψ) (region ψ g a),
    ← Work.SurgeryInvariance.windingSpan_ne_bot_iff (torus ψ) (region ψ g b),
    h.windingSpan_eq]

/-- **Item 3, from the isolated analytic input.**  The transport of sublevel regions across the
regular intervals implies the loop-level `RegularEquivalent` of the level family. -/
theorem regularEquivalent_of_hasRegularTransport (ψ : Submission.Diffeo) {g : R3 → ℝ}
    (h : HasRegularTransport ψ g) : RegularEquivalent ψ g :=
  regularEquivalent_of_transport h

end

end Work.Smooth.Morse