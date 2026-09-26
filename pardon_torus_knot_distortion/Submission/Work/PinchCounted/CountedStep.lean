import Submission.Work.PinchCounted.Assemble

/-!
# One local move of Pardon's pinching family, with the counting it consumes

`CountedSweep` (`Assemble.lean`) records the pinching family as a *function* of the parameter, with
the local moves spread over the fields `regular` and `surgery`.  The residue of the counted form of
Pardon's Lemma 3 is then "such a family exists", and the only thing that is ever used about it is
the *local move at each parameter*.  This module isolates that datum as a single `Prop`,
`CountedStep P β A A'`, so that the residual can be stated *without* the auxiliary fields of
`CountedSweep` (no global set of exceptional parameters, no global sphere family, no ε-uniformity in
the statement of the residual).

A `CountedStep` is one of the three local models of a `2`-surgery of the sphere family:

1. `RegionEquivalent P A A'` — the loop content is transported ("no surgery, no change");
2. the region changes by an open piece `Z` whose loops are matched, with their winding vectors, by
   loops of a clean sphere `S` meeting the knot `β` fewer than `I(F,β)` times.  This is Pardon's
   description of the pinched neck: the changed piece is a collar of the trace `F ∩ S` of an
   intermediate sphere, so its loops are homotopic in `F` to loops of that trace, and Pardon's
   Lemma 2 makes those inessential;
3. the region changes by an open piece of vanishing winding span
   (`Work.SurgeryInvariance.SurgeryStepZero`) — the pure geometric local model of a `2`-surgery.

The three are not exclusive: (2) *implies* (3) in the counted setting, by Pardon's Lemma 2
(`CountedSweep.windingSpan_eq_bot_of_loops_match`), which is precisely the content of Pardon's
counting argument.  Recording the union makes the residual of `Local.lean` the weakest of the
ladder — it is implied both by `CountedStep2` (through case 2) and by `CountedPinchSweep`
(through case 3).

The two facts proved here are the ones the residual consumes:

* `CountedStep.windingSpan_eq` — a `CountedStep` does not change the winding span;
* `countedStep_of_countedSweep` — every local move of a `CountedSweep` is a `CountedStep`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.PinchCounted

noncomputable section

variable {P : Work.CoreTopology.ParamTorus} {β : Work.CoreTopology.ClosedCurve P}

/-- **One local move of Pardon's pinching family, with the counting.**  Either the loop content of
the region is transported, or the region changes by an open piece `Z` whose loops are matched, with
the same winding vectors, by loops of a clean sphere `S` meeting the knot `β` fewer than `I(F,β)`
times, or the region changes by an open piece of vanishing winding span.

In the first two alternatives both pieces are required to be open in the surface
(`IsOpenInCarrier`) and disjoint, in the shape of the local model
`Work.SurgeryInvariance.SurgeryStepZero`; the vanishing of the winding span of `Z` is *not* asked
for in the second alternative, it is derived (`CountedStep.windingSpan_eq`). -/
def CountedStep (P : Work.CoreTopology.ParamTorus) (β : Work.CoreTopology.ClosedCurve P)
    (A A' : Set R3) : Prop :=
  Work.SurgeryInvariance.RegionEquivalent P A A' ∨
    (∃ Z S : Set R3, Work.SurgeryInvariance.IsOpenInCarrier P Z ∧
      Work.SurgeryInvariance.IsOpenInCarrier P A ∧
      Work.SurgeryInvariance.IsOpenInCarrier P A' ∧
      Work.InnermostDisk.CleansInSphere P S ∧
      Set.encard (Set.range β.γ ∩ S) < Work.CoreTopology.pardonsI P β ∧
      (∀ γ : Work.CoreTopology.ClosedCurve P, (∀ u : ℝ, γ u ∈ Z) →
        ∃ γ' : Work.CoreTopology.ClosedCurve P, (∀ u : ℝ, γ' u ∈ S) ∧
          Work.SurgeryInvariance.windingOf P γ' = Work.SurgeryInvariance.windingOf P γ) ∧
      ((A = A' ∪ Z ∧ Disjoint A' Z) ∨ (A' = A ∪ Z ∧ Disjoint A Z))) ∨
    Work.SurgeryInvariance.SurgeryStepZero P A A'

theorem countedStep_def {A A' : Set R3} :
    CountedStep P β A A' ↔
      Work.SurgeryInvariance.RegionEquivalent P A A' ∨
        (∃ Z S : Set R3, Work.SurgeryInvariance.IsOpenInCarrier P Z ∧
          Work.SurgeryInvariance.IsOpenInCarrier P A ∧
          Work.SurgeryInvariance.IsOpenInCarrier P A' ∧
          Work.InnermostDisk.CleansInSphere P S ∧
          Set.encard (Set.range β.γ ∩ S) < Work.CoreTopology.pardonsI P β ∧
          (∀ γ : Work.CoreTopology.ClosedCurve P, (∀ u : ℝ, γ u ∈ Z) →
            ∃ γ' : Work.CoreTopology.ClosedCurve P, (∀ u : ℝ, γ' u ∈ S) ∧
              Work.SurgeryInvariance.windingOf P γ' = Work.SurgeryInvariance.windingOf P γ) ∧
          ((A = A' ∪ Z ∧ Disjoint A' Z) ∨ (A' = A ∪ Z ∧ Disjoint A Z))) ∨
        Work.SurgeryInvariance.SurgeryStepZero P A A' := Iff.rfl

namespace CountedStep

/-- A transport of the loop content is a `CountedStep`. -/
theorem of_regionEquivalent {A A' : Set R3}
    (h : Work.SurgeryInvariance.RegionEquivalent P A A') : CountedStep P β A A' := Or.inl h

/-- A change by an open piece of vanishing winding span is a `CountedStep`. -/
theorem of_stepZero {A A' : Set R3} (h : Work.SurgeryInvariance.SurgeryStepZero P A A') :
    CountedStep P β A A' := Or.inr (Or.inr h)

/-- **A `CountedStep` can be reversed**: each of the three local models is symmetric in the two
regions. -/
theorem symm {A A' : Set R3} (h : CountedStep P β A A') : CountedStep P β A' A := by
  rcases h with h | ⟨Z, S, hZ, hA, hA', hclean, hcount, hmatch, hcase⟩ | h
  · exact Or.inl ⟨h.2, h.1⟩
  · exact Or.inr (Or.inl ⟨Z, S, hZ, hA', hA, hclean, hcount, hmatch,
      hcase.elim (fun ⟨h1, h2⟩ => Or.inr ⟨h1, h2⟩) fun ⟨h1, h2⟩ => Or.inl ⟨h1, h2⟩⟩)
  · exact Or.inr (Or.inr h.symm)

/-- **A `CountedStep` does not change the winding span.**  In the transported case this is
`RegionEquivalent.windingSpan_eq`; in the changed-piece case the piece has vanishing winding span —
by Pardon's Lemma 2 at the intermediate sphere (`CountedSweep.windingSpan_eq_bot_of_loops_match`) in
the matched case, by hypothesis in the `SurgeryStepZero` case — and the two pieces are open and
disjoint, so `Work.SurgeryInvariance.Span.union_eq_sup` applies. -/
theorem windingSpan_eq {A A' : Set R3} (h : CountedStep P β A A') :
    Work.SurgeryInvariance.WindingSpan P A = Work.SurgeryInvariance.WindingSpan P A' := by
  rcases h with h | ⟨Z, S, hZ, hA, hA', hclean, hcount, hmatch, hcase⟩ | hstep
  · exact Work.SurgeryInvariance.RegionEquivalent.windingSpan_eq h
  · have hZbot : Work.SurgeryInvariance.WindingSpan P Z = ⊥ :=
      CountedSweep.windingSpan_eq_bot_of_loops_match hclean hcount hmatch
    rcases hcase with ⟨hAeq, hd⟩ | ⟨hA'eq, hd⟩
    · rw [hAeq, Work.SurgeryInvariance.Span.union_eq_sup hA' hZ hd, hZbot, sup_bot_eq]
    · rw [hA'eq, Work.SurgeryInvariance.Span.union_eq_sup hA hZ hd, hZbot, sup_bot_eq]
  · exact hstep.windingSpan_eq

/-- **A `CountedStep` does not change the essential-loop invariant.** -/
theorem containsEssentialLoop_iff {A A' : Set R3} (h : CountedStep P β A A') :
    P.ContainsEssentialLoop A ↔ P.ContainsEssentialLoop A' := by
  rw [← Work.SurgeryInvariance.windingSpan_ne_bot_iff P A,
    ← Work.SurgeryInvariance.windingSpan_ne_bot_iff P A', h.windingSpan_eq]

end CountedStep

/-- **Every local move of a `CountedSweep` is a `CountedStep`.**  At a regular parameter the region
is transported (`CountedSweep.regular`); at an exceptional one, either the region changes by an open
piece whose loops are matched by loops of the intermediate sphere `S_t` (`CountedSweep.surgery`) —
which is exactly case 2 of `CountedStep` — or it is transported.

This is the forgetful map which makes the reduced residual `Work.PinchCounted.CountedPinch`
*weaker* than `Work.PinchCounted.CountedStep2`. -/
theorem countedStep_of_countedSweep (D : CountedSweep P β) (t : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, |s - t| < ε → CountedStep P β (D.region t) (D.region s) := by
  by_cases ht : t ∈ D.exc
  · obtain ⟨ε, hε, hstep⟩ := D.surgery t ht
    refine ⟨ε, hε, fun s hs => ?_⟩
    rcases hstep s hs with ⟨Z, hZ, hmatch, hcase⟩ | h
    · exact Or.inr (Or.inl ⟨Z, D.sphere t, hZ, D.region_open t, D.region_open s,
        D.sphere_clean t, D.sphere_count t, hmatch, hcase⟩)
    · exact Or.inl h
  · obtain ⟨ε, hε, _, hequiv⟩ := D.regular t ht
    exact ⟨ε, hε, fun s hs => Or.inl (hequiv s hs)⟩

/-- **Every local move of a loop-level sweep is a `CountedStep`** (through the zero-span local
model, case 3 of `CountedStep`).  This is the other forgetful map of the ladder: it makes
`CountedPinch` weaker than `CountedPinchSweep` (the residual which asks for a span-preserving
pinching family). -/
theorem countedStep_of_sweepLoops (S : Work.SurgeryInvariance.SweepLoops P) (t : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, |s - t| < ε → CountedStep P β (S.region t) (S.region s) := by
  by_cases ht : t ∈ S.exc
  · obtain ⟨ε, hε, hstep⟩ := S.surgery t ht
    exact ⟨ε, hε, fun s hs => hstep s hs |>.elim (fun h => Or.inr (Or.inr h))
      (fun h => Or.inl h)⟩
  · obtain ⟨ε, hε, _, hequiv⟩ := S.regular t ht
    exact ⟨ε, hε, fun s hs => Or.inl (hequiv s hs)⟩

end

end Work.PinchCounted
