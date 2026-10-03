/-
Copyright: subproject `OROneRel` -- one-relator combinatorics (node N2).

# Vertex data of a Magnus--Moldavanskii step (exposing the vertex relator)

`HasMMStepData r` (see `Submission.Work.OROneRel.MMAssembly`) is the `Prop` recording that
`⟨α | r⟩` is an HNN extension of some strictly shorter one-relator group.  When the step is
*assembled* from a specific vertex group it is convenient to have the vertex data separated from the
norm bound: `HasMMVertexData r β r'` records that `⟨α | r⟩` is an HNN extension of `⟨β | r'⟩` whose
associated subgroups are Magnus subgroups of `⟨β | r'⟩`, together with the requirement that `r'` be
a legal level of the hierarchy (terminal, or cyclically reduced and nontrivial).

Why separate them: the vertex of the exponent-sum-zero Magnus step is the Magnus rewriting
`mmW t r` of a relator which may be *longer* than `r` after a Nielsen ("Euclidean") change of
presentation, while the rewriting itself is short.  The relevant norm bound is therefore
`relatorNorm (mmW t (ψ r)) < relatorNorm r`, which is not the bound appearing in
`HasMMStepData (ψ r)`; separating the vertex from the bound is what makes the transport across such
a `ψ` possible.

This file is `sorry`-free; it is imported by the lemma requests of the surrounding development.
-/
import Mathlib
import Submission.Work.OROneRel.MMAssembly

namespace Work.OROneRel

universe u

/-- **Vertex data.**  `⟨α | r⟩` is an HNN extension of the one-relator group `⟨β | r'⟩` with
associated subgroups Magnus subgroups of `⟨β | r'⟩`, and `r'` is a legal level of the hierarchy
(terminal, or cyclically reduced and nontrivial).  The norm bound `relatorNorm r' < relatorNorm r`
is deliberately *not* part of this predicate. -/
def HasMMVertexData {α : Type u} (r : FreeGroup α) (β : Type u) (r' : FreeGroup β) : Prop :=
  (IsTerminalRelator r' ∨ (IsCyclicallyReducedRelator r' ∧ r' ≠ 1)) ∧
    ∃ (A B : Subgroup (PresentedGroup ({r'} : Set (FreeGroup β)))),
      IsMagnusSubgroup A ∧ IsMagnusSubgroup B ∧ ∃ (φ : A ≃* B),
        Nonempty (PresentedGroup ({r} : Set (FreeGroup α)) ≃*
          HNNExtension (PresentedGroup ({r'} : Set (FreeGroup β))) A B φ)

/-- Unpacking: `HasMMStepData r` is exactly `HasMMVertexData r β r'` together with the strict norm
bound on the vertex relator. -/
theorem hasMMStepData_iff {α : Type u} (r : FreeGroup α) :
    HasMMStepData r ↔ ∃ (β : Type u) (r' : FreeGroup β),
      relatorNorm r' < relatorNorm r ∧ HasMMVertexData r β r' := by
  constructor
  · rintro ⟨β, r', hlt, hgood, A, B, hA, hB, φ, h⟩
    exact ⟨β, r', hlt, hgood, A, B, hA, hB, φ, h⟩
  · rintro ⟨β, r', hlt, hgood, A, B, hA, hB, φ, h⟩
    exact ⟨β, r', hlt, hgood, A, B, hA, hB, φ, h⟩

/-- **Building the step from vertex data.**  If `⟨α | r⟩` is an HNN extension of `⟨β | r'⟩` over
Magnus subgroups with `r'` short, then `r` has the one-step data. -/
theorem hasMMStepData_of_vertexData {α : Type u} {r : FreeGroup α} {β : Type u} {r' : FreeGroup β}
    (hlt : relatorNorm r' < relatorNorm r) (h : HasMMVertexData r β r') :
    HasMMStepData r :=
  (hasMMStepData_iff r).mpr ⟨β, r', hlt, h⟩

/-- **Transport of vertex data along an isomorphism of the presenting groups.**  If `⟨α | r⟩` and
`⟨β | R⟩` present isomorphic groups then vertex data for `R` is vertex data for `r`. -/
theorem hasMMVertexData_of_iso {α β : Type u} {r : FreeGroup α} {R : FreeGroup β}
    (e : PresentedGroup ({r} : Set (FreeGroup α)) ≃*
      PresentedGroup ({R} : Set (FreeGroup β)))
    {γ : Type u} {s : FreeGroup γ} (h : HasMMVertexData R γ s) :
    HasMMVertexData r γ s := by
  obtain ⟨hgood, A, B, hA, hB, φ, ⟨e₂⟩⟩ := h
  exact ⟨hgood, A, B, hA, hB, φ, ⟨e.trans e₂⟩⟩

/-- **The step from vertex data of an isomorphic presentation, with the norm bound measured against
the *original* relator.**  This is the form needed by the Nielsen ("Euclidean") route: `R = ψ r` may
be much longer than `r`, but the vertex relator `s` of the step for `R` need only be shorter than the
original `r`. -/
theorem hasMMStepData_of_vertexData_iso {α β : Type u} {r : FreeGroup α} {R : FreeGroup β}
    (e : PresentedGroup ({r} : Set (FreeGroup α)) ≃*
      PresentedGroup ({R} : Set (FreeGroup β)))
    {γ : Type u} {s : FreeGroup γ} (h : HasMMVertexData R γ s)
    (hlt : relatorNorm s < relatorNorm r) :
    HasMMStepData r :=
  hasMMStepData_of_vertexData hlt (hasMMVertexData_of_iso e h)

end Work.OROneRel
