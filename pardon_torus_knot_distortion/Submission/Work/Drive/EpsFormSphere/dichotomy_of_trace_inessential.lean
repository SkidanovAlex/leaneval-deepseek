import Mathlib
import Submission.Work.SurgeryInvariance.Defs
import Submission.Work.BoxShrink.PinchOff.windingSpan_bot_or_top_of_inessential_boundary

/-!
# P4: Pardon's dichotomy at a level whose trace is inessential

The `ε`-form of Pardon's Lemma 3 is driven by a one-parameter family of regions of the surface
`F = P.carrier`, and at every *regular* level `lam` of the family Pardon's dichotomy pins the
winding span of the region to `⊥` or `⊤`: the trace of the level in the surface is a finite family of
pairwise disjoint simple closed curves, Pardon's Lemma 2 (`mustbeinessential`, from the count on the
level sphere) makes every one of them *inessential* in `F`, and then a region bounded by inessential
curves carries no loop or the whole of `H₁`.

This module isolates the *second* half of that step — the topological part, which needs no counting —
in the form in which the sweep design consumes it: given that the frontier *in the surface* of a
region `X` is exactly the union of finitely many pairwise disjoint simple inessential closed curves
of `F`, the span of `X` is `⊥` or `⊤`.  The curve family, the inessentiality of each curve and the
identification of the trace with the frontier of the region are the input the counting supplies; the
argument below is the peel of
`Work.BoxShrink.PinchOff.windingSpan_bot_or_top_of_inessential_boundary`.

The two frontier clauses are the two halves of "the trace is exactly the frontier of the region":

* `hfront`: a point of the surface which is not on the trace and not in the region is not in the
  closure of the region either (it lies strictly behind the wall);
* `hon`: every point of the trace is in the closure of the region and outside it.

Together they give that the complement of the trace is the disjoint union of the region `X` and the
open piece `Y = {x ∈ F | x ∉ closure X}` behind the wall, after which the peel applies.
-/

namespace Work.Drive.EpsFormSphere

open LeanEval.KnotTheory.PardonDistortion
open Set

/-- **P4 (topological half): Pardon's dichotomy from an inessential trace.**

If the frontier in `F = P.carrier` of a region `X` is exactly the union of finitely many pairwise
disjoint simple closed curves of `F`, each *inessential* in `F`, then `X` realises no winding class or
all of them: `WindingSpan P X = ⊥` or `WindingSpan P X = ⊤`. -/
theorem windingSpan_bot_or_top_of_trace_inessential {P : Work.CoreTopology.ParamTorus}
    {X : Set R3} {n : ℕ} {γ : Fin n → Work.CoreTopology.ClosedCurve P}
    (hXc : X ⊆ P.carrier)
    (hsimple : ∀ i, Work.CoreTopology.IsSimple P (γ i))
    (hiness : ∀ i, ¬ Work.CoreTopology.IsEssential P (γ i))
    (hdisj : ∀ i j : Fin n, i ≠ j → Disjoint (Set.range (γ i).γ) (Set.range (γ j).γ))
    (hX : Work.SurgeryInvariance.IsOpenInCarrier P X)
    (hfront : ∀ x ∈ P.carrier, x ∉ X → (∀ (i : Fin n) (t : ℝ), (γ i).γ t ≠ x) →
      x ∉ closure X)
    (hon : ∀ (i : Fin n) (t : ℝ), (γ i).γ t ∈ closure X ∧ (γ i).γ t ∉ X) :
    Work.SurgeryInvariance.WindingSpan P X = ⊥ ∨
      Work.SurgeryInvariance.WindingSpan P X = ⊤ := by
  -- the piece behind the wall: the surface points outside the closure of the region
  set Y : Set R3 := P.carrier ∩ {x : R3 | x ∉ closure X} with hYdef
  have hYopen : Work.SurgeryInvariance.IsOpenInCarrier P Y := by
    rw [Work.SurgeryInvariance.IsOpenInCarrier]
    have hpre : (Subtype.val ⁻¹' Y : Set P.carrier) = Subtype.val ⁻¹' (closure X)ᶜ := by
      ext x
      exact ⟨fun hx => hx.2, fun hx => ⟨x.2, hx⟩⟩
    rw [hpre]
    exact isClosed_closure.isOpen_compl.preimage continuous_subtype_val
  refine Work.BoxShrink.PinchOff.windingSpan_bot_or_top_of_inessential_boundary
    hsimple hiness hdisj hX hYopen ?_ ?_
  · rw [Set.disjoint_left]
    rintro x hxX hxY
    exact hxY.2 (subset_closure hxX)
  · ext x
    constructor
    · rintro ⟨hxc, hnot⟩
      by_cases hxX : x ∈ X
      · exact Or.inl hxX
      · refine Or.inr ⟨hxc, ?_⟩
        intro hxc'
        exact hfront x hxc hxX (fun i t ht => hnot (Set.mem_iUnion.mpr
          ⟨i, Set.mem_range.mpr ⟨t, ht⟩⟩)) hxc'
    · rintro (hxX | hxY)
      · refine ⟨hXc hxX, ?_⟩
        intro hmem
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hmem
        obtain ⟨t, ht⟩ := Set.mem_range.mp hi
        exact (hon i t).2 (by rw [ht]; exact hxX)
      · refine ⟨hxY.1, ?_⟩
        intro hmem
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hmem
        obtain ⟨t, ht⟩ := Set.mem_range.mp hi
        exact hxY.2 (by rw [← ht]; exact (hon i t).1)

/-- The same dichotomy for a family indexed by an arbitrary finite type — the form in which the
slicings of the level sphere (`Work.InnermostDisk.SphereSlicing`) present their curves. -/
theorem windingSpan_bot_or_top_of_trace_inessential_fintype {P : Work.CoreTopology.ParamTorus}
    {X : Set R3} {ι : Type} [Fintype ι] {γ : ι → Work.CoreTopology.ClosedCurve P}
    (hXc : X ⊆ P.carrier)
    (hsimple : ∀ i, Work.CoreTopology.IsSimple P (γ i))
    (hiness : ∀ i, ¬ Work.CoreTopology.IsEssential P (γ i))
    (hdisj : ∀ i j : ι, i ≠ j → Disjoint (Set.range (γ i).γ) (Set.range (γ j).γ))
    (hX : Work.SurgeryInvariance.IsOpenInCarrier P X)
    (hfront : ∀ x ∈ P.carrier, x ∉ X → (∀ (i : ι) (t : ℝ), (γ i).γ t ≠ x) →
      x ∉ closure X)
    (hon : ∀ (i : ι) (t : ℝ), (γ i).γ t ∈ closure X ∧ (γ i).γ t ∉ X) :
    Work.SurgeryInvariance.WindingSpan P X = ⊥ ∨
      Work.SurgeryInvariance.WindingSpan P X = ⊤ := by
  classical
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  set γ' : Fin (Fintype.card ι) → Work.CoreTopology.ClosedCurve P := fun k => γ (e.symm k)
    with hγ'def
  refine windingSpan_bot_or_top_of_trace_inessential (n := Fintype.card ι) (γ := γ') (X := X) hXc ?_ ?_ ?_ hX ?_ ?_
  · intro k
    simpa [hγ'def] using hsimple (e.symm k)
  · intro k
    simpa [hγ'def] using hiness (e.symm k)
  · intro k l hkl
    simpa [hγ'def] using hdisj (e.symm k) (e.symm l) (fun h => hkl (by simpa using congrArg e h))
  · intro x hxc hxX hoff
    refine hfront x hxc hxX ?_
    intro i t
    simpa [hγ'def] using hoff (e i) t
  · intro k t
    simpa [hγ'def] using hon (e.symm k) t

end Work.Drive.EpsFormSphere
