import ChallengeDeps
import Submission.Helpers
import Submission.KnotMap
import Submission.SecantSpace
import Submission.QuadrisecantChord
import Submission.TrisecantClosed

open LeanEval.KnotTheory.Quadrisecant

/-!
# Layer A (iv) — degenerate limits of quadrisecant configurations

A *quadrisecant configuration* of a smooth knot `r` is a quadruple of
parameters `(a, b, z, w)`, pairwise distinct, with the `z`-th and `w`-th
knot points strictly inside the chord from `a` to `b` (two strict middle
points; `quadrisecantData r`, equivalently `QuadrisecantChord r`).  This
module analyses what happens to families of such configurations as they
degenerate — the elementary content behind Kuperberg's "by compactness,
$\{Q_i\}$ has a convergent subsequence" step, freed of any generic-position
hypotheses.

The object that stays closed under degeneration is the *attached*
two-middle data with middle points on the **closed** chord:

    closedDoubleMiddleData r :=
      { (a, b, z, w) | knotMap z ∈ [knotMap a, knotMap b] ∧ knotMap w ∈ [knotMap a, knotMap b] }.

It is closed in the compact parameter quadruple cube
(`isClosed_closedDoubleMiddleData`): it is the preimage of the square of the
closed attached data `closedMiddleData r` (TrisecantClosed.lean) under a
continuous map, so it is compact as well
(`isCompact_closedDoubleMiddleData`).  Its strict counterpart
`openDoubleMiddleData r` (both middle points strictly inside) lies inside it,
hence

    closure (openDoubleMiddleData r) ⊆ closedDoubleMiddleData r :

every limit of strict two-middle data still has both middle points on the
closed chord (`closure_openDoubleMiddleData_subset_closedDoubleMiddleData`).

The sharp statement is the **nondegenerate-limit characterization**: among
configurations whose four parameters stay pairwise distinct, "two middle
points on the closed chord" already means "two middle points strictly
inside" (a non-endpoint of a closed segment lies in its interior —
`mem_openSegment_of_ne_left_right`, Mathlib; parameters are distinct
precisely because `knotMap` is injective).  Hence

    quadrisecantData r =
      closure (openDoubleMiddleData r) ∩ { q | QuadDistinct q }         (✶)

(`quadrisecantData_eq_closure_openDouble_inter`): a configuration is an
honest quadrisecant **iff** it is a nondegenerate (pairwise distinct) limit
of strict two-middle configurations.  In particular any such limit that has
not degenerated its four parameters is already a genuine quadrisecant
(`quadrisecant_of_closure_nondegenerate`), and `QuadrisecantChord r` is
exactly non-emptiness of the quadrisecant data
(`quadrisecantChord_iff_quadrisecantData_nonempty`).  This is the set-level
replacement for the sequential-compactness step: any family of
quadrisecant configurations has its limits inside the compact
`closedDoubleMiddleData`, and those limits that remain nondegenerate are
quadrisecants.

Everything here is elementary and verified (no axioms, no `sorry`).
-/

noncomputable section

namespace LeanEval.KnotTheory.Quadrisecant

/-- A quadruple of parameters `(a, b, z, w)` (right-associative product). -/
abbrev KnotParamQuad := KnotParam × KnotParam × KnotParam × KnotParam

/-- Two closed middle points on one chord: `z` and `w` (as knot points) both
lie on the closed chord from `a` to `b`.  This is the attached
(degeneration-closed) two-middle data over the compact parameter cube. -/
def closedDoubleMiddleData (r : ℝ → Space) : Set KnotParamQuad :=
  {q | IsMiddleOnClosedChord r q.1 q.2.1 q.2.2.1 ∧
    IsMiddleOnClosedChord r q.1 q.2.1 q.2.2.2}

/-- Two *strict* middle points on one chord: `z` and `w` both lie strictly
inside the chord from `a` to `b` (this is the quadrisecant condition, with
the pairwise-distinctness requirement separated out). -/
def openDoubleMiddleData (r : ℝ → Space) : Set KnotParamQuad :=
  {q | IsMiddleOnChord r q.1 q.2.1 q.2.2.1 ∧
    IsMiddleOnChord r q.1 q.2.1 q.2.2.2}

/-- Membership in the closed two-middle data, in terms of the knot points on
the two closed segments. -/
lemma mem_closedDoubleMiddleData_iff (r : ℝ → Space) {q : KnotParamQuad} :
    q ∈ closedDoubleMiddleData r ↔
      knotMap r q.2.2.1 ∈ segment ℝ (knotMap r q.1) (knotMap r q.2.1) ∧
        knotMap r q.2.2.2 ∈ segment ℝ (knotMap r q.1) (knotMap r q.2.1) := by
  simp [closedDoubleMiddleData, IsMiddleOnClosedChord]

/-- Membership in the strict two-middle data, in terms of the knot points on
the two open segments. -/
lemma mem_openDoubleMiddleData_iff (r : ℝ → Space) {q : KnotParamQuad} :
    q ∈ openDoubleMiddleData r ↔
      knotMap r q.2.2.1 ∈ openSegment ℝ (knotMap r q.1) (knotMap r q.2.1) ∧
        knotMap r q.2.2.2 ∈ openSegment ℝ (knotMap r q.1) (knotMap r q.2.1) := by
  simp [openDoubleMiddleData, IsMiddleOnChord]

/-- The closed two-middle data is the preimage, under the map that copies the
chord pair to both middle slots, of the square of the closed attached
single-middle data `closedMiddleData`. -/
lemma closedDoubleMiddleData_eq_preimage (r : ℝ → Space) :
    closedDoubleMiddleData r =
      (fun q : KnotParamQuad => ((q.1, q.2.1, q.2.2.1), (q.1, q.2.1, q.2.2.2))) ⁻¹'
        ((closedMiddleData r) ×ˢ (closedMiddleData r)) := by
  ext q
  simp [closedDoubleMiddleData, IsMiddleOnClosedChord, closedMiddleData]

/-- The closed two-middle data is closed in the (compact) parameter
quadruple cube. -/
lemma isClosed_closedDoubleMiddleData {r : ℝ → Space} (h : IsSmoothKnot r) :
    IsClosed (closedDoubleMiddleData r) := by
  rw [closedDoubleMiddleData_eq_preimage]
  exact ((isClosed_closedMiddleData h).prod (isClosed_closedMiddleData h)).preimage
    (by fun_prop :
      Continuous (fun q : KnotParamQuad =>
        ((q.1, q.2.1, q.2.2.1), (q.1, q.2.1, q.2.2.2))))

/-- Consequently the closed two-middle data are compact: any family of
two-middle configurations has all its limits inside this set. -/
lemma isCompact_closedDoubleMiddleData {r : ℝ → Space} (h : IsSmoothKnot r) :
    IsCompact (closedDoubleMiddleData r) :=
  (isClosed_closedDoubleMiddleData h).isCompact

/-- Strict two-middle data are closed two-middle data. -/
lemma openDoubleMiddleData_subset_closedDoubleMiddleData (r : ℝ → Space) :
    openDoubleMiddleData r ⊆ closedDoubleMiddleData r := by
  intro q hq
  rw [mem_openDoubleMiddleData_iff] at hq
  rw [mem_closedDoubleMiddleData_iff]
  exact ⟨openSegment_subset_segment ℝ (knotMap r q.1) (knotMap r q.2.1) hq.1,
    openSegment_subset_segment ℝ (knotMap r q.1) (knotMap r q.2.1) hq.2⟩

/-- Limits of strict two-middle data still have both middle points on the
closed chord: `closure (openDoubleMiddleData r) ⊆ closedDoubleMiddleData r`.
This is the rigorous sense in which two-middle (quadrisecant) configurations
persist under degeneration — the middle points survive on the closed chord,
exactly as attached data (Kuperberg's convergence convention). -/
lemma closure_openDoubleMiddleData_subset_closedDoubleMiddleData {r : ℝ → Space}
    (h : IsSmoothKnot r) :
    closure (openDoubleMiddleData r) ⊆ closedDoubleMiddleData r :=
  closure_minimal (openDoubleMiddleData_subset_closedDoubleMiddleData r)
    (isClosed_closedDoubleMiddleData h)

/-- An honest quadrisecant configuration: four pairwise-distinct parameters
whose chord `(a, b)` carries two strict middle points `z` and `w`.  (This is
`QuadrisecantChord` with the witnesses packaged as a point of the parameter
quadruple cube.) -/
def quadrisecantData (r : ℝ → Space) : Set KnotParamQuad :=
  {q | QuadDistinct q.1 q.2.1 q.2.2.1 q.2.2.2 ∧
    IsMiddleOnChord r q.1 q.2.1 q.2.2.1 ∧
    IsMiddleOnChord r q.1 q.2.1 q.2.2.2}

/-- Membership in the quadrisecant data, unfolded to segment memberships. -/
lemma mem_quadrisecantData_iff (r : ℝ → Space) {q : KnotParamQuad} :
    q ∈ quadrisecantData r ↔
      QuadDistinct q.1 q.2.1 q.2.2.1 q.2.2.2 ∧
        knotMap r q.2.2.1 ∈ openSegment ℝ (knotMap r q.1) (knotMap r q.2.1) ∧
          knotMap r q.2.2.2 ∈ openSegment ℝ (knotMap r q.1) (knotMap r q.2.1) := by
  simp [quadrisecantData, IsMiddleOnChord]

/-- Among pairwise-distinct configurations, "two middle points on the closed
chord" is exactly "two middle points strictly inside the chord": a point of a
closed segment different from both endpoints lies in its interior
(`mem_openSegment_of_ne_left_right`), and distinct parameters give distinct
knot points (`knotMap_injective`).  Hence the honest quadrisecant data is the
intersection of the (closed, compact) closed two-middle data with the
pairwise-distinct configurations. -/
lemma quadrisecantData_eq_closedDoubleMiddle_inter {r : ℝ → Space} (h : IsSmoothKnot r) :
    quadrisecantData r =
      closedDoubleMiddleData r ∩ {q | QuadDistinct q.1 q.2.1 q.2.2.1 q.2.2.2} := by
  ext q
  constructor
  · rintro ⟨hd, hz, hw⟩
    refine ⟨?_, hd⟩
    rw [mem_closedDoubleMiddleData_iff]
    exact ⟨openSegment_subset_segment ℝ (knotMap r q.1) (knotMap r q.2.1) hz,
      openSegment_subset_segment ℝ (knotMap r q.1) (knotMap r q.2.1) hw⟩
  · rintro ⟨hcl, hd⟩
    have hparts := hd
    rcases hparts with ⟨hab, haz, haw, hbz, hbw, hzw⟩
    have hinj : Function.Injective (knotMap r) := knotMap_injective h
    have hzseg : knotMap r q.2.2.1 ∈ segment ℝ (knotMap r q.1) (knotMap r q.2.1) :=
      (mem_closedDoubleMiddleData_iff r).mp hcl |>.1
    have hwseg : knotMap r q.2.2.2 ∈ segment ℝ (knotMap r q.1) (knotMap r q.2.1) :=
      (mem_closedDoubleMiddleData_iff r).mp hcl |>.2
    refine ⟨hd, ?_, ?_⟩
    · exact mem_openSegment_of_ne_left_right (x := knotMap r q.1) (y := knotMap r q.2.1)
        (z := knotMap r q.2.2.1)
        (by intro heq; exact haz (hinj heq))
        (by intro heq; exact hbz (hinj heq))
        hzseg
    · exact mem_openSegment_of_ne_left_right (x := knotMap r q.1) (y := knotMap r q.2.1)
        (z := knotMap r q.2.2.2)
        (by intro heq; exact haw (hinj heq))
        (by intro heq; exact hbw (hinj heq))
        hwseg

/-- **The nondegenerate-limit characterization of quadrisecants** (✶): an
honest quadrisecant configuration is exactly a *pairwise-distinct* limit of
strict two-middle configurations.  Indeed strict data are dense among the
pairwise-distinct points of the closed data (strict = closed for
nondegenerate points), and closed data are exactly the closure of strict
data.  This is the set-theoretic compactness step: quadrisecant existence is
equivalent to the existence of a nondegenerate limit of a family of
two-middle configurations. -/
theorem quadrisecantData_eq_closure_openDouble_inter {r : ℝ → Space} (h : IsSmoothKnot r) :
    quadrisecantData r =
      closure (openDoubleMiddleData r) ∩ {q | QuadDistinct q.1 q.2.1 q.2.2.1 q.2.2.2} := by
  ext q
  constructor
  · intro hq
    rw [mem_quadrisecantData_iff] at hq
    refine ⟨subset_closure ?_, hq.1⟩
    rw [mem_openDoubleMiddleData_iff]
    exact ⟨hq.2.1, hq.2.2⟩
  · rintro ⟨hcl, hd⟩
    have hqcl : q ∈ closedDoubleMiddleData r :=
      closure_openDoubleMiddleData_subset_closedDoubleMiddleData h hcl
    rw [quadrisecantData_eq_closedDoubleMiddle_inter h]
    exact ⟨hqcl, hd⟩

/-- A pairwise-distinct limit of strict two-middle configurations is a
genuine quadrisecant configuration. -/
theorem quadrisecant_of_closure_nondegenerate {r : ℝ → Space} (h : IsSmoothKnot r) :
    closure (openDoubleMiddleData r) ∩ {q | QuadDistinct q.1 q.2.1 q.2.2.1 q.2.2.2}
      ⊆ quadrisecantData r := by
  intro q hq
  rw [quadrisecantData_eq_closure_openDouble_inter h]
  exact hq

/-- The `QuadrisecantChord` predicate is exactly non-emptiness of the
quadrisecant configuration data. -/
theorem quadrisecantChord_iff_quadrisecantData_nonempty {r : ℝ → Space} :
    QuadrisecantChord r ↔ (quadrisecantData r).Nonempty := by
  constructor
  · rintro ⟨a, b, z, w, hd, hz, hw⟩
    refine ⟨(a, b, z, w), ?_⟩
    rw [mem_quadrisecantData_iff]
    exact ⟨hd, by simpa [IsMiddleOnChord] using hz, by simpa [IsMiddleOnChord] using hw⟩
  · rintro ⟨q, hq⟩
    rw [mem_quadrisecantData_iff] at hq
    exact ⟨q.1, q.2.1, q.2.2.1, q.2.2.2, hq.1,
      by simpa [IsMiddleOnChord] using hq.2.1, by simpa [IsMiddleOnChord] using hq.2.2⟩

end LeanEval.KnotTheory.Quadrisecant
