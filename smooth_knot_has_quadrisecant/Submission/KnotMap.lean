import ChallengeDeps
import Submission.Helpers

open LeanEval.KnotTheory.Quadrisecant

/-!
# Layer A1/A2 — the parameter circle and its homeomorphism onto the knot

A smooth knot `r : ℝ → Space` is `period`-periodic, so it factors through the
additive circle `AddCircle period` (the topological circle `S¹`, quotiented
out by the period).  This module constructs that factorization `knotMap r`,
proves it continuous and injective (using the injectivity of `r` on one
period), identifies its range with the knot image `r '' Ico 0 period`, and
builds the resulting homeomorphism

    knotMap_homeo r h : AddCircle period ≃ₜ Set.range (knotMap r)

(`AddCircle period` is compact and `Space` is Hausdorff, so a continuous
bijection is automatically a homeomorphism; the range is a compact subset of
`Space`.)

This is the base layer for the chord / trisecant topology of Kuperberg's
argument: chords of the knot will be parametrized by pairs of points of this
circle, and a *cycle* of chords — the engine of the Möbius-strip counting
argument — is a loop in `AddCircle period`.

Everything here is elementary and verified (no axioms, no `sorry`).
-/

noncomputable section

namespace LeanEval.KnotTheory.Quadrisecant

/-- `period = 2π` is positive, as a typeclass fact needed by the `AddCircle`
quotient construction (and by its compactness / continuity theorems). -/
instance fact_period_pos : Fact (0 < period) :=
  ⟨period_pos⟩

/-- The quotient map of a `period`-periodic curve `r : ℝ → Space` to the
additive circle of parameters.  On the half-open period it agrees with `r`
(see `knotMap_coe`); every point of `AddCircle period` has a representative
in `Ico 0 period`, so this is the canonical factorization. -/
def knotMap (r : ℝ → Space) : AddCircle period → Space :=
  AddCircle.liftIco period 0 r

/-- `knotMap` extends `r` over the defining half-open period. -/
lemma knotMap_coe (r : ℝ → Space) {t : ℝ} (ht : t ∈ Set.Ico 0 period) :
    knotMap r (t : AddCircle period) = r t := by
  unfold knotMap
  exact AddCircle.liftIco_zero_coe_apply ht

/-- Every point of the parameter circle has a representative in `[0, period)`. -/
lemma knotMap_representative (z : AddCircle period) :
    ∃ t : ℝ, t ∈ Set.Ico 0 period ∧ (t : AddCircle period) = z :=
  AddCircle.eq_coe_Ico z

/-- A continuous `period`-periodic curve lifts to a continuous map on the
parameter circle. -/
lemma knotMap_continuous_of (r : ℝ → Space) (hrc : Continuous r)
    (hper : Function.Periodic r period) : Continuous (knotMap r) := by
  unfold knotMap
  apply AddCircle.liftIco_zero_continuous
  · simpa using (hper 0).symm
  · exact hrc.continuousOn

/-- A smooth knot induces a continuous map on the parameter circle. -/
lemma IsSmoothKnot.knotMap_continuous {r : ℝ → Space} (h : IsSmoothKnot r) :
    Continuous (knotMap r) :=
  knotMap_continuous_of r h.continuous h.periodic

/-- A smooth knot is injective on the parameter circle (equivalently, distinct
parameters modulo the period give distinct points of the knot). -/
lemma knotMap_injective {r : ℝ → Space} (h : IsSmoothKnot r) :
    Function.Injective (knotMap r) := by
  intro x y hxy
  rcases knotMap_representative x with ⟨tx, htx, hx⟩
  rcases knotMap_representative y with ⟨ty, hty, hy⟩
  have h1 : knotMap r x = r tx := by
    rw [← hx]
    exact knotMap_coe r htx
  have h2 : knotMap r y = r ty := by
    rw [← hy]
    exact knotMap_coe r hty
  have hte : tx = ty := by
    apply h.injective_on_period htx hty
    rw [h1, h2] at hxy
    exact hxy
  rw [← hx, ← hy, hte]

/-- The range of the induced circle map is exactly the knot image over one
period. -/
lemma knotMap_range (r : ℝ → Space) :
    Set.range (knotMap r) = r '' Set.Ico 0 period := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    rcases knotMap_representative x with ⟨tx, htx, hx⟩
    refine ⟨tx, htx, ?_⟩
    rw [← hx]
    exact (knotMap_coe r htx).symm
  · rintro ⟨t, ht, rfl⟩
    exact ⟨(t : AddCircle period), knotMap_coe r ht⟩

/-- The image of the knot in `Space` is compact (it is the continuous image of
the compact circle of parameters). -/
lemma knotMap_range_isCompact {r : ℝ → Space} (h : IsSmoothKnot r) :
    IsCompact (Set.range (knotMap r)) :=
  isCompact_range h.knotMap_continuous

/-- The smooth knot, viewed on its parameter circle, is a *topological circle*:
`AddCircle period ≃ₜ K`, homeomorphic onto its compact image. -/
noncomputable def knotMap_homeo (r : ℝ → Space) (h : IsSmoothKnot r) :
    AddCircle period ≃ₜ Set.range (knotMap r) := by
  refine Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofInjective (knotMap r) (knotMap_injective h)) ?_
  change Continuous (fun x : AddCircle period =>
    (⟨knotMap r x, ⟨x, rfl⟩⟩ : Set.range (knotMap r)))
  exact Continuous.subtype_mk h.knotMap_continuous _

/-- The homeomorphism commutes with the knot map (by construction). -/
@[simp]
lemma knotMap_homeo_apply (r : ℝ → Space) (h : IsSmoothKnot r) (x : AddCircle period) :
    (knotMap_homeo r h x : Set.range (knotMap r)).1 = knotMap r x :=
  rfl

end LeanEval.KnotTheory.Quadrisecant
