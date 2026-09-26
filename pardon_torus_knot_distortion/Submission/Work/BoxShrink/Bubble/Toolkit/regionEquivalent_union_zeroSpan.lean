import Mathlib
import Submission.Work.BoxShrink.Bubble.Basic

namespace Work.BoxShrink.Bubble.Toolkit

open LeanEval.KnotTheory.PardonDistortion

/-- The **constant closed curve** at a point `a` of the torus `F = P.carrier`.  It is a closed
curve of `F` (continuous, `2π`-periodic, lying in `F`) and, as a loop, it is null-homotopic in
`F`. -/
def constCurve (P : Work.CoreTopology.ParamTorus) (a : R3) (ha : a ∈ P.carrier) :
    Work.CoreTopology.ClosedCurve P where
  γ := fun _ => a
  cont := continuous_const
  periodic := fun _ => rfl
  mem := fun _ => ha

/-- The winding vector of the constant curve is zero: a constant curve lifts to a constant map of
the parameter plane, which advances by `0` over a period. -/
theorem windingOf_constCurve {P : Work.CoreTopology.ParamTorus} {a : R3}
    (ha : a ∈ P.carrier) :
    Work.SurgeryInvariance.windingOf P (constCurve P a ha) = (0, 0) := by
  obtain ⟨x, y, hxy⟩ := (P.mem_carrier_iff a).mp ha
  let L : Work.CoreTopology.LiftOf P (constCurve P a ha) :=
    { Θ := fun _ => x
      Φ := fun _ => y
      contΘ := continuous_const
      contΦ := continuous_const
      lifts := fun _ => hxy }
  rw [Work.SurgeryInvariance.windingOf_eq P (constCurve P a ha) L]
  have h1 : ((L.winding).1 : ℝ) * (2 * Real.pi) = 0 := by
    have hspec := L.winding_spec.1
    have hconst : L.Θ (2 * Real.pi) = L.Θ 0 := rfl
    linarith [hspec, hconst]
  have h2 : ((L.winding).2 : ℝ) * (2 * Real.pi) = 0 := by
    have hspec := L.winding_spec.2
    have hconst : L.Φ (2 * Real.pi) = L.Φ 0 := rfl
    linarith [hspec, hconst]
  have hw1 : (L.winding).1 = 0 := by
    rcases mul_eq_zero.mp h1 with h | h
    · exact_mod_cast h
    · exact absurd h (by positivity)
  have hw2 : (L.winding).2 = 0 := by
    rcases mul_eq_zero.mp h2 with h | h
    · exact_mod_cast h
    · exact absurd h (by positivity)
  exact Prod.ext hw1 hw2

/-- **Adding an open piece of zero winding content does not change the loops of a region.**  If
`A` and `Z` are disjoint open pieces of the surface `F = P.carrier`, `Z` contains no essential
loop (`WindingSpan P Z = ⊥`) and `A` meets `F`, then `A ∪ Z` and `A` are `RegionEquivalent`:
every closed curve of `F` inside `A ∪ Z` is matched by a closed curve inside `A` with the same
winding vector, and conversely.

The point is that a connected curve cannot cross between the two disjoint open pieces
(`Work.SurgeryInvariance.Span.curve_subset_of_union`): a curve of `A ∪ Z` lies entirely in `A`
(whence it is its own match) or entirely in `Z` (whence its winding vanishes, and the constant
curve at a point of `A` matches it). -/
theorem regionEquivalent_union_zeroSpan
    {P : Work.CoreTopology.ParamTorus}
    {A Z : Set LeanEval.KnotTheory.PardonDistortion.R3}
    (hA : Work.SurgeryInvariance.IsOpenInCarrier P A)
    (hZ : Work.SurgeryInvariance.IsOpenInCarrier P Z) (hdisj : Disjoint A Z)
    (hspan : Work.SurgeryInvariance.WindingSpan P Z = ⊥)
    (ha : ∃ a : LeanEval.KnotTheory.PardonDistortion.R3, a ∈ A ∧ a ∈ P.carrier) :
    Work.SurgeryInvariance.RegionEquivalent P (A ∪ Z) A := by
  obtain ⟨a, haA, hacar⟩ := ha
  -- a closed curve of the torus contained in `Z` has zero winding
  have hZzero : ∀ γ : Work.CoreTopology.ClosedCurve P, (∀ t : ℝ, γ t ∈ Z) →
      Work.SurgeryInvariance.windingOf P γ = (0, 0) := by
    intro γ hγ
    by_contra hne
    have hess : Work.CoreTopology.IsEssential P γ :=
      (Work.SurgeryInvariance.isEssential_iff_windingOf_ne_zero P γ).mpr hne
    have hcon : P.ContainsEssentialLoop Z := ⟨γ, hess, hγ⟩
    exact (Work.SurgeryInvariance.windingSpan_ne_bot_iff P Z).mpr hcon hspan
  refine ⟨?_, ?_⟩
  · -- loops of `A ∪ Z` are matched by loops of `A`
    intro γ hγ
    rcases Work.SurgeryInvariance.Span.curve_subset_of_union hA hZ hdisj γ hγ with h | h
    · exact ⟨γ, h, rfl⟩
    · exact ⟨constCurve P a hacar, fun _ => haA,
        by rw [windingOf_constCurve hacar, hZzero γ h]⟩
  · -- loops of `A` are loops of `A ∪ Z`
    intro γ hγ
    exact ⟨γ, fun t => Or.inl (hγ t), rfl⟩

end Work.BoxShrink.Bubble.Toolkit
