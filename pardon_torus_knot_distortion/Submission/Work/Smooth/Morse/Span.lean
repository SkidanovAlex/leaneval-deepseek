import Mathlib
import Submission.Work.Smooth.Morse.Defs
import Submission.Work.SurgeryInvariance.API

/-!
# The winding span of a region contained in a union of two open pieces

At a critical value of `g|_F` the sublevel region `F ∩ {g < t₀}` is contained in the union of the
previous region `F ∩ {g < t₀ - ε}` and the piece of the surface added by the surgery (the trace of
a small ball around the critical point).  Both pieces are open in the surface and disjoint, so a
loop of the torus inside the region lies entirely in one of them — this is
`Work.SurgeryInvariance.Span.curve_subset_of_union`, whose hypotheses are openness and
disjointness, not a covering by exactly the region.

Consequently the winding span of the region is bounded by the span of the previous region as soon
as the added piece has zero winding span.  This is the form in which the local model at a critical
value is used; it is the "one-sided" version of
`Work.SurgeryInvariance.Span.union_eq_sup`, and it is what makes the span locally constant at a
critical value even though the region at the critical value itself is neither the region below nor
the region above.

## Main result

* `Work.Smooth.Morse.WindingSpan.le_of_subset_union`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.Smooth.Morse

noncomputable section

/-- **The winding span of a region contained in the union of two disjoint open pieces is bounded by
the span of the first piece, if the second piece has zero winding span.**

Every loop of the region lies in one of the two pieces (`curve_subset_of_union`, using that the
pieces are open in the surface and disjoint and that the loop's image is covered); in the second
piece its winding vector is zero because that piece has zero winding span. -/
theorem WindingSpan.le_of_subset_union (ψ : Submission.Diffeo) {A B Z : Set R3}
    (hB : Work.SurgeryInvariance.IsOpenInCarrier (torus ψ) B)
    (hZ : Work.SurgeryInvariance.IsOpenInCarrier (torus ψ) Z)
    (hdisj : Disjoint B Z)
    (hZspan : Work.SurgeryInvariance.WindingSpan (torus ψ) Z = ⊥)
    (hsub : A ⊆ B ∪ Z) :
    Work.SurgeryInvariance.WindingSpan (torus ψ) A ≤
      Work.SurgeryInvariance.WindingSpan (torus ψ) B := by
  rw [Work.SurgeryInvariance.WindingSpan, Submodule.span_le]
  rintro v ⟨γ, hγ, rfl⟩
  rcases Work.SurgeryInvariance.Span.curve_subset_of_union hB hZ hdisj γ
      (fun t => hsub (hγ t)) with h | h
  · exact Submodule.subset_span ⟨γ, h, rfl⟩
  · have hmem : ((((Work.SurgeryInvariance.windingOf (torus ψ) γ).1 : ℤ) : ℚ),
        (((Work.SurgeryInvariance.windingOf (torus ψ) γ).2 : ℤ) : ℚ)) ∈
        Work.SurgeryInvariance.WindingSpan (torus ψ) Z :=
      Submodule.subset_span ⟨γ, h, rfl⟩
    rw [hZspan] at hmem
    have hmem0 : ((((Work.SurgeryInvariance.windingOf (torus ψ) γ).1 : ℤ) : ℚ),
        (((Work.SurgeryInvariance.windingOf (torus ψ) γ).2 : ℤ) : ℚ)) = 0 := by
      simpa using hmem
    have hzero : Work.SurgeryInvariance.windingOf (torus ψ) γ = 0 :=
      Work.SurgeryInvariance.intPair_cast_eq_zero_iff _ |>.mp hmem0
    rw [hzero]
    exact Submodule.zero_mem _

end

end Work.Smooth.Morse
