import Mathlib
import Submission.Work.SurgeryInvariance.Defs

namespace Work.SurgeryInvariance.Span

open Set

/-- **A closed curve cannot cross between the two pieces.**  If `X` and `Y` are disjoint subsets
of the torus surface `F = P.carrier`, each open in `F` for the subspace topology, then any closed
curve of the torus whose image lies in `X ∪ Y` lies entirely in `X` or entirely in `Y`.

Indeed `γ ⁻¹' X` and `γ ⁻¹' Y` are two disjoint open subsets of `ℝ` covering `ℝ`, and `ℝ` is
preconnected, so one of them is all of `ℝ`; this is exactly
`IsPreconnected.subset_or_subset` applied to `s = univ`. -/
theorem curve_subset_of_union {P : Work.CoreTopology.ParamTorus}
    {X Y : Set LeanEval.KnotTheory.PardonDistortion.R3}
    (hX : IsOpenInCarrier P X) (hY : IsOpenInCarrier P Y) (hd : Disjoint X Y)
    (γ : Work.CoreTopology.ClosedCurve P) (hγ : ∀ t : ℝ, γ t ∈ X ∪ Y) :
    (∀ t : ℝ, γ t ∈ X) ∨ (∀ t : ℝ, γ t ∈ Y) := by
  have hf : Continuous (fun t : ℝ => (⟨γ t, γ.mem t⟩ : P.carrier)) :=
    γ.cont.subtype_mk γ.mem
  have hU : IsOpen (γ.γ ⁻¹' X : Set ℝ) := by
    have heq : (γ.γ ⁻¹' X : Set ℝ) =
        (fun t : ℝ => (⟨γ t, γ.mem t⟩ : P.carrier)) ⁻¹'
          (Subtype.val ⁻¹' X : Set P.carrier) := by
      ext t; rfl
    rw [heq]; exact hX.preimage hf
  have hV : IsOpen (γ.γ ⁻¹' Y : Set ℝ) := by
    have heq : (γ.γ ⁻¹' Y : Set ℝ) =
        (fun t : ℝ => (⟨γ t, γ.mem t⟩ : P.carrier)) ⁻¹'
          (Subtype.val ⁻¹' Y : Set P.carrier) := by
      ext t; rfl
    rw [heq]; exact hY.preimage hf
  have hdUV : Disjoint (γ.γ ⁻¹' X) (γ.γ ⁻¹' Y) := by
    rw [Set.disjoint_iff]
    rintro t ⟨h1, h2⟩
    exact (Set.disjoint_iff.mp hd) ⟨h1, h2⟩
  have hcover : (Set.univ : Set ℝ) ⊆ γ.γ ⁻¹' X ∪ γ.γ ⁻¹' Y := by
    intro t _
    rcases hγ t with h | h
    · exact Or.inl h
    · exact Or.inr h
  rcases IsPreconnected.subset_or_subset hU hV hdUV hcover isPreconnected_univ with h | h
  · exact Or.inl fun t => h trivial
  · exact Or.inr fun t => h trivial

/-- **The winding span is additive over disjoint open pieces of the surface.**

Every closed curve of the torus contained in `X ∪ Y` lies entirely in `X` or entirely in `Y`
(`curve_subset_of_union`), so the set of winding vectors realised in `X ∪ Y` is the union of the
two sets realised in `X` and in `Y`; its span is therefore the supremum of the two spans.
Monotonicity gives the reverse inclusion. -/
theorem union_eq_sup {P : Work.CoreTopology.ParamTorus}
    {X Y : Set LeanEval.KnotTheory.PardonDistortion.R3}
    (hX : Work.SurgeryInvariance.IsOpenInCarrier P X)
    (hY : Work.SurgeryInvariance.IsOpenInCarrier P Y) (hd : Disjoint X Y) :
    Work.SurgeryInvariance.WindingSpan P (X ∪ Y) =
      Work.SurgeryInvariance.WindingSpan P X ⊔ Work.SurgeryInvariance.WindingSpan P Y := by
  apply le_antisymm
  · rw [WindingSpan, Submodule.span_le]
    rintro v ⟨γ, hγ, rfl⟩
    rcases curve_subset_of_union hX hY hd γ hγ with h | h
    · exact Submodule.mem_sup_left (Submodule.subset_span ⟨γ, h, rfl⟩)
    · exact Submodule.mem_sup_right (Submodule.subset_span ⟨γ, h, rfl⟩)
  · exact sup_le (WindingSpan_mono P Set.subset_union_left)
      (WindingSpan_mono P Set.subset_union_right)

end Work.SurgeryInvariance.Span
