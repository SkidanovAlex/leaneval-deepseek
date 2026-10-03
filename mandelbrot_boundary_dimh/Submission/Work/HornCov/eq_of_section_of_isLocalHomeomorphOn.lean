import Mathlib

set_option linter.unusedVariables false

namespace Work.HornCov

/-- Two continuous sections `σ, τ : ↥S → X` of a map `p : X → ℂ` which is a local homeomorphism
over `p ⁻¹' S`, with `S` open and preconnected and `X` Hausdorff, agree as soon as they agree at
one point.

The set on which they agree is clopen: it is closed because `X` is Hausdorff (equalizer of two
continuous maps), and it is open because locally `p` is a homeomorphism, so two sections with the
same image under `p` must coincide in a neighbourhood.  A nonempty clopen subset of a preconnected
space is everything. -/
theorem eq_of_section_of_isLocalHomeomorphOn {X : Type*} [TopologicalSpace X] [T2Space X]
    {p : X → ℂ} {S : Set ℂ} (hSopen : IsOpen S) (hSconn : IsPreconnected S)
    (hloc : IsLocalHomeomorphOn p (p ⁻¹' S))
    {σ τ : ↥S → X} (hσ : Continuous σ) (hτ : Continuous τ)
    (hσsec : ∀ u : ↥S, p (σ u) = (u : ℂ)) (hτsec : ∀ u : ↥S, p (τ u) = (u : ℂ))
    {u₀ : ↥S} (h₀ : σ u₀ = τ u₀) : σ = τ := by
  have hpre : PreconnectedSpace ↥S := isPreconnected_iff_preconnectedSpace.mp hSconn
  -- The agreement set is open: locally `p` is a homeomorphism.
  have hAopen : IsOpen {u : ↥S | σ u = τ u} := by
    rw [isOpen_iff_mem_nhds]
    rintro u hu
    obtain ⟨e, hmem, he⟩ := hloc (σ u) (by show p (σ u) ∈ S; rw [hσsec u]; exact u.2)
    have hVopen : IsOpen (σ ⁻¹' e.source ∩ τ ⁻¹' e.source) :=
      (e.open_source.preimage hσ).inter (e.open_source.preimage hτ)
    have humem : u ∈ σ ⁻¹' e.source ∩ τ ⁻¹' e.source := by
      refine ⟨hmem, ?_⟩
      show τ u ∈ e.source
      rw [← hu]
      exact hmem
    refine Filter.mem_of_superset (hVopen.mem_nhds humem) ?_
    rintro v ⟨hvσ, hvτ⟩
    show σ v = τ v
    have h1 : (e : X → ℂ) (σ v) = (v : ℂ) := by
      rw [← congrFun he (σ v)]; exact hσsec v
    have h2 : (e : X → ℂ) (τ v) = (v : ℂ) := by
      rw [← congrFun he (τ v)]; exact hτsec v
    rw [← e.left_inv hvσ, h1, ← h2, e.left_inv hvτ]
  -- The agreement set is closed because `X` is Hausdorff.
  have hcl : IsClopen {u : ↥S | σ u = τ u} := ⟨isClosed_eq hσ hτ, hAopen⟩
  funext u
  exact (Set.ext_iff.mp (hcl.eq_univ ⟨u₀, h₀⟩) u).mpr trivial

end Work.HornCov
