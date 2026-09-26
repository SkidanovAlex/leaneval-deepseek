import Mathlib
import Submission.Work.Smooth.SphereJordan.exists_half_spans_defs

namespace Work.Smooth.SphereJordan

open Set Metric
open LeanEval.KnotTheory.PardonDistortion

/-- **The slit annulus lies in the finite part of the sphere.**  Its points lie in the open unit
disc, hence are the coercions of complex numbers.  This is what lets the plane splitting of
`preimage_slitAnnulus` be pushed forward to the sphere. -/
theorem slitAnnulus_subset_range_coe {c : ℝ → RiemannSphere} (T : TwoDiscs c)
    (w₁ w₂ : Metric.sphere (0 : ℂ) 1) :
    slitAnnulus T w₁ w₂ ⊆ Set.range ((↑) : ℂ → RiemannSphere) := by
  intro x hx
  obtain ⟨hA, -⟩ := hx
  obtain ⟨hD, -⟩ := mem_openAnnulus.mp hA
  obtain ⟨z, -, hzx⟩ := hD
  exact ⟨z, hzx⟩

/-- The range of the composition of a complex-valued map with the coercion to the sphere is the
image of its range. -/
theorem range_coe_comp {X : Type*} [TopologicalSpace X] (F : C(X, ℂ)) :
    Set.range (fun x => (F x : RiemannSphere)) =
      ((↑) : ℂ → RiemannSphere) '' Set.range F := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨F x, ⟨x, rfl⟩, rfl⟩
  · rintro ⟨z, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, rfl⟩

/-- **Closure commutes with the coercion to the sphere**, for a plane set whose closure is compact:
the coercion is a continuous injection and the image of the closure is closed (indeed compact), so
the closure of the image is the image of the closure. -/
theorem image_closure_coe_eq_closure_image {S : Set ℂ}
    (hS : IsCompact (closure S)) :
    ((↑) : ℂ → RiemannSphere) '' closure S
      = closure (((↑) : ℂ → RiemannSphere) '' S) := by
  apply Subset.antisymm
  · exact image_closure_subset_closure_image OnePoint.continuous_coe
  · apply closure_minimal (Set.image_mono subset_closure)
    exact (hS.image OnePoint.continuous_coe).isClosed

/-- **The two half-discs of the sphere from the two half-discs of the plane.**

Assume the slit annulus of the two-disc datum is split, inside the plane, into two non-empty open
preconnected sets `P₁`, `P₂`, each of which is a disc (closure the image of an injective disc map
`𝔻 → ℂ`).  Then the coercion `ℂ ↪ ℂ ∪ {∞}` carries them to two non-empty open preconnected subsets
`Qᵢ = ↑''Pᵢ` of the sphere which partition `slitAnnulus T w₁ w₂`, and each of whose closures is the
image of an injective disc map `𝔻 → ℂ ∪ {∞}` (namely the composition of the plane disc map with the
coercion).

The proof is purely topological: the coercion is an open embedding (`OnePoint.isOpenEmbedding_coe`),
so it preserves openness, preconnectedness and disjointness, its injectivity preserves the disc-map
condition, and (because the sets are bounded) it also commutes closure with image.  The only place
the geometry enters is that the slit annulus lies in the finite part of the sphere
(`slitAnnulus_subset_range_coe`), so that the image of its preimage is the whole slit annulus. -/
theorem half_spans_of_plane {c : ℝ → RiemannSphere} (T : TwoDiscs c)
    (hball : ∀ z : Disc, InOpenDisc (T.e z))
    (w₁ w₂ : Metric.sphere (0 : ℂ) 1) (hw : w₁ ≠ w₂)
    (hne₁ : (arcOutSet T w₁).Nonempty) (hne₂ : (arcOutSet T w₂).Nonempty)
    (h : PlaneHypothesis)
    (hplane : ∃ P₁ P₂ : Set ℂ,
      P₁.Nonempty ∧ P₂.Nonempty ∧ IsOpen P₁ ∧ IsOpen P₂ ∧ Disjoint P₁ P₂ ∧
      P₁ ∪ P₂ = {z : ℂ | ‖z‖ < 1 ∧ z ∉ Set.range (ep T hball) ∧
        ((z : ℂ) : RiemannSphere) ∈ openAnnulus T ∧
        ((z : ℂ) : RiemannSphere) ∉ cutSet T w₁ ∧
        ((z : ℂ) : RiemannSphere) ∉ cutSet T w₂} ∧
      IsPreconnected P₁ ∧ IsPreconnected P₂ ∧
      (∃ Φ : C(Disc, ℂ), Function.Injective Φ ∧ Set.range Φ = closure P₁) ∧
      (∃ Ψ : C(Disc, ℂ), Function.Injective Ψ ∧ Set.range Ψ = closure P₂)) :
    ∃ Q₁ Q₂ : Set RiemannSphere,
      Q₁.Nonempty ∧ Q₂.Nonempty ∧ IsOpen Q₁ ∧ IsOpen Q₂ ∧ Disjoint Q₁ Q₂ ∧
      Q₁ ∪ Q₂ = slitAnnulus T w₁ w₂ ∧
      IsPreconnected Q₁ ∧ IsPreconnected Q₂ ∧
      (∃ Φ : C(Disc, RiemannSphere), Function.Injective Φ ∧ Set.range Φ = closure Q₁) ∧
      (∃ Ψ : C(Disc, RiemannSphere), Function.Injective Ψ ∧ Set.range Ψ = closure Q₂) := by
  obtain ⟨P₁, P₂, hP₁ne, hP₂ne, hP₁o, hP₂o, hPdisj, hPunion,
    hP₁c, hP₂c, ⟨Φ, hΦinj, hΦrange⟩, ⟨Ψ, hΨinj, hΨrange⟩⟩ := hplane
  -- the plane splitting of the slit annulus, in terms of the preimage under the coercion
  have hset : P₁ ∪ P₂ = ((↑) : ℂ → RiemannSphere) ⁻¹' slitAnnulus T w₁ w₂ := by
    rw [hPunion, preimage_slitAnnulus]
  refine ⟨(↑) '' P₁, (↑) '' P₂,
    hP₁ne.image ((↑) : ℂ → RiemannSphere), hP₂ne.image ((↑) : ℂ → RiemannSphere),
    OnePoint.isOpenMap_coe P₁ hP₁o, OnePoint.isOpenMap_coe P₂ hP₂o, ?_, ?_,
    hP₁c.image ((↑) : ℂ → RiemannSphere) OnePoint.continuous_coe.continuousOn,
    hP₂c.image ((↑) : ℂ → RiemannSphere) OnePoint.continuous_coe.continuousOn, ?_, ?_⟩
  · -- disjointness: the coercion is injective
    rw [Set.disjoint_left]
    rintro x ⟨a, ha, rfl⟩ ⟨b, hb, hbx⟩
    exact (Set.disjoint_left.mp hPdisj ha) (OnePoint.coe_injective hbx ▸ hb)
  · -- the union is the slit annulus: the coercion is surjective onto it
    rw [← Set.image_union, hset, Set.image_preimage_eq_inter_range,
      Set.inter_eq_left.mpr (slitAnnulus_subset_range_coe T w₁ w₂)]
  · -- the first half is a disc: push the plane disc map forward
    refine ⟨⟨fun z : Disc => (Φ z : RiemannSphere),
      OnePoint.continuous_coe.comp Φ.continuous⟩, ?_, ?_⟩
    · intro a b hab
      exact hΦinj (OnePoint.coe_injective hab)
    · show Set.range (fun z : Disc => (Φ z : RiemannSphere)) = closure ((↑) '' P₁)
      have hK : IsCompact (closure P₁) := by
        rw [← hΦrange]; exact isCompact_range Φ.continuous
      rw [range_coe_comp Φ, hΦrange]
      exact image_closure_coe_eq_closure_image hK
  · -- the second half is a disc: push the plane disc map forward
    refine ⟨⟨fun z : Disc => (Ψ z : RiemannSphere),
      OnePoint.continuous_coe.comp Ψ.continuous⟩, ?_, ?_⟩
    · intro a b hab
      exact hΨinj (OnePoint.coe_injective hab)
    · show Set.range (fun z : Disc => (Ψ z : RiemannSphere)) = closure ((↑) '' P₂)
      have hK : IsCompact (closure P₂) := by
        rw [← hΨrange]; exact isCompact_range Ψ.continuous
      rw [range_coe_comp Ψ, hΨrange]
      exact image_closure_coe_eq_closure_image hK

end Work.Smooth.SphereJordan
