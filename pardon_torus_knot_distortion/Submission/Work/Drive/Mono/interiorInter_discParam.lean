import Mathlib
import Submission.Work.CoreTopology.Disk
import Submission.Work.Drive.Mono.exists_discParam_of_two_convex

/-!
# A disc parametrisation of the union of two compact convex planar sets

`Work.Drive.Mono.interiorInter_discParam`: if `A`, `B ⊆ ℝ²` are compact, convex, have non-empty
interior, and their intersection has non-empty interior (so that `int A ∩ int B ≠ ∅`), then
`A ∪ B` is the image of the closed unit disc `𝔻 ⊂ ℂ` under an injective continuous map whose
boundary circle maps onto `frontier (A ∪ B)`.

The proof reduces to the case where the origin is an interior point of both sets, by translating a
point of `interior (A ∩ B)` to the origin.  In that case the "gauge of two convex sets"

`G x = min (gauge A x) (gauge B x)`

and its radial map `x ↦ (‖x‖ / G x) • x` retract the unit disc onto `A ∪ B` with the unit circle
landing on `frontier (A ∪ B)`.  The gauge lemmas are those of
`Work.Drive.Mono.exists_discParam_of_two_convex`; here they are applied to *closed* convex sets,
which are exactly the sets in the statement, so no passage from `closure A` back to `A` through
interiors is needed.
-/

namespace Work.Drive.Mono

open Set Metric
open scoped Topology

noncomputable section

/-- **The disc parametrisation of the union of two compact convex sets containing the origin in
their interiors.**  `radial (twoConvexG A B)` maps the closed unit disc injectively onto `A ∪ B`
and the unit circle onto `frontier (A ∪ B)`. -/
theorem exists_discParam_of_two_closedConvex_zero
    (A B : Set (EuclideanSpace ℝ (Fin 2)))
    (hAc : Convex ℝ A) (hAcl : IsCompact A)
    (h0A : (0 : EuclideanSpace ℝ (Fin 2)) ∈ interior A)
    (hBc : Convex ℝ B) (hBcl : IsCompact B)
    (h0B : (0 : EuclideanSpace ℝ (Fin 2)) ∈ interior B) :
    ∃ e : C(Metric.closedBall (0 : ℂ) 1, EuclideanSpace ℝ (Fin 2)),
      Function.Injective e ∧ Set.range e = A ∪ B ∧
      Set.range (fun θ : ℝ => e (Work.CoreTopology.circlePoint θ)) = frontier (A ∪ B) := by
  have hAb : Bornology.IsBounded A := hAcl.isBounded
  have hBb : Bornology.IsBounded B := hBcl.isBounded
  have hcA : closure A = A := hAcl.isClosed.closure_eq
  have hcB : closure B = B := hBcl.isClosed.closure_eq
  have hAn : closure A ∈ 𝓝 (0 : EuclideanSpace ℝ (Fin 2)) :=
    Filter.mem_of_superset (IsOpen.mem_nhds isOpen_interior h0A)
      (fun x hx => subset_closure (interior_subset hx))
  have hBn : closure B ∈ 𝓝 (0 : EuclideanSpace ℝ (Fin 2)) :=
    Filter.mem_of_superset (IsOpen.mem_nhds isOpen_interior h0B)
      (fun x hx => subset_closure (interior_subset hx))
  have hpos : ∀ x : EuclideanSpace ℝ (Fin 2), x ≠ 0 → 0 < twoConvexG A B x :=
    fun x hx => twoConvexG_pos hAb hAn hBb hBn hx
  obtain ⟨R, hRpos, hbound⟩ := twoConvexG_bound hAb hAn hBb hBn
  have hGc : Continuous (twoConvexG A B) :=
    (continuous_gauge hAc.closure hAn).min (continuous_gauge hBc.closure hBn)
  have hρc : Continuous (radial (twoConvexG A B)) :=
    continuous_radial hGc (twoConvexG_zero A B) hpos hbound
  set Φ : ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) := Complex.orthonormalBasisOneI.repr with hΦdef
  have hΦ0 : Φ 0 = 0 := map_zero Φ
  set f : Metric.closedBall (0 : ℂ) 1 → EuclideanSpace ℝ (Fin 2) :=
    fun z => radial (twoConvexG A B) (Φ (z : ℂ)) with hfdef
  have hfc : Continuous f := hρc.comp (Φ.continuous.comp continuous_subtype_val)
  refine ⟨⟨f, hfc⟩, ?_, ?_, ?_⟩
  · intro z w hzw
    exact Subtype.ext (Φ.injective (radial_injective (A := A) (B := B) hpos hzw))
  · show Set.range f = A ∪ B
    have hφ : Set.range (fun z : Metric.closedBall (0 : ℂ) 1 => Φ (z : ℂ))
        = Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
      rw [show (fun z : Metric.closedBall (0 : ℂ) 1 => Φ (z : ℂ))
          = Φ ∘ (Subtype.val : Metric.closedBall (0 : ℂ) 1 → ℂ) from rfl, Set.range_comp,
        Subtype.range_coe, LinearIsometryEquiv.image_closedBall, hΦ0]
    rw [show f = (radial (twoConvexG A B)) ∘ (fun z : Metric.closedBall (0 : ℂ) 1 => Φ (z : ℂ))
        from rfl, Set.range_comp, hφ,
      radial_image_closedBall hAc hAn hAb hBc hBn hBb, hcA, hcB]
  · show Set.range (fun θ : ℝ => f (Work.CoreTopology.circlePoint θ)) = frontier (A ∪ B)
    have hφ : Set.range (fun θ : ℝ => Φ (((Work.CoreTopology.circlePoint θ :
        Metric.closedBall (0 : ℂ) 1) : ℂ)))
        = Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
      rw [show (fun θ : ℝ => Φ (((Work.CoreTopology.circlePoint θ :
            Metric.closedBall (0 : ℂ) 1) : ℂ)))
          = Φ ∘ (fun θ : ℝ => ((Work.CoreTopology.circlePoint θ :
              Metric.closedBall (0 : ℂ) 1) : ℂ)) from rfl, Set.range_comp,
        range_circlePoint, LinearIsometryEquiv.image_sphere, hΦ0]
    rw [show (fun θ : ℝ => f (Work.CoreTopology.circlePoint θ))
        = (radial (twoConvexG A B)) ∘ (fun θ : ℝ => Φ (((Work.CoreTopology.circlePoint θ :
            Metric.closedBall (0 : ℂ) 1) : ℂ))) from rfl, Set.range_comp, hφ,
      radial_image_sphere hAc hAn hAb hBc hBn hBb, hcA, hcB]

/-- **The union of two compact convex planar sets with non-empty interior whose intersection has
non-empty interior is a disc.** -/
theorem interiorInter_discParam (A B : Set (EuclideanSpace ℝ (Fin 2)))
    (hAc : Convex ℝ A) (hAcl : IsCompact A) (hAne : (interior A).Nonempty)
    (hBc : Convex ℝ B) (hBcl : IsCompact B) (hBne : (interior B).Nonempty)
    (h : (interior (A ∩ B)).Nonempty) :
    ∃ e : C(Metric.closedBall (0 : ℂ) 1, EuclideanSpace ℝ (Fin 2)),
      Function.Injective e ∧ Set.range e = A ∪ B ∧
      Set.range (fun θ : ℝ => e (Work.CoreTopology.circlePoint θ)) = frontier (A ∪ B) := by
  obtain ⟨p, hp⟩ := h
  have hpA : p ∈ interior A := interior_mono inter_subset_left hp
  have hpB : p ∈ interior B := interior_mono inter_subset_right hp
  set τ : EuclideanSpace ℝ (Fin 2) ≃ₜ EuclideanSpace ℝ (Fin 2) :=
    Homeomorph.subRight p with hτdef
  set A' : Set (EuclideanSpace ℝ (Fin 2)) := τ '' A with hA'def
  set B' : Set (EuclideanSpace ℝ (Fin 2)) := τ '' B with hB'def
  have hA'c : Convex ℝ A' := by
    rw [hA'def, hτdef, Homeomorph.coe_subRight]
    rintro x ⟨a, ha, rfl⟩ y ⟨b, hb, rfl⟩ u v hu hv huv
    refine ⟨u • a + v • b, hAc ha hb hu hv huv, ?_⟩
    have hv' : v = 1 - u := by linarith
    rw [hv']
    module
  have hB'c : Convex ℝ B' := by
    rw [hB'def, hτdef, Homeomorph.coe_subRight]
    rintro x ⟨a, ha, rfl⟩ y ⟨b, hb, rfl⟩ u v hu hv huv
    refine ⟨u • a + v • b, hBc ha hb hu hv huv, ?_⟩
    have hv' : v = 1 - u := by linarith
    rw [hv']
    module
  have hA'k : IsCompact A' := by
    rw [hA'def]; exact hAcl.image τ.continuous
  have hB'k : IsCompact B' := by
    rw [hB'def]; exact hBcl.image τ.continuous
  have h0A' : (0 : EuclideanSpace ℝ (Fin 2)) ∈ interior A' := by
    rw [hA'def, ← Homeomorph.image_interior τ A, hτdef, Homeomorph.coe_subRight]
    exact ⟨p, hpA, by simp⟩
  have h0B' : (0 : EuclideanSpace ℝ (Fin 2)) ∈ interior B' := by
    rw [hB'def, ← Homeomorph.image_interior τ B, hτdef, Homeomorph.coe_subRight]
    exact ⟨p, hpB, by simp⟩
  obtain ⟨e₀, he₀inj, he₀range, he₀circ⟩ :=
    exists_discParam_of_two_closedConvex_zero A' B' hA'c hA'k h0A' hB'c hB'k h0B'
  set σ : EuclideanSpace ℝ (Fin 2) ≃ₜ EuclideanSpace ℝ (Fin 2) :=
    Homeomorph.addLeft p with hσdef
  have hσA : σ '' A' = A := by
    rw [hA'def, hσdef, hτdef, Homeomorph.coe_addLeft, Homeomorph.coe_subRight]
    ext x
    constructor
    · rintro ⟨y, ⟨a, ha, rfl⟩, rfl⟩
      simpa using ha
    · intro hx
      exact ⟨x - p, ⟨x, hx, rfl⟩, by simp⟩
  have hσB : σ '' B' = B := by
    rw [hB'def, hσdef, hτdef, Homeomorph.coe_addLeft, Homeomorph.coe_subRight]
    ext x
    constructor
    · rintro ⟨y, ⟨a, ha, rfl⟩, rfl⟩
      simpa using ha
    · intro hx
      exact ⟨x - p, ⟨x, hx, rfl⟩, by simp⟩
  have hσAB : σ '' (A' ∪ B') = A ∪ B := by
    rw [image_union, hσA, hσB]
  refine ⟨⟨fun z => σ (e₀ z), σ.continuous.comp e₀.continuous⟩, ?_, ?_, ?_⟩
  · intro z w hzw
    exact he₀inj (σ.injective hzw)
  · show Set.range (fun z : Metric.closedBall (0 : ℂ) 1 => σ (e₀ z)) = A ∪ B
    rw [show (fun z : Metric.closedBall (0 : ℂ) 1 => σ (e₀ z)) = σ ∘ e₀ from rfl,
      Set.range_comp, he₀range, hσAB]
  · show Set.range (fun θ : ℝ => σ (e₀ (Work.CoreTopology.circlePoint θ))) = frontier (A ∪ B)
    rw [show (fun θ : ℝ => σ (e₀ (Work.CoreTopology.circlePoint θ)))
        = σ ∘ (fun θ : ℝ => e₀ (Work.CoreTopology.circlePoint θ)) from rfl,
      Set.range_comp, he₀circ, Homeomorph.image_frontier, hσAB]

end

end Work.Drive.Mono
