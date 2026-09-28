import Mathlib
import Submission.Work.RatHurewicz.AvoidOrigin.Class
import Submission.Work.RatHurewicz.AvoidOrigin.chartDefs
import Submission.Work.RatHurewicz.cellDefs

/-!
# The image of a compact piece of the stratum of a cell is closed in the model

The model `Model D` of a cycle is the quotient of `Raw D = (Σ i, Δ^{n+1}) ⊕ (Σ i, I)` by the
gluing relation `modelRel D` (`Submission/Work/RatHurewicz/cycleModelDefs.lean`).  For a point `x`
of a copy of the standard simplex whose support is a set `S` of at least three vertices,
`Work.RatHurewicz.chainTrans` describes its whole class: the points of `Raw D` equivalent to
`Sum.inl ⟨i, x⟩` are exactly the transports of `x` along the chains of `ChainTrans`.

This file deduces from that description that the image of a compact piece of the stratum `S` of the
cell `i` is closed in the model.  The saturated preimage of the image is a finite union of images of
`K` under the continuous maps `x ↦ Sum.inl ⟨c.j, c.center x …⟩`, indexed by the (finitely many)
chain data `c` issued from `(i, S)`; each of these images is compact, hence closed, and a finite
union of closed sets is closed.
-/

set_option linter.style.haveILetI false

open scoped Topology Simplicial unitInterval

namespace Work.RatHurewicz

noncomputable section

variable {X : Type} [TopologicalSpace X] {x₀ : X} {n : ℕ}

/-- **The transport of a point of the face `S` along the vertex map of a chain is continuous in the
point**, on the set of points of the standard simplex whose support is `S`. -/
theorem continuous_chainDatum_center {D : MData X n x₀} {i : D.Idx} {S : Finset (Fin (n + 2))}
    (c : AvoidOrigin.ChainDatum D i S) {K : Set (stdSimplex ℝ (Fin (n + 2)))}
    (hKs : ∀ x ∈ K, ptSupport x = S) :
    Continuous (fun x : {x : stdSimplex ℝ (Fin (n + 2)) // x ∈ K} =>
      c.center x.1 (hKs x.1 x.2)) := by
  refine Continuous.subtype_mk
    (f := fun x : {x : stdSimplex ℝ (Fin (n + 2)) // x ∈ K} =>
      transportFun (x.1 : Fin (n + 2) → ℝ) c.τ) ?_
    (fun x => (c.center x.1 (hKs x.1 x.2)).2)
  refine continuous_pi fun w => ?_
  simp only [transportFun_apply]
  refine continuous_finsetSum _ fun t _ => ?_
  by_cases h : c.τ t = w
  · have hiff : (fun x : {x : stdSimplex ℝ (Fin (n + 2)) // x ∈ K} =>
        (if c.τ t = w then (x.1 : Fin (n + 2) → ℝ) t else 0))
        = fun x : {x : stdSimplex ℝ (Fin (n + 2)) // x ∈ K} =>
          (x.1 : Fin (n + 2) → ℝ) t := by
      funext x; rw [if_pos h]
    rw [hiff]
    have h1 : Continuous (fun x : {x : stdSimplex ℝ (Fin (n + 2)) // x ∈ K} =>
        (x.1 : Fin (n + 2) → ℝ)) := continuous_subtype_val.comp continuous_subtype_val
    exact (continuous_apply (t : Fin (n + 2))).comp h1
  · have hiff : (fun x : {x : stdSimplex ℝ (Fin (n + 2)) // x ∈ K} =>
        (if c.τ t = w then (x.1 : Fin (n + 2) → ℝ) t else 0))
        = fun _ : {x : stdSimplex ℝ (Fin (n + 2)) // x ∈ K} => (0 : ℝ) := by
      funext x; rw [if_neg h]
    rw [hiff]
    exact continuous_const

/-- The index type of the pieces is finite: a chain datum is determined by its cell and its vertex
map. -/
theorem finite_chainDatum {D : MData X n x₀} {i : D.Idx} {S : Finset (Fin (n + 2))} :
    Finite (AvoidOrigin.ChainDatum D i S) :=
  Finite.of_injective (fun c : AvoidOrigin.ChainDatum D i S => (c.j, c.τ)) (by
    intro a b h
    obtain ⟨aj, aτ, ainj, ach⟩ := a
    obtain ⟨bj, bτ, binj, bch⟩ := b
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl)

/-- **The description of the saturated preimage of the image of a piece of the stratum.**  A point
`a` of `Raw D` is equivalent to a point `Sum.inl ⟨i, x⟩` with `x ∈ K` if and only if it is the
transport of such an `x` along the vertex map of a chain datum. -/
theorem mem_preimage_image_iff {D : MData X n x₀} {i : D.Idx} {S : Finset (Fin (n + 2))}
    (hS : 2 < S.card) {K : Set (stdSimplex ℝ (Fin (n + 2)))}
    (hKs : ∀ x ∈ K, ptSupport x = S) (a : Raw D) :
    Quotient.mk'' a ∈ topMap D i '' K ↔
      ∃ c : AvoidOrigin.ChainDatum D i S,
        ∃ x : {x : stdSimplex ℝ (Fin (n + 2)) // x ∈ K},
          a = Sum.inl ⟨c.j, c.center x.1 (hKs x.1 x.2)⟩ := by
  constructor
  · intro ha
    rw [Set.mem_image] at ha
    obtain ⟨y, hyK, hy⟩ := ha
    have hrel : Relation.EqvGen (modelRel D) (Sum.inl ⟨i, y⟩) a :=
      Quotient.exact (show Quotient.mk'' (Sum.inl ⟨i, y⟩) = Quotient.mk'' a from hy)
    obtain ⟨j, τ, hτ, hCT, ha'⟩ := (chainTrans D i S hS y (hKs y hyK) a).mp hrel
    exact ⟨⟨j, τ, hτ, hCT⟩, ⟨y, hyK⟩, ha'⟩
  · rintro ⟨c, x, rfl⟩
    rw [Set.mem_image]
    refine ⟨x.1, x.2, ?_⟩
    have hic : InClass D i S x.1 (hKs x.1 x.2)
        (Sum.inl ⟨c.j, c.center x.1 (hKs x.1 x.2)⟩) :=
      ⟨c.j, c.τ, c.inj, c.chain, rfl⟩
    exact Quotient.sound ((chainTrans D i S hS x.1 (hKs x.1 x.2) _).mpr hic)

/-- **The image of a compact piece of the stratum of a cell is closed in the model.** -/
theorem isClosed_image_stratum_compact {X : Type} [TopologicalSpace X] {x₀ : X} {n : ℕ}
    {D : MData X n x₀} {i : D.Idx} {S : Finset (Fin (n + 2))} (hS : 2 < S.card)
    {K : Set (stdSimplex ℝ (Fin (n + 2)))}
    (hKc : IsCompact K) (hKs : ∀ x ∈ K, ptSupport x = S) :
    IsClosed (topMap D i '' K) := by
  classical
  haveI hfin : Finite (AvoidOrigin.ChainDatum D i S) := finite_chainDatum
  haveI hcomp : CompactSpace {x : stdSimplex ℝ (Fin (n + 2)) // x ∈ K} :=
    (isCompact_iff_compactSpace (s := K)).mp hKc
  have hq : Topology.IsCoinducing (Quotient.mk'' : Raw D → Model D) :=
    (isQuotientMap_quotient_mk' (s := Relation.EqvGen.setoid (modelRel D))).isCoinducing
  refine (hq.isClosed_preimage (s := topMap D i '' K)).mp ?_
  have hA : Quotient.mk'' ⁻¹' (topMap D i '' K)
      = ⋃ c : AvoidOrigin.ChainDatum D i S,
          Set.range (fun x : {x : stdSimplex ℝ (Fin (n + 2)) // x ∈ K} =>
            (Sum.inl ⟨c.j, c.center x.1 (hKs x.1 x.2)⟩ : Raw D)) := by
    ext a
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_range]
    constructor
    · intro h
      obtain ⟨c, x, hx⟩ := (mem_preimage_image_iff hS hKs a).mp h
      exact ⟨c, x, hx.symm⟩
    · rintro ⟨c, x, hx⟩
      exact (mem_preimage_image_iff hS hKs a).mpr ⟨c, x, hx.symm⟩
  rw [hA]
  refine isClosed_iUnion_of_finite fun c => ?_
  have hcont : Continuous (fun x : {x : stdSimplex ℝ (Fin (n + 2)) // x ∈ K} =>
      (Sum.inl ⟨c.j, c.center x.1 (hKs x.1 x.2)⟩ : Raw D)) :=
    continuous_inl.comp (continuous_sigmaMk.comp (continuous_chainDatum_center c hKs))
  exact (isCompact_range hcont).isClosed

end

end Work.RatHurewicz
