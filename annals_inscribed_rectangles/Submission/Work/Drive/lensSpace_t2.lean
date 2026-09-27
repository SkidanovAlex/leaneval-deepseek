import Mathlib
import Submission.Work.Drive.CappingSpace

/-!
# `T2Space` for the lens space `L(2,1)` of the capping

`Submission.Work.Drive.LensSpace` is the quotient of the disjoint union of the two solid tori
`CapTorus = S¹ × D²` and `ConfTorus = D² × S¹` by the boundary identification `lensRel` which glues
the boundary torus point `(θ, φ)` of the cap to the boundary torus point `(φ, θ + 2φ)` of the
configuration torus.  This file proves that this quotient is Hausdorff (`lensSpace_t2`).

The proof is the general fact that a quotient of a compact Hausdorff space by a *closed* equivalence
relation is Hausdorff (`t2Space_quotient_of_isClosed`), together with the concrete verification that
`lensRel ⊆ (CapTorus ⊕ ConfTorus) × (CapTorus ⊕ ConfTorus)` is closed: it is the union of the
diagonal and the two graphs of the boundary identification

`(θ, φ) ↦ (inl (θ, bdy φ), inr (bdy φ, θ + 2φ))`  and its transpose,

which are continuous images of the compact space `S¹ × S¹`.

The reduction to the general fact is the standard one: a quotient map `q : X → Y` of a compact space
is proper (closed with compact fibres) when the relation is closed, the product `q × q` is then
closed, and the diagonal of `Y` is the closed image of the relation under `q × q`.
-/

namespace Work.Drive

noncomputable section

open scoped Topology
open Set

/-! ## A general fact: quotients by closed relations on compact Hausdorff spaces are Hausdorff -/

/-- **A quotient of a compact Hausdorff space by a closed equivalence relation is Hausdorff.**
If `s` is an equivalence relation on the compact Hausdorff space `X` whose graph
`{p : X × X | s p.1 p.2}` is closed in `X × X`, then `X / s` is Hausdorff.

The quotient map `q` is closed (the saturation of a closed set is the image of a closed subset of
`X × X` under a projection, hence compact) with compact fibres, i.e. proper; a product of proper maps
is proper and hence closed, and the diagonal of `X / s` is the image under `q × q` of the (closed)
graph of `s`, so it is closed. -/
theorem t2Space_quotient_of_isClosed {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (s : Setoid X) (hs : IsClosed {p : X × X | s.r p.1 p.2}) : T2Space (Quotient s) := by
  rw [t2_iff_isClosed_diagonal]
  set q : X → Quotient s := Quotient.mk''
  have hsurj : Function.Surjective q := Quotient.mk''_surjective
  have hcont : Continuous q := continuous_quotient_mk'
  have hquot : Topology.IsQuotientMap q := isQuotientMap_quotient_mk'
  -- the graph of the relation is the preimage of the diagonal
  have hR : {p : X × X | s.r p.1 p.2}
      = (Prod.map q q) ⁻¹' Set.diagonal (Quotient s) := by
    ext p
    simp only [Set.mem_preimage, Set.mem_diagonal_iff, Set.mem_ofPred_eq]
    change s p.1 p.2 ↔ q p.1 = q p.2
    exact Quotient.eq.symm
  -- a saturation of a closed set is described as the image of a closed set of `X × X` under `snd`
  have hpre : ∀ A : Set X, q ⁻¹' (q '' A)
      = Prod.snd '' ({p : X × X | s.r p.1 p.2} ∩ (A ×ˢ Set.univ)) := by
    intro A
    ext x
    simp only [Set.mem_preimage, Set.mem_image, Set.mem_inter_iff, Set.mem_prod, Set.mem_univ,
      and_true, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨a, ha, hqa⟩
      exact ⟨(a, x), ⟨⟨Quotient.eq.mp hqa, ha⟩, rfl⟩⟩
    · rintro ⟨⟨a, b⟩, ⟨⟨hab, ha⟩, hb⟩⟩
      exact ⟨a, ha, by rw [← hb]; exact Quotient.eq.mpr hab⟩
  -- hence the quotient map is closed
  have hclosed : IsClosedMap q := by
    intro A hA
    rw [(Topology.isQuotientMap_iff_isClosed.mp hquot).2 (q '' A)]
    rw [hpre A]
    exact ((hs.inter (hA.prod isClosed_univ)).isCompact.image continuous_snd).isClosed
  -- and its fibres are compact, so it is proper
  have hproper : IsProperMap q := by
    rw [isProperMap_iff_isClosedMap_and_compact_fibers]
    refine ⟨hcont, hclosed, fun y => ?_⟩
    obtain ⟨x₀, rfl⟩ := Quotient.exists_rep y
    have hfiber : q ⁻¹' {Quotient.mk'' x₀}
        = Prod.fst '' ({p : X × X | s.r p.1 p.2} ∩ (Set.univ ×ˢ {x₀})) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_image, Set.mem_inter_iff,
        Set.mem_prod, Set.mem_univ, true_and, Set.mem_ofPred_eq]
      constructor
      · intro h
        exact ⟨(x, x₀), ⟨⟨Quotient.eq.mp h, rfl⟩, rfl⟩⟩
      · rintro ⟨⟨a, b⟩, ⟨⟨hab, hb⟩, ha⟩⟩
        rw [← ha, ← hb]
        exact Quotient.eq.mpr hab
    rw [hfiber]
    exact ((hs.inter (isClosed_univ.prod isClosed_singleton)).isCompact.image continuous_fst)
  have hproper2 : IsProperMap (Prod.map q q) := hproper.prodMap hproper
  have himg : (Prod.map q q) '' {p : X × X | s.r p.1 p.2} = Set.diagonal (Quotient s) := by
    rw [hR]
    exact Set.image_preimage_eq _ (hsurj.prodMap hsurj)
  have hsub := hproper2.isClosedMap.closure_image_subset {p : X × X | s.r p.1 p.2}
  rw [himg, hs.closure_eq, himg] at hsub
  exact isClosed_of_closure_subset hsub

/-! ## The graph of `lensRel` is closed -/

/-- The parametrisation `φ ↦ bdy φ` of the boundary circle of the disk is continuous. -/
@[fun_prop] lemma lensT2_continuous_bdy : Continuous bdy := by
  unfold bdy
  exact Continuous.subtype_mk
    (continuous_subtype_val.comp (AddCircle.homeomorphCircle (T := 1) one_ne_zero).continuous) _

/-- The boundary identification `(θ, φ) ↦ (inl (θ, bdy φ), inr (bdy φ, θ + 2φ))` as a map on the
compact torus `S¹ × S¹`. -/
def lensT2_gluePt : UnitAddCircle × UnitAddCircle →
    (CapTorus ⊕ ConfTorus) × (CapTorus ⊕ ConfTorus) :=
  fun p => (Sum.inl (p.1, bdy p.2), Sum.inr (bdy p.2, p.1 + 2 • p.2))

/-- The transpose of `lensT2_gluePt`, accounting for the symmetry of `lensRel`. -/
def lensT2_gluePtSwap : UnitAddCircle × UnitAddCircle →
    (CapTorus ⊕ ConfTorus) × (CapTorus ⊕ ConfTorus) :=
  fun p => (lensT2_gluePt p).swap

lemma lensT2_continuous_gluePt : Continuous lensT2_gluePt := by
  unfold lensT2_gluePt
  fun_prop

lemma lensT2_continuous_gluePtSwap : Continuous lensT2_gluePtSwap := by
  unfold lensT2_gluePtSwap
  exact continuous_swap.comp lensT2_continuous_gluePt

/-- The graph of the boundary identification is compact, hence closed. -/
lemma lensT2_isClosed_range_gluePt : IsClosed (Set.range lensT2_gluePt) :=
  (isCompact_range lensT2_continuous_gluePt).isClosed

lemma lensT2_isClosed_range_gluePtSwap : IsClosed (Set.range lensT2_gluePtSwap) :=
  (isCompact_range lensT2_continuous_gluePtSwap).isClosed

/-- **The graph of `lensRel` is closed** in `(CapTorus ⊕ ConfTorus) × (CapTorus ⊕ ConfTorus)`: it is
the union of the diagonal and the (compact, hence closed) graphs of the boundary identification and
its transpose. -/
lemma lensT2_isClosed_lensRel :
    IsClosed {p : (CapTorus ⊕ ConfTorus) × (CapTorus ⊕ ConfTorus) | lensRel p.1 p.2} := by
  have h : {p : (CapTorus ⊕ ConfTorus) × (CapTorus ⊕ ConfTorus) | lensRel p.1 p.2}
      = Set.diagonal (CapTorus ⊕ ConfTorus) ∪ Set.range lensT2_gluePt
        ∪ Set.range lensT2_gluePtSwap := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_range, Set.mem_diagonal_iff, lensRel,
      lensT2_gluePt, lensT2_gluePtSwap, Prod.swap_prod_mk, Prod.ext_iff, Prod.exists]
    constructor
    · rintro (h | ⟨θ, φ, h | h⟩)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr ⟨θ, φ, h.1.symm, h.2.symm⟩)
      · exact Or.inr ⟨θ, φ, h.2.symm, h.1.symm⟩
    · rintro ((h | ⟨θ, φ, h1, h2⟩) | ⟨θ, φ, h1, h2⟩)
      · exact Or.inl h
      · exact Or.inr ⟨θ, φ, Or.inl ⟨h1.symm, h2.symm⟩⟩
      · exact Or.inr ⟨θ, φ, Or.inr ⟨h2.symm, h1.symm⟩⟩
  rw [h]
  exact (isClosed_diagonal.union lensT2_isClosed_range_gluePt).union
    lensT2_isClosed_range_gluePtSwap

/-- `Work.Drive.LensSpace` (the quotient of `CapTorus ⊕ ConfTorus` by the boundary identification
`lensRel`) is Hausdorff.  The relation is closed in the compact Hausdorff space
`(CapTorus ⊕ ConfTorus) × (CapTorus ⊕ ConfTorus)` (it is a finite union of the diagonal and the graph
of the continuous boundary identification), and a quotient of a compact Hausdorff space by a closed
equivalence relation is Hausdorff. -/
theorem lensSpace_t2 : T2Space LensSpace :=
  t2Space_quotient_of_isClosed lensSetoid lensT2_isClosed_lensRel

end

end Work.Drive
