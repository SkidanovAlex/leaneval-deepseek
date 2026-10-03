import Mathlib
import Submission.Work.ORLocInd.FKSKernel.Kurosh.RepProjection
import Submission.Work.ORLocInd.FKSKernel.Kurosh.ArrowSupport
import Submission.Work.ORLocInd.FKSKernel.Kurosh.EdgeLink
import Submission.Work.ORLocInd.FKSKernel.Kurosh.spanning_arrows
import Submission.Work.ORBassSerre.Action.isTree_orbitV_of_normalClosure_elliptic
import Submission.Work.ORBassSerre.Action.Structure.Phi_surjective

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Quiver.Path

/-- Casting the endpoints of a path does not change the set of arrows occurring in it. -/
theorem allArrows_cast {V : Type*} [Quiver V] {S : Set (Quiver.Total V)} {a b a' b' : V}
    (p : Quiver.Path a b) (h₁ : a = a') (h₂ : b = b') :
    (p.cast h₁ h₂).AllArrows S ↔ p.AllArrows S := by
  obtain rfl := h₁
  obtain rfl := h₂
  rw [Quiver.Path.cast_rfl_rfl]

end Quiver.Path

namespace Work.ORLocInd.FKSKernel.Kurosh

open Classical
open Work.ORBassSerre
open Work.ORBassSerre.Action

universe u

variable {G : Type u} {V : Type u} [Group G] [Quiver V] [Quiver.HasInvolutiveReverse V]
  [MulAction G V] [Work.ORBassSerre.GraphAction G V]

/-! ## The quotient graph of a tree whose vertex stabilisers generate

If the vertex stabilisers of an action on a tree `V` generate the acting group, the quotient
graph `V/G` is again a tree (the `N = ⊤` case of JL, Lemma 4.1). -/

theorem isTree_orbitV_of_hgen (hT : Work.ORBassSerre.IsTree V)
    (hgen : Subgroup.closure (⋃ v : V, (MulAction.stabilizer G v : Set G)) = ⊤) :
    Work.ORBassSerre.IsTree (Work.ORBassSerre.orbitV G V) := by
  have hgen' : Subgroup.closure {g : G | ∃ v : V, g • v = v} = ⊤ := by
    rw [← hgen]
    congr 1
    ext g
    rw [Set.mem_setOf_eq, Set.mem_iUnion]
    exact exists_congr fun v => (MulAction.mem_stabilizer_iff).symm
  refine ⟨Work.ORBassSerre.Action.connected_orbitV (G := G) (V := V) hT, ?_⟩
  intro A p hp
  exact Work.ORBassSerre.Action.eq_nil_of_isReduced_of_reducesTo_nil (G := G) (V := V) hp
    (Work.ORBassSerre.Action.reducesTo_nil_of_closed (G := G) (V := V) hT hgen' A p)

/-- The orbit of an edge orbit under reversal is an involution on edge orbits. -/
theorem orbitEReverse_involutive (E : Work.ORBassSerre.orbitE G V) :
    Work.ORBassSerre.orbitEReverse (G := G) (V := V)
      (Work.ORBassSerre.orbitEReverse (G := G) (V := V) E) = E := by
  refine Quotient.inductionOn E ?_
  intro e
  rw [Work.ORBassSerre.orbitEReverse_mk, Work.ORBassSerre.orbitEReverse_mk,
    Quiver.Total.reverse_reverse]

/-! ## The arrows of the spanning tree -/

namespace TreeDatum

variable (d : TreeDatum G V)

/-- The arrow of the quotient graph `V/G` determined by an edge orbit. -/
noncomputable def edgeArrow (d : TreeDatum G V) (E : Work.ORBassSerre.orbitE G V) :
    Work.ORBassSerre.Action.srcE (G := G) (V := V) E ⟶
      Work.ORBassSerre.Action.tgtE (G := G) (V := V) E :=
  ⟨E, Work.ORBassSerre.Action.orbitRepE (G := G) (V := V) E,
    Work.ORBassSerre.Action.orbitRepE_mk (G := G) (V := V) E, rfl, rfl⟩

/-- The arrow of the quotient graph from the lifted vertex of the parent orbit to the lifted
vertex of `A`. -/
noncomputable def parArrowX (A : Work.ORBassSerre.orbitV G V) (hA : A ≠ d.root) :
    d.par A ⟶ A :=
  ⟨Quotient.mk'' (d.parArrow A hA), d.parArrow A hA, rfl,
    by rw [d.parArrow_left A hA, d.vert_mk],
    by rw [d.parArrow_right A hA, d.vert_mk]⟩

/-- The edge orbits of the spanning tree, and their reverses. -/
def treeOrbitSet : Set (Work.ORBassSerre.orbitE G V) :=
  {E | (∃ (A : Work.ORBassSerre.orbitV G V) (hA : A ≠ d.root),
        E = Quotient.mk'' (d.parArrow A hA)) ∨
      (∃ (A : Work.ORBassSerre.orbitV G V) (hA : A ≠ d.root),
        E = Work.ORBassSerre.orbitEReverse (G := G) (V := V)
          (Quotient.mk'' (d.parArrow A hA)))}

/-- The arrows of the quotient graph whose edge orbit belongs to the spanning tree. -/
def treeArrowSet : Set (Quiver.Total (Work.ORBassSerre.orbitV G V)) :=
  {e | e.hom.1 ∈ d.treeOrbitSet}

theorem treeOrbitSet_reverse (E : Work.ORBassSerre.orbitE G V) :
    E ∈ d.treeOrbitSet ↔
      Work.ORBassSerre.orbitEReverse (G := G) (V := V) E ∈ d.treeOrbitSet := by
  constructor
  · rintro (⟨A, hA, rfl⟩ | ⟨A, hA, rfl⟩)
    · exact Or.inr ⟨A, hA, rfl⟩
    · refine Or.inl ⟨A, hA, ?_⟩
      rw [orbitEReverse_involutive]
  · rintro (⟨A, hA, h⟩ | ⟨A, hA, h⟩)
    · refine Or.inr ⟨A, hA, ?_⟩
      rw [← h, orbitEReverse_involutive]
    · refine Or.inl ⟨A, hA, ?_⟩
      have := congrArg (Work.ORBassSerre.orbitEReverse (G := G) (V := V)) h
      simpa [orbitEReverse_involutive] using this

theorem treeArrowSet_reverse (e : Quiver.Total (Work.ORBassSerre.orbitV G V)) :
    e ∈ d.treeArrowSet ↔ Quiver.Total.reverse e ∈ d.treeArrowSet := by
  have hhom : (Quiver.Total.reverse e).hom.1 =
      Work.ORBassSerre.orbitEReverse (G := G) (V := V) (e.hom.1) := rfl
  show e.hom.1 ∈ d.treeOrbitSet ↔ (Quiver.Total.reverse e).hom.1 ∈ d.treeOrbitSet
  rw [hhom]
  exact d.treeOrbitSet_reverse (e.hom.1)

/-- A path in the quotient graph from the root orbit to `A` using only arrows of the spanning
tree, together with the proof that it only uses those arrows. -/
noncomputable def chainAux : (A : Work.ORBassSerre.orbitV G V) →
    {p : Quiver.Path d.root A // p.AllArrows d.treeArrowSet}
  | A => if h : A = d.root then
      ⟨(Quiver.Path.nil : Quiver.Path d.root d.root).cast rfl h.symm,
        by rw [Quiver.Path.allArrows_cast]; exact Quiver.Path.allArrows_nil _ _⟩
    else
      ⟨((chainAux (d.par A)).1).cons (d.parArrowX A h), by
        rw [Quiver.Path.allArrows_cons]
        exact ⟨(chainAux (d.par A)).2, Or.inl ⟨A, h, rfl⟩⟩⟩
termination_by A => d.rank A
decreasing_by exact d.rank_par_lt A h

/-- The path in the quotient graph from the root orbit to `A` along the spanning tree. -/
noncomputable def chain (A : Work.ORBassSerre.orbitV G V) : Quiver.Path d.root A :=
  (d.chainAux A).1

theorem chain_allArrows (A : Work.ORBassSerre.orbitV G V) :
    (d.chain A).AllArrows d.treeArrowSet :=
  (d.chainAux A).2

/-- The arrows of the spanning tree connect any two vertices of the quotient graph. -/
theorem exists_chain_path (a b : Work.ORBassSerre.orbitV G V) :
    ∃ p : Quiver.Path a b, p.AllArrows d.treeArrowSet := by
  refine ⟨(d.chain a).reverse.comp (d.chain b), ?_⟩
  rw [Quiver.Path.allArrows_comp]
  exact ⟨(Quiver.Path.allArrows_reverse d.treeArrowSet_reverse (d.chain a)).mp
      (d.chain_allArrows a),
    d.chain_allArrows b⟩

/-- **Every edge orbit of the quotient graph is a tree edge, up to reversal**, when the quotient
graph is a tree. -/
theorem isTreeEdge_or_isTreeEdge_orbitEReverse
    (hX : Work.ORBassSerre.IsTree (Work.ORBassSerre.orbitV G V))
    (E : Work.ORBassSerre.orbitE G V) :
    d.IsTreeEdge E ∨ d.IsTreeEdge (Work.ORBassSerre.orbitEReverse (G := G) (V := V) E) := by
  have hmem : E ∈ d.treeOrbitSet :=
    spanning_arrows hX d.treeArrowSet d.treeArrowSet_reverse d.exists_chain_path
      (Quiver.Total.mk (Work.ORBassSerre.Action.srcE (G := G) (V := V) E)
        (Work.ORBassSerre.Action.tgtE (G := G) (V := V) E) (d.edgeArrow E))
  rcases hmem with ⟨A, hA, h⟩ | ⟨A, hA, h⟩
  · exact Or.inl ⟨⟨A, hA⟩, h.symm⟩
  · refine Or.inr ⟨⟨A, hA⟩, ?_⟩
    have := congrArg (Work.ORBassSerre.orbitEReverse (G := G) (V := V)) h
    simpa [orbitEReverse_involutive] using this.symm

/-- **Every stable letter lies in the subgroup generated by the vertex groups of the lifted
vertices** when the quotient graph is a tree. -/
theorem sElt_mem_closure (hT : Work.ORBassSerre.IsTree V)
    (hX : Work.ORBassSerre.IsTree (Work.ORBassSerre.orbitV G V))
    (E : Work.ORBassSerre.orbitE G V) :
    d.sElt E ∈ Subgroup.closure (⋃ A : Work.ORBassSerre.orbitV G V, (d.vgroup A : Set G)) := by
  rcases d.isTreeEdge_or_isTreeEdge_orbitEReverse hX E with h | h
  · rw [d.sElt_eq_one h]
    exact Subgroup.one_mem _
  · have hmemK : (d.linkK E : G) ∈
        Subgroup.closure (⋃ A : Work.ORBassSerre.orbitV G V, (d.vgroup A : Set G)) :=
      Subgroup.subset_closure (Set.mem_iUnion.mpr ⟨_, (d.linkK E).2⟩)
    have hmemH : (d.linkH E : G) ∈
        Subgroup.closure (⋃ A : Work.ORBassSerre.orbitV G V, (d.vgroup A : Set G)) :=
      Subgroup.subset_closure (Set.mem_iUnion.mpr ⟨_, (d.linkH E).2⟩)
    have h1 : (d.sElt (Work.ORBassSerre.orbitEReverse (G := G) (V := V) E))⁻¹ ∈
        Subgroup.closure (⋃ A : Work.ORBassSerre.orbitV G V, (d.vgroup A : Set G)) := by
      rw [d.sElt_eq_one h, inv_one]
      exact Subgroup.one_mem _
    have h2 : d.sElt E =
        (d.linkH E : G) * (d.sElt (Work.ORBassSerre.orbitEReverse (G := G) (V := V) E))⁻¹ *
          (d.linkK E : G) := by
      rw [d.sElt_orbitEReverse E]
      group
    rw [h2]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hmemH h1) hmemK

end TreeDatum

theorem closure_vgroup_eq_top {G : Type u} {V : Type u} [Group G] [Quiver V]
    [Quiver.HasInvolutiveReverse V] [MulAction G V] [Work.ORBassSerre.GraphAction G V]
    (hT : Work.ORBassSerre.IsTree V)
    (hninv : Work.ORBassSerre.ActsWithoutInversions G V)
    (hedge : ∀ e : Quiver.Total V, MulAction.stabilizer G e = ⊥)
    (hgen : Subgroup.closure (⋃ v : V, (MulAction.stabilizer G v : Set G)) = ⊤)
    (d : Work.ORLocInd.FKSKernel.Kurosh.TreeDatum G V) :
    Subgroup.closure (⋃ A : Work.ORBassSerre.orbitV G V, (d.vgroup A : Set G)) = ⊤ := by
  classical
  haveI : Nonempty V := ⟨d.vert d.root⟩
  have hX : Work.ORBassSerre.IsTree (Work.ORBassSerre.orbitV G V) :=
    isTree_orbitV_of_hgen (G := G) (V := V) hT hgen
  have hspan : Subgroup.closure
      ((⋃ A : Work.ORBassSerre.orbitV G V, (d.vgroup A : Set G)) ∪ Set.range d.sElt) = ⊤ :=
    Work.ORBassSerre.Action.Structure.closure_lifts_top_aux (G := G) (V := V) hT d.vert
      d.vert_mk d.sElt d.elift d.elift_orbit d.elift_left d.elift_right
  have hle : Subgroup.closure
      ((⋃ A : Work.ORBassSerre.orbitV G V, (d.vgroup A : Set G)) ∪ Set.range d.sElt) ≤
      Subgroup.closure (⋃ A : Work.ORBassSerre.orbitV G V, (d.vgroup A : Set G)) := by
    rw [Subgroup.closure_le]
    rintro g (hg | hg)
    · rw [Set.mem_iUnion] at hg
      obtain ⟨A, hgA⟩ := hg
      exact Subgroup.subset_closure (Set.mem_iUnion.mpr ⟨A, hgA⟩)
    · obtain ⟨E, rfl⟩ := hg
      exact d.sElt_mem_closure hT hX E
  rw [hspan] at hle
  exact le_antisymm le_top hle

end Work.ORLocInd.FKSKernel.Kurosh
