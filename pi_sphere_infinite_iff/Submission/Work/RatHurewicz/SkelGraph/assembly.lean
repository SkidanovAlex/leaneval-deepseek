import Mathlib
import Submission.Work.RatHurewicz.SkelGraph.points
import Submission.Work.Stems.mulEquiv_of_homotopyEquiv

/-!
# From the graph structure of the `1`-skeleton to finite generation of its fundamental group

Given the combinatorial description of the low dimensional points of the model
(`Work.RatHurewicz.SkelGraph.graphElement`) and the fact that the resulting map
`Phi D : GraphX (a D) (b D) → ↥(skeleton D)` is open, that map is a homeomorphism, and finite
generation of the fundamental group of the finite graph transfers to the `1`-skeleton (using
`Work.Stems.mulEquiv_of_homotopyEquiv`).
-/

namespace Work.RatHurewicz.SkelGraph

open scoped Topology unitInterval

noncomputable section

variable {X : Type} [TopologicalSpace X] {x₀ : X} {n : ℕ}

/-- The hypothesis of `graphElement`, kept as a named predicate. -/
def GraphElementData (D : MData X n x₀) : Prop :=
  ∃ f : {y : Raw D // isLowDim D y} → GraphX (a D) (b D),
    (∀ y, Phi D (f y) = toSkeleton D y) ∧
    (∀ (y : {y : Raw D // isLowDim D y}) (w : V D ⊕ (E D × I)),
      psi D w = toSkeleton D y → f y = gq (a D) (b D) w) ∧
    (∀ y y', Relation.EqvGen (modelRel D) y.1 y'.1 → f y = f y')

theorem Phi_surjective (D : MData X n x₀) (h : GraphElementData D) :
    Function.Surjective (Phi D) := by
  obtain ⟨f, h1, _, _⟩ := h
  intro z
  obtain ⟨y, hy⟩ := toSkeleton_surjective D z
  exact ⟨f y, hy ▸ h1 y⟩

theorem Phi_injective (D : MData X n x₀) (h : GraphElementData D) :
    Function.Injective (Phi D) := by
  obtain ⟨f, h1, h2, h3⟩ := h
  intro p p' hp
  obtain ⟨w, rfl⟩ := Quotient.mk''_surjective p
  obtain ⟨w', rfl⟩ := Quotient.mk''_surjective p'
  have hw : psi D w = toSkeleton D (rawOf D w) := psi_rawOf D w
  have hw' : psi D w' = toSkeleton D (rawOf D w') := psi_rawOf D w'
  have hpsi : psi D w = psi D w' := hp
  have heq : toSkeleton D (rawOf D w) = toSkeleton D (rawOf D w') := by
    rw [← hw, ← hw', hpsi]
  have hrel : Relation.EqvGen (modelRel D) (rawOf D w).1 (rawOf D w').1 := by
    have h2' : (Quotient.mk'' (rawOf D w).1 : Model D) = Quotient.mk'' (rawOf D w').1 :=
      congrArg Subtype.val heq
    exact Quotient.eq.mp h2'
  have hfw : f (rawOf D w) = (gq (a D) (b D) w : GraphX (a D) (b D)) := h2 (rawOf D w) w hw
  have hfw' : f (rawOf D w') = (gq (a D) (b D) w' : GraphX (a D) (b D)) := h2 (rawOf D w') w' hw'
  have hff : f (rawOf D w) = f (rawOf D w') := h3 _ _ hrel
  exact hfw.symm.trans (hff.trans hfw')

/-- The map `Phi` as a homeomorphism, given that it is bijective and open. -/
def phiHomeomorph (D : MData X n x₀) (hbij : Function.Bijective (Phi D))
    (hopen : IsOpenMap (Phi D)) : GraphX (a D) (b D) ≃ₜ ↥(skeleton D) :=
  IsHomeomorph.homeomorph (Phi D) ⟨continuous_Phi D, hopen, hbij⟩

theorem phiHomeomorph_apply (D : MData X n x₀) (hbij : Function.Bijective (Phi D))
    (hopen : IsOpenMap (Phi D)) (p : GraphX (a D) (b D)) :
    phiHomeomorph D hbij hopen p = Phi D p := rfl

/-- **Finite generation of the fundamental group of the `1`-skeleton at a general base point**,
given the openness of `Phi` and finite generation for the finite graph. -/
theorem fg_of_fg_graph_aux (D : MData X n x₀)
    (hbij : Function.Bijective (Phi D)) (hopen : IsOpenMap (Phi D))
    (w : GraphX (a D) (b D))
    (hgraph : Group.FG (HomotopyGroup (Fin 1) (GraphX (a D) (b D)) w)) :
    Group.FG (HomotopyGroup (Fin 1) ↥(skeleton D) (Phi D w)) := by
  obtain ⟨me⟩ := Work.Stems.mulEquiv_of_homotopyEquiv (N := Fin 1)
    (phiHomeomorph D hbij hopen).toHomotopyEquiv w
  haveI : Monoid.FG (HomotopyGroup (Fin 1) (GraphX (a D) (b D)) w) :=
    (Group.fg_iff_monoid_fg).mp hgraph
  exact Group.fg_iff_monoid_fg.mpr (Monoid.fg_of_surjective me.toMonoidHom me.surjective)

/-- **Finite generation of the fundamental group of the `1`-skeleton**, given the graph data, the
openness of `Phi` and finite generation for the finite graph. -/
theorem fg_of_fg_graph (D : MData X n x₀) [Nonempty D.Idx]
    (hbij : Function.Bijective (Phi D)) (hopen : IsOpenMap (Phi D))
    (hgraph : Group.FG (HomotopyGroup (Fin 1) (GraphX (a D) (b D))
      (gq (a D) (b D) (Sum.inl (v₀ D))))) :
    Group.FG (HomotopyGroup (Fin 1) ↥(skeleton D)
      ⟨modelBase D, mem_skeleton_modelBase D⟩) :=
  (Phi_base D) ▸ fg_of_fg_graph_aux D hbij hopen (gq (a D) (b D) (Sum.inl (v₀ D))) hgraph

end

end Work.RatHurewicz.SkelGraph
