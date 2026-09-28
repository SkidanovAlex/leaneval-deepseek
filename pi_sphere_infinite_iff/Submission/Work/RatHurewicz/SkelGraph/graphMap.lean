import Mathlib
import Submission.Work.RatHurewicz.SkelGraph.defs

/-!
# The map from the abstract graph to the `1`-skeleton

The edge parametrisations of `Submission/Work/RatHurewicz/SkelGraph/defs.lean` respect the gluing
relation of the abstract finite graph `Work.RatHurewicz.GraphX a b` of the model, so the map
`psi` descends to a continuous map `Phi` from that graph to the `1`-skeleton.
-/

namespace Work.RatHurewicz.SkelGraph

open scoped Topology unitInterval

noncomputable section

variable {X : Type} [TopologicalSpace X] {x₀ : X} {n : ℕ}

theorem psi_inr_zero (D : MData X n x₀) (e : E D) :
    psi D (Sum.inr (e, 0)) = vertSk D (a D e) := by
  induction e using Quotient.inductionOn with
  | h e' =>
    obtain ⟨i, ⟨⟨p, q⟩, hpq⟩⟩ | ⟨i, u⟩ := e'
    · show (edgeContinuous D (Sum.inl ⟨i, ⟨⟨p, q⟩, hpq⟩⟩) 0 : ↥(skeleton D))
        = vertSk D (vCl D (Sum.inl ⟨i, p⟩))
      exact Subtype.ext (edgeM_zero_simplex D i p q hpq)
    · show (edgeContinuous D (Sum.inr ⟨i, u⟩) 0 : ↥(skeleton D))
        = vertSk D (vCl D (Sum.inr ⟨i, 0⟩))
      exact Subtype.ext (edgeM_zero_arc D i u)

theorem psi_inr_one (D : MData X n x₀) (e : E D) :
    psi D (Sum.inr (e, 1)) = vertSk D (b D e) := by
  induction e using Quotient.inductionOn with
  | h e' =>
    obtain ⟨i, ⟨⟨p, q⟩, hpq⟩⟩ | ⟨i, u⟩ := e'
    · show (edgeContinuous D (Sum.inl ⟨i, ⟨⟨p, q⟩, hpq⟩⟩) 1 : ↥(skeleton D))
        = vertSk D (vCl D (Sum.inl ⟨i, q⟩))
      exact Subtype.ext (edgeM_one_simplex D i p q hpq)
    · show (edgeContinuous D (Sum.inr ⟨i, u⟩) 1 : ↥(skeleton D))
        = vertSk D (vCl D (Sum.inr ⟨i, 1⟩))
      exact Subtype.ext (edgeM_one_arc D i u)

theorem psi_rel (D : MData X n x₀) {p q : V D ⊕ (E D × I)}
    (h : Relation.EqvGen (graphRel (a D) (b D)) p q) : psi D p = psi D q := by
  induction h with
  | rel x y hxy =>
    rcases hxy with ⟨e, rfl, rfl⟩ | ⟨e, rfl, rfl⟩ | ⟨e, rfl, rfl⟩ | ⟨e, rfl, rfl⟩
    · exact (psi_inr_zero D e).symm
    · exact (psi_inr_one D e).symm
    · exact psi_inr_zero D e
    · exact psi_inr_one D e
  | refl x => rfl
  | symm x y hxy ih => exact ih.symm
  | trans x y z hxy hyz ih1 ih2 => exact ih1.trans ih2

theorem continuous_psi_rel (D : MData X n x₀) {x y : V D ⊕ (E D × I)}
    (h : (graphSetoid (a D) (b D)).r x y) : psi D x = psi D y :=
  psi_rel D h

/-- The continuous map from the abstract finite graph of the model to its `1`-skeleton. -/
def Phi (D : MData X n x₀) : GraphX (a D) (b D) → ↥(skeleton D) :=
  Quotient.lift (psi D) (fun x y h => continuous_psi_rel D h)

theorem continuous_Phi (D : MData X n x₀) : Continuous (Phi D) :=
  Continuous.quotient_lift (continuous_psi D) (fun x y h => continuous_psi_rel D h)

theorem Phi_apply (D : MData X n x₀) (p : V D ⊕ (E D × I)) :
    Phi D (gq (a D) (b D) p) = psi D p := rfl

/-- The base point of the graph of the `1`-skeleton: the class of the end point of the arcs. -/
def v₀ (D : MData X n x₀) [Nonempty D.Idx] : V D :=
  vCl D (Sum.inr ⟨Classical.choice ‹Nonempty D.Idx›, 1⟩)

theorem Phi_base (D : MData X n x₀) [Nonempty D.Idx] :
    Phi D (gq (a D) (b D) (Sum.inl (v₀ D))) = ⟨modelBase D, mem_skeleton_modelBase D⟩ := by
  show psi D (Sum.inl (v₀ D)) = _
  show (vertSk D (vCl D (Sum.inr ⟨Classical.choice ‹Nonempty D.Idx›, 1⟩)) : ↥(skeleton D)) = _
  apply Subtype.ext
  show vertM D (Sum.inr ⟨Classical.choice ‹Nonempty D.Idx›, 1⟩) = modelBase D
  show Quotient.mk'' ((Sum.inr ⟨Classical.choice ‹Nonempty D.Idx›, arcEnd 1⟩) : Raw D)
    = Quotient.mk'' ((Sum.inr ⟨Classical.choice ‹Nonempty D.Idx›, (1 : I)⟩) : Raw D)
  rw [arcEnd_one]

end

end Work.RatHurewicz.SkelGraph
