import Mathlib
import Submission.Work.RatHurewicz.SkelGraph.graphMap

/-!
# Points of the skeleton and raw points of graph elements

`toSkeleton` turns a point of `Raw D` (together with the proof that it is low dimensional) into a
point of the `1`-skeleton.  `rawOf` chooses, for an element of the abstract graph `V ⊕ (E × I)`, a
low dimensional point of `Raw D` whose class is the image of that graph element under `psi`.
-/

namespace Work.RatHurewicz.SkelGraph

open scoped Topology unitInterval

noncomputable section

variable {X : Type} [TopologicalSpace X] {x₀ : X} {n : ℕ}

/-- The point of the `1`-skeleton represented by a low dimensional point of `Raw`. -/
def toSkeleton (D : MData X n x₀) (y : {y : Raw D // isLowDim D y}) : ↥(skeleton D) :=
  ⟨Quotient.mk'' y.1, ⟨y.1, rfl, y.2⟩⟩

theorem toSkeleton_mk (D : MData X n x₀) (y : {y : Raw D // isLowDim D y}) :
    (toSkeleton D y : ↥(skeleton D)).1 = Quotient.mk'' y.1 := rfl

theorem toSkeleton_surjective (D : MData X n x₀) :
    Function.Surjective (toSkeleton D) := by
  rintro ⟨z, y, rfl, hy⟩
  exact ⟨⟨y, hy⟩, rfl⟩

/-- A raw low dimensional point of `Raw` whose class is the image of a graph element under `psi`:
for a vertex class we take a representative vertex, for an edge class a representative edge. -/
def rawOf (D : MData X n x₀) (w : V D ⊕ (E D × I)) : {y : Raw D // isLowDim D y} :=
  match w with
  | Sum.inl v => ⟨vertPt D (Quotient.out v), isLowDim_vertPt D _⟩
  | Sum.inr p => ⟨edgePt D (Quotient.out p.1) p.2, isLowDim_edgePt D _ _⟩

theorem psi_rawOf (D : MData X n x₀) (w : V D ⊕ (E D × I)) :
    psi D w = toSkeleton D (rawOf D w) := by
  rcases w with v | ⟨e, s⟩
  · show vertSk D v = toSkeleton D ⟨vertPt D (Quotient.out v), isLowDim_vertPt D _⟩
    conv_rhs => rw [toSkeleton]
    rw [show (⟨Quotient.mk'' (vertPt D (Quotient.out v)),
        ⟨vertPt D (Quotient.out v), rfl, isLowDim_vertPt D _⟩⟩ : ↥(skeleton D)) = _ from rfl]
    conv_lhs => rw [← Quotient.out_eq v]
    rw [show vertSk D (Quotient.mk'' (Quotient.out v))
        = (⟨vertM D (Quotient.out v), mem_skeleton_vertM D _⟩ : ↥(skeleton D)) from rfl]
    rfl
  · show edgeParam D e s = toSkeleton D ⟨edgePt D (Quotient.out e) s, isLowDim_edgePt D _ _⟩
    conv_rhs => rw [toSkeleton]
    rw [show (⟨Quotient.mk'' (edgePt D (Quotient.out e) s),
        ⟨edgePt D (Quotient.out e) s, rfl, isLowDim_edgePt D _ _⟩⟩ : ↥(skeleton D)) = _ from rfl]
    conv_lhs => rw [← Quotient.out_eq e]
    rw [show edgeParam D (Quotient.mk'' (Quotient.out e)) s
        = (⟨edgeM D (Quotient.out e) s, mem_skeleton_edgeM D _ _⟩ : ↥(skeleton D)) from rfl]
    rfl

end

end Work.RatHurewicz.SkelGraph
