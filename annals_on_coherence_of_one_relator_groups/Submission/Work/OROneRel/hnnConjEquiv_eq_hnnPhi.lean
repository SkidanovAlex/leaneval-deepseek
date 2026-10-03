import Mathlib
import Submission.Work.OROneRel.hnnConjSplit
import Submission.Work.ORBassSerre.Action.Structure.isFinitelyPresented_of_hnn_case

namespace Work.OROneRel

universe u

/-- The two conjugation isomorphisms `A → B` attached to the same tree data agree: the Bass--Serre
one `hnnPhi` (defined through `hnnA`/`hnnB`, the edge stabilisers) and the group-theoretic
`hnnConjEquiv` (defined through `hnnEdgeA H t = H ⊓ t⁻¹ H t`) are both multiplication by `t` on the
left, hence equal after coercion to the vertex group. -/
theorem hnnConjEquiv_eq_hnnPhi {G : Type u} [Group G] {V : Type u} [Quiver V]
    [Quiver.HasInvolutiveReverse V] [MulAction G V] [Work.ORBassSerre.GraphAction G V]
    (v : V) (t : G) (e : v ⟶ t • v) (x : ↥(MulAction.stabilizer G v))
    (hx : x ∈ (Work.OROneRel.hnnEdgeA (MulAction.stabilizer G v) t).subgroupOf
      (MulAction.stabilizer G v))
    (hx' : x ∈ Work.ORBassSerre.Action.Structure.hnnA v t e) :
    ((Work.OROneRel.hnnConjEquiv (MulAction.stabilizer G v) t ⟨x, hx⟩ :
        (Work.OROneRel.hnnEdgeB (MulAction.stabilizer G v) t).subgroupOf
          (MulAction.stabilizer G v)) : ↥(MulAction.stabilizer G v)) =
      ((Work.ORBassSerre.Action.Structure.hnnPhi v t e ⟨x, hx'⟩ :
        Work.ORBassSerre.Action.Structure.hnnB v t e) : ↥(MulAction.stabilizer G v)) := by
  apply Subtype.ext
  rw [Work.OROneRel.hnnConjEquiv_coe]
  rfl

end Work.OROneRel
