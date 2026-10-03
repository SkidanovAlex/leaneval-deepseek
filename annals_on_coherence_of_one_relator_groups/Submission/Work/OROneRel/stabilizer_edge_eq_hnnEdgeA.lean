import Mathlib
import Submission.Work.OROneRel.hnnConjSplit
import Submission.Work.ORBassSerre.Action.Structure.hnn_reduced_word_ne_one

namespace Work.OROneRel

universe u

/-- The stabiliser of an arrow `e : v ⟶ z` (as an element of `Quiver.Total V`) is the
intersection of the stabilisers of its two endpoints.  The tree hypothesis is used for the
inclusion: two arrows with the same endpoints coincide in a tree. -/
theorem stabilizer_total_mk_eq_inf {G : Type u} [Group G] {V : Type u} [Quiver V]
    [Quiver.HasInvolutiveReverse V] [MulAction G V] [Work.ORBassSerre.GraphAction G V]
    (hT : Work.ORBassSerre.IsTree V) {v z : V} (e : v ⟶ z) :
    MulAction.stabilizer G (Quiver.Total.mk v z e) =
      MulAction.stabilizer G v ⊓ MulAction.stabilizer G z := by
  ext g
  rw [Subgroup.mem_inf, MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff,
    MulAction.mem_stabilizer_iff]
  constructor
  · intro hg
    refine ⟨?_, ?_⟩
    · have h := congrArg Quiver.Total.left hg
      simpa using h
    · have h := congrArg Quiver.Total.right hg
      simpa using h
  · rintro ⟨hgv, hgz⟩
    refine Work.ORBassSerre.Action.Structure.total_ext_of_isTree (hT := hT) ?_ ?_
    · rw [Work.ORBassSerre.Action.Structure.total_smul_left]
      exact hgv
    · rw [Work.ORBassSerre.Action.Structure.total_smul_right]
      exact hgz

/-- If `t • z = v` then the stabiliser of `z` is the `t⁻¹`-conjugate of the stabiliser of `v`. -/
theorem stabilizer_eq_map_conj_of_smul_eq {G : Type u} [Group G] {V : Type u} [MulAction G V]
    {v z : V} {t : G} (ht : t • z = v) :
    MulAction.stabilizer G z = (MulAction.stabilizer G v).map (MulAut.conj t⁻¹) := by
  have hz : z = t⁻¹ • v := by
    have h := congrArg (fun x => t⁻¹ • x) ht
    simpa only [← mul_smul, inv_mul_cancel, one_smul] using h
  rw [hz, MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  rfl

/-- For a group acting on a tree with `e : v ⟶ z` and `t • z = v`, the stabiliser of the edge `e`
is exactly `hnnEdgeA (Stab v) t = Stab v ⊓ t⁻¹ (Stab v) t`. -/
theorem stabilizer_edge_eq_hnnEdgeA {G : Type u} [Group G] {V : Type u} [Quiver V]
    [Quiver.HasInvolutiveReverse V] [MulAction G V] [Work.ORBassSerre.GraphAction G V]
    (hT : Work.ORBassSerre.IsTree V)
    (v : V) (t : G) {z : V} (e : v ⟶ z) (ht : t • z = v) :
    Work.OROneRel.hnnEdgeA (MulAction.stabilizer G v) t =
      MulAction.stabilizer G (Quiver.Total.mk v z e) := by
  have hz : z = t⁻¹ • v := by
    have h := congrArg (fun x => t⁻¹ • x) ht
    simpa only [← mul_smul, inv_mul_cancel, one_smul] using h
  rw [stabilizer_total_mk_eq_inf (G := G) (hT := hT) e, hz,
    MulAction.stabilizer_smul_eq_stabilizer_map_conj, hnnEdgeA]
  rfl

end Work.OROneRel
