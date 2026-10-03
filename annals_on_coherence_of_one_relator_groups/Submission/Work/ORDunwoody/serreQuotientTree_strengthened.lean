/-
Copyright: work of the ORDunwoody subproject (node N13 of the
`annals_on_coherence_of_one_relator_groups` project).

# Serre's quotient-tree construction, in the exact form of `SerreQuotientTree`

`Hypotheses.SerreQuotientTree` asks for the quotient of an `H`-tree `S'` by the normal closure
`K` of a finite family of vertex subgroups, together with the four structural clauses of Serre
§5 / JL Lemma 4.1:

* `equivariance` of the quotient map `g = Quotient.mk''` over `H → H ⧸ K`;
* `lift`: *every* edge of the quotient tree comes from an edge of `S'` (the quotient is the
  *full* quotient of the edge set, not merely a graph admitting a domination map);
* `fibre`: the fibres of `g` are exactly the `K`-orbits — this is what makes the quotient map
  a *quotient by `K`* rather than merely `K`-equivariant;
* `stab`: vertex stabilizers of the quotient are the images of the vertex stabilizers of `S'`.

The sibling development
`Submission/Work/ORBassSerre/Assembly/quotientTreeByNormalClosureOfElliptic_corrected.lean`
proves the same construction with the one-sided clause
`S'.Adj u v → S.Adj (g u) (g v) ∨ g u = g v` in place of `lift`, and without `fibre`.  The
one-sided clause is strictly weaker — it is the domination-map condition, whereas `lift` is the
converse direction — and it cannot be recovered from it, since the existential produced by the
corrected statement is not pinned down by its other clauses.  Here the quotient tree is
therefore rebuilt as the quotient graph of the `K`-action itself
(`Work.ORDunwoody.quotientTreeOfNormalClosure`): its edge set is, by construction, the set of
`K`-orbits of edges of `S'`, which gives `lift` and `fibre` directly, while cocompactness
(`Work.ORDunwoody.quotientTreeOfNormalClosure_isCocompact`), finite generation of stabilizers
and the stabilizer formula are the bookkeeping of the corrected statement.

This discharges the named input `Work.ORDunwoody.SerreQuotientTree` of `Hypotheses.lean`
unconditionally.

Owner: node N12 ("G-trees and quotient graphs", "JL Lemma 4.1").
-/
import Mathlib
import Submission.Work.ORDunwoody.Hypotheses
import Submission.Work.ORDunwoody.QuotientTreeDefs
import Submission.Work.ORDunwoody.quotientTreeOfNormalClosure_isCocompact
import Submission.Work.ORBassSerre.Assembly.quotientTreeByNormalClosureOfElliptic_corrected
import Submission.Work.ORBassSerre.QuotientTree.stabilizer_quotient_mk
import Submission.Work.ORBassSerre.QuotientTree.orbitQuiver_nonempty_hom_iff

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

universe u

namespace Work.ORDunwoody

open Work.ORBassSerre

theorem serreQuotientTree_strengthened (Y : Type u) : Work.ORDunwoody.SerreQuotientTree Y := by
  intro H _instH W _instW S' A N hN hA K _instK hK hc hfg
  classical
  -- Read `S'` as a quiver tree, so that the Bass–Serre quotient construction applies to it.
  letI : Quiver W := Work.ORDunwoody.Lemmas.graphQuiver S'.graph
  letI : Quiver.HasInvolutiveReverse W :=
    Work.ORDunwoody.Lemmas.graphQuiverHasInvolutiveReverse S'.graph
  letI : Work.ORBassSerre.GraphAction H W := Work.ORDunwoody.Lemmas.graphQuiverAction S'
  have hT : Work.ORBassSerre.IsTree W := Work.ORDunwoody.Lemmas.graphQuiver_isTree S'
  haveI : Nonempty W := S'.isTree.connected.nonempty
  -- `K` is the normal closure of the subgroups `N w`, each of which consists of elliptic
  -- elements of the action on `S'`.
  have hEll : ∀ g ∈ (⋃ (w : W) (hw : w ∈ A), (N w hw : Set H)), ∃ v : W, g • v = v := by
    intro g hg
    simp only [Set.mem_iUnion] at hg
    obtain ⟨w, hw, hgw⟩ := hg
    exact ⟨w, hN w hw hgw⟩
  have hgen : Subgroup.normalClosure (⋃ (w : W) (hw : w ∈ A), (N w hw : Set H)) = K := hK.symm
  -- The quotient tree of Serre §5, and the fact (JL Lemma 4.1) that it is a tree.
  let S : Work.ORDunwoody.GTree (H ⧸ K) (MulAction.orbitRel.Quotient ↥K W) :=
    Work.ORDunwoody.quotientTreeOfNormalClosure S' K
      (⋃ (w : W) (hw : w ∈ A), (N w hw : Set H)) hEll hgen
  haveI : Nonempty (Work.ORBassSerre.orbitV ↥K W) :=
    (inferInstance : Nonempty W).map Quotient.mk''
  have htree : Work.ORBassSerre.IsTree (Work.ORBassSerre.orbitV ↥K W) :=
    Work.ORBassSerre.Action.isTree_orbitV_of_normalClosure_elliptic hT K
      (⋃ (w : W) (hw : w ∈ A), (N w hw : Set H)) hEll hgen
  -- Vertex stabilizers of the quotient are the images of vertex stabilizers of `S'`.
  have hstab : ∀ w : W, S.vertexStab (Quotient.mk'' w) =
      (S'.vertexStab w).map (QuotientGroup.mk' K) := by
    intro w
    rw [Work.ORDunwoody.GTree.vertexStab, Work.ORDunwoody.GTree.vertexStab,
      Work.ORBassSerre.QuotientTree.stabilizer_quotient_mk K w]
  have hstabAll : ∀ x : Work.ORBassSerre.orbitV ↥K W, S.vertexStab x =
      (S'.vertexStab (Function.surjInv (Work.ORBassSerre.Assembly.mk_surjective K) x)).map
        (QuotientGroup.mk' K) := by
    intro x
    conv_lhs => rw [← Function.surjInv_eq (Work.ORBassSerre.Assembly.mk_surjective K) x]
    exact hstab (Function.surjInv (Work.ORBassSerre.Assembly.mk_surjective K) x)
  refine ⟨Work.ORBassSerre.orbitV ↥K W, inferInstance, S, Quotient.mk'',
    Work.ORBassSerre.Assembly.mk_surjective K, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- cocompactness: `(H ⧸ K)`-orbits of vertices and of edges of the quotient
    exact Work.ORDunwoody.quotientTreeOfNormalClosure_isCocompact S' K
      (⋃ (w : W) (hw : w ∈ A), (N w hw : Set H)) hEll hgen hc
  · -- finite generation of the stabilizers of the quotient
    refine ⟨?_, ?_⟩
    · intro x
      rw [hstabAll x]
      exact Work.ORBassSerre.Assembly.fg_map (QuotientGroup.mk' K)
        (hfg.1 (Function.surjInv (Work.ORBassSerre.Assembly.mk_surjective K) x))
    · intro A' B' hAB
      rw [Work.ORDunwoody.GTree.edgeStab_eq]
      obtain ⟨a, b, ha, hb, hab⟩ :=
        (Work.ORBassSerre.QuotientTree.orbitQuiver_nonempty_hom_iff K A' B').mp hAB
      rw [Work.ORDunwoody.GTree.vertexStab, Work.ORDunwoody.GTree.vertexStab,
        Work.ORBassSerre.QuotientTree.inf_stabilizer_eq_map K htree ha hb hab]
      exact Work.ORBassSerre.Assembly.fg_map (QuotientGroup.mk' K) (by
        have h1 := hfg.2 a b
          ((Work.ORDunwoody.Lemmas.nonempty_hom_iff_adj S'.graph a b).mp hab)
        rwa [Work.ORDunwoody.GTree.edgeStab_eq, Work.ORDunwoody.GTree.vertexStab,
          Work.ORDunwoody.GTree.vertexStab] at h1)
  · -- equivariance of the quotient map
    intro h w
    exact (Work.ORBassSerre.quotient_smul_mk K h w).symm
  · -- (`lift`) every edge of the quotient comes from an edge of `S'`
    intro x y hxy
    have hxy' : Nonempty (x ⟶ y) := hxy
    obtain ⟨u, v, hu, hv, huv⟩ :=
      (Work.ORBassSerre.QuotientTree.orbitQuiver_nonempty_hom_iff K x y).mp hxy'
    exact ⟨u, v, (Work.ORDunwoody.Lemmas.nonempty_hom_iff_adj S'.graph u v).mp huv, hu, hv⟩
  · -- (`fibre`) the fibres of the quotient map are the `K`-orbits
    intro u v
    constructor
    · intro huv
      have hrel : (MulAction.orbitRel ↥K W) u v := Quotient.exact huv
      obtain ⟨k, hk⟩ := MulAction.mem_orbit_iff.mp ((MulAction.orbitRel_apply).mp hrel)
      have hk' : (k : H) • v = u := by rw [← Subgroup.smul_def]; exact hk
      refine ⟨k⁻¹, ?_⟩
      rw [Subgroup.coe_inv, inv_smul_eq_iff]
      exact hk'.symm
    · rintro ⟨k, hk⟩
      refine Quotient.sound (show (MulAction.orbitRel ↥K W) u v from ?_)
      rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
      refine ⟨k⁻¹, ?_⟩
      rw [Subgroup.smul_def, Subgroup.coe_inv, inv_smul_eq_iff]
      exact hk.symm
  · -- (`stab`) vertex stabilizers of the quotient are images of vertex stabilizers of `S'`
    exact hstabAll

end Work.ORDunwoody
