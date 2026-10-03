import Mathlib
import Submission.Work.ORBassSerre.Action.Structure.BSWalk
import Submission.Work.ORBassSerre.Action.Structure.exists_parent_chain
import Submission.Work.ORBassSerre.Action.Structure.exists_concat
import Submission.Work.ORBassSerre.Action.Structure.exists_inv
import Submission.Work.ORBassSerre.Action.Structure.exists_pathWord_root_to
import Submission.Work.ORBassSerre.Action.Structure.pathWord_of_generator

set_option linter.unusedSectionVars false

namespace Work.ORBassSerre.Action.Structure

/-!
# Every generator of `Γ` is the `elt` of a closed path word based at the root

Let `d` be the spanning-tree datum of a cocompact action of `G` on a graph `V` without inversions
and `D : d.PresData` the presentation data of the fundamental domain, with fundamental group
`Γ = Gamma d D`.  The generators of `Γ` are the chosen generators of the vertex groups together
with the stable letters of the non-tree edge orbits.

Each generator is realised as the `elt` of a closed path word based at the root of the spanning
tree: for a vertex-group generator at the orbit `A` we walk along the parent chain from the root
down to `A` (all steps tree edges, hence trivial contributions), take the single letter carrying the
chosen element of `vgroup A`, and walk back to the root; for a stable letter of a non-tree edge
orbit `E` we walk from the root to `srcE E`, take the single step along `E` (which contributes
exactly the stable letter), and walk back to the root from `tgtE E`.  The walk back uses the reverse
of the walk down (`exists_inv`), and the pieces are glued with `exists_concat`.
-/

theorem exists_closed_pathWord_of_generator {G : Type*} {V : Type*}
    [Group G] [Quiver V] [Quiver.HasInvolutiveReverse V] [MulAction G V]
    [Work.ORBassSerre.GraphAction G V]
    {d : Work.ORBassSerre.Action.Structure.TreeDatum G V}
    [Fintype (Work.ORBassSerre.orbitV G V)] [Fintype (Work.ORBassSerre.orbitE G V)]
    [Nonempty (Work.ORBassSerre.orbitE G V)]
    (D : d.PresData) (x : d.PresGen D) :
    ∃ W : Work.ORBassSerre.Action.Structure.TreeDatum.PathWord d,
      W.orb 0 = d.root ∧ W.Closed ∧ W.elt D = PresentedGroup.of x := by
  classical
  rcases x with ⟨A, i⟩ | ⟨E, hE⟩
  · -- a chosen generator of a vertex group
    obtain ⟨Wr, hWr0, hWrL, hWrelt⟩ := exists_pathWord_root_to (d := d) A
    obtain ⟨Ws, hWs0, hWslen, hWselt⟩ :=
      TreeDatum.exists_singleLetter (d := d) A (D.πV A (FreeGroup.of i))
    obtain ⟨Wb, _, hWb0, hWbL, hWbelt⟩ := exists_inv (d := d) Wr
    have h12 : Wr.orb Wr.len = Ws.orb 0 := by rw [hWrL, hWs0]
    obtain ⟨W12, _, hW120, hW12L, hW12elt⟩ := exists_concat Wr Ws h12
    have h23 : W12.orb W12.len = Wb.orb 0 := by rw [hW12L, hWslen, hWs0, hWb0, hWrL]
    obtain ⟨W, _, hW0, hWL, hWelt⟩ := exists_concat W12 Wb h23
    refine ⟨W, ?_, ?_, ?_⟩
    · rw [hW0, hW120, hWr0]
    · rw [TreeDatum.PathWord.Closed]
      rw [hWL, hWbL, hWr0, hW0, hW120, hWr0]
    · rw [hWelt D, hW12elt D, hWrelt D, hWselt D, hWbelt D, hWrelt D, inv_one, one_mul, mul_one,
        TreeDatum.gEltHom_generator]
  · -- the stable letter of a non-tree edge orbit
    obtain ⟨W1, hW10, hW1L, hW1elt⟩ := exists_pathWord_root_to (d := d) (srcE (G := G) (V := V) E)
    obtain ⟨W2, hW20, hW2L, hW2elt⟩ := TreeDatum.exists_stepWord (d := d) E
    obtain ⟨Wt, hWt0, hWtL, hWtelt⟩ := exists_pathWord_root_to (d := d) (tgtE (G := G) (V := V) E)
    obtain ⟨W3, _, hW30, hW3L, hW3elt⟩ := exists_inv (d := d) Wt
    have h12 : W1.orb W1.len = W2.orb 0 := by rw [hW1L, hW20]
    obtain ⟨W12, _, hW120, hW12L, hW12elt⟩ := exists_concat W1 W2 h12
    have h23 : W12.orb W12.len = W3.orb 0 := by rw [hW12L, hW2L, hW30, hWtL]
    obtain ⟨W, _, hW0, hWL, hWelt⟩ := exists_concat W12 W3 h23
    refine ⟨W, ?_, ?_, ?_⟩
    · rw [hW0, hW120, hW10]
    · rw [TreeDatum.PathWord.Closed]
      rw [hWL, hW3L, hWt0, hW0, hW120, hW10]
    · rw [hWelt D, hW12elt D, hW1elt D, hW2elt D, hW3elt D, hWtelt D, inv_one, one_mul, mul_one]
      exact TreeDatum.stepGam_true_eq_of_not_tree (d := d) D hE

end Work.ORBassSerre.Action.Structure
