import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE3.InvCountH
import Submission.Work.CORE2A.lemma22
import Submission.Work.CORE3.NcardInvSetCentralizerConj

namespace Work.CORE3

open Work.GW2

/-- Membership in `involutionSet ⊤ ∩ K` (for a subgroup `K`) is the same as membership in
`involutionSet K`. -/
private lemma involutionSet_top_inter_aux {G : Type} [Group G] (K : Subgroup G) :
    (Work.GW2.involutionSet (⊤ : Subgroup G) ∩ (K : Set G)) = Work.GW2.involutionSet K := by
  ext x
  simp only [Work.GW2.involutionSet, Set.mem_inter_iff, Set.mem_ofPred_eq, Subgroup.mem_top,
    true_and]
  exact and_comm

/-- **Bender 1981 §3, p. 223** (in the subcase `V = O₂(Ĥ)` of type `(2,2)`): for *every*
involution `s` of the minimal counterexample `G`, the centralizer `C_G(s)` contains exactly
`3 + 2|K|` involutions.

Since `G` is non-abelian simple with dihedral Sylow 2-subgroups, Bender's fusion theorem
(`InvolutionFusionProp`, part of the local toolkit `I.T`) makes all involutions conjugate.
Conjugation is a bijection of `G` preserving the order of elements and carrying `C_G(s)` onto
the centralizer of the conjugate, so the count `|{x : orderOf x = 2, x ∈ C_G(s)}|` is a class
function: it is the same for `s` as for `B.t`.  For `s = B.t` the count is `3 + 2|K|` by the
first counting identity of Bender 1981 §3 (`Work.CORE3.InvCountH`). -/
theorem InvolutionCentralizerCount (G : Type) [Group G] [Finite G] (I : Work.CORE3.Case1Inputs) (h : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) (h1 : Work.GW2.Case1 B) (D : Work.GW2.Case1bData B) :
    ∀ s : G, orderOf s = 2 →
      (Work.GW2.involutionSet (⊤ : Subgroup G) ∩ Subgroup.centralizer ({s} : Set G)).ncard
        = 3 + 2 * Nat.card D.K := by
  intro s hs
  -- The Sylow 2-subgroup is dihedral of order `2n`, `n ≥ 2`; no normal subgroup of index two.
  obtain ⟨n, hn, ⟨e⟩⟩ := SylowDihedral G h B
  have hnoN := Work.CORE2A.bender_no_index_two h B
  -- Bender's fusion: all involutions of `G` are conjugate.
  have hconj : ∀ x y : G, orderOf x = 2 → orderOf y = 2 → IsConj x y :=
    (I.T.fus G B.S n hn ⟨e⟩ hnoN).1
  obtain ⟨g, hg⟩ := isConj_iff.mp (hconj s B.t hs B.t_order)
  -- Conjugation invariance of the count.
  have hconjset := NcardInvSetCentralizerConj s B.t g hg
  -- `B.H = C_G(B.t)`, so the count for `B.t` is the one computed by `InvCountH`.
  have hH : (Work.GW2.involutionSet (⊤ : Subgroup G) ∩
        Subgroup.centralizer ({B.t} : Set G)).ncard = (Work.GW2.involutionSet B.H).ncard := by
    rw [involutionSet_top_inter_aux]
  rw [hconjset, hH]
  exact InvCountH I h B h1 D

end Work.CORE3
