/-
# L5d with the forest hypothesis localised at `e.left` and the deletion hypothesis `hbr`

This is the variant of `Work.ORLocInd.Howie.false_of_bridge_forest_side_avoid` in which

* `hbr` is the honest bridge hypothesis of the deleted graph `Γ ∖ e`, namely
  `∀ q : Quiver.Path e.right e.left, Avoids P e q → False`, i.e. `¬ DelReach P e e.right`;
* `hfor` is **localised at `e.left`**: every reduced closed path at `e.left` avoiding the code of
  `e` is the empty path (rather than the strengthened hypothesis "for every vertex `y`").

The argument is the same as in `false_of_bridge_forest_side_avoid`: split `r` at an occurrence of
the arrow `e`, rotate to `t = s ∗ q : e.right ⟶ e.left`, apply the honest bridge decomposition
`delBridge_decomp` to read `t = u ∗ e⁻¹ ∗ v` with `v` avoiding the code of `e`, and use `hfor` at
`e.left` when `v` is nonempty; when `v` is empty, the cyclic rotation of `r` ends in the crossing
`e⁻¹` right after `e`, producing the forbidden backtrack (or the forbidden cyclic backtrack).
-/
import Mathlib
import Submission.Work.ORLocInd.Howie.DelReach
import Submission.Work.ORLocInd.Howie.BridgeSide
import Submission.Work.ORLocInd.Howie.endsWith_comp
import Submission.Work.ORLocInd.Howie.startsWith_comp
import Submission.Work.ORLocInd.Howie.exists_comp_of_mem_arrowList
import Submission.Work.ORLocInd.Howie.isReduced_comp_of_decomp
import Submission.Work.ORLocInd.Howie.bridge_decomp
import Submission.Work.ORLocInd.Howie.delBridge_decomp
import Submission.Work.ORLocInd.Howie.Defs2

namespace Work.ORLocInd.Howie.L5

theorem false_of_bridge_forest_side_del {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V]
    (P : Work.ORLocInd.Howie.Presentation V) (hsep : P.CodeSeparates) (e : Quiver.Total V)
    (hbr : ∀ q : Quiver.Path e.right e.left, Work.ORLocInd.Howie.Avoids P e q → False)
    (hfor : ∀ q : Quiver.Path e.left e.left, Work.ORLocInd.Howie.Avoids P e q → q.IsReduced →
      q = Quiver.Path.nil)
    {w : V} (r : Quiver.Path w w) (hr : r.IsReduced)
    (hcr : Work.ORLocInd.Howie.IsCyclicallyReduced r) (he : e ∈ r.arrowList) : False := by
  -- `hbr` is the failure of `e`-reachability of `e.right`, while `e.left` is `e`-reachable.
  have hnot : ¬ Work.ORLocInd.Howie.DelReach P e e.right :=
    (Work.ORLocInd.Howie.not_delReach_right_iff P e).mpr hbr
  have hreach : Work.ORLocInd.Howie.DelReach P e e.left := Work.ORLocInd.Howie.delReach_self P e
  -- Split `r` at the occurrence of the arrow `e = mk e.left e.right e.hom`.
  have he' : Quiver.Total.mk e.left e.right e.hom ∈ r.arrowList := by
    have h : e = Quiver.Total.mk e.left e.right e.hom := by cases e; rfl
    rwa [h] at he
  obtain ⟨q, s, hqs⟩ := Work.ORLocInd.Howie.exists_comp_of_mem_arrowList (p := r) (f := e.hom) he'
  -- The cyclic rotation `t = s ∗ q : e.right ⟶ e.left` of `r` is reduced.
  have hr' : (q.comp (e.hom.toPath.comp s)).IsReduced := by rw [← hqs]; exact hr
  have hcr' : Work.ORLocInd.Howie.IsCyclicallyReduced (q.comp (e.hom.toPath.comp s)) := by
    rw [← hqs]; exact hcr
  have htred : (s.comp q).IsReduced :=
    Work.ORLocInd.Howie.isReduced_comp_of_decomp e q s hr' hcr'
  -- The honest bridge decomposition: `t = u ∗ e⁻¹ ∗ v` with `v` avoiding the code of `e`.
  obtain ⟨u, v, huv, hv⟩ :=
    Work.ORLocInd.Howie.delBridge_decomp P hsep e hnot (s.comp q) htred hreach
  have hvred : v.IsReduced := by
    have h1 : ((u.cons (Quiver.reverse e.hom)).comp v).IsReduced := by rw [← huv]; exact htred
    exact (Quiver.Path.isReduced_comp_iff.mp h1).2.1
  rcases Nat.eq_zero_or_pos v.length with hv0 | hvpos
  · -- The tail `v` is empty: `t` ends with the crossing `e⁻¹`.
    have hvnil : v = Quiver.Path.nil := Quiver.Path.eq_nil_of_length_zero v hv0
    have ht_eq : s.comp q = u.cons (Quiver.reverse e.hom) := by
      rw [huv, hvnil, Quiver.Path.comp_nil]
    cases q with
    | nil =>
      -- `r = e ∗ s = e ∗ (u ∗ e⁻¹)` begins with `e` and ends with its reverse: not cyclically
      -- reduced, contradicting `hcr`.
      rw [Quiver.Path.nil_comp] at hqs
      rw [Quiver.Path.comp_nil] at ht_eq
      exact hcr ⟨e.right, e.hom, u, by rw [hqs, ht_eq]⟩
    | cons q' f' =>
      -- The last arrow of `q` is the last arrow of `t = s ∗ q`, i.e. `e⁻¹`, and in `r` it is
      -- immediately followed by `e`: a backtrack, contradicting `hr`.
      have hqne : (q'.cons f').length ≠ 0 := by simp
      have hend : Quiver.Path.EndsWith (q'.cons f') (Quiver.reverse e.hom) :=
        (Work.ORLocInd.Howie.endsWith_comp (q := (q'.cons f')) (p := s) hqne
          (Quiver.reverse e.hom)).mp ⟨u, ht_eq⟩
      obtain ⟨g, hg⟩ := hend
      have hjc : Quiver.Path.JoinConflict (q'.cons f') (e.hom.toPath.comp s) :=
        ⟨e.right, g, Quiver.reverse e.hom, s, hg, by rw [Quiver.reverse_reverse]⟩
      exact (Quiver.Path.isReduced_comp_iff.mp hr').2.2 hjc
  · -- The tail `v` is a nonempty reduced closed path at `e.left` avoiding `e`, contradicting
    -- `hfor` (which says that `Γ ∖ e` has no nonempty reduced closed path at `e.left`).
    have hvnil := hfor v hv hvred
    rw [hvnil] at hvpos
    simp at hvpos

end Work.ORLocInd.Howie.L5
