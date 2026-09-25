import Mathlib
import Submission.Work.RelatorRank.Bridge
import Submission.Work.TameRelation.Padding.exists_padding

/-!
# Padding a pro-`2` presentation by trivial generators

**Namespace** `Work.RelatorRank.Transfer`; module
`Submission.Work.RelatorRank.Transfer.hasProP2Presentation_pad_generators`.

The relation-rank predicates of `Submission/Work/RelatorRank/Defs.lean` are insensitive to the
*number* of generators once one allows relations: adding `k` dummy generators (sent to the
identity) costs exactly `k` extra relations, namely the `k` dummy generators themselves.

Concretely, from a datum with `d` generators and `r` relators we build one with `d + k` generators
and `r + k` relators:

* the padded generating family `gen' : Fin (d + k) → Γ` extends `gen` along `Fin.castLE` and sends
  the new generators to `1`; it therefore still *densely* generates `Γ`, because the image of
  `gen'` contains the image of `gen`;
* the padded relator set `rel'` consists of the images of the old relators under the inclusion
  `FreeGroup (Fin d) →* FreeGroup (Fin (d + k))` of the first `d` letters, together with the `k`
  new letters `x_d, …, x_{d+k-1}`; it has at most `r + k` elements;
* the kernel equality is the content of `Work.TameRelation.Padding.exists_padding`, whose proof
  compares the quotients `FreeGroup (Fin d) ⧸ normalClosure rel` and
  `FreeGroup (Fin (d + k)) ⧸ normalClosure rel'` through the projection that kills the padding
  generators.

This is the `HasProP2Presentation`-level form of the padding bookkeeping used by
`Work.TameRelation.tameRelationBound_of_deficiencyBound` (which pads a presentation of a Galois
group from `d ≤ 5` generators to `5` generators).
-/

namespace Work.RelatorRank.Transfer

/-- **A presentation can be padded by trivial generators.**  If `Γ` admits a topological
presentation with `d` generators and at most `r` relators, then it admits one with `d + k`
generators and at most `r + k` relators: the `k` extra generators are sent to the identity and the
`k` extra relators are the extra generators themselves. -/
theorem hasProP2Presentation_pad_generators {Γ : Type*} [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] {d r k : ℕ} (h : HasProP2Presentation Γ d r) :
    HasProP2Presentation Γ (d + k) (r + k) := by
  obtain ⟨P⟩ := h
  obtain ⟨gen', rel', hcard', hcomp, hker'⟩ :=
    Work.TameRelation.Padding.exists_padding (G := Γ) (d := d) (n := d + k)
      (Nat.le_add_right d k) P.gen P.rel P.ker_eq
  refine ⟨{ gen := gen', rel := rel', dense := ?_, card_le := ?_, ker_eq := hker' }⟩
  · -- the padded family still generates densely: its range contains the range of `gen`
    have hsub : Subgroup.closure (Set.range P.gen) ≤ Subgroup.closure (Set.range gen') := by
      apply Subgroup.closure_mono
      rintro x ⟨i, rfl⟩
      exact ⟨Fin.castLE (Nat.le_add_right d k) i, congrFun hcomp i⟩
    have hdense : (Subgroup.closure (Set.range P.gen)).topologicalClosure = ⊤ :=
      (denseGenerating_iff P.gen).mp P.dense
    have htc := Subgroup.topologicalClosure_mono hsub
    rw [hdense] at htc
    exact top_le_iff.mp htc
  · -- the `k` padding generators contribute exactly `k` relators
    have hcard := hcard'
    have hrel := P.card_le
    have hsub : d + k - d = k := Nat.add_sub_cancel_left d k
    omega

end Work.RelatorRank.Transfer
