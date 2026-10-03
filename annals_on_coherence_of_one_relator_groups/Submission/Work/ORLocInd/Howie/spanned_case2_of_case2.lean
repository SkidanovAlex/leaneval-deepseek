import Mathlib
import Submission.Work.ORLocInd.Howie.SpanPresentation
import Submission.Work.ORLocInd.Howie.exists_spanDatum
import Submission.Work.ORLocInd.Howie.Datum
import Submission.Work.ORLocInd.Howie.not_hasIndicableLabelling

universe u

namespace Work.ORLocInd.Howie

/-- **Howie's Case 2 for a spanning datum.**

`hcase2` is the statement of `Work.ORLocInd.Howie.case2`: for a *finite* `CodeSeparates`
presentation admitting no indicable labelling, every vertex group is trivial and every arrow occurs
at most once in every relator.  The lemma below removes the finiteness hypotheses (they follow from
the datum: `hpair` exhibits `Quiver.Total V` as a quotient of the finite list `D.usedArrowsList` and
`hrel` exhibits `P.ι` as a quotient of the finite list of terms of `D`) and replaces the hypothesis
`P.HasIndicableLabelling` by non-indicability of the vertex group at `v` (which is equivalent by
`not_hasIndicableLabelling`, using the connectivity `hconn`). -/
theorem spanned_case2_of_case2
    (hcase2 : ∀ (N : ℕ) {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V] [DecidableEq V]
      (P : Work.ORLocInd.Howie.Presentation V), Nat.card P.ι = N → Finite P.ι →
      Finite (Quiver.Total V) → P.CodeSeparates → ¬ P.HasIndicableLabelling →
      (∀ x : V, Subsingleton (P.vertexGroup x)) ∧
        ∀ (i : P.ι) (e : Quiver.Total V), e ∈ (P.path i).arrowList →
          Work.ORLocInd.Howie.edgeCount P.edgeOf (P.path i) e = 1)
    {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V] [DecidableEq V]
    (P : Work.ORLocInd.Howie.Presentation V) (hsep : P.CodeSeparates) (v : V) {n : ℕ}
    (D : Work.ORLocInd.Howie.Datum P v n)
    (hconn : ∀ x : V, Nonempty (Quiver.Path v x))
    (hpair : ∀ e : Quiver.Total V, e ∈ D.usedArrowsList)
    (hrel : ∀ i : P.ι, Work.ORLocInd.Howie.UsedRelator D i)
    (hnonind : ∀ f : P.vertexGroup v →* Multiplicative ℤ, ¬ Function.Surjective f) :
    Subsingleton (P.vertexGroup v) ∧
      ∀ (i : P.ι) (e : Quiver.Total V), Work.ORLocInd.Howie.edgeCount P.edgeOf (P.path i) e ≤ 1 := by
  -- `hpair` exhibits `Quiver.Total V` as a quotient of the finite list `D.usedArrowsList`, and
  -- `hrel` exhibits `P.ι` as a quotient of the finite list of all terms of the datum.  These are
  -- exactly the finiteness hypotheses under which `hcase2` is stated, so the latter applies
  -- verbatim.
  haveI : Fintype P.ι := by
    let L : List (RelatorTerm P v) := (List.finRange n).flatMap (fun j => D.terms j)
    have hf : Function.Surjective (fun k : Fin L.length => RelatorTerm.i (L.get k)) := by
      intro i
      obtain ⟨j, t, ht, hi⟩ := hrel i
      obtain ⟨k, hk⟩ := List.get_of_mem
        (List.mem_flatMap.mpr ⟨j, List.mem_finRange j, ht⟩ : t ∈ L)
      refine ⟨k, ?_⟩
      show RelatorTerm.i (L.get k) = i
      rw [show L.get k = t from hk, hi]
    haveI : Finite P.ι :=
      Finite.of_surjective (fun k : Fin L.length => RelatorTerm.i (L.get k)) hf
    exact Fintype.ofFinite P.ι
  haveI : Fintype (Quiver.Total V) := by
    have hfin : Finite (Quiver.Total V) :=
      Finite.of_surjective (fun k : Fin D.usedArrowsList.length => D.usedArrowsList.get k)
        (by
          intro e
          obtain ⟨k, hk⟩ := List.get_of_mem (hpair e)
          exact ⟨k, hk⟩)
    exact Fintype.ofFinite _
  obtain ⟨hsub, hclause⟩ := hcase2 (Nat.card P.ι) P rfl inferInstance inferInstance hsep
    (Work.ORLocInd.Howie.not_hasIndicableLabelling P v hconn hnonind)
  refine ⟨hsub v, fun i e => ?_⟩
  -- `edgeCount` only depends on the *code* of `e`, so the statement for `e ∈ (P.path i).arrowList`
  -- gives it for every `e` (an arrow with the code of `e` is `e` or `e⁻¹`, by `hsep`).
  by_cases he : e ∈ (P.path i).arrowList
  · exact le_of_eq (hclause i e he)
  · have hEq : Work.ORLocInd.Howie.edgeCount P.edgeOf (P.path i) e =
        Work.ORLocInd.Howie.edgeCount P.edgeOf (P.path i) (Quiver.totalReverse e) := by
      unfold Work.ORLocInd.Howie.edgeCount
      rw [P.edgeOf_reverse e]
    rw [hEq]
    by_cases he' : Quiver.totalReverse e ∈ (P.path i).arrowList
    · exact le_of_eq (hclause i (Quiver.totalReverse e) he')
    · have hzero : Work.ORLocInd.Howie.edgeCount P.edgeOf (P.path i)
          (Quiver.totalReverse e) = 0 := by
        unfold Work.ORLocInd.Howie.edgeCount
        rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
        intro g hg hge
        have hge' : P.edgeOf g = P.edgeOf (Quiver.totalReverse e) := by
          simpa only [decide_eq_true_eq] using hge
        rcases hsep g (Quiver.totalReverse e) hge' with h | h
        · exact he' (h ▸ hg)
        · rw [Quiver.totalReverse_involutive] at h
          exact he (h ▸ hg)
      rw [hzero]
      omega

end Work.ORLocInd.Howie
