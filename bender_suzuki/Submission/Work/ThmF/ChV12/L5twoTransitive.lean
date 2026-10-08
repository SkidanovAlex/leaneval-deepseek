import Mathlib
import Submission.Work.ThmF.ChV12.L5Base
import Submission.Work.ThmF.ChV12.L5Struct
import Submission.Work.ThmF.ChV12.X5RankOneAux
import Submission.Work.Models.Port.Commons.GroupTheory.GroupAction.coset_multiplyPretransitive_two_of_two_doubleCosets

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.ChV12.L5twoTransitive` — `X = ⟨Q₀,K,t⟩` is 2-transitive on `X ⧸ B`

Let `(H,Q,t,s)` satisfy `Hyp5` and let `B = bor H t = Q₀sub H ⊔ Ksub H t` be the "Borel" of
`X = X5 H t = ⟨Q₀, K, t⟩`.  This file proves Peterfalvi II Ch. V §2, Lemma 5's group-theoretic
statement that **`X` acts 2-transitively on the set `X ⧸ B` of left cosets of `B`**, i.e.

  `Submission.Blueprint.IsTwoTransitiveOn (bor H t).subgroupOf (X5 H t)`.

The mathematics is the classical two-double-coset criterion for 2-transitivity (Bruhat):
`X` acts 2-transitively on `X ⧸ B` as soon as `X = B ∪ B·t·B` for a single element `t`, because
then every coset `≠ B` is of the form `b·(tB)` with `b ∈ B`, i.e. the stabiliser `B` of the base
point is already transitive on the complement of the base point.  No hypothesis on `t` is needed
(beyond `t` being one of the two double-coset representatives).

The two inputs are:

* `Work.ThmF.L5.X5_eq_borel` (in `L5Struct.lean`), the Bruhat decomposition
  `X5 H t = B ∪ B·t·B`, exported in membership form as `Work.ThmF.L5.mem_bor_or_btb`
  (`X5RankOneAux.lean`), together with `Work.ThmF.L5.bor_le_X5`;
* the general criterion `Commons.GroupTheory.GroupAction.coset_multiplyPretransitive_two_of_two_doubleCosets`.

`bor_subgroupOf_cover` below is the elementwise form of the decomposition, phrased entirely
inside `X`; it is the hypothesis of the general criterion.

(For the record: the same statement is also proved, independently and by a direct coset
computation, as `Work.ThmF.ChV12.X5_twoTransitive` in `L5simpleX5.lean`.  The proof here is
kept separate so that `L5twoTransitive` does not depend on that larger module.)
-/

namespace Work.ThmF.ChV12

/-- **Bruhat decomposition of `X = ⟨Q₀,K,t⟩` inside `X`.**  Every element of
`X = X5 H t = ⟨Q₀,K,t⟩` lies either in the Borel `B = bor H t = Q₀sub H ⊔ Ksub H t` or in the
single double coset `B · t · B`.  This is the elementwise form of `Work.ThmF.L5.X5_eq_borel`
(`X = B ∪ B·t·B`), read inside `↥(X5 H t)` with the witnesses taken in
`↥(B.subgroupOf (X5 H t))`. -/
theorem bor_subgroupOf_cover {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s : G}
    (hC4 : Submission.Blueprint.ChIIFourProp) (h : Work.ThmF.Lemma5.Hyp5 H Q t s) :
    ∀ g : ↥(Work.ThmF.Lemma5.X5 H t),
      g ∈ (Work.ThmF.L5.bor H t).subgroupOf (Work.ThmF.Lemma5.X5 H t) ∨
        ∃ b₁ b₂ : ↥((Work.ThmF.L5.bor H t).subgroupOf (Work.ThmF.Lemma5.X5 H t)),
          g = b₁ * Work.ThmF.Lemma5.tX H t * b₂ := by
  intro g
  rcases Work.ThmF.L5.mem_bor_or_btb hC4 h g.2 with hg | ⟨b₁, hb₁, b₂, hb₂, hgb⟩
  · exact Or.inl (by rwa [Subgroup.mem_subgroupOf])
  · refine Or.inr ⟨⟨⟨b₁, Work.ThmF.L5.bor_le_X5 hb₁⟩, hb₁⟩,
      ⟨⟨b₂, Work.ThmF.L5.bor_le_X5 hb₂⟩, hb₂⟩, ?_⟩
    apply Subtype.ext
    simpa [Work.ThmF.Lemma5.tX] using hgb

theorem L5twoTransitive {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s : G} (hC4 : Submission.Blueprint.ChIIFourProp) (h : Work.ThmF.Lemma5.Hyp5 H Q t s) : Submission.Blueprint.IsTwoTransitiveOn ((Work.ThmF.L5.bor H t).subgroupOf (Work.ThmF.Lemma5.X5 H t)) := by
  exact Commons.GroupTheory.GroupAction.coset_multiplyPretransitive_two_of_two_doubleCosets _ _
    (bor_subgroupOf_cover hC4 h)

end Work.ThmF.ChV12
