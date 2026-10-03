import Mathlib
import Submission.Work.ORLocInd.Howie.Defs2
import Submission.Work.ORLocInd.Howie.SpanPresentation
import Submission.Work.ORLocInd.Howie.exists_spanDatum
import Submission.Work.ORLocInd.Howie.Datum

universe u

set_option linter.style.haveILetI false

namespace Work.ORLocInd.Howie

theorem datum_vanishes_spanned
    (hcase1 : ∀ {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V] [DecidableEq V]
      (P : Work.ORLocInd.Howie.Presentation V) (hsep : P.CodeSeparates) (v : V) {n : ℕ}
      (D : Work.ORLocInd.Howie.Datum P v n),
      (∀ x : V, Nonempty (Quiver.Path v x)) → (∀ e : Quiver.Total V, e ∈ D.usedArrowsList) →
      (∀ i : P.ι, Work.ORLocInd.Howie.UsedRelator D i) →
      (∃ φ : P.vertexGroup v →* Multiplicative ℤ, Function.Surjective φ) →
      Finite (Abelianization (PresentedGroup (Set.range D.W))) →
      ∃ (V' : Type u) (_ : Quiver V') (_ : Quiver.HasInvolutiveReverse V') (_ : DecidableEq V')
        (P' : Work.ORLocInd.Howie.Presentation V') (v' : V') (D' : Work.ORLocInd.Howie.Datum P' v' n),
        P'.CodeSeparates ∧ D'.measure < D.measure ∧ D'.W = D.W ∧
        (∀ e : Quiver.Total V', e ∈ D'.usedArrowsList) ∧
        (∀ i : P'.ι, Work.ORLocInd.Howie.UsedRelator D' i) ∧
        (∀ x : V', Nonempty (Quiver.Path v' x)) ∧
        ((∀ j, D'.γ j ∈ P'.relatorNormalClosure v') → ∀ j, D.γ j ∈ P.relatorNormalClosure v))
    (hcase2 : ∀ {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V] [DecidableEq V]
      (P : Work.ORLocInd.Howie.Presentation V) (hsep : P.CodeSeparates) (v : V) {n : ℕ}
      (D : Work.ORLocInd.Howie.Datum P v n),
      (∀ x : V, Nonempty (Quiver.Path v x)) → (∀ e : Quiver.Total V, e ∈ D.usedArrowsList) →
      (∀ i : P.ι, Work.ORLocInd.Howie.UsedRelator D i) →
      (∀ f : P.vertexGroup v →* Multiplicative ℤ, ¬ Function.Surjective f) →
      Subsingleton (P.vertexGroup v) ∧
        ∀ (i : P.ι) (e : Quiver.Total V), Work.ORLocInd.Howie.edgeCount P.edgeOf (P.path i) e ≤ 1)
    {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V] [DecidableEq V]
    (P : Work.ORLocInd.Howie.Presentation V) (hsep : P.CodeSeparates) (v : V) {n : ℕ}
    (D : Work.ORLocInd.Howie.Datum P v n)
    (hconn : ∀ x : V, Nonempty (Quiver.Path v x))
    (hpair : ∀ e : Quiver.Total V, e ∈ D.usedArrowsList)
    (hrel : ∀ i : P.ι, Work.ORLocInd.Howie.UsedRelator D i)
    (hfin : Finite (Abelianization (PresentedGroup (Set.range D.W)))) :
    ∀ j, D.γ j ∈ P.relatorNormalClosure v := by
  classical
  -- Strong induction on the induction measure `D.measure`.
  have key : ∀ m : ℕ, ∀ {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V] [DecidableEq V]
      (P : Work.ORLocInd.Howie.Presentation V) (hsep : P.CodeSeparates) (v : V) {n : ℕ}
      (D : Work.ORLocInd.Howie.Datum P v n),
      D.measure = m →
      (∀ x : V, Nonempty (Quiver.Path v x)) →
      (∀ e : Quiver.Total V, e ∈ D.usedArrowsList) →
      (∀ i : P.ι, Work.ORLocInd.Howie.UsedRelator D i) →
      Finite (Abelianization (PresentedGroup (Set.range D.W))) →
      ∀ j, D.γ j ∈ P.relatorNormalClosure v := by
    intro m
    induction m using Nat.strongRecOn with
    | ind m ih =>
      intro V _ _ _ P hsep v n D hmeas hconn hpair hrel hfin
      by_cases hind : ∃ φ : P.vertexGroup v →* Multiplicative ℤ, Function.Surjective φ
      · -- Case 1: an epimorphism onto `ℤ`; descend along the cyclic cover.
        obtain ⟨V', iq, ir, ide, P', v', D', hsep', hlt, hW, hpair', hrel', hconn', htr⟩ :=
          hcase1 (P := P) (v := v) (D := D) hsep hconn hpair hrel hind hfin
        letI : Quiver V' := iq
        letI : Quiver.HasInvolutiveReverse V' := ir
        letI : DecidableEq V' := ide
        refine htr (ih D'.measure ?_ P' hsep' v' D' rfl hconn' hpair' hrel' ?_)
        · rw [← hmeas]; exact hlt
        · rw [hW]; exact hfin
      · -- Case 2: no epimorphism onto `ℤ`; the vertex group is trivial.
        have hnonind : ∀ f : P.vertexGroup v →* Multiplicative ℤ, ¬ Function.Surjective f :=
          fun f hf => hind ⟨f, hf⟩
        obtain ⟨hsub, _⟩ := hcase2 (P := P) (v := v) (D := D) hsep hconn hpair hrel hnonind
        intro j
        have htop : P.relatorNormalClosure v = ⊤ :=
          QuotientGroup.subgroup_eq_top_of_subsingleton (P.relatorNormalClosure v) hsub
        rw [htop]
        exact Subgroup.mem_top _
  exact key D.measure (P := P) (hsep := hsep) (v := v) (D := D) rfl hconn hpair hrel hfin

end Work.ORLocInd.Howie
