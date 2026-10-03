import Mathlib
import Submission.Work.ORLocInd.Howie.datum_vanishes_spanned
import Submission.Work.ORLocInd.Howie.codeSeparates_span
import Submission.Work.ORLocInd.Howie.exists_spanDatum
import Submission.Work.ORLocInd.Howie.exists_relation_words
import Submission.Work.ORLocInd.Howie.exists_datum_of_lift_eq_one
import Submission.Work.ORLocInd.Howie.span_reachable
import Submission.Work.ORLocInd.Howie.finite_of_fg_of_no_surjective_int
import Submission.Work.ORLocInd.Basic

namespace Work.ORLocInd.Howie

universe u

/-- **Howie's Theorem 3.1, assembled.**  Combining Howie's two cases — the cyclic-cover step
(`hcase1`) and the non-indicable case (`hcase2`), both hypothesis-driven — every datum of a
staggered presentation without proper powers vanishes: `W_j(γ_1, …, γ_n) = 1` in `π₁(⟨Γ | R⟩, v)`
forces `γ_j ∈ N` for every `j`.

The only ingredients beyond the two cases are (i) Howie's step 1, the passage to the subgraph
spanned by the datum (`exists_spanDatum`), whose connectivity from the base vertex is
`span_reachable`, and (ii) the strong induction on `D.measure` (`datum_vanishes_spanned`). -/
theorem datum_vanishes
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
    (hfin : Finite (Abelianization (PresentedGroup (Set.range D.W)))) :
    ∀ j, D.γ j ∈ P.relatorNormalClosure v := by
  -- Howie's step 1: replace `P` by the sub-presentation spanned by the datum.  It keeps `L` and
  -- `M`, its datum uses every arrow and every relator of the span, and its vanishing implies the
  -- vanishing of `D`; so it suffices to treat spanning data.
  obtain ⟨D₀, hW, hpair, hrel, htr⟩ := exists_spanDatum D
  have hconn : ∀ x : Work.ORLocInd.Howie.SpanVertex D,
      Nonempty (Quiver.Path (Work.ORLocInd.Howie.spanV D) x) := span_reachable D
  have hfin₀ : Finite (Abelianization (PresentedGroup (Set.range D₀.W))) := by rw [hW]; exact hfin
  exact htr (datum_vanishes_spanned hcase1 hcase2 (spanPresentation D)
    (codeSeparates_span hsep D) (spanV D) D₀ hconn hpair hrel hfin₀)

/-- **Every vertex group of a staggered groupoid presentation without proper powers is locally
indicable** (Howie 2000, Theorem 3.1), in the form in which the outer induction of the proof
supplies its two cases `hcase1` (the cyclic-cover step) and `hcase2` (the non-indicable case).

Proof.  Let `H ≤ P.vertexGroup v` be finitely generated and non-trivial.  If `H` admits a surjection
onto `ℤ` we are done.  Otherwise `Abelianization H` is finite
(`finite_of_fg_of_no_surjective_int`), so `exists_relation_words` produces `n` relations `W_j` of a
generating tuple `ε_1, …, ε_n` of `H` whose presented group has finite abelianisation.  Lifting the
`ε_j` to `VertexGroup v` and applying `exists_datum_of_lift_eq_one` produces a datum `D` with
`D.γ = γ` and `D.W = W`; `datum_vanishes` then gives `γ_j ∈ N`, i.e. `ε_j = 1` for every `j`.
Hence `H = ⟨ε_1, …, ε_n⟩ = ⊥`, contradicting `H ≠ ⊥`. -/
theorem locallyIndicable_vertexGroup
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
    (P : Work.ORLocInd.Howie.Presentation V) (hsep : P.CodeSeparates) (v : V) :
    Work.ORLocInd.Group.LocallyIndicable (P.vertexGroup v) := by
  intro H hFG hne
  by_cases hind : ∃ f : H →* Multiplicative ℤ, Function.Surjective f
  · exact hind
  · -- `H` is finitely generated and not indicable; it will turn out to be trivial.
    exfalso
    have hfg : Group.FG H := (Group.fg_iff_subgroup_fg H).2 hFG
    -- No quotient of `Abelianization H` can surject onto `ℤ`, else `H` would be indicable.
    have hab : ∀ g : Abelianization H →* Multiplicative ℤ, ¬ Function.Surjective g := by
      intro g hg
      have hg' : Function.Surjective (g.comp Abelianization.of) :=
        hg.comp (abelianization_of_surjective H)
      exact hind ⟨g.comp Abelianization.of, hg'⟩
    have hfin : Finite (Abelianization H) := by
      have hfgA : Group.FG (Abelianization H) :=
        Group.fg_of_surjective (f := Abelianization.of) (hG := hfg) (abelianization_of_surjective H)
      exact finite_of_fg_of_no_surjective_int hfgA hab
    -- A finite enumerating tuple of generators of `H`.
    have htop : (⊤ : Subgroup H).FG := Group.fg_def.mp hfg
    obtain ⟨S, hS⟩ := Group.isMulFG_iff.mp hfg
    let n : ℕ := S.card
    let ee : ↥S ≃ Fin n := Finset.equivFin S
    let ε : Fin n → H := fun j => (ee.symm j : H)
    have hrange : Set.range ε = (↑S : Set H) := by
      ext x
      constructor
      · rintro ⟨j, rfl⟩
        exact (ee.symm j).2
      · intro hx
        refine ⟨ee ⟨x, hx⟩, ?_⟩
        show ((ee.symm (ee ⟨x, hx⟩) : ↥S) : H) = x
        rw [Equiv.symm_apply_apply]
    have hgen : Subgroup.closure (Set.range ε) = ⊤ := by rw [hrange]; exact hS
    -- Relations of `H` with finite abelianisation.
    obtain ⟨W, hWrel, hWfin⟩ := exists_relation_words ε hgen hfin
    -- Lift the generators to `VertexGroup v`.
    have hsurj : Function.Surjective (P.toVertexGroup v) :=
      QuotientGroup.mk'_surjective (P.relatorNormalClosure v)
    let γ : Fin n → VertexGroup v := fun j => Classical.choose (hsurj (ε j : P.vertexGroup v))
    have hγ : ∀ j, P.toVertexGroup v (γ j) = (ε j : P.vertexGroup v) :=
      fun j => Classical.choose_spec (hsurj (ε j : P.vertexGroup v))
    -- The relations `W_j` hold in the free groupoid's vertex group after projection.
    have hlift : ∀ j, FreeGroup.lift (fun i => P.toVertexGroup v (γ i)) (W j) = 1 := by
      intro j
      have h1 : (fun i => P.toVertexGroup v (γ i)) = (fun i => ((ε i : H) : P.vertexGroup v)) :=
        funext (fun i => hγ i)
      rw [h1]
      have h2 : FreeGroup.lift (fun i => ((ε i : H) : P.vertexGroup v)) (W j)
          = (Subgroup.subtype H) (FreeGroup.lift ε (W j)) := by
        refine (FreeGroup.lift_unique (f := fun i => ((ε i : H) : P.vertexGroup v))
          ((Subgroup.subtype H).comp (FreeGroup.lift ε)) ?_ (x := W j)).symm
        intro i
        simp only [MonoidHom.comp_apply, FreeGroup.lift_apply_of, Subgroup.coe_subtype]
      rw [h2, hWrel j, map_one]
    -- The datum whose generators are `γ` and whose words are `W`.
    obtain ⟨D, hDγ, hDW⟩ := exists_datum_of_lift_eq_one γ W hlift
    have hvan : ∀ j, D.γ j ∈ P.relatorNormalClosure v :=
      datum_vanishes hcase1 hcase2 P hsep v D (by rw [hDW]; exact hWfin)
    -- So every generator of `H` is trivial.
    have hε1 : ∀ j, ε j = 1 := by
      intro j
      have h1 : P.toVertexGroup v (D.γ j) = 1 := by
        rw [Work.ORLocInd.Howie.Presentation.toVertexGroup_apply]
        exact (QuotientGroup.eq_one_iff (D.γ j)).mpr (hvan j)
      have h1' : P.toVertexGroup v (γ j) = 1 := by rw [← hDγ]; exact h1
      apply Subtype.ext
      rw [Subgroup.coe_one, ← hγ j]
      exact h1'
    have hclos : Subgroup.closure (Set.range ε) ≤ (⊥ : Subgroup H) := by
      rw [Subgroup.closure_le]
      rintro y ⟨j, rfl⟩
      exact Subgroup.mem_bot.mpr (hε1 j)
    have hle : H ≤ ⊥ := by
      intro x hx
      rw [Subgroup.mem_bot]
      have hmem : (⟨x, hx⟩ : H) ∈ Subgroup.closure (Set.range ε) := by
        rw [hgen]; exact Subgroup.mem_top _
      have h1 : (⟨x, hx⟩ : H) = 1 := by
        have := hclos hmem
        rwa [Subgroup.mem_bot] at this
      have h2 : (x : P.vertexGroup v) = ((1 : H) : P.vertexGroup v) := congrArg Subtype.val h1
      simpa using h2
    exact absurd (le_antisymm hle bot_le) hne

end Work.ORLocInd.Howie
