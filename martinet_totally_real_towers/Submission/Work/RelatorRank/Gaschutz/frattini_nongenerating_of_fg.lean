import Mathlib

/-!
# Gaschütz: the Frattini subgroup is non-generating for finitely generated groups

**Namespace** `Work.RelatorRank.Gaschutz`; module
`Submission.Work.RelatorRank.Gaschutz.frattini_nongenerating_of_fg`.

The *Frattini subgroup* `frattini G` of a group is the intersection of its maximal
subgroups (`Order.radical` of the subgroup lattice, see `Mathlib.GroupTheory.Frattini`).
Mathlib's `frattini_nongenerating` proves the classical non-generator property

  `K ⊔ frattini G = ⊤ → K = ⊤`

under the hypothesis `[IsCoatomic (Subgroup G)]`, i.e. that every proper subgroup of `G`
is contained in a maximal subgroup.  That hypothesis holds in particular for **finitely
generated** groups: the proof is the Zorn argument on the set of proper subgroups
containing a given proper subgroup, whose upper bounds exist because a strictly
increasing union of subgroups of a finitely generated group is again a proper subgroup.

The mathematical content of this file is therefore the reduction of coatomicity of the
subgroup lattice to finite generation, which we phrase in the equivalent compact form:
`⊤ : Subgroup G` is a *compact* element of the subgroup lattice whenever `G` is finitely
generated.  Concretely, if `s` is a directed family of subgroups of a finitely generated
group `G` with `sSup s = ⊤`, then some member of `s` already equals `⊤`: a finite
generating set has all of its elements in the (directed) union of `s`, hence in a single
member of `s`.

Mathlib supplies the two bridges used here:
* `CompleteLattice.coatomic_of_top_compact`, that a complete lattice whose top element is
  compact is coatomic;
* `Subgroup.mem_sSup_of_directedOn`, that an element of the supremum of a directed family
  of subgroups already lies in one of them.
-/

set_option linter.style.haveILetI false

namespace Work.RelatorRank.Gaschutz

/-- **The subgroup lattice of a finitely generated group has compact top.**  If `G` is
finitely generated and `s` is a directed family of subgroups with `sSup s = ⊤`, then some
member of `s` is already everything. -/
theorem isCompactElement_top_of_fg {G : Type*} [Group G] (hG : Group.FG G) :
    IsCompactElement (⊤ : Subgroup G) := by
  classical
  rw [isCompactElement_iff_le_of_directed_sSup_le]
  intro s hsne hdir hle
  obtain ⟨T, hT⟩ := hG.out
  -- A finite set of elements, each of which lies in some member of the directed family `s`,
  -- is contained in a single member of `s`.
  have key : ∀ t : Finset G, (∀ x ∈ t, ∃ K ∈ s, x ∈ K) → ∃ K ∈ s, ∀ x ∈ t, x ∈ K := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
        intro _
        obtain ⟨K, hKs⟩ := hsne
        exact ⟨K, hKs, by simp⟩
    | insert a u hau ihu =>
        intro ht
        obtain ⟨Ka, hKa, haK⟩ := ht a (Finset.mem_insert_self a u)
        obtain ⟨Ku, hKu, huK⟩ := ihu (fun x hx => ht x (Finset.mem_insert_of_mem hx))
        obtain ⟨K, hKs, h1, h2⟩ := hdir Ka hKa Ku hKu
        exact ⟨K, hKs, fun x hx => by
          rcases Finset.mem_insert.mp hx with h | h
          · subst h; exact h1 haK
          · exact h2 (huK x h)⟩
  -- Each element of the finite generating set `T` lies in some member of `s`.
  have hgen : ∀ x ∈ T, ∃ K ∈ s, x ∈ K := by
    intro x hx
    have hxg : x ∈ (⊤ : Subgroup G) := by
      rw [← hT]; exact Subgroup.subset_closure (by simpa using hx)
    exact (Subgroup.mem_sSup_of_directedOn hsne hdir).mp (hle hxg)
  obtain ⟨K, hKs, hKT⟩ := key T hgen
  exact ⟨K, hKs, le_trans (le_of_eq hT.symm) ((Subgroup.closure_le K).mpr hKT)⟩

/-- **Coatomicity of the subgroup lattice of a finitely generated group.**  Every proper
subgroup of a finitely generated group is contained in a maximal subgroup. -/
theorem isCoatomic_subgroup_of_fg {G : Type*} [Group G] (hG : Group.FG G) :
    IsCoatomic (Subgroup G) :=
  CompleteLattice.coatomic_of_top_compact (isCompactElement_top_of_fg hG)

/-- **Gaschütz's non-generator property for finitely generated groups.**  If a subgroup `H`
of a finitely generated group `G` together with the Frattini subgroup generates `G`, then
`H` is already all of `G`. -/
theorem frattini_nongenerating_of_fg {G : Type*} [Group G] (hG : Group.FG G) (H : Subgroup G)
    (h : H ⊔ frattini G = ⊤) : H = ⊤ := by
  haveI : IsCoatomic (Subgroup G) := isCoatomic_subgroup_of_fg hG
  exact frattini_nongenerating h

end Work.RelatorRank.Gaschutz
