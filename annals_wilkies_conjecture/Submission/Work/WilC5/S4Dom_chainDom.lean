import Mathlib
import Submission.Work.WilC5.S4Setup
import Submission.Work.WilC5.ExtPair_chain_upper
import Submission.Work.WilC5.dcl_iUnion_chain
import Submission.Work.WilC5.finite_subset_iUnion_monotone

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Work.WilC5

/-!
  Auxiliary lemmas for `Work.WilC5.S4Dom_chainDom`: the union `ExtPair.chainDom c` of the domains
  of a chain of partial extensions is `Dcl`-closed (resp. log-closed) as soon as every member is.

  Both closures are *finitary*: a point of `Dcl A` is definable from finitely many parameters of
  `A` (`Work.WilC5.dcl_finite_params`), and if `A` is the union of the domains of a chain then
  finitely many of its elements lie in the domain of a single member (`ExtPair.chain_common_upper`,
  or `chainDom_exists_dom_of_finite` below for an arbitrary finite set of parameters).
-/

section Aux

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture FirstOrder Language
open scoped FirstOrder

/-- **Finitely many points of the union of the domains of a chain lie in a single domain.**  If
`S` is a finite set contained in `ExtPair.chainDom c`, then it is contained in the domain of one
member of the chain; this is the directedness of the family of domains. -/
theorem chainDom_exists_dom_of_finite {L : FirstOrder.Language.{0, 0}} {T : L.Theory}
    {M N : Type} [L.Structure M] [L.Structure N]
    {A₀ : L.Substructure M} {σ₀ : L.Embedding A₀ N}
    {c : Set (ExtPair T A₀ σ₀)} (hc : IsChain (· ≤ ·) c) (hne : c.Nonempty)
    {S : Set M} (hSfin : S.Finite) (hS : S ⊆ (ExtPair.chainDom c : Set M)) :
    ∃ p ∈ c, S ⊆ (p.dom : Set M) := by
  classical
  -- choose, for each `t ∈ S`, a member of the chain whose domain contains `t`
  let g : S → {p // p ∈ c} := fun t =>
    ⟨Classical.choose ((ExtPair.chainDom_mem hc hne).1 (hS t.2)),
      (Classical.choose_spec ((ExtPair.chainDom_mem hc hne).1 (hS t.2))).1⟩
  have hg : ∀ t : S, (t : M) ∈ (g t).1.dom := fun t =>
    (Classical.choose_spec ((ExtPair.chainDom_mem hc hne).1 (hS t.2))).2
  haveI : Nonempty {p // p ∈ c} := hne.to_subtype
  haveI : Finite S := hSfin.to_subtype
  -- the finite family of chosen domains has an upper bound in the directed family
  obtain ⟨z, hz⟩ := (ExtPair.chain_directed_dom hc).finite_le g
  exact ⟨z.1, z.2, fun t ht => hz ⟨t, ht⟩ (hg ⟨t, ht⟩)⟩

end Aux

theorem S4Dom_chainDom {M N : Type} [WilkiesDesign.CG.LEc.Structure M] [WilkiesDesign.CG.LEc.Structure N]
    {A₀ : WilkiesDesign.CG.LRc.Substructure M}
    {σ₀ : @FirstOrder.Language.Embedding WilkiesDesign.CG.LRc ↥A₀ N _ (Work.WilC5.reductStruct N)}
    {c : Set (Work.WilC5.ExtPair Work.WilC5.emptyTheory A₀ σ₀)}
    (hc : IsChain (· ≤ ·) c) (hne : c.Nonempty)
    (h : ∀ p ∈ c, Work.WilC5.S4Dom p.dom) :
    Work.WilC5.S4Dom (Work.WilC5.ExtPair.chainDom c) := by
  refine ⟨?_, ?_⟩
  · -- `Dcl`-closure: `Dcl` is finitary, and finitely many points of the union lie in one domain
    intro x hx
    obtain ⟨S, hSfin, hS, hxS⟩ := dcl_finite_params hx
    obtain ⟨p, hp, hSp⟩ := chainDom_exists_dom_of_finite hc hne hSfin hS
    exact (ExtPair.chainDom_mem hc hne).2
      ⟨p, hp, (h p hp).dcl_closed (Work.WilC2.dcl_mono hSp hxS)⟩
  · -- log-closure: `logFun x` lies in the domain of any member containing `x`
    intro x hx
    obtain ⟨p, hp, hxp⟩ := (ExtPair.chainDom_mem hc hne).1 hx
    exact (ExtPair.chainDom_mem hc hne).2 ⟨p, hp, (h p hp).log_closed x hxp⟩

end Work.WilC5
