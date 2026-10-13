/-
  WilC5 — the union step for the Zorn argument.

  Given a chain `c` of partial extensions `(A, σ)` of `σ₀ : A₀ → N` (where `M ⊨ T` and every
  substructure of `M` models `T`), the domains of the members of `c` form a directed family of
  substructures of `M`.  Their union `ExtPair.chainDom c` is again a substructure of `M`, and the
  embeddings `σ` glue — compatibly, because any two members of a chain agree on the intersection
  of their domains — to a well defined function `ExtPair.chainEmbFun` from the union to `N`.

  The lemmas here are the shared vocabulary of the chain-upper-bound step:

  * `ExtPair.exists_upper_of_chain` — any two members of a chain have a common upper bound;
  * `ExtPair.chain_directed_dom` — the family of domains is directed;
  * `ExtPair.chainDom`, `ExtPair.chainDom_mem` — the union and its membership criterion;
  * `ExtPair.chainEmbFun`, `ExtPair.chainEmbFun_eq` — the glued function and its description;
  * `ExtPair.chain_common_upper` — finitely many elements of the union lie in one member;
  * `ExtPair.dom_le_chainDom` — each domain is contained in the union.
-/
import Mathlib
import Submission.Work.WilC5.ExtChain

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilC5

open FirstOrder Language

namespace ExtPair

variable {L : FirstOrder.Language.{0, 0}} {T : L.Theory}
variable {M N : Type} [L.Structure M] [L.Structure N]
variable {A₀ : L.Substructure M} {σ₀ : L.Embedding A₀ N}

/-- Any two members of a chain of partial extensions have a common upper bound in the chain. -/
theorem exists_upper_of_chain {c : Set (ExtPair T A₀ σ₀)} (hc : IsChain (· ≤ ·) c)
    {p q : ExtPair T A₀ σ₀} (hp : p ∈ c) (hq : q ∈ c) : ∃ z ∈ c, p ≤ z ∧ q ≤ z := by
  rcases eq_or_ne p q with h | h
  · exact ⟨p, hp, le_rfl, le_of_eq h.symm⟩
  · rcases hc hp hq h with hpq | hqp
    · exact ⟨q, hq, hpq, le_rfl⟩
    · exact ⟨p, hp, le_rfl, hqp⟩

/-- The domains of the members of a chain, as a directed family. -/
theorem chain_directed_dom {c : Set (ExtPair T A₀ σ₀)} (hc : IsChain (· ≤ ·) c) :
    Directed (· ≤ ·) fun p : {p // p ∈ c} => (p : ExtPair T A₀ σ₀).dom := by
  intro p q
  obtain ⟨z, hpz, hqz⟩ := hc.directedOn.directed_val p q
  exact ⟨z, le_dom_of_le hpz, le_dom_of_le hqz⟩

/-- **The union of the domains of a chain of partial extensions.** -/
def chainDom (c : Set (ExtPair T A₀ σ₀)) : L.Substructure M :=
  sSup ((fun p : ExtPair T A₀ σ₀ => p.dom) '' c)

/-- An element lies in the union of the domains of a chain iff it lies in the domain of one of the
members of the chain. -/
theorem chainDom_mem {c : Set (ExtPair T A₀ σ₀)} (hc : IsChain (· ≤ ·) c) (hne : c.Nonempty)
    {x : M} : x ∈ chainDom c ↔ ∃ p ∈ c, x ∈ p.dom := by
  have hne' : ((fun p : ExtPair T A₀ σ₀ => p.dom) '' c).Nonempty := hne.image _
  have hdir : DirectedOn (· ≤ ·) ((fun p : ExtPair T A₀ σ₀ => p.dom) '' c) := by
    rintro s ⟨p, hp, rfl⟩ t ⟨q, hq, rfl⟩
    obtain ⟨z, hz, hpz, hqz⟩ := exists_upper_of_chain hc hp hq
    exact ⟨z.dom, ⟨z, hz, rfl⟩, le_dom_of_le hpz, le_dom_of_le hqz⟩
  refine (Substructure.mem_sSup_of_directedOn hne' hdir).trans ?_
  constructor
  · rintro ⟨s, ⟨p, hp, rfl⟩, hx⟩
    exact ⟨p, hp, hx⟩
  · rintro ⟨p, hp, hx⟩
    refine ⟨p.dom, ?_, hx⟩
    exact ⟨p, hp, rfl⟩

/-- Each member of the chain has its domain contained in the union. -/
theorem dom_le_chainDom {c : Set (ExtPair T A₀ σ₀)} {p : ExtPair T A₀ σ₀} (hp : p ∈ c) :
    p.dom ≤ chainDom c := by
  rw [chainDom]
  exact le_sSup (Set.mem_image_of_mem (fun p : ExtPair T A₀ σ₀ => p.dom) hp)

/-- **The glued map.**  On the union of the domains of a chain, the embeddings of the members of
the chain agree on overlaps, so they define a single function into `N`. -/
noncomputable def chainEmbFun {c : Set (ExtPair T A₀ σ₀)} (hc : IsChain (· ≤ ·) c)
    (hne : c.Nonempty) (x : chainDom c) : N :=
  (Classical.choose ((chainDom_mem hc hne).1 x.2)).emb
    ⟨(x : M), (Classical.choose_spec ((chainDom_mem hc hne).1 x.2)).2⟩

/-- The glued map is computed by any member of the chain whose domain contains the point. -/
theorem chainEmbFun_eq {c : Set (ExtPair T A₀ σ₀)} (hc : IsChain (· ≤ ·) c) (hne : c.Nonempty)
    {p : ExtPair T A₀ σ₀} (hp : p ∈ c) (x : chainDom c) (hx : (x : M) ∈ p.dom) :
    chainEmbFun hc hne x = p.emb ⟨(x : M), hx⟩ := by
  set h := (chainDom_mem hc hne).1 x.2 with hh
  have hspec : (Classical.choose h) ∈ c ∧ (x : M) ∈ (Classical.choose h).dom :=
    Classical.choose_spec h
  change (Classical.choose h).emb ⟨(x : M), hspec.2⟩ = p.emb ⟨(x : M), hx⟩
  exact compat_of_chain hc hspec.1 hp hspec.2 hx

/-- Finitely many elements of the union lie in the domain of a single member of the chain. -/
theorem chain_common_upper {c : Set (ExtPair T A₀ σ₀)} (hc : IsChain (· ≤ ·) c) (hne : c.Nonempty)
    {n : ℕ} (v : Fin n → chainDom c) : ∃ p ∈ c, ∀ i, (v i : M) ∈ p.dom := by
  have hne' : Nonempty {p // p ∈ c} := hne.to_subtype
  let g : Fin n → {p // p ∈ c} := fun i =>
    ⟨Classical.choose ((chainDom_mem hc hne).1 (v i).2),
      (Classical.choose_spec ((chainDom_mem hc hne).1 (v i).2)).1⟩
  have hg : ∀ i, (v i : M) ∈ (g i).1.dom := fun i =>
    (Classical.choose_spec ((chainDom_mem hc hne).1 (v i).2)).2
  obtain ⟨z, hz⟩ := (chain_directed_dom hc).finite_le g
  exact ⟨z.1, z.2, fun i => hz i (hg i)⟩

end ExtPair

end Work.WilC5
