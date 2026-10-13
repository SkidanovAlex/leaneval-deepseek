/-
  WilC5 — the chain step of the Zorn argument for the extension property.

  Given a chain `c` of partial extensions `(A, σ)` of `σ₀ : A₀ → N` and the hypothesis that every
  substructure of `M` models `T`, the union `ExtPair.chainDom c` of the domains is a substructure
  of `M` (hence models `T`), and the embeddings of the members of the chain glue to an embedding
  `ExtPair.chainEmbedding hc hne : chainDom c ↪[L] N` extending all of them.  This yields the
  upper bound `ExtPair_chain_upper` needed for Zorn's lemma.

  The gluing lemmas (`chainEmbFun_injective`, `chainEmbFun_map_fun`, `chainEmbFun_map_rel`) are
  proved in the neighbouring modules `WilC5/chainEmbFun_*`.
-/
import Mathlib
import Submission.Work.WilC5.ExtChain
import Submission.Work.WilC5.ExtChainUnion
import Submission.Work.WilC5.chainEmbFun_injective
import Submission.Work.WilC5.chainEmbFun_map_fun
import Submission.Work.WilC5.chainEmbFun_map_rel

namespace Work.WilC5

namespace ExtPair

open FirstOrder Language

variable {L : FirstOrder.Language.{0, 0}} {T : L.Theory}
variable {M N : Type} [L.Structure M] [L.Structure N]
variable {A₀ : L.Substructure M} {σ₀ : L.Embedding A₀ N}

/-- **The glued embedding of the union of a chain.**  The embeddings of the members of a chain of
partial extensions agree on overlaps, so they define a single embedding of the union of their
domains into `N`. -/
noncomputable def chainEmbedding {c : Set (ExtPair T A₀ σ₀)} (hc : IsChain (· ≤ ·) c)
    (hne : c.Nonempty) : L.Embedding (chainDom c) N where
  toEmbedding := ⟨chainEmbFun hc hne, chainEmbFun_injective hc hne⟩
  map_fun' := fun {_} f v => chainEmbFun_map_fun hc hne f v
  map_rel' := fun {_} r v => chainEmbFun_map_rel hc hne r v

end ExtPair

theorem ExtPair_chain_upper {L : FirstOrder.Language.{0, 0}} {T : L.Theory}
    {M N : Type} [L.Structure M] [L.Structure N] {A₀ : L.Substructure M}
    {σ₀ : L.Embedding A₀ N} (hmod : ∀ A : L.Substructure M, (A : Type) ⊨ T)
    {c : Set (Work.WilC5.ExtPair T A₀ σ₀)} (hc : IsChain (· ≤ ·) c) (hne : c.Nonempty) :
    ∃ ub : Work.WilC5.ExtPair T A₀ σ₀, ∀ a ∈ c, a ≤ ub := by
  classical
  have hne0 : c.Nonempty := hne
  obtain ⟨p₀, hp₀⟩ := hne0
  have hA₀ : A₀ ≤ ExtPair.chainDom c := p₀.le_dom.trans (ExtPair.dom_le_chainDom hp₀)
  refine ⟨{ dom := ExtPair.chainDom c
            emb := ExtPair.chainEmbedding hc hne
            le_dom := hA₀
            agrees := ?_
            models := ?_ }, ?_⟩
  · intro a
    have hne1 : c.Nonempty := hne
    obtain ⟨p, hp⟩ := hne1
    have ha : (a : M) ∈ p.dom := p.le_dom a.2
    change ExtPair.chainEmbFun hc hne ⟨(a : M), hA₀ a.2⟩ = σ₀ a
    rw [ExtPair.chainEmbFun_eq hc hne hp ⟨(a : M), hA₀ a.2⟩ ha]
    exact (congrArg p.emb (Subtype.ext rfl)).trans (p.agrees a)
  · exact hmod _
  · intro a ha
    refine ⟨ExtPair.dom_le_chainDom ha, ?_⟩
    intro x
    change ExtPair.chainEmbFun hc hne ⟨(x : M), ExtPair.dom_le_chainDom ha x.2⟩ = a.emb x
    exact ExtPair.chainEmbFun_eq hc hne ha ⟨(x : M), ExtPair.dom_le_chainDom ha x.2⟩ x.2

end Work.WilC5
