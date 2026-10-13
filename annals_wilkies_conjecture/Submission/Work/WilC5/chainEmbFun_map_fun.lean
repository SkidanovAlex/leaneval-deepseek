/-
  WilC5 — the glued map of a chain is a homomorphism for function symbols.

  With `ExtPair.chainDom c` the union of the domains of a chain `c` and `ExtPair.chainEmbFun hc hne`
  the embedding glued from the members of the chain (`ExtChainUnion.lean`), we show that the glued
  map commutes with the interpretation of every function symbol of `L`.

  The argument is the standard one for a union of a directed family of embeddings:

  * by `ExtPair.chain_common_upper` finitely many points of the union — here the entries of `v` —
    already lie in the domain `p.dom` of a single member `p ∈ c`;
  * `p.dom` is closed under `f`, so `funMap f v` also lies in `p.dom`, and on `p.dom` the glued map
    is computed by `p.emb` (`ExtPair.chainEmbFun_eq`) — indeed on **every** member of the chain,
    by compatibility of the chain;
  * `p.emb` is itself a homomorphism, so it commutes with `f`, and both sides are identified.

  The only point of care is that `funMap f` computed in the substructure `p.dom` and the same
  symbol computed in `chainDom c` (then restricted to `p.dom`) are the same element of `p.dom`,
  which is the (definitional) computation rule for the inherited structure on a substructure.
-/
import Mathlib
import Submission.Work.WilC5.ExtChainUnion
import Submission.Work.WilC5.ExtChain

namespace Work.WilC5

theorem chainEmbFun_map_fun {L : FirstOrder.Language.{0, 0}} {T : L.Theory}
    {M N : Type} [L.Structure M] [L.Structure N] {A₀ : L.Substructure M}
    {σ₀ : L.Embedding A₀ N} {c : Set (Work.WilC5.ExtPair T A₀ σ₀)}
    (hc : IsChain (· ≤ ·) c) (hne : c.Nonempty) {n : ℕ} (f : L.Functions n)
    (v : Fin n → Work.WilC5.ExtPair.chainDom c) :
    Work.WilC5.ExtPair.chainEmbFun hc hne (FirstOrder.Language.Structure.funMap f v) =
      FirstOrder.Language.Structure.funMap f (Work.WilC5.ExtPair.chainEmbFun hc hne ∘ v) := by
  -- A single member of the chain whose domain contains all the entries of `v`.
  obtain ⟨p, hp, hv⟩ := Work.WilC5.ExtPair.chain_common_upper hc hne v
  -- `p.dom` is closed under `f`, so `funMap f v` lies in it as well.
  have hmem : ((FirstOrder.Language.Structure.funMap f v : Work.WilC5.ExtPair.chainDom c) : M)
      ∈ p.dom := p.dom.fun_mem f (fun i => (v i : M)) hv
  -- Evaluating `f` in the substructure `p.dom` and in the ambient structure `M` agree.
  have harg : (⟨((FirstOrder.Language.Structure.funMap f v :
        Work.WilC5.ExtPair.chainDom c) : M), hmem⟩ : p.dom)
      = FirstOrder.Language.Structure.funMap f (fun i => (⟨(v i : M), hv i⟩ : p.dom)) :=
    Subtype.ext rfl
  -- On the union, the glued map is computed by `p.emb` (and by every member of the chain).
  have hcomp : (Work.WilC5.ExtPair.chainEmbFun hc hne ∘ v)
      = fun i => p.emb (⟨(v i : M), hv i⟩ : p.dom) := by
    funext i
    exact Work.WilC5.ExtPair.chainEmbFun_eq hc hne hp (v i) (hv i)
  rw [Work.WilC5.ExtPair.chainEmbFun_eq hc hne hp
    (FirstOrder.Language.Structure.funMap f v) hmem, harg, hcomp,
    FirstOrder.Language.Embedding.map_fun p.emb f (fun i => (⟨(v i : M), hv i⟩ : p.dom))]
  rfl

end Work.WilC5
