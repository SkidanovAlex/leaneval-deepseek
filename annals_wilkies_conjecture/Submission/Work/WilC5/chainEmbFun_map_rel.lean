import Mathlib
import Submission.Work.WilC5.ExtChainUnion
import Submission.Work.WilC5.ExtChain

namespace Work.WilC5

theorem chainEmbFun_map_rel {L : FirstOrder.Language.{0, 0}} {T : L.Theory}
    {M N : Type} [L.Structure M] [L.Structure N] {A₀ : L.Substructure M}
    {σ₀ : L.Embedding A₀ N} {c : Set (Work.WilC5.ExtPair T A₀ σ₀)}
    (hc : IsChain (· ≤ ·) c) (hne : c.Nonempty) {n : ℕ} (r : L.Relations n)
    (v : Fin n → Work.WilC5.ExtPair.chainDom c) :
    FirstOrder.Language.Structure.RelMap r (Work.WilC5.ExtPair.chainEmbFun hc hne ∘ v) ↔
      FirstOrder.Language.Structure.RelMap r v := by
  classical
  -- All the points `v i` lie in the domain of a single member of the chain.
  obtain ⟨p, hp, hv⟩ := ExtPair.chain_common_upper hc hne v
  -- Regard them as elements of `p.dom`.
  set w : Fin n → p.dom := fun i => ⟨(v i : M), hv i⟩ with hw
  -- The glued map agrees with `p.emb` on these points.
  have hfun : (ExtPair.chainEmbFun hc hne ∘ v) = (p.emb ∘ w) := by
    funext i
    exact ExtPair.chainEmbFun_eq hc hne hp (v i) (hv i)
  rw [hfun, FirstOrder.Language.Embedding.map_rel]
  -- `Structure.RelMap` on a substructure is the ambient relation on the underlying points, and
  -- `w` has the same underlying points as `v`.
  exact Iff.rfl

end Work.WilC5
