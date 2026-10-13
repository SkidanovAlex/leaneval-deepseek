import Mathlib
import Submission.Work.WilC5.ExtChainUnion
import Submission.Work.WilC5.ExtChain

namespace Work.WilC5

theorem chainEmbFun_injective {L : FirstOrder.Language.{0, 0}} {T : L.Theory}
    {M N : Type} [L.Structure M] [L.Structure N] {A₀ : L.Substructure M}
    {σ₀ : L.Embedding A₀ N} {c : Set (Work.WilC5.ExtPair T A₀ σ₀)}
    (hc : IsChain (· ≤ ·) c) (hne : c.Nonempty) :
    Function.Injective (Work.WilC5.ExtPair.chainEmbFun (T := T) (A₀ := A₀) (σ₀ := σ₀) hc hne) := by
  intro x y hxy
  -- two points of the union lie in the domains of two members of the chain ...
  obtain ⟨px, hpx, hxx⟩ := (ExtPair.chainDom_mem hc hne).1 x.2
  obtain ⟨py, hpy, hyy⟩ := (ExtPair.chainDom_mem hc hne).1 y.2
  -- ... and, the chain being directed, in the domain of a common member.
  obtain ⟨z, hz, hxz, hyz⟩ := ExtPair.exists_upper_of_chain hc hpx hpy
  have hx : (x : M) ∈ z.dom := ExtPair.le_dom_of_le hxz hxx
  have hy : (y : M) ∈ z.dom := ExtPair.le_dom_of_le hyz hyy
  -- on that member the glued map is its embedding, which is injective.
  rw [ExtPair.chainEmbFun_eq hc hne hz x hx, ExtPair.chainEmbFun_eq hc hne hz y hy] at hxy
  have h2 : (⟨(x : M), hx⟩ : z.dom) = ⟨(y : M), hy⟩ := z.emb.injective hxy
  have h3 : (x : M) = (y : M) := congrArg (fun t : z.dom => (t : M)) h2
  exact Subtype.ext h3

end Work.WilC5
