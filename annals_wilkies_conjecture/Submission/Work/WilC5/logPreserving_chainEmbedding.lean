import Mathlib
import Submission.Work.WilC5.S4Setup

namespace Work.WilC5

theorem logPreserving_chainEmbedding {M N : Type} [WilkiesDesign.CG.LEc.Structure M] [WilkiesDesign.CG.LEc.Structure N]
    {A₀ : WilkiesDesign.CG.LRc.Substructure M}
    {σ₀ : @FirstOrder.Language.Embedding WilkiesDesign.CG.LRc ↥A₀ N _ (Work.WilC5.reductStruct N)}
    {c : Set (Work.WilC5.ExtPair Work.WilC5.emptyTheory A₀ σ₀)}
    (hc : IsChain (· ≤ ·) c) (hne : c.Nonempty)
    (hmem : ∀ p ∈ c, Work.WilC5.LogClosed (p.dom : Set M))
    (hpres : ∀ (p : Work.WilC5.ExtPair Work.WilC5.emptyTheory A₀ σ₀) (hp : p ∈ c),
      Work.WilC5.LogPreserving p.dom (hmem p hp) p.emb)
    (hlog : Work.WilC5.LogClosed (Work.WilC5.ExtPair.chainDom c : Set M)) :
    Work.WilC5.LogPreserving (Work.WilC5.ExtPair.chainDom c) hlog
      (Work.WilC5.ExtPair.chainEmbedding hc hne) := by
  intro x
  obtain ⟨p, hp, hxp⟩ := (ExtPair.chainDom_mem hc hne).1 x.2
  show ExtPair.chainEmbFun hc hne ⟨logFun (x : M), hlog (x : M) x.2⟩
      = logFun (ExtPair.chainEmbFun hc hne x)
  rw [ExtPair.chainEmbFun_eq hc hne hp _ (hmem p hp (x : M) hxp),
      ExtPair.chainEmbFun_eq hc hne hp x hxp]
  exact hpres p hp ⟨(x : M), hxp⟩

end Work.WilC5
