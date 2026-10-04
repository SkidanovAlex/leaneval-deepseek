import Mathlib.Topology.UniformSpace.HeineCantor

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.Topology.UniformSpace

theorem tendstoUniformlyOn_comp_of_isCompact
    {α : Type*} [TopologicalSpace α]
    {β : Type*} [UniformSpace β] {γ : Type*} [UniformSpace γ]
    {ι : Type*} {l : Filter ι} {s : Set α} {F : ι → α → β} {f : α → β} {g : β → γ} {K : Set β}
    (hK : IsCompact K) (hg : ContinuousOn g K)
    (hF : TendstoUniformlyOn F f l s)
    (hfK : Set.MapsTo f s K) (hFK : ∀ᶠ n in l, Set.MapsTo (F n) s K) :
    TendstoUniformlyOn (fun n => g ∘ F n) (g ∘ f) l s := by
  exact UniformContinuousOn.comp_tendstoUniformlyOn_eventually hFK hfK
    (hK.uniformContinuousOn_of_continuous hg) hF

end Commons.Topology.UniformSpace