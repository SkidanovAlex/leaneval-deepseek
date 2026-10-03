import Mathlib
import Submission.Work.PlanarSC.Tools
import Submission.Work.PlanarSC.exists_periodic_not_hasArg_of_component
import Submission.Lib.Unif2.Work.Mori.hasArg_comp_of_holomorphic_of_subsingleton
import Submission.Lib.Unif2.Work.Mori.holomorphicOnX_opens_sub_const
import Submission.Lib.Unif2.Work.SimplyConnected.Basic

namespace Work.PlanarSC

open Set

noncomputable section

/-- **A simply connected plane domain has no bounded complementary component.**

Let `Ω ⊆ ℂ` be open, connected and simply connected, and `z ∉ Ω`.  Then the connected component of
`z` in `Ωᶜ` is unbounded.

The proof is by contradiction.  If `K := connectedComponentIn Ωᶜ z` were bounded it would be a
compact connected component of the closed set `Ωᶜ`; the (delegated) plane-topological input
`Work.PlanarSC.exists_periodic_not_hasArg_of_component` then produces a `1`-periodic loop
`f : ℝ → ℂ` with values in `Ω` whose argument around `z` is not periodic, i.e. which winds
non-trivially around `z`.  On the other hand, on a simply connected surface every homomorphism
`π₁ →+ ℝ` vanishes, so every non-vanishing holomorphic function has a global holomorphic logarithm
(`Work.Mori.hasArg_comp_of_holomorphic_of_subsingleton`); applied to `w ↦ w - z` (which is
non-vanishing on `Ω`, since `z ∉ Ω`) this forces the argument of `f - z` to be periodic —
contradiction. -/
theorem no_bounded_component_of_simplyConnected {Ω : Set ℂ} (hΩo : IsOpen Ω) (hΩc : IsConnected Ω)
    (hsc : SimplyConnectedSpace Ω) {z : ℂ} (hz : z ∉ Ω) :
    ¬ Bornology.IsBounded (connectedComponentIn (Ωᶜ) z) := by
  intro hbdd
  have hzK : z ∈ connectedComponentIn (Ωᶜ) z := mem_connectedComponentIn (by simpa using hz)
  -- `K` is closed: its closure is preconnected inside `Ωᶜ`, hence inside the component.
  have hclsub : closure (connectedComponentIn (Ωᶜ) z) ⊆ connectedComponentIn (Ωᶜ) z :=
    (isPreconnected_connectedComponentIn.closure).subset_connectedComponentIn
      (subset_closure hzK)
      (closure_minimal (connectedComponentIn_subset Ωᶜ z) hΩo.isClosed_compl)
  have hKclosed : IsClosed (connectedComponentIn (Ωᶜ) z) := isClosed_of_closure_subset hclsub
  have hKcpt : IsCompact (connectedComponentIn (Ωᶜ) z) :=
    Metric.isCompact_iff_isClosed_bounded.mpr ⟨hKclosed, hbdd⟩
  have hKconn : IsConnected (connectedComponentIn (Ωᶜ) z) :=
    ⟨⟨z, hzK⟩, isPreconnected_connectedComponentIn⟩
  have hKmax : ∀ S : Set ℂ, IsPreconnected S → connectedComponentIn (Ωᶜ) z ⊆ S → S ⊆ Ωᶜ →
      S = connectedComponentIn (Ωᶜ) z := by
    intro S hS hKS hSF
    exact (hS.subset_connectedComponentIn (hKS hzK) hSF).antisymm hKS
  obtain ⟨f, hf, hfper, hfΩ, hno⟩ :=
    exists_periodic_not_hasArg_of_component hΩo hΩc hKcpt hKconn
      (connectedComponentIn_subset Ωᶜ z) hKmax hzK
  -- The loop `f` lies in `Ω`; regard `Ω` as an open subtype and use simple connectivity to
  -- produce a periodic argument of `t ↦ f t - z`, contradicting `hno`.
  set U : TopologicalSpace.Opens ℂ := ⟨Ω, hΩo⟩ with hU
  have hUset : (U : Set ℂ) = Ω := rfl
  haveI : ConnectedSpace ↥U := isConnected_iff_connectedSpace.mp (hUset ▸ hΩc)
  haveI : Subsingleton (Additive (FundamentalGroup ↥U ⟨f 0, hfΩ 0⟩) →+ ℝ) :=
    Work.SC.subsingleton_hom_additive_fundamentalGroup_of_simplyConnected _
  have hGhol : Submission.HolomorphicOnX (fun y : ↥U => (y : ℂ) - z) Set.univ :=
    Work.Mori.holomorphicOnX_opens_sub_const U z
  have hGne : ∀ y : ↥U, (y : ℂ) - z ≠ 0 := by
    intro y hy
    have hyz : (y : ℂ) = z := sub_eq_zero.mp hy
    exact hz (hyz ▸ (hUset ▸ y.2))
  have hloop : Continuous (fun t : ℝ => (⟨f t, hfΩ t⟩ : ↥U)) := by fun_prop
  have hlper : ∀ t : ℝ, (fun s : ℝ => (⟨f s, hfΩ s⟩ : ↥U)) (t + 1)
      = (fun s : ℝ => (⟨f s, hfΩ s⟩ : ↥U)) t := by
    intro t; ext; simp [hfper t]
  have hga := Work.Mori.hasArg_comp_of_holomorphic_of_subsingleton
    (X := ↥U) (x := ⟨f 0, hfΩ 0⟩) hGhol hGne hloop hlper
  have hga' : Commons.Topology.Winding.HasArg (fun t : ℝ => f t - z) 0 := by
    simpa using hga
  exact hno hga'

end

end Work.PlanarSC
