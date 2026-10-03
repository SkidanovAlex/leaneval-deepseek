import Mathlib
import Submission.Work.PlanarSC.Tools
import Submission.Work.PlanarSC.jordan_criterion_simplyConnected

/-!
# A plane domain with no bounded complementary component is simply connected

The classical criterion: an open connected `Ω ⊆ ℂ` is simply connected exactly when its complement
in the Riemann sphere is connected; for `Ω ⊆ ℂ` that is the same as asking that no connected
component of `Ωᶜ` is bounded.

Here the *sufficient* direction is reduced to the Jordan criterion for plane domains
(`Work.PlanarSC.jordan_criterion_simplyConnected`), the reduction itself being elementary: if `γ` is
a closed curve (in particular a Jordan curve) with values in `Ω` and `z` lies in a bounded component
of `(range γ)ᶜ`, then `z` cannot lie in `Ωᶜ` — the component of `Ωᶜ` through `z` would be unbounded,
could not cross `range γ ⊆ Ω`, and would therefore be trapped in that bounded component.
-/

open Set Metric Bornology

namespace Work.PlanarSC

/-- **The Jordan criterion for `Ω`.**  If every component of `Ωᶜ` is unbounded, then every Jordan
curve in `Ω` has its bounded complementary component inside `Ω`. -/
theorem jordan_criterion_of_no_bounded_component {Ω : Set ℂ}
    (h : ∀ z : ℂ, z ∉ Ω → ¬ Bornology.IsBounded (connectedComponentIn (Ωᶜ) z))
    {γ : C(Circle, ℂ)} (hγ : Set.range γ ⊆ Ω) :
    ∀ z : ℂ, z ∉ Set.range γ →
      Bornology.IsBounded (connectedComponentIn ((Set.range γ)ᶜ) z) → z ∈ Ω := by
  intro z _ hb
  by_contra hzΩ
  have hz' : z ∈ Ωᶜ := hzΩ
  have hsub : connectedComponentIn (Ωᶜ) z ⊆ connectedComponentIn ((Set.range γ)ᶜ) z :=
    (isPreconnected_connectedComponentIn).subset_connectedComponentIn (mem_connectedComponentIn hz')
      (fun w hw => by
        simp only [Set.mem_compl_iff, Set.mem_range, not_exists]
        rintro t rfl
        exact (connectedComponentIn_subset (Ωᶜ) z hw) (hγ ⟨t, rfl⟩))
  exact h z hzΩ (hb.subset hsub)

/-- **A plane domain with no bounded complementary component is simply connected.** -/
theorem simplyConnected_of_no_bounded_component {Ω : Set ℂ} (hΩo : IsOpen Ω) (hΩc : IsConnected Ω)
    (h : ∀ z : ℂ, z ∉ Ω → ¬ Bornology.IsBounded (connectedComponentIn (Ωᶜ) z)) :
    SimplyConnectedSpace Ω :=
  jordan_criterion_simplyConnected hΩo hΩc
    (fun _ _ hrange => jordan_criterion_of_no_bounded_component h hrange)

end Work.PlanarSC
