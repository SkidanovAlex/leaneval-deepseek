import Mathlib
import Submission.Work.WilE9.Sharp.EffInput
import Submission.Work.WilE9G.Basic

namespace Work.WilE9G.Cover

open Topology

/-- A preconnected set which is contained in the `x`-fibre of the projection of a connected
component, and whose projected points belong to a *finite* set, projects to a single point.

The point is that `stratProj` is continuous, so `stratProj '' K` is preconnected; it is contained
in the finite set `{y' | y' ∈ stratProj '' connectedComponentIn X.set z₀ ∧ Fin.init y' = x}`, and
a finite subset of a `T1` space is discrete, whence preconnected means a subsingleton. -/
theorem stratProj_eq_of_isPreconnected {n m : ℕ} {X : WilkiesDesign.E.SemiPf (n + (1 + m))}
    {z₀ : Fin (n + (1 + m)) → ℝ} {x : Fin n → ℝ} {K : Set (Fin (n + (1 + m)) → ℝ)}
    (hK : IsPreconnected K) (hsub : K ⊆ connectedComponentIn X.set z₀)
    (hfib : ∀ u ∈ K, Fin.init (Work.WilE9.Sharp.stratProj u) = x)
    (hfin : {y' : Fin (n + 1) → ℝ |
        y' ∈ Work.WilE9.Sharp.stratProj '' connectedComponentIn X.set z₀ ∧ Fin.init y' = x}.Finite) :
    ∀ u ∈ K, ∀ v ∈ K, Work.WilE9.Sharp.stratProj u = Work.WilE9.Sharp.stratProj v := by
  set T : Set (Fin (n + 1) → ℝ) :=
    {y' | y' ∈ Work.WilE9.Sharp.stratProj '' connectedComponentIn X.set z₀ ∧ Fin.init y' = x}
    with hT
  have hmaps : Set.MapsTo (Work.WilE9.Sharp.stratProj (n := n) (m := m)) K T := by
    intro u hu
    exact ⟨⟨u, hsub hu, rfl⟩, hfib u hu⟩
  have hd : IsDiscrete T := hfin.isDiscrete
  intro u hu v hv
  exact hK.constant_of_mapsTo hd (continuous_stratProj.continuousOn) hmaps hu hv

end Work.WilE9G.Cover
