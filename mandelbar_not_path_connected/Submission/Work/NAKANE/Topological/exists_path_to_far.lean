import Mathlib
import Submission.Work.NAKANE.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.NAKANE.Topological

/-- **A path from a point of the critical domain to a far point, staying in the critical domain.**
For `z₀ ∈ critDomain c₀` and any `R` there is a far point `z₁` (with `R < ‖z₁‖`) in
`critDomain c₀` and a path `γ : C(I, ℂ)` from `z₀` to `z₁` whose image lies in `critDomain c₀`.

Route: `critDomain c₀` is open (`isOpen_critDomain`), preconnected (`isPreconnected_critDomain`)
and nonempty (`exists_mem_critDomain_gt_norm`), hence `IsConnected`, hence path connected
(`IsOpen.isConnected_iff_isPathConnected` in `Mathlib.Topology.Connected.LocallyPathConnected`, for
open subsets of a locally path connected space, which `ℂ` is); pick `z₁` in `critDomain c₀` with
`R < ‖z₁‖` (`exists_mem_critDomain_gt_norm c₀ R`) and apply path connectedness to get `Joined`
inside the set, which is a `Path` (`Mathlib.Topology.Path` API). -/
theorem exists_path_to_far {c₀ z₀ : ℂ} (hz₀ : z₀ ∈ Work.ParamRays.critDomain c₀) (R : ℝ) :
    ∃ z₁ : ℂ, R < ‖z₁‖ ∧ z₁ ∈ Work.ParamRays.critDomain c₀ ∧
      ∃ γ : C(Set.Icc (0 : ℝ) 1, ℂ),
        γ 0 = z₀ ∧ γ 1 = z₁ ∧ ∀ t, γ t ∈ Work.ParamRays.critDomain c₀ := by
  -- A far point of the critical domain, which is also a witness that the domain is nonempty.
  obtain ⟨z₁, hR, hz₁⟩ := Work.ParamRays.exists_mem_critDomain_gt_norm c₀ R
  -- `critDomain c₀` is connected: preconnected and nonempty.
  have hconn : IsConnected (Work.ParamRays.critDomain c₀) :=
    ⟨⟨z₀, hz₀⟩, Work.ParamRays.isPreconnected_critDomain c₀⟩
  -- An open set of a locally path connected space is connected iff it is path connected.
  have hpc : IsPathConnected (Work.ParamRays.critDomain c₀) :=
    (Work.ParamRays.isOpen_critDomain c₀).isConnected_iff_isPathConnected.mp hconn
  obtain ⟨x, _, hjoin⟩ := hpc
  -- Path connectedness turns the two membership proofs into a `JoinedIn` inside the domain.
  have hjoined : JoinedIn (Work.ParamRays.critDomain c₀) z₀ z₁ :=
    (hjoin hz₀).symm.trans (hjoin hz₁)
  -- `JoinedIn.somePath` is the desired path, as a continuous map on `I = Icc 0 1`.
  exact ⟨z₁, hR, hz₁, hjoined.somePath.toContinuousMap,
    hjoined.somePath.source, hjoined.somePath.target, hjoined.somePath_mem⟩

end Work.NAKANE.Topological
