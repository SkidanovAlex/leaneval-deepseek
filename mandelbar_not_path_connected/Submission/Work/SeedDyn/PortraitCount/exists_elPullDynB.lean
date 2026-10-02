/-
# SeedDyn · PortraitCount — the `EL → ELPull` adapter (`exists_elPullDynB`)

The two dynamical-plane vocabularies of the fleet differ **only** in which Böttcher coordinate
they carry:

* `Work.EL.DynB c φ = Work.Top.NakaneData (K c) (Work.EL.dynPhi c φ)`, where
  `Work.EL.dynPhi c φ z = if z ∈ K c then 0 else φ z` is `φ` extended by `0` on the filled Julia
  set — the `hN` of the `EL`/`ELTop` side, obtained (as `Work.EL.RootParabolic.hN`) from a
  *chosen* Böttcher coordinate `φ` with `Work.ParamRays.IsDynBottcher c φ`;
* `Work.ELPull.DynB c = Work.Top.NakaneData (K c) (Work.ParamRays.dynPhi c)`, the *canonical*
  coordinate `dynPhiOf c` (`Classical.choose` of `DynBottcherExists c`) extended by `0`.

The adapter asked for here is the statement that the whole landing relation of the `EL` side
transports to a `Work.ELPull.DynB c`, *with the same rays*.

## The mathematics

At a point `z` off the filled Julia set the two functions are `φ z` and `dynPhiOf c z`, and
Böttcher's theorem gives `φ z = dynPhiOf c z` there (`isDynBottcher_unique`); on the filled
Julia set both are `0`.  Hence `Work.EL.dynPhi c φ = Work.ParamRays.dynPhi c` is an equality of
*functions* (`dynPhi_EL_eq`).

Since `Work.Top.NakaneData.rayPt hN θ t` only ever reads the field `hN.e` (the homeomorphism
`Mbᶜ ≃ₜ exteriorDisc` underlying `Φ`), the transport of the record along that equality can be
done **keeping the same `e`** — so all ray points, and hence the whole landing relation, are
literally unchanged (`nakaneData_congr`, and then `exists_elPullDynB` by `Tendsto.congr'`).

## Main results

* `Work.SeedDyn.PortraitCount.nakaneData_congr` — transport of the Nakane interface along a
  pointwise equality of the Böttcher coordinates, with the same rays.
* `Work.SeedDyn.PortraitCount.dynPhi_EL_eq` — `Work.EL.dynPhi c φ = Work.ParamRays.dynPhi c`.
* `Work.SeedDyn.PortraitCount.exists_elPullDynB` — the adapter (the target of this file).
-/
import Mathlib
import Submission.Work.SeedDyn.Defs
import Submission.Work.ELTop.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set

namespace Work.SeedDyn.PortraitCount

/-! ## 1. Transport of the Nakane interface along an equality of Böttcher coordinates -/

/-- **Transport of `Work.Top.NakaneData` along a pointwise equality of the Böttcher
coordinates.**  The underlying homeomorphism `e` (and hence every ray point `rayPt`) is kept,
so the transported record *has the same rays*.

The point is that `rayPt hN θ t` is defined from `hN.e` alone: once the two `Φ`'s are equal as
functions, `potential Mb Φ` and `potential Mb Ψ` are equal as functions, and the only fields a
`NakaneData` stores besides the homeomorphism are the analytic requirements on that potential. -/
theorem nakaneData_congr {Mb : Set ℂ} {Φ Ψ : ℂ → ℂ} (h : Φ = Ψ)
    (hN : Work.Top.NakaneData Mb Φ) :
    ∃ hN' : Work.Top.NakaneData Mb Ψ, ∀ (θ t : ℝ),
      Work.Top.NakaneData.rayPt hN' θ t = Work.Top.NakaneData.rayPt hN θ t := by
  have hpot : Work.Top.potential Mb Φ = Work.Top.potential Mb Ψ := by
    funext z
    simp only [Work.Top.potential, h]
  refine ⟨{ e := hN.e, he := ?_, Phi_eq_zero_of_mem := ?_, continuous_potential := ?_, tendsto_potential := ?_ }, ?_⟩
  · intro z
    rw [← h]
    exact hN.he z
  · intro z hz
    rw [← h]
    exact hN.Phi_eq_zero_of_mem z hz
  · rw [← hpot]
    exact hN.continuous_potential
  · intro t
    obtain ⟨R, hR⟩ := hN.tendsto_potential t
    exact ⟨R, fun z hz => by rw [← hpot]; exact hR z hz⟩
  · intro θ t
    rfl

/-! ## 2. The two Böttcher coordinates of the dynamical plane agree -/

/-- **The Böttcher coordinate of `Work.EL` is the canonical one.**  For a genuine Böttcher
coordinate `φ` of `T_c` (i.e. `Work.ParamRays.IsDynBottcher c φ`) the extension
`Work.EL.dynPhi c φ` (`φ` off the filled Julia set, `0` on it) is *the same function* as the
canonical `Work.ParamRays.dynPhi c` (`dynPhiOf c` off the filled Julia set, `0` on it).

Indeed, both vanish on `K c = filledJulia c`; off it, `z` is an escaping point, and
`Work.ParamRays.dynPhiOf_eq_of_isDynBottcher` (Böttcher uniqueness) gives
`dynPhiOf c z = φ z`. -/
theorem dynPhi_EL_eq {c : ℂ} {φ : ℂ → ℂ} (hφ : Work.ParamRays.IsDynBottcher c φ) :
    Work.EL.dynPhi c φ = Work.ParamRays.dynPhi c := by
  funext z
  by_cases hz : z ∈ Work.ParamRays.filledJulia c
  · rw [Work.EL.dynPhi_of_mem hz, Work.ParamRays.dynPhi_eq_zero_of_mem hz]
  · have hesc : Work.ParamRays.Escaping c z := by
      have h : z ∈ Work.ParamRays.escapingSet c := by
        rw [← Work.ParamRays.compl_filledJulia c]; exact hz
      exact h
    rw [Work.EL.dynPhi_of_notMem hz, Work.ParamRays.dynPhi_of_not_mem hz]
    exact (Work.ParamRays.dynPhiOf_eq_of_isDynBottcher ⟨φ, hφ⟩ hφ hesc).symm

/-! ## 3. The adapter -/

/-- **EL → ELPull adapter.**  Every `Work.EL` dynamical Böttcher datum `hN` at a genuine Böttcher
coordinate `φ` can be re-read as a `Work.ELPull` datum `hN'` *with the same rays*, i.e. the two
landing relations agree at every angle and every point. -/
theorem exists_elPullDynB {c : ℂ} {φ : ℂ → ℂ}
    (hφ : Work.ParamRays.IsDynBottcher c φ) (hN : Work.EL.DynB c φ) :
    ∃ hN' : Work.ELPull.DynB c, ∀ (θ : ℝ) (y : ℂ),
      Work.ELPull.LandsN hN' θ y ↔ Work.EL.LandsN hN θ y := by
  obtain ⟨hN', hpt⟩ := nakaneData_congr (dynPhi_EL_eq hφ) hN
  refine ⟨hN', fun θ y => ?_⟩
  have heq : (fun t : ℝ => Work.Top.NakaneData.rayPt hN' θ t)
      =ᶠ[nhdsWithin 1 (Set.Ioi 1)] (fun t : ℝ => Work.Top.NakaneData.rayPt hN θ t) :=
    Filter.Eventually.of_forall (fun t => hpt θ t)
  exact ⟨Filter.Tendsto.congr' heq, Filter.Tendsto.congr' heq.symm⟩

end Work.SeedDyn.PortraitCount
