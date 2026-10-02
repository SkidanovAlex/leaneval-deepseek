import Mathlib
import Submission.Work.LANDCL.Defs
import Submission.Work.LandLeaves.Defs
import Submission.Work.LandLeaves.isCompact_rayAccum
import Submission.Work.LandLeaves.rayAccum_nonempty

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.LandLeaves

/-- The quantitative form of the landing hypothesis, usable at the limit parameter: if `φ` is a
Böttcher coordinate of `T_c` and the accumulation set of the dynamic ray `R_c(θ)` is the
singleton `{y}`, then for every `ε > 0` there is a level `ρ > 1` such that every ray point of
Böttcher level `≤ ρ` is within `ε` of `y`.

Proof: the set of ray points of level `≤ ρ₁` is bounded (`IsDynBottcher` is asymptotic to the
identity), so its closure `X_ρ` is compact; the `X_ρ` (`ρ > 1`) are nested with intersection
`rayAccum c φ θ = {y}`, so for every `ε > 0` some `X_ρ` is contained in the ball of radius `ε`
about `y` (otherwise the nested nonempty compact sets `X_ρ ∩ {‖· - y‖ ≥ ε}` would have a common
point of `rayAccum` at distance `≥ ε` from `y`).

The hypothesis `Work.ParamRays.IsDynBottcher c φ` is essential: for an arbitrary `φ` the level
sets need not be precompact and the statement is false. -/
theorem rayAccum_entry {c : ℂ} {φ : ℂ → ℂ} (hφ : Work.ParamRays.IsDynBottcher c φ) {θ : ℝ} {y : ℂ}
    (hland : Work.Landing.rayAccum c φ θ = {y}) {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ : ℝ, 1 < ρ ∧ ∀ z : ℂ, z ∈ Work.Landing.dynRay c φ θ → ‖φ z‖ ≤ ρ → ‖z - y‖ ≤ ε := by
  -- Suppose no level `ρ > 1` works: then for every `ρ > 1` there is a ray point of level `≤ ρ`
  -- at distance `> ε` from `y`.
  by_contra hcon
  push Not at hcon
  -- the truncations of the ray at Böttcher level `≤ ρ`, and their closures
  let S : ℝ → Set ℂ := fun ρ => {z : ℂ | z ∈ Work.Landing.dynRay c φ θ ∧ ‖φ z‖ ≤ ρ}
  have hSmono : Monotone S := fun ρ σ hρσ z hz => ⟨hz.1, le_trans hz.2 hρσ⟩
  -- the truncation at level `2` is bounded, hence its closure is compact
  have hX2 : IsCompact (closure (S 2)) :=
    (Work.Landing.Rays.isBounded_dynRay_sublevel hφ θ 2).isCompact_closure
  -- the closed sets `X_ρ ∩ {‖· - y‖ ≥ ε}` for `1 < ρ ≤ 2`
  let ι := {ρ : ℝ // 1 < ρ ∧ ρ ≤ 2}
  have hι : Nonempty ι := ⟨⟨2, by norm_num, le_rfl⟩⟩
  let T : ι → Set ℂ := fun i => closure (S i.1) ∩ {u : ℂ | ε ≤ ‖u - y‖}
  have hTdir : Directed (· ⊇ ·) T := by
    rintro ⟨ρ, h1ρ, h2ρ⟩ ⟨σ, h1σ, h2σ⟩
    refine ⟨⟨min ρ σ, lt_min h1ρ h1σ, le_trans (min_le_left _ _) h2ρ⟩, ?_, ?_⟩
    · intro u hu
      exact ⟨closure_mono (hSmono (min_le_left ρ σ)) hu.1, hu.2⟩
    · intro u hu
      exact ⟨closure_mono (hSmono (min_le_right ρ σ)) hu.1, hu.2⟩
  -- each of them is nonempty, by the contradictory hypothesis
  have hTne : ∀ i : ι, (T i).Nonempty := by
    rintro ⟨ρ, h1ρ, -⟩
    obtain ⟨z, hz, hzφ, hzy⟩ := hcon ρ h1ρ
    exact ⟨z, subset_closure ⟨hz, hzφ⟩, le_of_lt hzy⟩
  -- and each of them is compact, being a closed subset of `X_2`
  have hTcp : ∀ i : ι, IsCompact (T i) := by
    rintro ⟨ρ, h1ρ, h2ρ⟩
    refine hX2.of_isClosed_subset ?_ ?_
    · exact isClosed_closure.inter
        (isClosed_le continuous_const (continuous_norm.comp (continuous_id.sub continuous_const)))
    · intro u hu
      exact closure_mono (hSmono h2ρ) hu.1
  have hTcl : ∀ i : ι, IsClosed (T i) := fun i => (hTcp i).isClosed
  -- the finite intersection property of nested nonempty compacta gives a common point
  obtain ⟨x, hx⟩ :=
    IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed (hι := hι) T hTdir hTne
      hTcp hTcl
  have hxT : ∀ i : ι, x ∈ T i := Set.mem_iInter.mp hx
  -- that common point lies in `rayAccum c φ θ`
  have hxacc : x ∈ Work.Landing.rayAccum c φ θ := by
    intro ρ hρ
    rcases le_or_gt ρ 2 with h2 | h2
    · exact (hxT ⟨ρ, hρ, h2⟩).1
    · exact closure_mono (hSmono h2.le) (hxT ⟨2, by norm_num, le_rfl⟩).1
  -- hence it equals `y`, by the landing hypothesis
  have hxy : x = y := by
    have : x ∈ ({y} : Set ℂ) := hland ▸ hxacc
    simpa using this
  -- but it lies at distance `≥ ε > 0` from `y`: contradiction
  have h2mem : ε ≤ ‖x - y‖ := (hxT ⟨2, by norm_num, le_rfl⟩).2
  rw [hxy, sub_self, norm_zero] at h2mem
  linarith

end Work.LandLeaves
