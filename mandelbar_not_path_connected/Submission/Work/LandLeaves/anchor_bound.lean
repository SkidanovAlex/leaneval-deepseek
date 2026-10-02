import Mathlib
import Submission.Work.LandLeaves.rayPtCore
import Submission.Work.LandLeaves.rayAccum_entry
import Submission.Work.LandLeaves.dynBottcherOnlyOnMandelbar

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.LandLeaves

/-- **The anchor bound.**  If the dynamic ray at angle `θ` of `T_c` lands at `y`
(`Work.Landing.landsAt c θ y`), then the level-`t` points of the *critical* ray at angle `θ`
are uniformly close to `y` for all levels `t` in a window `(1, η₀]` just above the unit circle:
for every `ε > 0` there is `η₀ > 1` such that every `z` in the critical domain `critDomain c`
with `varphiCrit c z = t · rayDir θ`, `1 < t ≤ η₀`, satisfies `‖z - y‖ ≤ ε`.

The proof is the landing statement itself, read quantitatively.  `hland` forces `c` into the
mandelbar, so the canonical critical Böttcher coordinate `varphiCrit c` is a Böttcher coordinate
on the whole escaping set (`isCritBottcher_iff_isDynBottcher`) and the accumulation set it
computes is the one `hland` speaks about (`rayAccum_congr` + uniqueness of the Böttcher
coordinate).  The quantitative form of landing, `Work.LandLeaves.rayAccum_entry`, then supplies
a level `ρ > 1` below which every ray point is within `ε` of `y`; the level-`t` critical points
with `1 < t ≤ ρ` are such ray points, because `‖varphiCrit c z‖ = t`. -/
theorem anchor_bound {c : ℂ} {θ : ℝ} {y : ℂ} (hland : Work.Landing.landsAt c θ y)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ η₀ : ℝ, 1 < η₀ ∧ ∀ t : ℝ, 1 < t → t ≤ η₀ → ∀ z : ℂ,
      z ∈ Work.ParamRays.critDomain c →
      Work.Bottcher.varphiCrit c z = (t : ℂ) * Work.ParamRays.rayDir θ → ‖z - y‖ ≤ ε := by
  -- `hland` forces `c` into the mandelbar, hence the critical Böttcher coordinate is global
  have hc : c ∈ LeanEval.ComplexAnalysis.Mandelbar :=
    Work.LandLeaves.mem_mandelbar_of_landsAt hland
  have hdyn : Work.ParamRays.IsDynBottcher c (Work.Bottcher.varphiCrit c) :=
    (Work.ParamRays.isCritBottcher_iff_isDynBottcher hc).mp
      (Work.Bottcher.isCritBottcher_varphiCrit c)
  obtain ⟨φ, hφ, hacc⟩ := hland
  have haccφ : Work.Landing.rayAccum c φ θ = {y} := hacc
  -- the accumulation set is independent of the Böttcher coordinate
  have hacc' : Work.Landing.rayAccum c (Work.Bottcher.varphiCrit c) θ = {y} := by
    rw [Work.Landing.rayAccum_congr
      (fun w hw => Work.ParamRays.isDynBottcher_unique hdyn hφ hw) θ, haccφ]
  -- the quantitative form of landing: a level window in which every ray point is close to `y`
  obtain ⟨ρ, hρ1, hρ⟩ := Work.LandLeaves.rayAccum_entry hdyn hacc' hε
  refine ⟨ρ, hρ1, ?_⟩
  intro t ht1 htρ z hz hzφ
  refine hρ z ?_ ?_
  · -- the level-`t` critical point lies on the dynamic ray at angle `θ`
    rw [Work.Landing.dynRay]
    refine ⟨?_, ?_⟩
    · rw [← Work.ParamRays.mem_escapingSet, ← Work.ParamRays.critDomain_eq_escapingSet hc]
      exact hz
    · rw [Work.Landing.radialRay]
      exact ⟨t, ht1, by rw [hzφ]; rfl⟩
  · -- and its Böttcher level is `t ≤ ρ`
    rw [hzφ, norm_mul, Work.ParamRays.norm_rayDir, mul_one,
      Complex.norm_of_nonneg (le_of_lt (lt_trans zero_lt_one ht1))]
    exact htρ

end Work.LandLeaves
