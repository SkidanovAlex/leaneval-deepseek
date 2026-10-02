/-
Copyright: subproject `Submission/Work/PARIMPL2/` of `mandelbar_not_path_connected`.

# `Work.PARIMPL2.Lavaurs.exists_rho_direct` — the quantitative neighbourhood of the root parameter

The three germ-level inputs of the direct transit argument (`L3`, see
`Submission/Work/NOTES_LEAD_mandelbar_implosion.md` §3.5 and the docstring of
`Submission/Work/PARIMPL2/Lavaurs/transit_exit_direct.lean`), packaged as a single radius
`ρ = ρ (R) > 0` around the root parameter `c₀`: on `P.Nm ∩ ball c₀ ρ`

* `λ_c R² ≤ 1` — the parameter is deep enough for the chart strip of depth `R` to be principal
  (`λ_c → 0` along `Nm` at the parabolic parameter `c₀`: `ParNormal.tendsto_lam`);
* `‖h₁ c‖ ≤ ‖h₁ c₀‖ + 1` — the linear coefficient of the germ stays bounded, by continuity of
  `h₁` on the normal-form ball (`ParNormal.cont_h1`);
* `‖h c 0 − 1‖ ≤ 1/8` — the rotation constant of the germ is close to `1`, by continuity of
  `c ↦ h c 0` (`ParNormal.cont_τ`) and the value `h c₀ 0 = 1` of L0.5;
* `(π/λ_c)·‖h c 0 − 1‖ ≤ 1/(8R)` — the **phase** of the rotation is small compared with `1/R`,
  which is L0.5's phase vanishing `(π/λ_c)·‖h c 0 − 1‖ → 0` along `Nm ∋ c → c₀`,
  `Work.PARIMPL2.Lavaurs.L0_symmetry`.

Nothing here uses the symmetry `h(a) = conj (h(−a))`: only the *limit* statements at `c₀` are
needed, i.e. the last two conjuncts of `Work.PARIMPL2.Lavaurs.L0_symmetry`.
-/
import Mathlib
import Submission.Work.PARIMPL.Basic
import Submission.Work.PARIMPL2.Lavaurs.L0_symmetry
import Submission.Work.PARIMPL.Nm_mem_closure

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedVariables false

open Classical Filter Set Metric
open scoped Topology

noncomputable section

namespace Work.PARIMPL2.Lavaurs

/-- **The quantitative neighbourhood of the root parameter.**  For every depth `R ≥ 128` there is
a radius `ρ > 0` such that on the implosion side inside `ball c₀ ρ` the germ constants of the
parameter normal form are controlled: `λ_c R² ≤ 1`, `‖h₁ c‖ ≤ ‖h₁ c₀‖ + 1`, `‖h c 0 − 1‖ ≤ 1/8`
and `(π/λ_c)·‖h c 0 − 1‖ ≤ 1/(8R)`.

Assembly of four eventual statements in `𝓝[P.Nm] c₀` (`ParNormal.tendsto_lam` for `λ`,
`ParNormal.cont_h1` and `ParNormal.cont_τ` for the germ constants, and the phase vanishing L0.5
`Work.PARIMPL2.Lavaurs.L0_symmetry`), converted into a radius with
`eventually_nhdsWithin_iff` + `Metric.eventually_nhds_iff`. -/
theorem exists_rho_direct {c₀ : ℂ} {d : Work.EL.RootParabolic c₀} (P : Work.PARIMPL.ParNormal d)
    (R : ℝ) (hR : 128 ≤ R) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ c ∈ P.Nm ∩ Metric.ball c₀ ρ,
      P.lam c * R ^ 2 ≤ 1 ∧ ‖P.h1 c‖ ≤ ‖P.h1 c₀‖ + 1 ∧
      ‖P.h c 0 - 1‖ ≤ 1 / 8 ∧
      (Real.pi / P.lam c) * ‖P.h c 0 - 1‖ ≤ 1 / (8 * R) := by
  have hRpos : 0 < R := by linarith
  have hc₀ : c₀ ∈ Metric.ball c₀ P.ρ₀ := by simpa using P.hρ₀
  obtain ⟨-, -, hτ₀, hphase⟩ := L0_symmetry d P
  have hlam : Filter.Tendsto P.lam (𝓝[P.Nm] c₀) (𝓝 0) := P.tendsto_lam c₀ P.a2₀ hc₀
  have hev : ∀ᶠ c in 𝓝[P.Nm] c₀,
      P.lam c * R ^ 2 ≤ 1 ∧ ‖P.h1 c‖ ≤ ‖P.h1 c₀‖ + 1 ∧
      ‖P.h c 0 - 1‖ ≤ 1 / 8 ∧
      (Real.pi / P.lam c) * ‖P.h c 0 - 1‖ ≤ 1 / (8 * R) := by
    -- `λ_c → 0` along `Nm` at `c₀`
    have e1 : ∀ᶠ c in 𝓝[P.Nm] c₀, P.lam c * R ^ 2 ≤ 1 := by
      filter_upwards [hlam.eventually (Iic_mem_nhds (show (0 : ℝ) < 1 / R ^ 2 by positivity))]
        with c hc
      calc P.lam c * R ^ 2 ≤ (1 / R ^ 2) * R ^ 2 := mul_le_mul_of_nonneg_right hc (sq_nonneg R)
        _ = 1 := one_div_mul_cancel (pow_ne_zero 2 (ne_of_gt hRpos))
    -- continuity of `h₁` at `c₀`
    have e2 : ∀ᶠ c in 𝓝[P.Nm] c₀, ‖P.h1 c‖ ≤ ‖P.h1 c₀‖ + 1 := by
      have hcont : ContinuousAt P.h1 c₀ :=
        P.cont_h1.continuousAt (Metric.isOpen_ball.mem_nhds hc₀)
      have h : ∀ᶠ c in 𝓝[P.Nm] c₀, ‖P.h1 c‖ < ‖P.h1 c₀‖ + 1 :=
        (hcont.norm.tendsto.mono_left nhdsWithin_le_nhds).eventually
          (Iio_mem_nhds (by linarith))
      filter_upwards [h] with c hc
      exact le_of_lt hc
    -- continuity of `c ↦ h c 0` at `c₀`, where `h c₀ 0 = 1` (L0.5)
    have e3 : ∀ᶠ c in 𝓝[P.Nm] c₀, ‖P.h c 0 - 1‖ ≤ 1 / 8 := by
      have hcont : ContinuousAt (fun c : ℂ => P.h c 0 - 1) c₀ :=
        (P.cont_τ.continuousAt (Metric.isOpen_ball.mem_nhds hc₀)).sub continuousAt_const
      have ht : Filter.Tendsto (fun c => ‖P.h c 0 - 1‖) (𝓝 c₀) (𝓝 0) := by
        simpa [hτ₀] using hcont.norm.tendsto
      have h : ∀ᶠ c in 𝓝[P.Nm] c₀, ‖P.h c 0 - 1‖ < 1 / 8 :=
        (ht.mono_left nhdsWithin_le_nhds).eventually (Iio_mem_nhds (by norm_num))
      filter_upwards [h] with c hc
      exact le_of_lt hc
    -- the phase vanishing `(π/λ_c)·‖h c 0 − 1‖ → 0` (L0.5)
    have e4 : ∀ᶠ c in 𝓝[P.Nm] c₀,
        (Real.pi / P.lam c) * ‖P.h c 0 - 1‖ ≤ 1 / (8 * R) :=
      hphase.eventually (Iic_mem_nhds (by positivity))
    filter_upwards [e1, e2, e3, e4] with c h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
  obtain ⟨ρ, hρ, hρ'⟩ := hev
  exact ⟨ρ, hρ, fun c hc => hρ' (Metric.mem_ball.mp hc.2) hc.1⟩

end Work.PARIMPL2.Lavaurs

end
