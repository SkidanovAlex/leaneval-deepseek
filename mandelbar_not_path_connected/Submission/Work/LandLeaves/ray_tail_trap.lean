import Mathlib
import Submission.Work.LandLeaves.ccBet_v2_defs
import Submission.Work.LandLeaves.rayAccum_entry
import Submission.Work.ELTop.All
import Submission.Work.NAKANE.GreenJoint
import Submission.Work.ParamRays.IsDynBottcher_modulus

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.LandLeaves

/-- **Ray-tail trap.**  If the accumulation set of the dynamic ray `R_c(a)` is the single
point `y`, then the part of the ray near `y` stays at Böttcher level `< 1 + δ`: there is a
radius `ε > 0` such that every ray point within `ε` of `y` satisfies `‖φ z‖ < 1 + δ`.

Why: `y ∈ rayAccum c φ a` means that for every `ρ > 1` the point `y` lies in the closure of
the ray truncation at level `≤ ρ`.  Since `‖φ w‖ = exp (G_c w)` on the escaping set
(`Work.ParamRays.IsDynBottcher_modulus`), that truncation is contained in the closed sublevel
set `{G_c ≤ log ρ}`, hence `G_c y ≤ log ρ` for every `ρ > 1`, i.e. `G_c y ≤ 0`.  Now the
Green function is continuous (`Work.Escape.continuous_green_Tantibar` transported to
`Work.ParamRays.greenFun` by `Work.Bottcher.Contraction.green_eq_greenFun`), so
`G_c < log (1 + δ)` on a neighbourhood of `y`, which is exactly `‖φ‖ < 1 + δ` on the ray
there. -/
theorem ray_tail_trap {c : ℂ} {φ : ℂ → ℂ} (hφ : Work.ParamRays.IsDynBottcher c φ)
    {a : ℝ} {y : ℂ} (ha : Work.Landing.rayAccum c φ a = {y}) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z : ℂ, z ∈ Work.Landing.dynRay c φ a → ‖z - y‖ < ε → ‖φ z‖ < 1 + δ := by
  -- Continuity of the Green function in the point, at fixed parameter.
  have hGcont : Continuous fun z : ℂ => Work.ParamRays.greenFun c z :=
    (Work.Escape.continuous_green_Tantibar c).congr
      fun z => Work.Bottcher.Contraction.green_eq_greenFun c z
  -- `y` lies in the accumulation set.
  have hy : y ∈ Work.Landing.rayAccum c φ a := by rw [ha]; exact Set.mem_singleton y
  -- Every ray truncation is contained in a closed sublevel set of `G_c`.
  have hsub : ∀ ρ : ℝ, 1 < ρ →
      {z : ℂ | z ∈ Work.Landing.dynRay c φ a ∧ ‖φ z‖ ≤ ρ}
        ⊆ {z : ℂ | Work.ParamRays.greenFun c z ≤ Real.log ρ} := by
    intro ρ hρ z hz
    rw [Set.mem_setOf_eq] at hz ⊢
    obtain ⟨hzd, hzφ⟩ := hz
    simp only [Work.Landing.dynRay, Set.mem_setOf_eq] at hzd
    have hesc : Work.ParamRays.Escaping c z := hzd.1
    have hmod := Work.ParamRays.IsDynBottcher_modulus hφ hesc
    have hpos : 0 < ‖φ z‖ := by rw [hmod]; exact Real.exp_pos _
    have hle := Real.log_le_log hpos hzφ
    rwa [hmod, Real.log_exp] at hle
  -- Hence `G_c y ≤ log ρ` for every `ρ > 1`.
  have hGy_le : ∀ ρ : ℝ, 1 < ρ → Work.ParamRays.greenFun c y ≤ Real.log ρ := by
    intro ρ hρ
    have hmem : y ∈ closure {z : ℂ | Work.ParamRays.greenFun c z ≤ Real.log ρ} :=
      closure_mono (hsub ρ hρ) (hy ρ hρ)
    have hclosed : IsClosed {z : ℂ | Work.ParamRays.greenFun c z ≤ Real.log ρ} :=
      isClosed_le hGcont continuous_const
    rwa [hclosed.closure_eq] at hmem
  -- Consequently `G_c y ≤ 0`.
  have hGy0 : Work.ParamRays.greenFun c y ≤ 0 := by
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    have h1 := hGy_le (1 + ε) (by linarith)
    have h2 : Real.log (1 + ε) < ε := by
      have hpos : (0 : ℝ) < 1 + ε := by linarith
      have hne : (1 : ℝ) + ε ≠ 1 := by linarith
      have := Real.log_lt_sub_one_of_pos hpos hne
      linarith
    linarith
  -- The Green function is `< log (1+δ)` on an open neighbourhood of `y`.
  have hmem : y ∈ {z : ℂ | Work.ParamRays.greenFun c z < Real.log (1 + δ)} := by
    rw [Set.mem_setOf_eq]
    have : 0 < Real.log (1 + δ) := Real.log_pos (by linarith)
    linarith
  have hopen : IsOpen {z : ℂ | Work.ParamRays.greenFun c z < Real.log (1 + δ)} :=
    isOpen_lt hGcont continuous_const
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hmem)
  refine ⟨ε, hε, fun z hz hzy => ?_⟩
  have hzball : z ∈ Metric.ball y ε := by
    rw [Metric.mem_ball, dist_eq_norm]; exact hzy
  have hGz : Work.ParamRays.greenFun c z < Real.log (1 + δ) := hball hzball
  -- Translate back through the modulus identity.
  have hzd : z ∈ Work.Landing.dynRay c φ a := hz
  simp only [Work.Landing.dynRay, Set.mem_setOf_eq] at hzd
  have hesc : Work.ParamRays.Escaping c z := hzd.1
  have hmod := Work.ParamRays.IsDynBottcher_modulus hφ hesc
  rw [hmod, ← Real.exp_log (by linarith : (0 : ℝ) < 1 + δ), Real.exp_lt_exp]
  exact hGz

end Work.LandLeaves
