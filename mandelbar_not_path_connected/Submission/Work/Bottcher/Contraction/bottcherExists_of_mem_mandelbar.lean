import Mathlib
import Submission.Work.Bottcher.Defs
import Submission.Work.ParamRays.Bottcher
import Submission.Work.Bottcher.Contraction.exists_analyticBottcher_of_mem_mandelbar
import Submission.Work.Bottcher.Contraction.bottcher_comm_Tantibar_of_analytic
import Submission.Work.Bottcher.Green.green_pos_iff
import Submission.Work.Bottcher.Contraction.isPreconnected_escapeSet
import Submission.Work.Bottcher.Inverse.bottcher_comm_Tantibar_of_pMap_eq

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Bottcher.Contraction

/-!
# Existence of a Böttcher coordinate for parameters of the mandelbar

For `c` in the mandelbar the critical orbit of `T_c` is bounded, the filled Julia set is
connected, and the escaping set `EscapeSet c = {G_c > 0}` is simply connected; hence the
Böttcher coordinate of the holomorphic quartic `p_c = T_c ∘ T_c` — whose existence on the
whole escape set is the content of
`Work.Bottcher.Contraction.exists_analyticBottcher_of_mem_mandelbar` — is single valued and
analytic there, and is a Böttcher coordinate of the antiholomorphic quadratic `T_c` itself
(`Work.ParamRays.IsDynBottcher c`).

This file only assembles the two supplied inputs; the analytic existence theorem and the
passage from the Böttcher equation of `p_c` to that of `T_c` are proved elsewhere.
-/

open Filter
open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-- The asymptotic clause `φ z / z → 1` at infinity implies `‖φ z - z‖ ≤ ε ‖z‖`
eventually: the quotient `(φ z - z) / z = φ z / z - 1` is eventually small. -/
theorem eventually_norm_sub_le_of_tendsto_div {φ : ℂ → ℂ}
    (has : Filter.Tendsto (fun z : ℂ => φ z / z) (Filter.cocompact ℂ) (nhds (1 : ℂ)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ z : ℂ in Filter.cocompact ℂ, ‖φ z - z‖ ≤ ε * ‖z‖ := by
  have hA' : ∀ᶠ z : ℂ in Filter.cocompact ℂ, dist (φ z / z) 1 ≤ ε / 2 :=
    has.eventually (Metric.closedBall_mem_nhds (1 : ℂ) (half_pos hε))
  have hA : ∀ᶠ z : ℂ in Filter.cocompact ℂ, ‖φ z / z - 1‖ ≤ ε / 2 := by
    simpa [dist_eq_norm] using hA'
  have hB : ∀ᶠ z : ℂ in Filter.cocompact ℂ, (1 : ℝ) ≤ ‖z‖ := by
    refine Filter.mem_of_superset
      (isCompact_closedBall (0 : ℂ) 1).compl_mem_cocompact ?_
    intro z hz
    simp only [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right] at hz
    exact le_of_lt (not_le.mp hz)
  filter_upwards [hA, hB] with z hA1 hB1
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, norm_zero] at hB1
    linarith
  have hmul : φ z - z = z * (φ z / z - 1) := by
    field_simp
  rw [hmul, norm_mul]
  have h1 : ‖z‖ * ‖φ z / z - 1‖ ≤ ‖z‖ * (ε / 2) :=
    mul_le_mul_of_nonneg_left hA1 (norm_nonneg z)
  have h2 : ‖z‖ * (ε / 2) ≤ ε * ‖z‖ := by
    nlinarith [norm_nonneg z]
  linarith

/-- An escaping point has positive Green function (definitional unwinding of
`Work.ParamRays.Escaping` through the positivity criterion for `G_c`). -/
theorem green_pos_of_escaping {c z : ℂ} (hz : Work.ParamRays.Escaping c z) :
    0 < Work.Bottcher.green c z :=
  (Work.Bottcher.Green.green_pos_iff c z).mpr hz

/-- **Assembly.**  An analytic solution of the Böttcher problem of the holomorphic quartic
`p_c = T_c ∘ T_c` on the escape set, with the right modulus and the right asymptotics, is a
Böttcher coordinate of `T_c` in the sense of `Work.ParamRays.IsDynBottcher`. -/
theorem isDynBottcher_of_analyticBottcher (c : ℂ) (φ : ℂ → ℂ)
    (han : AnalyticOnNhd ℂ φ (Work.Bottcher.EscapeSet c))
    (hfe : ∀ z : ℂ, 0 < Work.Bottcher.green c z →
      φ (Work.Bottcher.pMap c z) = (φ z) ^ 4)
    (hmod : ∀ z : ℂ, 0 < Work.Bottcher.green c z →
      ‖φ z‖ = Real.exp (Work.Bottcher.green c z))
    (has : Filter.Tendsto (fun z : ℂ => φ z / z) (Filter.cocompact ℂ) (nhds (1 : ℂ))) :
    Work.ParamRays.IsDynBottcher c φ := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← escapeSet_eq_escapingSet c]
    exact han.continuousOn
  · intro z hz
    exact bottcher_comm_Tantibar_of_analytic c φ han hfe hmod has z (green_pos_of_escaping hz)
  · intro ε hε
    exact eventually_norm_sub_le_of_tendsto_div has hε

/-- The escape set is eventually all of `cocompact`: outside a large ball every point has
positive Green function. -/
theorem eventually_green_pos_of_cocompact (c : ℂ) :
    ∀ᶠ z : ℂ in Filter.cocompact ℂ, 0 < Work.Bottcher.green c z := by
  refine Filter.mem_of_superset
    (isCompact_closedBall (0 : ℂ) (Work.Bottcher.escapeRadius c)).compl_mem_cocompact ?_
  intro z hz
  rw [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right] at hz
  exact green_pos_of_escapeRadius_le c (le_of_lt (not_le.mp hz))

/-- **Assembly at the level of a continuous Böttcher coordinate.**  A function which is
continuous on the escape set, satisfies the Böttcher equation of the holomorphic quartic
`p_c = T_c ∘ T_c`, has modulus `exp ∘ green` and is tangent to the identity at infinity, and in
addition solves the antiholomorphic Böttcher equation of `T_c`, is a Böttcher coordinate of
`T_c` in the sense of `Work.ParamRays.IsDynBottcher`. -/
theorem isDynBottcher_of_continuousBottcher (c : ℂ) (φ : ℂ → ℂ)
    (hcont : ContinuousOn φ (Work.Bottcher.EscapeSet c))
    (hfe : ∀ z : ℂ, 0 < Work.Bottcher.green c z → φ (Work.Bottcher.pMap c z) = (φ z) ^ 4)
    (hmod : ∀ z : ℂ, 0 < Work.Bottcher.green c z → ‖φ z‖ = Real.exp (Work.Bottcher.green c z))
    (has : Filter.Tendsto (fun z : ℂ => φ z / z) (Filter.cocompact ℂ) (nhds (1 : ℂ)))
    (htc : ∀ z : ℂ, 0 < Work.Bottcher.green c z →
      φ (LeanEval.ComplexAnalysis.Tantibar c z) = (starRingEnd ℂ) (φ z) ^ 2) :
    Work.ParamRays.IsDynBottcher c φ := by
  refine ⟨?_, ?_, ?_⟩
  · rw [escapeSet_eq_escapingSet c] at hcont
    exact hcont
  · intro z hz
    exact htc z (green_pos_of_escaping hz)
  · intro ε hε
    exact eventually_norm_sub_le_of_tendsto_div has hε

/-- **From a continuous Böttcher coordinate to `IsDynBottcher`.**  Continuity on the escape
set, the Böttcher equation of the quartic `p_c`, the modulus `exp ∘ green` and the tangency at
infinity suffice: the antiholomorphic equation is supplied by
`Work.Bottcher.Inverse.bottcher_comm_Tantibar_of_pMap_eq` (which replaces analyticity by the
tangency hypothesis). -/
theorem isDynBottcher_of_continuousBottcher' (c : ℂ) (φ : ℂ → ℂ)
    (hcont : ContinuousOn φ (Work.Bottcher.EscapeSet c))
    (hfe : ∀ z : ℂ, 0 < Work.Bottcher.green c z → φ (Work.Bottcher.pMap c z) = (φ z) ^ 4)
    (hmod : ∀ z : ℂ, 0 < Work.Bottcher.green c z → ‖φ z‖ = Real.exp (Work.Bottcher.green c z))
    (has : Filter.Tendsto (fun z : ℂ => φ z / z) (Filter.cocompact ℂ) (nhds (1 : ℂ))) :
    Work.ParamRays.IsDynBottcher c φ :=
  isDynBottcher_of_continuousBottcher c φ hcont hfe hmod has
    (Work.Bottcher.Inverse.bottcher_comm_Tantibar_of_pMap_eq c φ hcont hfe hmod
      (fun z hz h => by
        have h1 := hmod z hz
        rw [h, norm_zero] at h1
        exact Real.exp_ne_zero _ h1.symm)
      (fun ε hε => eventually_norm_sub_le_of_tendsto_div has hε)
      (eventually_green_pos_of_cocompact c))

theorem bottcherExists_of_mem_mandelbar :
    ∀ c : ℂ, c ∈ LeanEval.ComplexAnalysis.Mandelbar →
      ∃ φ : ℂ → ℂ, Work.ParamRays.IsDynBottcher c φ := by
  intro c hc
  obtain ⟨φ, han, hfe, hmod, has⟩ := exists_analyticBottcher_of_mem_mandelbar c hc
  exact ⟨φ, isDynBottcher_of_analyticBottcher c φ han hfe hmod has⟩

end Work.Bottcher.Contraction
