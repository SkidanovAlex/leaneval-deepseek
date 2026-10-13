import Mathlib
import Submission.Work.WilE9G.Sard.morseDefs
import Submission.Work.WilE9G.Sard.chartDiffBound
import Submission.Work.WilE9G.Sard.flatAtChartUpgrade

/-!
# Flatness of `f ∘ γ` from flatness of `fderiv f ∘ γ`

If the differential of `f`, evaluated along the chart `γ`, is flat of order `q - 1` at an interior
point `u` of the chart, then `f ∘ γ` is flat of order `q` at `u` (in the form of a bound on
`‖f (γ w) - f (γ u)‖`).

This is Morse's Lemma 3.2 applied to the shifted map `y ↦ f y - f (γ u)`, whose differential
coincides with that of `f` (`fderiv_sub_const`); the Lipschitz bound and differentiability of the
chart near the interior point `u` are supplied by `Work.WilE9G.Sard.chartDiffBound` inside
`Work.WilE9G.Sard.flatAtChartUpgrade`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.WilE9G.Sard

theorem subFlatOfFderivFlat {d n q : ℕ} (hq : 1 ≤ q)
    {f : (Fin d → ℝ) → (Fin n → ℝ)} (hf : ContDiff ℝ 1 f)
    (C : Work.WilE9G.Sard.ChartDatum d) {u : Fin C.t → ℝ}
    (hu : u ∈ Metric.ball C.base C.rad)
    (hflat : ∀ ε > 0, ∃ ρ > 0, ∀ v, ‖v - u‖ ≤ ρ →
      ‖fderiv ℝ f (C.γ v)‖ ≤ ε * ‖v - u‖ ^ (q - 1)) :
    ∀ ε > 0, ∃ ρ > 0, ∀ w, ‖w - u‖ ≤ ρ → ‖f (C.γ w) - f (C.γ u)‖ ≤ ε * ‖w - u‖ ^ q := by
  -- Flatness of the differential of the shifted map `y ↦ f y - f (γ u)` (same differential,
  -- `fderiv_sub_const`), which vanishes at `γ u`.
  have hflat' : FlatAt (fun z => fderiv ℝ (fun y : Fin d → ℝ => f y - f (C.γ u)) (C.γ z))
      (q - 1) u := by
    intro ε hε
    obtain ⟨ρ, hρ, h⟩ := hflat ε hε
    exact ⟨ρ, hρ, fun v hv => by
      change ‖fderiv ℝ (fun y : Fin d → ℝ => f y - f (C.γ u)) (C.γ v)‖
        ≤ ε * ‖v - u‖ ^ (q - 1)
      rw [fderiv_sub_const]
      exact h v hv⟩
  -- Morse's Lemma 3.2 along the chart.
  have hup := flatAtChartUpgrade (m := q) hq
    (F := fun y : Fin d → ℝ => f y - f (C.γ u)) (U := Set.univ)
    isOpen_univ (hf.sub contDiff_const).contDiffOn C hu (Set.mem_univ _) (sub_self _) hflat'
  intro ε hε
  obtain ⟨ρ, hρ, h⟩ := hup ε hε
  exact ⟨ρ, hρ, fun w hw => by simpa using h w hw⟩

end Work.WilE9G.Sard
