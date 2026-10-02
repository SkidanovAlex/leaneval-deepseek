import Mathlib
import Submission.Work.Bottcher.Defs
import Submission.Work.Escape.Defs
import Submission.Work.Escape.Basic
import Submission.Work.Escape.tendsto_norm_iterate_atTop

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The mandelbar is bounded away from infinity

For a parameter `c` of large modulus the critical orbit of the tricorn map
`T̄_c(z) = z̄² + c` escapes to infinity: `T̄_c(0) = c` and the second critical value
`T̄_c(T̄_c(0)) = T̄_c(c) = c̄² + c` already has modulus at least `‖c‖² - ‖c‖ > max 2 ‖c‖`
once `‖c‖ ≥ 4`.  The escaping region `{w | max 2 ‖c‖ < ‖w‖}` of the degree-`2`
monic-growth map `T̄_c` (`Work.Escape.MonicGrowth`) is forward invariant with norms
growing to infinity (`Work.Escape.tendsto_norm_iterate_atTop`).  Hence every `c` with
`‖c‖ ≥ 4` lies outside the mandelbar, and gluing this with the cocompact filter gives
`∀ᶠ c in cocompact ℂ, c ∉ M*`.
-/

namespace Work.Bottcher.Green

open Filter
open scoped Topology

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-- **Escape for large parameters.**  If `‖c‖ ≥ 4` then the critical orbit of `T̄_c` is
unbounded, so `c` lies outside the mandelbar. -/
theorem not_mem_mandelbar_of_four_le_norm (c : ℂ) (hc : 4 ≤ ‖c‖) : c ∉ Mandelbar := by
  rintro ⟨M, hM⟩
  have hmg : Work.Escape.MonicGrowth (Tantibar c) 2 ‖c‖ := Work.Escape.monicGrowth_Tantibar c
  have hTc : Tantibar c 0 = c := by simp [LeanEval.ComplexAnalysis.Tantibar]
  -- The second critical value already lies in the escaping region.
  have hzmem : Tantibar c (Tantibar c 0) ∈ Work.Escape.escapeRegion ‖c‖ := by
    rw [Work.Escape.mem_escapeRegion]
    have hge : ‖c‖ ^ 2 - ‖c‖ ≤ ‖Tantibar c (Tantibar c 0)‖ := by
      have h := Work.Escape.norm_Td_ge 2 c c
      rw [hTc]
      exact h
    have hlt : max 2 ‖c‖ < ‖c‖ ^ 2 - ‖c‖ := by
      rw [max_lt_iff]
      exact ⟨by nlinarith [norm_nonneg c], by nlinarith [norm_nonneg c]⟩
    linarith
  have hten : Tendsto (fun n : ℕ => ‖(Tantibar c)^[n] (Tantibar c (Tantibar c 0))‖) atTop atTop :=
    Work.Escape.tendsto_norm_iterate_atTop (Tantibar c) 2 ‖c‖ hmg le_rfl hzmem
  rw [Filter.tendsto_atTop_atTop] at hten
  obtain ⟨i, hi⟩ := hten (M + 1)
  have h1 : M + 1 ≤ ‖(Tantibar c)^[i] (Tantibar c (Tantibar c 0))‖ := hi i le_rfl
  have h2 : ‖(Tantibar c)^[i] (Tantibar c (Tantibar c 0))‖ ≤ M := by
    have htwo : (Tantibar c)^[2] 0 = Tantibar c (Tantibar c 0) := by simp
    have hidx : (Tantibar c)^[i] (Tantibar c (Tantibar c 0)) = (Tantibar c)^[i + 2] 0 := by
      rw [← htwo, ← Function.iterate_add_apply]
    rw [hidx]
    exact hM (i + 2)
  linarith

theorem eventually_not_mem_mandelbar :
    ∀ᶠ c : ℂ in Filter.cocompact ℂ, c ∉ LeanEval.ComplexAnalysis.Mandelbar := by
  filter_upwards [tendsto_norm_cocompact_atTop.eventually_ge_atTop (4 : ℝ)] with c hc
  exact not_mem_mandelbar_of_four_le_norm c hc

end Work.Bottcher.Green
