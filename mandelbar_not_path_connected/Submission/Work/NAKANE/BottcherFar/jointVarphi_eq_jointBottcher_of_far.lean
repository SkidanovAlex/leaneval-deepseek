import Mathlib
import Submission.Work.NAKANE.Defs
import Submission.Work.NAKANE.BottcherFar.mem_critDomain_of_farRadius_lt
import Submission.Work.Bottcher.Core.eq_bottcher_of_analytic_tail

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.NAKANE.BottcherFar

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)
open scoped ComplexConjugate

/-- The escape radius of the family never exceeds the coarse far radius. -/
theorem escapeRadius_le_farRadius (c : ℂ) :
    Work.Bottcher.escapeRadius c ≤ Work.NAKANE.farRadius ‖c‖ := by
  rw [Work.Bottcher.escapeRadius, Work.NAKANE.farRadius]
  set M : ℝ := max 2 (1 + ‖c‖)
  have h1 : 1 + ‖c‖ ≤ M := le_max_right _ _
  have hMge : (2 : ℝ) ≤ M := le_max_left _ _
  have hMsq : M ≤ M ^ 2 := by nlinarith
  nlinarith [h1, hMsq, hMge]

/-- `p_c` is the second iterate of `T_c`, written out. -/
theorem pMap_eq_Tantibar_comp (c z : ℂ) :
    Work.Bottcher.pMap c z = Tantibar c (Tantibar c z) := by
  rw [Work.Bottcher.pMap_eq_iterate_two,
    show (2 : ℕ) = 1 + 1 from rfl, Function.iterate_add_apply]
  simp only [Function.iterate_one]

/-- The functional equation of the canonical coordinate for `p_c`. -/
theorem varphiCrit_comm_pMap {c z : ℂ} (hz : z ∈ Work.ParamRays.critDomain c) :
    Work.Bottcher.varphiCrit c (Work.Bottcher.pMap c z)
      = (Work.Bottcher.varphiCrit c z) ^ 4 := by
  have h1 : Tantibar c z ∈ Work.ParamRays.critDomain c :=
    Work.ParamRays.Tantibar_mem_critDomain hz
  rw [pMap_eq_Tantibar_comp, Work.Bottcher.varphiCrit_comm_Tantibar h1,
    Work.Bottcher.varphiCrit_comm_Tantibar hz]
  simp only [map_pow, Complex.conj_conj]
  ring

/-- **Far beyond the critical domain the canonical Böttcher coordinate of `T_c` *is* the explicit
product formula of `Work.Bottcher`.**  For `‖z‖ > farRadius ‖c‖`
(`farRadius C = 2 * (max 2 (1+C))^2 + 2`, `Work.NAKANE.farRadius`), `varphiCrit c z = bottcher c z`.

Route: `Work.Bottcher.Core.eq_bottcher_of_analytic_tail c R hR (varphiCrit c) han hfe hmod has`
with `R := farRadius ‖c‖` gives exactly this, for any `ψ` which is analytic on `{R < ‖z‖}`, solves
`ψ (p_c z) = ψ z ^ 4` there, has `‖ψ z‖ = exp (G_c z)` there and is tangent to the identity at
infinity.  For `ψ := varphiCrit c` all four hold:

* analyticity: `Work.Bottcher.analyticOnNhd_varphiCrit c` on `CritDomain c`, restricted to
  `{R < ‖z‖}` via `{R < ‖z‖} ⊆ CritDomain c`
  (`Work.NAKANE.BottcherFar.mem_critDomain_of_farRadius_lt`, already proved in
  `Submission/Work/NAKANE/BottcherFar/mem_critDomain_of_farRadius_lt.lean`; it is stated for
  `Work.ParamRays.critDomain`, which is `Work.Bottcher.CritDomain` by
  `Work.Bottcher.CritBasic.critDomain_eq`);
* `p_c`-equation: `Work.Bottcher.varphiCrit_comm_Tantibar` twice, using
  `Work.Bottcher.CritBasic.Tantibar_mem_CritDomain` for the invariance of the domain and
  `conj (conj w ^ 2) ^ 2 = w ^ 4`; note `p_c z = T_c (T_c z)`
  (`Work.Bottcher.pMap_eq_iterate_two`);
* modulus: `Work.Bottcher.norm_varphiCrit` (needs `z ∈ CritDomain c`, again from the inclusion);
* tangency: the third field of `Work.Bottcher.isCritBottcher_varphiCrit`
  (`varphiCrit_div_tendsto_one`).

`hR : escapeRadius c ≤ farRadius ‖c‖` holds since `escapeRadius c = 2 (1 + ‖c‖) ≤ 2 (max 2 (1+‖c‖))^2 + 2`. -/
theorem jointVarphi_eq_jointBottcher_of_far {c z : ℂ}
    (hz : Work.NAKANE.farRadius ‖c‖ < ‖z‖) :
    Work.NAKANE.jointVarphi (c, z) = Work.NAKANE.jointBottcher (c, z) := by
  rw [Work.NAKANE.jointVarphi_apply, Work.NAKANE.jointBottcher_apply]
  refine Work.Bottcher.Core.eq_bottcher_of_analytic_tail c (Work.NAKANE.farRadius ‖c‖)
    (escapeRadius_le_farRadius c) (Work.Bottcher.varphiCrit c) ?_ ?_ ?_ ?_ z hz
  · exact (Work.Bottcher.analyticOnNhd_varphiCrit c).mono
      (fun w hw => mem_critDomain_of_farRadius_lt hw)
  · intro w hw
    exact varphiCrit_comm_pMap (mem_critDomain_of_farRadius_lt hw)
  · intro w hw
    exact Work.Bottcher.norm_varphiCrit (mem_critDomain_of_farRadius_lt hw)
  · exact Work.Bottcher.varphiCrit_div_tendsto_one c

end Work.NAKANE.BottcherFar
