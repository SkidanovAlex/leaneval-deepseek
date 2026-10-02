import Mathlib
import Submission.Work.Bottcher.Defs
import Submission.Work.Bottcher.CritBasic
import Submission.Work.Bottcher.Contraction.analyticOnNhd_log_of_exp_eq_CritDomain
import Submission.Work.Bottcher.Contraction.exists_continuous_log_of_monodromy_CritDomain
import Submission.Work.Bottcher.Contraction.liftChange_normFactorPath_eq_zero_of_preconnected
import Submission.Work.Bottcher.Contraction.isPreconnected_green_le_greenParam

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Bottcher.Contraction

open Filter
open scoped Topology

/--
Generalises `Work.Bottcher.Contraction.exists_analytic_log_normFactor_of_mem_mandelbar`
(there: `c ∈ M*`, domain `EscapeSet c = {G_c > 0}`) to an arbitrary parameter and the critical
domain `CritDomain c = {G_c > G_c 0}`.

Assume the sublevel set `{z | green c z ≤ greenParam c}` is preconnected (true for every `c` by
`Work.Bottcher.Contraction.isPreconnected_green_le_greenParam`).  Then the normalised Böttcher
factor `normFactor c z = pMap c z / z^4` has a holomorphic logarithm on `CritDomain c`, vanishing
at infinity.

Assembly of three already-deliverable lemmas:

1. `Work.Bottcher.Contraction.liftChange_normFactorPath_eq_zero_of_preconnected c
   (greenParam c) hK le_rfl` gives trivial monodromy for every closed loop in `CritDomain c`
   (a loop in `CritDomain c` satisfies `greenParam c < green c (γ t)` by definition).
2. `Work.Bottcher.Contraction.exists_continuous_log_of_monodromy_CritDomain c` gives a continuous
   `L` with `exp (L z) = normFactor c z` on `CritDomain c` and `L → 0` at infinity.
3. `Work.Bottcher.Contraction.analyticOnNhd_log_of_exp_eq_CritDomain c` upgrades `L` to an
   analytic function.
-/
theorem exists_analytic_log_normFactor_of_CritDomain (c : ℂ)
    (hK : IsPreconnected {z : ℂ | Work.Bottcher.green c z ≤ Work.Bottcher.greenParam c}) :
    ∃ L : ℂ → ℂ,
      AnalyticOnNhd ℂ L (Work.Bottcher.CritDomain c) ∧
        (∀ z : ℂ, z ∈ Work.Bottcher.CritDomain c →
          Complex.exp (L z) = Work.Bottcher.normFactor c z) ∧
        Filter.Tendsto L (Filter.cocompact ℂ) (nhds (0 : ℂ)) := by
  -- Trivial monodromy for every closed loop in `CritDomain c`.
  have hmono : ∀ (γ : C(unitInterval, ℂ)) (hloop : γ 1 = γ 0)
      (hγ : ∀ t, γ t ∈ Work.Bottcher.CritDomain c) (hγne : ∀ t, γ t ≠ 0)
      (h : ∀ t, Work.Bottcher.Contraction.normFactorPath c γ hγne t ≠ 0),
      Work.Bottcher.Contraction.liftChange
        (Work.Bottcher.Contraction.normFactorPath c γ hγne) h = 0 := by
    intro γ hloop hγ hγne h
    refine Work.Bottcher.Contraction.liftChange_normFactorPath_eq_zero_of_preconnected c
      (Work.Bottcher.greenParam c) hK le_rfl γ hloop ?_ hγne h
    intro t
    exact (Work.Bottcher.mem_CritDomain.mp (hγ t))
  -- A continuous logarithm vanishing at infinity ...
  obtain ⟨L, hLc, hLexp, hLt⟩ :=
    Work.Bottcher.Contraction.exists_continuous_log_of_monodromy_CritDomain c hmono
  -- ... is automatically holomorphic.
  exact ⟨L, Work.Bottcher.Contraction.analyticOnNhd_log_of_exp_eq_CritDomain c hLc hLexp,
    hLexp, hLt⟩

end Work.Bottcher.Contraction
