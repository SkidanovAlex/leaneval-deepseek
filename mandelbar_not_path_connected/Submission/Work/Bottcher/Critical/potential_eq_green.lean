import Mathlib
import Submission.Work.Bottcher.Defs
import Submission.Work.Escape.Defs
import Submission.Work.Bottcher.Core.norm_bottcher_domain
import Submission.Work.Bottcher.Critical.mem_CritDomain_self_iff
import Submission.Work.Bottcher.Critical.norm_Phi_eq_exp_green

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Bottcher.Critical

/-- For a parameter `c` outside the mandelbar the potential `log ‖Φ c‖` of the parameter is the
Green function of the critical value `c = T_c 0`:

`Φ c = φ_c c` has modulus `exp (G_c c)` off the mandelbar (`norm_Phi_eq_exp_green`), and
`Real.log` inverts `Real.exp`, so `log ‖Φ c‖ = G_c c`. -/
theorem potential_eq_green (c : ℂ) (hc : c ∉ LeanEval.ComplexAnalysis.Mandelbar) :
    Work.Bottcher.potential c = Work.Bottcher.green c c := by
  classical
  have hnorm : ‖Work.Bottcher.Phi c‖ = Real.exp (Work.Bottcher.green c c) :=
    norm_Phi_eq_exp_green c hc
  simp only [Work.Bottcher.potential, hc, ite_false]
  rw [hnorm, Real.log_exp]

end Work.Bottcher.Critical
