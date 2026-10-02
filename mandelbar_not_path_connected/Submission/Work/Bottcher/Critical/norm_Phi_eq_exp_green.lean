import Mathlib
import Submission.Work.Bottcher.Defs
import Submission.Work.Escape.Defs
import Submission.Work.Bottcher.Core.norm_bottcher_domain
import Submission.Work.Bottcher.Critical.mem_CritDomain_self_iff

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Bottcher.Critical

/-- For a parameter `c` outside the mandelbar the critical value `c` lies in its own critical
domain, so the norm of the parameter Böttcher coordinate `Φ c = φ_c c` is the exponential of
the Green function of the critical value, `‖Φ c‖ = exp (G_c c)`. -/
theorem norm_Phi_eq_exp_green (c : ℂ) (hc : c ∉ LeanEval.ComplexAnalysis.Mandelbar) :
    ‖Work.Bottcher.Phi c‖ = Real.exp (Work.Bottcher.green c c) := by
  have hmem : c ∈ Work.Bottcher.CritDomain c :=
    (Work.Bottcher.Critical.mem_CritDomain_self_iff c).mpr hc
  rw [Work.Bottcher.Phi_eq_bottcher hc]
  exact Work.Bottcher.Core.norm_bottcher_domain c c hmem

end Work.Bottcher.Critical
