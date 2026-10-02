import Mathlib
import Submission.Work.Bottcher.Defs
import Submission.Work.Bottcher.CritBasic
import Submission.Work.Escape.differentiableOn_of_continuousOn_exp_eq

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Bottcher.Contraction

/--
A continuous logarithm of the normalised Böttcher factor `normFactor c = pMap c z / z^4` on the
critical domain `Work.Bottcher.CritDomain c = {z | greenParam c < green c z}` is analytic there.

This generalises `Work.Bottcher.Contraction.analyticOnNhd_log_of_exp_eq` from the escape set
`EscapeSet c = {G_c > 0}` of a mandelbar parameter to the critical domain of an arbitrary
parameter.  Everything needed is in `Work.Bottcher.CritBasic`:

* `isOpen_CritDomain c`,
* `differentiableOn_normFactor_CritDomain c`,
* `normFactor_ne_zero_of_mem_CritDomain`,

so the result follows from the general fact
`Work.Escape.differentiableOn_of_continuousOn_exp_eq`
(a continuous logarithm of a holomorphic non-vanishing function is holomorphic) followed by
`DifferentiableOn.analyticOnNhd`.
-/
theorem analyticOnNhd_log_of_exp_eq_CritDomain (c : ℂ) {L : ℂ → ℂ}
    (hcont : ContinuousOn L (Work.Bottcher.CritDomain c))
    (hexp : ∀ z : ℂ, z ∈ Work.Bottcher.CritDomain c →
      Complex.exp (L z) = Work.Bottcher.normFactor c z) :
    AnalyticOnNhd ℂ L (Work.Bottcher.CritDomain c) := by
  refine DifferentiableOn.analyticOnNhd ?_ (Work.Bottcher.CritBasic.isOpen_CritDomain c)
  exact Work.Escape.differentiableOn_of_continuousOn_exp_eq
    (Work.Bottcher.CritBasic.isOpen_CritDomain c) hcont
    (Work.Bottcher.CritBasic.differentiableOn_normFactor_CritDomain c)
    (fun z hz => Work.Bottcher.CritBasic.normFactor_ne_zero_of_mem_CritDomain hz)
    hexp

end Work.Bottcher.Contraction
