import Mathlib.NumberTheory.LSeries.RiemannZeta

namespace Commons.NumberTheory.Zeta

/-- The Riemann zeta function is measurable.

Mathlib proves that `riemannZeta` is analytic (hence continuous) away from the
single point `s = 1`: `differentiableOn_riemannZeta`.  A function that is
continuous outside a finite (in particular countable) set is measurable, via
`measurable_of_continuousOn_compl_singleton`. -/
lemma measurable_riemannZeta : Measurable riemannZeta :=
  measurable_of_continuousOn_compl_singleton 1 differentiableOn_riemannZeta.continuousOn

end Commons.NumberTheory.Zeta