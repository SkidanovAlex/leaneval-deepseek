import ChallengeDeps
import Mathlib
import Submission.Work.Diff.C.dmRadialBridge
import Submission.Work.Diff.C.JacobiLogDeriv
import Submission.Work.Diff.C.geoCrux.radial_modulus
import Submission.GExpTranslate

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Shared vocabulary for the radial modulus bound

This module re-exports the modules that a proof of
`Work.Diff.C.geoCrux.radial_modulus_sharp` (the radial Jacobi modulus bound
`‖Z ρ‖ ≤ (sin ρ + 25 ε₁) ‖∇Z(0)‖`) needs:

* `Submission.Work.Diff.C.far_sphere_diameter` — `Work.Diff.C.fcos`, `Work.Diff.C.rdist`,
  `Work.Diff.C.HessBoundRegion`, `Work.Diff.C.rhess_rdist_bound_of_hHess`,
  `Work.Diff.C.sturm_modulus_sharp`, `Submission.RauchGlobal.IsJacobiAt`,
  `Submission.JacobiGlobal.covAlong`, `Submission.GlobalExp.GExp`;
* `Submission.Work.Diff.C.dmRadialBridge` — the bridge
  `⟪∇_{γ'}Z, Z⟫ = rhess (rdist q)(Z, Z)` for the radial variation field;
* `Submission.Work.Diff.C.JacobiLogDeriv` — `jld_log_deriv_eq_rhess`,
  `jld_log_norm_hasDerivAt`, `jml_hasDerivAt_inner_covAlong_two` (the Wronskian);
* `Submission.Work.Diff.C.geoCrux.radial_modulus` — the two-centre interface
  (`RadialCutDataProp`, `RadialTwoCentreProp`) and the proved one-dimensional extraction
  (`twoCentre_N_bound`, `twoCentre_y_upper`, `twoCentre_y_lower`, `modulus_two_sided`);
* `Submission.GExpTranslate` — the two-sided geodesic flow (for the reversed ray
  `GExp (γ τ)(s • (-v_τ)) = γ (τ - s)`).

Note: several of the imported modules contain `sorry`ed *statements* (the targets of other
agents): a proof of the lemma below must not use them (the final `#print axioms` check detects any
such use).
-/

namespace Work.Diff.C.geoCrux

end Work.Diff.C.geoCrux
