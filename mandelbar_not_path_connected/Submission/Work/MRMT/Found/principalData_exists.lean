/-
Work.MRMT.Found — existence of the principal solution data (the "limit layer" of the
measurable Riemann mapping theorem).

Given an admissible Beltrami coefficient `μ` (measurable, `‖μ‖ ≤ k < 1` a.e., bounded support)
this produces the `PrincipalData μ` record:

* mollify `μ` to smooth compactly supported `μ n` with `‖μ n‖ ≤ k` everywhere and `μ n → μ` a.e.
  (`mollify_admissible`);
* let `F n` be the `C¹`-diffeomorphic solution for `μ n`
  (`exists_contDiff_principal_of_contDiff`, the smooth case of Ahlfors–Bers);
* `forward_limit_pd` supplies a locally uniform limit `φ` together with the uniform decay
  `φ z = z + O(1/‖z‖)`, `F n z = z + O(1/‖z‖)` (with constants independent of `n`) and the
  `L²_loc`-convergence of `dz (F n)`;
* `inverse_limit` supplies the convergence of the inverses to `φ.symm` and the two-sided inverse
  identities, so that `φ` is a homeomorphism.

The analytic content (uniform `L²` bound `‖∂̄F n‖₂ ≤ (1-k)⁻¹ k √(πM²)`, uniform decay of the
Cauchy transform, the Courant–Lebesgue modulus, the `L²`-convergence of the Ahlfors–Bers
solutions) lives in the auxiliary modules `Found/fw_*` and `Found/principalData_aux`; the
*assembly* of the record out of an approximating family is the reusable lemma
`Work.MRMT.Found.principalData_of_approx` (`Submission/Work/MRMTCont/PrincipalDataApprox.lean`),
which this file now applies.

This file owns the theorem `Work.MRMT.Found.principalData_exists`.
-/
import Mathlib
import Submission.Work.MRMT.Found.Defs
import Submission.Work.MRMT.Found.mollify_admissible
import Submission.Work.MRMT.Found.exists_contDiff_principal_of_contDiff
import Submission.Work.MRMT.Found.forward_limit_pd
import Submission.Work.MRMT.Found.inverse_limit
import Submission.Work.MRMTCont.PrincipalDataApprox

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open MeasureTheory Filter Topology Complex Function
open scoped Distributions Topology ENNReal

namespace Work.MRMT.Found

open Work.MRMT

theorem principalData_exists {μ : ℂ → ℂ} (hμ : Admissible μ) : Nonempty (PrincipalData μ) := by
  classical
  obtain ⟨k, M, μn, hk0, hk1, hM0, hμbd, _hμsupp, hμnC, hμnS, hμnB, hμnSp, hμnT⟩ :=
    mollify_admissible hμ
  -- the smooth approximants admit `C¹`-diffeomorphic solutions
  choose F hFC hFCS hFB hFD using fun n =>
    exists_contDiff_principal_of_contDiff (hμnC n) (hμnS n) hk1 (hμnB n)
  -- assemble the record from the extracted limit layer
  obtain ⟨d, _hd⟩ :=
    principalData_of_approx hk0 hk1 hM0 hμnC hμnS hμnB hμnSp hμnT hμbd hFC hFCS hFB hFD
  exact ⟨d⟩

end Work.MRMT.Found
