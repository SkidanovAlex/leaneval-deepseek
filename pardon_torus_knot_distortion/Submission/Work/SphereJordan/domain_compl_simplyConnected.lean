import Mathlib
import Submission.Work.SphereJordan.plane_crux
import Submission.Work.SphereJordan.sphere_of_plane_crux

/-!
# Complementary domains of continua in the Riemann sphere are simply connected

The target of this file: if `D ⊆ S²` is open, non-empty and preconnected and its complement is
preconnected, then `D` is simply connected.

Everything is reduced here to the single missing input `Work.SphereJordan.LWalkApprox` (the lattice
approximation of an arbitrary loop in an open `U ⊆ ℂ`, see `plane_crux.lean`):

* `Work.SphereJordan.plane_crux_of_approx` gives the plane crux
  (`IsSimplyConnected U` for `U` open preconnected with preconnected complement in the sphere)
  from `LWalkApprox` together with the peel `Work.SphereJordan.lwalk_nullhomotopic`;
* `Work.SphereJordan.domain_compl_simplyConnected_of_plane_crux` transports the plane crux to the
  sphere by a Möbius homeomorphism moving a point of `Dᶜ` to `∞`.

See `STATUS_domain_compl.md` in this directory for the full state and the design of the missing
approximation.
-/

namespace Work.SphereJordan

theorem domain_compl_simplyConnected {D : Set (OnePoint ℂ)} (hDopen : IsOpen D)
    (hDne : D.Nonempty) (hDpre : IsPreconnected D) (hDcompl : IsPreconnected Dᶜ) :
    IsSimplyConnected D :=
  domain_compl_simplyConnected_of_plane_crux
    (fun hUo hUne hUpre hpre => plane_crux_of_approx LWalkApprox_proof hUo hUne hUpre hpre)
    hDopen hDne hDpre hDcompl

end Work.SphereJordan
