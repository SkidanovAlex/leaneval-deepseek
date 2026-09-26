import Mathlib
import Submission.Work.Smooth.SphereJordan.Defs
import Submission.Work.Smooth.JordanSeparation.onePoint_locallyPathConnected
import Submission.Work.Smooth.JordanSeparation.isSimplyConnected_of_isPreconnected_compl

/-!
# Complementary domains of continua in the Riemann sphere are simply connected

If `D ⊆ OnePoint ℂ` is a non-empty open preconnected set whose complement is preconnected, then `D`
is simply connected.  This is the classical statement that every complementary domain of a
continuum in `S²` is simply connected.  It holds on the sphere but *not* in the plane: for
`K = {0}` the component of `1` in `Kᶜ ⊆ ℂ` is `ℂ ∖ {0}` (with `π₁ = ℤ`), whereas on the sphere the
corresponding component is `S² ∖ {0} ≅ ℂ`, which is simply connected.

The mathematics is the loop-level theorem of
`Submission.Work.Smooth.JordanSeparation.loops_nullhomotopic_of_isOpen_of_isPreconnected_compl`
(every loop in an open `D` with preconnected complement is null-homotopic in `D`), plus the
elementary fact that a non-empty open preconnected subset of the (locally path connected) sphere is
path connected.

This module records the statement in the `Work.Smooth.SphereJordan` namespace, which is where the
sphere-side arguments of Pardon's theorem consume it.
-/

namespace Work.Smooth.SphereJordan

noncomputable section

open Set

/-- **Complementary domains of continua in the Riemann sphere are simply connected.**

If `D ⊆ OnePoint ℂ` is a non-empty open preconnected set whose complement is preconnected, then `D`
is simply connected. -/
theorem isSimplyConnected_of_isPreconnected_compl {D : Set (OnePoint ℂ)} (hDo : IsOpen D)
    (hDne : D.Nonempty) (hDp : IsPreconnected D) (hDc : IsPreconnected Dᶜ) :
    IsSimplyConnected D :=
  Work.Smooth.JordanSeparation.isSimplyConnected_of_isPreconnected_compl hDo hDne hDp hDc

end

end Work.Smooth.SphereJordan

