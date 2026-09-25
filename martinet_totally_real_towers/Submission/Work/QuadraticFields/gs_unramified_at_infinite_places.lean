import Mathlib
import Submission.Work.QuadraticFields.gsF_isTotallyReal
import Submission.Work.QuadraticFields.gsM_isTotallyReal
import Submission.Work.QuadraticFields.CertificateReal

/-!
# The certificate `M/F` is unramified at the infinite places

The field extension of the totally real certificate is

  `F = gsF = ℚ(√(5·13·17·29·37·41·53)) ⊆ M = gsM = ℚ(√5, √13, √17, √29, √37, √41, √53)`.

Since `gsM` is **totally real** (`Work.QuadraticFields.gsM_isTotallyReal`), every infinite place of
`gsM` is real, and a real infinite place is always unramified
(Mathlib's `NumberField.InfinitePlace.IsReal.isUnramified`).  Hence the extension `M/F` is
unramified at all infinite places, which is the hypothesis required by the Hilbert-tower /
Golod–Shafarevich arithmetic input over the totally real base `gsF`.

## Main results

* `Work.QuadraticFields.isUnramifiedAtInfinitePlaces_of_isTotallyReal` -- a general form: an
  extension of number fields whose top field is totally real is unramified at infinity.
* `Work.QuadraticFields.gs_unramified_at_infinite_places` -- the certificate case.
-/

namespace Work.QuadraticFields

open NumberField

set_option autoImplicit false

noncomputable section

/-- **An extension of number fields with totally real top field is unramified at the infinite
places.**

For an infinite place `w` of the totally real field `K`, `w` is real, and
`NumberField.InfinitePlace.IsReal.isUnramified` says that a real infinite place is unramified. -/
theorem isUnramifiedAtInfinitePlaces_of_isTotallyReal {k K : Type*} [Field k] [Field K]
    [Algebra k K] [NumberField.IsTotallyReal K] : IsUnramifiedAtInfinitePlaces k K :=
  ⟨fun w => (NumberField.IsTotallyReal.isReal w).isUnramified (k := k)⟩

/-- **`M/F` is unramified at the infinite places.**

`gsM` is totally real (`Work.QuadraticFields.gsM_isTotallyReal`), so the general criterion
`isUnramifiedAtInfinitePlaces_of_isTotallyReal` applies with `k = ↥gsF`, `K = gsM`. -/
theorem gs_unramified_at_infinite_places : IsUnramifiedAtInfinitePlaces ↥gsF gsM := by
  have : NumberField.IsTotallyReal gsM := gsM_isTotallyReal
  exact isUnramifiedAtInfinitePlaces_of_isTotallyReal

end

end Work.QuadraticFields
