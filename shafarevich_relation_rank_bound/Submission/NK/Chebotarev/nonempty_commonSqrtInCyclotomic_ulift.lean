import Mathlib
import Submission.NK.Chebotarev.CommonSqrtInCyclotomic
import Submission.NK.Chebotarev.ExistsSqrtInCyclotomic

/-!
# Universe lifting for `CommonSqrtInCyclotomic`

`NK.Chebotarev.CommonSqrtInCyclotomic r d` records a cyclotomic field containing square roots of
all the rationals `d i`.  Since the cyclotomic field it records lives in a fixed universe, a
statement about it can only be used at that universe level; the present file removes the dependence
on the universe level by transporting the field along `ULift`.

The argument is exactly the one of `NK.Chebotarev.nonempty_sqrtInCyclotomic_ulift` (the
single-square-root case): `ULift.algEquiv` is a `ℚ`-algebra equivalence, so a cyclotomic extension
structure and a number field structure transfer along it
(`IsCyclotomicExtension.equiv`, `NumberField.of_ringEquiv`), and the square roots are transported
with `ULift.up` because `ULift.down` is a ring homomorphism compatible with `algebraMap`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace NK.Chebotarev

universe u

/-- **Universe lifting for `CommonSqrtInCyclotomic`.**  If a finite family of rationals has square
roots in a common cyclotomic field in universe `0`, then it has square roots in a common cyclotomic
field in any universe level `u`. -/
theorem nonempty_commonSqrtInCyclotomic_ulift (r : ℕ) (d : Fin r → ℚ)
    (h : Nonempty (NK.Chebotarev.CommonSqrtInCyclotomic.{0} r d)) :
    Nonempty (NK.Chebotarev.CommonSqrtInCyclotomic.{u} r d) := by
  obtain ⟨S⟩ := h
  -- fix the `Algebra ℚ (ULift S.F)` instance, so that the local cyclotomic and number field
  -- structures below are stated for the *transported* algebra structure `ULift.algebra`
  letI : Algebra ℚ (ULift.{u} S.F) := ULift.algebra
  haveI : IsCyclotomicExtension {S.n} ℚ (ULift.{u} S.F) := by
    letI := S.cycloF
    exact IsCyclotomicExtension.equiv {S.n} ℚ S.F (ULift.algEquiv (R := ℚ) (A := S.F)).symm
  haveI : NumberField (ULift.{u} S.F) :=
    NumberField.of_ringEquiv S.F (ULift.{u} S.F) (ULift.ringEquiv (R := S.F)).symm
  refine ⟨{ n := S.n, hn := S.hn, F := ULift.{u} S.F, s := fun i => ULift.up (S.s i),
            s_sq := ?_ }⟩
  intro i
  apply ULift.down_injective
  simp only [ULift.pow_down, ULift.down_algebraMap]
  exact S.s_sq i

end NK.Chebotarev
