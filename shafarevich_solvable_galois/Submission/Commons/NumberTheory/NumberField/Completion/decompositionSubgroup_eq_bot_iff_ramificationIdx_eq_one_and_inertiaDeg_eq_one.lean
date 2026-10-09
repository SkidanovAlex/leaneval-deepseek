import Mathlib
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_algEquiv_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.NumberTheory.NumberField.Completion

/-- **The decomposition group of a place is trivial exactly when the place is unramified with
residue degree one.**

For a finite Galois extension `L / K` of number fields, a finite place `p` of `K` and a finite
place `w` of `L` lying over `p`, the decomposition group `D_w ≤ Gal(L/K)` has order the local
degree `e(w|p) · f(w|p)` (`card_decompositionSubgroup`).  Since a group has trivial cardinality
`1` exactly when it is the trivial subgroup (`Subgroup.eq_bot_iff_card`), the decomposition group
is trivial if and only if `e · f = 1`, i.e. if and only if both the ramification index and the
inertia degree are one. -/
theorem decompositionSubgroup_eq_bot_iff_ramificationIdx_eq_one_and_inertiaDeg_eq_one
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hw : w.asIdeal.LiesOver p.asIdeal) :
    Commons.NumberTheory.NumberField.Completion.decompositionSubgroup (K := K) w = ⊥ ↔
      p.asIdeal.ramificationIdxIn (NumberField.RingOfIntegers L) = 1 ∧
        p.asIdeal.inertiaDegIn (NumberField.RingOfIntegers L) = 1 := by
  rw [Subgroup.eq_bot_iff_card (decompositionSubgroup (K := K) w),
    card_decompositionSubgroup p w hw]
  exact mul_eq_one

end Commons.NumberTheory.NumberField.Completion
