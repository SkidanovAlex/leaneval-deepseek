import Mathlib
import Submission.Work.ORHughesFree.SkewLaurentSeriesInstances
import Submission.Work.ORHughesFree.SkewLaurentSeries.exists_injective_ringHom_skewMonoidAlgebra
import Submission.Work.ORHughesFree.Prop51.coeff_zpowT
import Submission.Work.ORHughesFree.NaturalExtension.envelopeDefs

/-!
# The image of the monomial `tᵏ` of the skew monoid algebra under `A[t;τ] → A((t;τ))`

The skew monoid algebra `A[t;τ] = SkewMonoidAlgebra A (Multiplicative ℤ)` embeds in the skew
Laurent series ring `A((t;τ))` via `SkewLaurentSeries.toRingHom`.  The assignment
`k ↦ single (ofAdd k) 1` is the obvious monomial `tᵏ` of the monoid algebra, and its image is the
`k`-th integer power of the unit `t` of `A((t;τ))`.

Both sides are compared coefficientwise: `single (ofAdd k) 1` has `ofAdd n`-coefficient
`if n = k then 1 else 0`, and by `Prop51.coeff_zpowT` the `n`-th coefficient of `tᵏ` is the same.
-/

namespace Work.ORHughesFree.Section6

open Work.ORHughesFree

/-- The `n`-th coefficient of the integer power `tᵏ` of the unit `t` of `A((t;τ))` is `1` if
`n = k` and `0` otherwise. -/
theorem skewLaurentSeriesT_zpow_apply {A : Type} [Ring A]
    [MulSemiringAction (Multiplicative ℤ) A] (k n : ℤ) :
    (↑((Work.ORHughesFree.skewLaurentSeriesT A) ^ k : (Work.ORHughesFree.SkewLaurentSeries A)ˣ) :
        Work.ORHughesFree.SkewLaurentSeries A).1 n = if n = k then 1 else 0 := by
  have h := Work.ORHughesFree.Prop51.coeff_zpowT (A := A) (1 : A) k n
  rw [map_one (Work.ORHughesFree.skewLaurentCoeff A), one_mul] at h
  exact h

/-- The `n`-th coefficient of the image of the monomial `single (ofAdd k) 1` of the skew monoid
algebra is `1` if `n = k` and `0` otherwise. -/
theorem toRingHom_single_ofAdd_apply {A : Type} [Ring A]
    [MulSemiringAction (Multiplicative ℤ) A] (k n : ℤ) :
    (Work.ORHughesFree.SkewLaurentSeries.toRingHom
        (SkewMonoidAlgebra.single (Multiplicative.ofAdd k) (1 : A))).1 n =
      if n = k then 1 else 0 := by
  change (Work.ORHughesFree.SkewLaurentSeries.toSeries
      (SkewMonoidAlgebra.single (Multiplicative.ofAdd k) (1 : A))).1 n = _
  rw [SkewLaurentSeries.toSeries_apply, SkewMonoidAlgebra.coeff_single, Finsupp.single_apply]
  by_cases h : n = k
  · rw [if_pos (by rw [h]), if_pos h]
  · rw [if_neg (fun hh => h (Multiplicative.ofAdd.injective hh).symm), if_neg h]

theorem toRingHom_skewLaurentT_pow {A : Type} [Ring A]
    [MulSemiringAction (Multiplicative ℤ) A] (k : ℤ) :
    Work.ORHughesFree.SkewLaurentSeries.toRingHom
        (SkewMonoidAlgebra.single (Multiplicative.ofAdd k) (1 : A)) =
      (((Work.ORHughesFree.skewLaurentSeriesT A) ^ k : (Work.ORHughesFree.SkewLaurentSeries A)ˣ) :
        Work.ORHughesFree.SkewLaurentSeries A) := by
  apply Subtype.ext
  funext n
  rw [toRingHom_single_ofAdd_apply, skewLaurentSeriesT_zpow_apply]

end Work.ORHughesFree.Section6
