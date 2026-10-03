/-
# `Submission.Work.FIArea7.mk_injOn_primarySet`

`Associates.mk` is injective on the primary Gaussian integers of norm `M`: the elements of
`primarySet M` are pairwise non-associate.

Indeed, `Associates.mk z = Associates.mk w` means `z` and `w` are associated, i.e. `w = z * ε` for
a unit `ε`.  A primary element `z` is nonzero (its real part is odd) and satisfies
`z.im ≡ z.re - 1 (mod 4)` with `z.re` odd and `z.im` even; writing this congruence in `ZMod 4` and
applying `unit_eq_one_of_primary` to the primary element `z * ε` gives `ε = 1`, hence `w = z`.

(Used by `Submission.Work.FIArea7.primarySet_card_le_tau`, where the injectivity of
`Associates.mk` on `primarySet M` turns `(primarySet M).card` into the number of associate classes
of norm `M`.)
-/
import Mathlib
import Submission.Work.FIArea7.prop232Defs
import Submission.Commons.NumberTheory.GaussianInt.two_squares_repr_count
import Submission.Commons.NumberTheory.GaussianInt.two_squares_repr_count_le_tau_of_pos
import Submission.Commons.NumberTheory.GaussianInt.primary_associate_exists_unique

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace Work.FIArea7

/-- The primary condition `z.im ≡ z.re - 1 (mod 4)` (as in `Work.FIPlan.IsPrimary`) written in
`ZMod 4`. -/
lemma isPrimary_iff_zmod4 (z : GaussianInt) :
    Work.FIPlan.IsPrimary z ↔
      Odd z.re ∧ Even z.im ∧ (z.im : ZMod 4) = (z.re : ZMod 4) - 1 := by
  unfold Work.FIPlan.IsPrimary
  have hsub : (((z.re - 1 : ℤ)) : ZMod 4) = (z.re : ZMod 4) - 1 := by push_cast; ring
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, by rw [← hsub]; exact (ZMod.intCast_eq_intCast_iff _ _ 4).mpr h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, (ZMod.intCast_eq_intCast_iff _ _ 4).mp (by rw [hsub]; exact h3)⟩

/-- Two associated primary Gaussian integers are equal: the only primary unit of `ℤ[i]` is `1`. -/
lemma eq_of_associated_of_isPrimary_aux {z w : GaussianInt}
    (hzw : Associated z w) (hz : Work.FIPlan.IsPrimary z) (hw : Work.FIPlan.IsPrimary w) :
    z = w := by
  obtain ⟨u, rfl⟩ := hzw
  rw [isPrimary_iff_zmod4] at hz hw
  have hu1 : (↑u : GaussianInt) = 1 :=
    Commons.NumberTheory.GaussianInt.unit_eq_one_of_primary hz.1 hz.2.1 hz.2.2 hw.1 hw.2.2
  rw [hu1, mul_one]

theorem mk_injOn_primarySet (M : ℕ) :
    Set.InjOn (Associates.mk : GaussianInt → Associates GaussianInt)
      ((Work.FIArea7.primarySet M) : Set GaussianInt) := by
  intro z hz w hw hzw
  rw [Finset.mem_coe, mem_primarySet] at hz hw
  exact eq_of_associated_of_isPrimary_aux (Associates.mk_eq_mk_iff_associated.mp hzw) hz.1 hw.1

end Work.FIArea7
