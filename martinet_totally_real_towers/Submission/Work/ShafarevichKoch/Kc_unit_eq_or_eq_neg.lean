import Mathlib
import Submission.Work.ShafarevichKoch.Defs
import Submission.Work.ClassFieldTower.int_coords_and_norm

/-!
# `Work.ShafarevichKoch.Kc_unit_eq_or_eq_neg`

**Every unit of `𝓞 Kc` is `±` a square in `Kc`** (`Kc = ℚ(√-30030)`).

For the distinguished imaginary quadratic field `Kc = ℚ(√-30030)` the group of units of the ring
of integers is as small as it can be: `𝓞 Kcˣ = {±1}`.  Indeed `𝓞 Kc = ℤ[√-30030]` and an element
`x + y√-30030` has norm `x² + 30030 y²`, so a unit `u` — whose norm is a unit of `ℤ`, i.e. `±1`
— satisfies `x² + 30030 y² = ±1`; the sign `-1` is impossible and the sign `+1` forces `y = 0`
and `x = ±1`.

Consequently every unit of `𝓞 Kc` is a square or the negative of a square in `Kc`, which is the
statement proved here (the sharp form of the Kummer two-descent for `Kc`, cf.
`card_unramifiedQuadraticLevels_le_classGroupTwoRank`: the only square class of a unit of `Kc`
which can fail to be a square is the class of `-1`).

The proof uses `Work.ClassFieldTower.int_coords_and_norm` for the coordinates and the norm form
on `𝓞 Kc`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped Classical
open scoped nonZeroDivisors
open scoped NumberField
open NumberField

noncomputable section

namespace Work.ShafarevichKoch

open Work.ClassFieldTower

/-- **The units of `𝓞 Kc` are the units of `ℤ`.**  For `Kc = ℚ(√-30030)` every unit of the
ring of integers is `±1`.

Writing `u : 𝓞 Kc` as `x + y√-30030` with `x y ∈ ℤ` (`Work.ClassFieldTower.int_coords_and_norm`),
the norm form `N(u) = x² + 30030 y²` is a unit of `ℤ`, hence `±1`.  It cannot be `-1`, and
`x² + 30030 y² = 1` forces `y = 0`, `x = ±1`. -/
theorem unitEmbed_Kc_eq_one_or_eq_neg_one (u : RingUnit Kc) :
    unitEmbed Kc u = 1 ∨ unitEmbed Kc u = -1 := by
  obtain ⟨x, y, hxy, hnorm⟩ := int_coords_and_norm (u : 𝓞 Kc)
  have hd : (dWit : ℤ) = 30030 := rfl
  -- The norm of a unit is a unit of `ℤ`.
  have hunit : IsUnit (x ^ 2 + (dWit : ℤ) * y ^ 2) := by
    rw [← hnorm]
    exact IsUnit.map (Algebra.norm ℤ) u.isUnit
  -- The element of `Kcˣ` attached to `u` has the same coordinates as `u`.
  have hcoe : ((unitEmbed Kc u : Kcˣ) : Kc) = (x : Kc) + (y : Kc) * sc := by
    rw [unitEmbed_coe]
    exact hxy
  rw [hd] at hunit
  rcases Int.isUnit_iff.mp hunit with h | h
  · -- `x ^ 2 + 30030 * y ^ 2 = 1`: the norm form forces `y = 0` and `x = ± 1`.
    have hy2le : y ^ 2 ≤ 1 := by nlinarith [sq_nonneg x, sq_nonneg y]
    have hy2ne : y ^ 2 ≠ 1 := by
      intro h1
      nlinarith [sq_nonneg x]
    have hy2 : y ^ 2 = 0 := by
      have hy2nn : (0 : ℤ) ≤ y ^ 2 := sq_nonneg y
      omega
    have hy : y = 0 := sq_eq_zero_iff.mp hy2
    have hx2 : x ^ 2 = 1 := by
      rw [hy] at h
      simpa using h
    rcases sq_eq_one_iff.mp hx2 with hx | hx
    · left
      rw [Units.ext_iff]
      rw [hcoe, hy, hx]
      norm_num
    · right
      rw [Units.ext_iff]
      rw [hcoe, hy, hx]
      norm_num
  · -- `x ^ 2 + 30030 * y ^ 2 = -1` contradicts the positivity of the norm form.
    exfalso
    nlinarith [sq_nonneg x, sq_nonneg y]

theorem Kc_unit_eq_or_eq_neg :
    ∀ u : Work.ShafarevichKoch.RingUnit Work.ClassFieldTower.Kc, ∃ y : Work.ClassFieldTower.Kcˣ,
      Work.ShafarevichKoch.unitEmbed Work.ClassFieldTower.Kc u = y ^ 2 ∨
        Work.ShafarevichKoch.unitEmbed Work.ClassFieldTower.Kc u = -y ^ 2 := by
  intro u
  rcases unitEmbed_Kc_eq_one_or_eq_neg_one u with h | h
  · exact ⟨1, Or.inl (by rw [h, one_pow])⟩
  · exact ⟨1, Or.inr (by rw [h, one_pow])⟩

end Work.ShafarevichKoch
