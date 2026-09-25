import Mathlib

set_option linter.dupNamespace false

namespace Work.CMRealSubfield.RealSubfield

open NumberField

/-!
# The root discriminant of the maximal real subfield of a CM field

For a CM field `K` with maximal real subfield `K⁺` we prove `rootDiscr K⁺ ≤ rootDiscr K`.

The proof is the general tower argument and does not use the CM hypothesis at all: for a tower of
number fields `E ⊆ K` one has `disc E ^ [K : E] ∣ disc K` (the tower formula for the different,
`NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow`), hence, with
`[K : ℚ] = [E : ℚ] · [K : E]`,

`rootDiscr E ^ [K : ℚ] = |disc E| ^ [K : E] ≤ |disc K| = rootDiscr K ^ [K : ℚ]`,

and both sides are nonnegative while `[K : ℚ] ≠ 0`.  The CM hypothesis enters only in that it
supplies the instances making `K⁺` a number field over which `K` has degree `2`; the inequality
itself holds for the maximal real subfield of any number field (the totally real case being an
equality).

This is the ingredient that turns a family of CM fields with bounded root discriminant and
unbounded degree into a family of **totally real** fields with the same constant: `K⁺` is totally
real (`NumberField.isTotallyReal_maximalRealSubfield`), its degree is `[K : ℚ] / 2`
(`NumberField.finrank_eq_two_mul_finrank_maximalRealSubfield`), and its root discriminant is no
larger.
-/

/-- **The discriminant inequality for a tower of number fields.**  For number fields `E ⊆ K` the
absolute value of `disc E`, raised to the relative degree `[K : E]`, is at most `|disc K|`.

This is the integrality statement behind `rootDiscr E ≤ rootDiscr K`: the tower formula for the
different gives `|disc K| = N(𝔡_{K/E}) · |disc E| ^ [K : E]`. -/
private theorem abs_discr_pow_le_of_algebra_aux (E K : Type*) [Field E] [NumberField E] [Field K]
    [NumberField K] [Algebra E K] :
    |(NumberField.discr E : ℝ)| ^ Module.finrank E K ≤ |(NumberField.discr K : ℝ)| := by
  have h := NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow
    (K := E) (𝒪 := 𝓞 E) (L := K) (𝒪' := 𝓞 K)
  have hdvd : (NumberField.discr E).natAbs ^ Module.finrank E K ∣
      (NumberField.discr K).natAbs := by
    rw [h]; exact dvd_mul_left _ _
  have hle := Nat.le_of_dvd (Int.natAbs_pos.mpr (NumberField.discr_ne_zero K)) hdvd
  have hcast : (((NumberField.discr E).natAbs ^ Module.finrank E K : ℕ) : ℝ) ≤
      ((NumberField.discr K).natAbs : ℝ) := by exact_mod_cast hle
  rwa [Nat.cast_pow, Nat.cast_natAbs, Nat.cast_natAbs, Int.cast_abs, Int.cast_abs] at hcast

/-- **The root discriminant does not increase along a tower of number fields.**  For number fields
`E ⊆ K` over `ℚ` we have `rootDiscr E ≤ rootDiscr K`. -/
private theorem rootDiscr_le_of_algebra_aux (E K : Type*) [Field E] [NumberField E] [Field K]
    [NumberField K] [Algebra E K] [IsScalarTower ℚ E K] :
    NumberField.rootDiscr E ≤ NumberField.rootDiscr K := by
  have hfin : Module.finrank ℚ K = Module.finrank ℚ E * Module.finrank E K :=
    (Module.finrank_mul_finrank ℚ E K).symm
  have hEfin : 0 < Module.finrank ℚ E := Module.finrank_pos
  have hKfin : 0 < Module.finrank ℚ K := Module.finrank_pos
  have hEm : NumberField.rootDiscr E ^ Module.finrank ℚ K =
      |(NumberField.discr E : ℝ)| ^ Module.finrank E K := by
    rw [hfin, pow_mul, NumberField.rootDiscr_def, Int.cast_abs,
      Real.rpow_inv_natCast_pow (x := |(NumberField.discr E : ℝ)|)
        (n := Module.finrank ℚ E) (abs_nonneg _) hEfin.ne']
  have hKm : NumberField.rootDiscr K ^ Module.finrank ℚ K = |(NumberField.discr K : ℝ)| := by
    rw [NumberField.rootDiscr_def, Int.cast_abs,
      Real.rpow_inv_natCast_pow (x := |(NumberField.discr K : ℝ)|)
        (n := Module.finrank ℚ K) (abs_nonneg _) hKfin.ne']
  have hmain : NumberField.rootDiscr E ^ Module.finrank ℚ K ≤
      NumberField.rootDiscr K ^ Module.finrank ℚ K := by
    rw [hEm, hKm]
    exact abs_discr_pow_le_of_algebra_aux E K
  have hE0 : 0 ≤ NumberField.rootDiscr E := by
    rw [NumberField.rootDiscr_def, Int.cast_abs]
    exact Real.rpow_nonneg (abs_nonneg _) _
  have hK0 : 0 ≤ NumberField.rootDiscr K := by
    rw [NumberField.rootDiscr_def, Int.cast_abs]
    exact Real.rpow_nonneg (abs_nonneg _) _
  exact (pow_le_pow_iff_left₀ hE0 hK0 hKfin.ne').mp hmain

/-- **The root discriminant of the maximal real subfield of a CM field is at most the root
discriminant of the field.**

`K⁺` is a subfield of `K`, so the relative-discriminant divisibility
`disc(K⁺) ^ [K : K⁺] ∣ disc(K)` (from the tower formula for the different) gives the claim after
the degree identity `[K : ℚ] = [K⁺ : ℚ] · [K : K⁺]`. -/
theorem rootDiscr_maximalRealSubfield_le_of_isCMField (K : Type*) [Field K] [NumberField K]
    [NumberField.IsCMField K] :
    NumberField.rootDiscr (NumberField.maximalRealSubfield K) ≤ NumberField.rootDiscr K :=
  rootDiscr_le_of_algebra_aux (NumberField.maximalRealSubfield K) K

end Work.CMRealSubfield.RealSubfield

/-! The statement is also recorded under the (redundant) nested namespace used by the delegation
skeleton, so that consumers referring to the declaration by either name — in particular both
`Work.CMRealSubfield.RealSubfield.rootDiscr_maximalRealSubfield_le_of_isCMField` and
`Work.CMRealSubfield.RealSubfield.Work.CMRealSubfield.RealSubfield.rootDiscr_maximalRealSubfield_le_of_isCMField`
— find the same theorem. -/
namespace Work.CMRealSubfield.RealSubfield

namespace Work.CMRealSubfield.RealSubfield

theorem rootDiscr_maximalRealSubfield_le_of_isCMField (K : Type*) [Field K] [NumberField K]
    [NumberField.IsCMField K] :
    NumberField.rootDiscr (NumberField.maximalRealSubfield K) ≤ NumberField.rootDiscr K :=
  _root_.Work.CMRealSubfield.RealSubfield.rootDiscr_maximalRealSubfield_le_of_isCMField K

end Work.CMRealSubfield.RealSubfield

end Work.CMRealSubfield.RealSubfield
