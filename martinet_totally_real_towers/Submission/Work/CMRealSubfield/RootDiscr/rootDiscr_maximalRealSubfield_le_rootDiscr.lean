import Mathlib

set_option linter.dupNamespace false

open NumberField

namespace Work.CMRealSubfield.RootDiscr

/-- **Root discriminants do not decrease along subfields.**

For a number field `K` and a subfield `E ⊆ K` that is itself a number field
(here `E : Subfield K` with a `NumberField` instance), the root discriminant of
`E` is at most the root discriminant of `K`.

The mathematics is the classical relative-discriminant divisibility

  `disc(E) ^ [K : E] ∣ disc(K)`

(a consequence of `disc(K) = N(𝔡_{K/E}) · disc(E) ^ [K : E]`, i.e. of
`NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow`),
combined with the degree identity `[K : ℚ] = [E : ℚ] · [K : E]`:

  `rootDiscr K = |disc K| ^ (1/[K:ℚ]) ≥ (|disc E| ^ [K:E]) ^ (1/[K:ℚ])
               = |disc E| ^ (1/[E:ℚ]) = rootDiscr E`,

using `[K:E] · 1/[K:ℚ] = 1/[E:ℚ]` and monotonicity of `ℝ`-powers. -/
private theorem rootDiscr_le_of_subfield (K : Type*) [Field K] [NumberField K]
    (E : Subfield K) [NumberField ↥E] :
    NumberField.rootDiscr ↥E ≤ NumberField.rootDiscr K := by
  -- Relative discriminant divisibility, in `ℕ`-form.
  have hdvd : (NumberField.discr ↥E).natAbs ^ Module.finrank ↥E K ∣
      (NumberField.discr K).natAbs := by
    rw [NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow
      (K := ↥E) (𝒪 := 𝓞 ↥E) (L := K) (𝒪' := 𝓞 K)]
    exact dvd_mul_left _ _
  have hpos : 0 < (NumberField.discr K).natAbs :=
    Int.natAbs_pos.mpr (NumberField.discr_ne_zero K)
  have hle_nat : (NumberField.discr ↥E).natAbs ^ Module.finrank ↥E K ≤
      (NumberField.discr K).natAbs := Nat.le_of_dvd hpos hdvd
  -- The same inequality between absolute values of discriminants, in `ℝ`.
  have hle : |(NumberField.discr ↥E : ℝ)| ^ Module.finrank ↥E K ≤
      |(NumberField.discr K : ℝ)| := by
    have h := (Nat.cast_le (α := ℝ)).mpr hle_nat
    simpa [Nat.cast_pow] using h
  have hx0 : 0 ≤ |(NumberField.discr ↥E : ℝ)| := abs_nonneg _
  -- The degree identity `[K : ℚ] = [E : ℚ] * [K : E]`.
  have hf : (Module.finrank ℚ K : ℝ) =
      (Module.finrank ℚ ↥E : ℝ) * (Module.finrank ↥E K : ℝ) := by
    rw [← Nat.cast_mul, (Module.finrank_mul_finrank (F := ℚ) (K := ↥E) (A := K)).symm]
  have hmne : (Module.finrank ↥E K : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ↥E) (M := K)).ne'
  have hene : (Module.finrank ℚ ↥E : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := ↥E)).ne'
  have hexp : (Module.finrank ↥E K : ℝ) * (Module.finrank ℚ K : ℝ)⁻¹ =
      (Module.finrank ℚ ↥E : ℝ)⁻¹ := by
    rw [hf]; field_simp
  rw [NumberField.rootDiscr_def, NumberField.rootDiscr_def]
  simp only [Int.cast_abs]
  calc |(NumberField.discr ↥E : ℝ)| ^ (Module.finrank ℚ ↥E : ℝ)⁻¹
      = (|(NumberField.discr ↥E : ℝ)| ^ Module.finrank ↥E K) ^
          (Module.finrank ℚ K : ℝ)⁻¹ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hx0, hexp]
    _ ≤ |(NumberField.discr K : ℝ)| ^ (Module.finrank ℚ K : ℝ)⁻¹ :=
        Real.rpow_le_rpow (pow_nonneg hx0 _) hle (by positivity)

/-- The root discriminant of the maximal real subfield of a number field `K` is
at most the root discriminant of `K`.

This is the `Subfield`-instance of `rootDiscr_le_of_subfield`: the maximal real
subfield `NumberField.maximalRealSubfield K` is a subfield of `K`, so the
relative-discriminant divisibility
`disc(K⁺) ^ [K : K⁺] ∣ disc(K)` gives `rootDiscr K⁺ ≤ rootDiscr K` after
applying the degree identity `[K : ℚ] = [K⁺ : ℚ] · [K : K⁺]`.  No CM hypothesis
is needed: the statement holds for every number field, the totally real case
being an equality (`K⁺ = K`).

In particular, Martinet's asymptotically-good towers may be turned into
asymptotically-good *totally real* towers by passing to maximal real
subfields. -/
theorem rootDiscr_maximalRealSubfield_le_rootDiscr (K : Type*) [Field K] [NumberField K] :
    NumberField.rootDiscr (NumberField.maximalRealSubfield K) ≤ NumberField.rootDiscr K :=
  rootDiscr_le_of_subfield K (NumberField.maximalRealSubfield K)

end Work.CMRealSubfield.RootDiscr

/-! The statement is also recorded under the (redundant) nested namespace used
by the delegation skeleton, so that consumers referring to the declaration by
either name — in particular both
`Work.CMRealSubfield.RootDiscr.rootDiscr_maximalRealSubfield_le_rootDiscr` and
`Work.CMRealSubfield.RootDiscr.Work.CMRealSubfield.RootDiscr.rootDiscr_maximalRealSubfield_le_rootDiscr`
— find the same theorem. -/
namespace Work.CMRealSubfield.RootDiscr

namespace Work.CMRealSubfield.RootDiscr

theorem rootDiscr_maximalRealSubfield_le_rootDiscr (K : Type*) [Field K] [NumberField K] :
    NumberField.rootDiscr (NumberField.maximalRealSubfield K) ≤ NumberField.rootDiscr K :=
  _root_.Work.CMRealSubfield.RootDiscr.rootDiscr_maximalRealSubfield_le_rootDiscr K

end Work.CMRealSubfield.RootDiscr

end Work.CMRealSubfield.RootDiscr
