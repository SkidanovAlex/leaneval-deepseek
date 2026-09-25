import Mathlib
import Submission.Work.ClassFieldTower.Defs
import Submission.Work.ClassFieldTower.Objects

/-!
# `Work.ClassFieldTower.Tower` -- the tower consequence of an infinite `G_∅`

If `F_∅/F` is infinite then, for every `N`, there is a finite unramified Galois extension
`L/F` with `[L : F] ≥ N`.  Being unramified, `L/F` has trivial relative different, hence

* `|disc L| = |disc F| ^ [L : F]`  (the exponent is `[L : F]`),
* `rootDiscr L = rootDiscr F`  (the root discriminant is CONSTANT along the tower).

This is exactly the "asymptotically good" property of Martinet's towers: the levels have
degrees tending to infinity while the root discriminant stays bounded.

Nothing here uses class field theory; the input is the `unramified` clause of
`MaximalUnramifiedProP`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open scoped Classical
open scoped NumberField
open NumberField

noncomputable section

namespace Work.ClassFieldTower

/-- **`|disc L| = |disc F| ^ [L : F]` for an unramified extension of number fields.** -/
theorem natAbs_discr_eq_pow_of_differentIdeal_eq_top {F L : Type*} [Field F] [NumberField F]
    [Field L] [NumberField L] [Algebra F L] (h : differentIdeal (𝓞 F) (𝓞 L) = ⊤) :
    (NumberField.discr L).natAbs = (NumberField.discr F).natAbs ^ Module.finrank F L := by
  rw [NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow
    (K := F) (𝒪 := 𝓞 F) (L := L) (𝒪' := 𝓞 L)]
  simp [h]

/-- **`rootDiscr L = rootDiscr F` for an unramified extension of number fields.** -/
theorem rootDiscr_eq_of_differentIdeal_eq_top {F L : Type*} [Field F] [NumberField F]
    [Field L] [NumberField L] [Algebra F L] (h : differentIdeal (𝓞 F) (𝓞 L) = ⊤) :
    NumberField.rootDiscr L = NumberField.rootDiscr F :=
  Commons.NumberTheory.NumberField.rootDiscr_eq_of_different_eq_top h

/-- **Levels of a tower over a totally complex base are totally complex.**  Conversely to the
totally real case (`isTotallyReal_of_isUnramifiedAtInfinitePlaces`), this needs no unramifiedness:
a real place of `L` would restrict to a real place of the totally complex field `F`. -/
theorem isTotallyComplex_of_isTotallyComplex_base {F L : Type*} [Field F] [NumberField F]
    [Field L] [NumberField L] [Algebra F L] [NumberField.IsTotallyComplex F] :
    NumberField.IsTotallyComplex L :=
  NumberField.isTotallyComplex_of_algebra F L

namespace MaximalUnramifiedProP

variable {F : Type*} [Field F] [NumberField F] {p : ℕ} [Fact p.Prime]

/-- **The tower consequence, level form.**  If `G_∅` is infinite, then for every `N` there is
a finite dimensional Galois subextension `L ⊆ F_∅` with `[L : F] ≥ N`. -/
theorem exists_unramifiedLevel_finrank_ge (M : MaximalUnramifiedProP F p)
    (hinf : Infinite (galoisGroup M)) (N : ℕ) :
    ∃ L : IntermediateField F M.K, FiniteDimensional F L ∧ IsGalois F L ∧
      N ≤ Module.finrank F ↥L :=
  M.exists_finite_galois_subfield_finrank_ge hinf N

universe u

/-- **The tower consequence, in number-field form.**  Infinitude of `G_∅` gives, for every
`N`, a number field `L` (a level of the tower) with `[L : F] ≥ N`, unramified over `F`, and
`rootDiscr L = rootDiscr F` -- the root discriminant is constant along the whole tower. -/
theorem exists_unramifiedNumberField_rootDiscr_eq {F : Type u} [Field F] [NumberField F]
    {p : ℕ} [Fact p.Prime] (M : MaximalUnramifiedProP.{u} F p)
    (hinf : Infinite (galoisGroup M)) (N : ℕ) :
    ∃ (L : Type u) (_ : Field L) (_ : NumberField L) (_ : Algebra F L)
      (_ : FiniteDimensional F L) (_ : IsGalois F L),
      N ≤ Module.finrank F L ∧ differentIdeal (𝓞 F) (𝓞 L) = ⊤ ∧
        NumberField.rootDiscr L = NumberField.rootDiscr F := by
  obtain ⟨L, hfd, hgal, hdeg⟩ := M.exists_unramifiedLevel_finrank_ge hinf N
  haveI : FiniteDimensional F L := hfd
  haveI : IsGalois F L := hgal
  haveI : NumberField ↥L := NumberField.of_module_finite F ↥L
  have hdiff : differentIdeal (𝓞 F) (𝓞 ↥L) = ⊤ :=
    M.differentIdeal_eq_top_of_finite_galois_subfield L hfd hgal
  refine ⟨↥L, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    hdeg, hdiff, ?_⟩
  exact rootDiscr_eq_of_differentIdeal_eq_top hdiff

end MaximalUnramifiedProP

end Work.ClassFieldTower
