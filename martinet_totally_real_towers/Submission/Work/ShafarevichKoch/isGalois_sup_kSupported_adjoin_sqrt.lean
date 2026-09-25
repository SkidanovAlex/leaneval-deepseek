import Mathlib
import Submission.Work.ShafarevichKoch.SupportedTower
import Submission.Work.ClassFieldTower.All

/-!
# `Work.ShafarevichKoch.isGalois_sup_kSupported_adjoin_sqrt`

**The compositum of the maximal (`S`-supported) pro-`2` extension of `Kc` with the quadratic
extension `Kc(√x)` is Galois over `Kc`, for every `x ∈ Kc`.**

In the case at hand `S = ∅`, so `kSupported Kc 2 ∅` is the maximal everywhere-unramified pro-`2`
extension `F_∅` of `Kc`.  The two ingredients are:

* `kSupported F p S` is Galois over `F` whenever the individual `SupportedPField`s are
  (`isGalois_kSupported`, a supremum of Galois subextensions in characteristic zero);
* the field `F(√x)` obtained by adjoining *all* square roots of `x` is the splitting field of
  `X² - C x`, hence normal over `F`, and separable as soon as `F` has characteristic zero
  (`isGalois_adjoin_sqrt` below).

A compositum of two Galois extensions of a base field is Galois (Mathlib instance
`IntermediateField.normal_sup` together with `IntermediateField.isSeparable_sup`), and this is a
supremum *inside* the algebraic closure, so no finiteness hypothesis is needed at all.

## Contents

* `rootSet_X_sq_sub_C` -- the roots of `X ^ 2 - C x` in a field are exactly the square roots of
  `x`;
* `isGalois_adjoin_sqrt` -- `F(√x)/F` is Galois in characteristic zero;
* `isGalois_sup_kSupported_adjoin_sqrt` -- the requested statement.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped Classical
open Polynomial

noncomputable section

namespace Work.ShafarevichKoch

/-- **The roots of `X ^ 2 - C x` are the square roots of `x`.**  This identifies the `adjoin` of
the set of square roots of `x` with the `adjoin` of the root set of the quadratic polynomial
`X ^ 2 - C x`, so that the splitting-field machinery applies to it. -/
theorem rootSet_X_sq_sub_C {F : Type*} [Field F] (x : F) :
    (X ^ 2 - C x : F[X]).rootSet (AlgebraicClosure F) =
      {y : AlgebraicClosure F | y ^ 2 = algebraMap F (AlgebraicClosure F) x} := by
  ext y
  rw [Polynomial.mem_rootSet]
  constructor
  · rintro ⟨-, h⟩
    simpa [sub_eq_zero] using h
  · intro h
    exact ⟨X_pow_sub_C_ne_zero (by norm_num) x, by simpa [sub_eq_zero] using h⟩

/-- **Adjoining a square root is a Galois extension in characteristic zero.**

`F(√x)` is the splitting field of the quadratic polynomial `X ^ 2 - C x`: it is normal by
`Normal.of_isSplittingField`, and separable because it sits inside the algebraic closure of the
characteristic-zero field `F` (the same fact that makes `AlgebraicClosure F` Galois over `F`). -/
theorem isGalois_adjoin_sqrt {F : Type*} [Field F] [CharZero F] (x : F) :
    IsGalois F ↥(IntermediateField.adjoin F
      {y : AlgebraicClosure F | y ^ 2 = algebraMap F (AlgebraicClosure F) x}) := by
  rw [← rootSet_X_sq_sub_C x]
  haveI : Algebra.IsSeparable F ↥(IntermediateField.adjoin F
      ((X ^ 2 - C x : F[X]).rootSet (AlgebraicClosure F))) := inferInstance
  haveI : Normal F ↥(IntermediateField.adjoin F
      ((X ^ 2 - C x : F[X]).rootSet (AlgebraicClosure F))) :=
    Normal.of_isSplittingField _
      (hFEp := IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _))
  exact ⟨⟩

/-- **The requested statement.**  The compositum of the maximal pro-`2` extension of `Kc`
unramified outside `∅` with `Kc(√x)` is Galois over `Kc`, for every `x ∈ Kc`: it is a compositum
of two Galois extensions of `Kc` inside the algebraic closure. -/
theorem isGalois_sup_kSupported_adjoin_sqrt (x : Work.ClassFieldTower.Kc) :
    IsGalois Work.ClassFieldTower.Kc ↥(Work.ShafarevichKoch.kSupported Work.ClassFieldTower.Kc 2 (∅ : Finset ℕ) ⊔
      IntermediateField.adjoin Work.ClassFieldTower.Kc
        {y : AlgebraicClosure Work.ClassFieldTower.Kc |
          y ^ 2 = algebraMap Work.ClassFieldTower.Kc (AlgebraicClosure Work.ClassFieldTower.Kc) x}) := by
  haveI : IsGalois Work.ClassFieldTower.Kc
      ↥(Work.ShafarevichKoch.kSupported Work.ClassFieldTower.Kc 2 (∅ : Finset ℕ)) :=
    isGalois_kSupported (F := Work.ClassFieldTower.Kc) (p := 2) (∅ : Finset ℕ)
  haveI : IsGalois Work.ClassFieldTower.Kc ↥(IntermediateField.adjoin Work.ClassFieldTower.Kc
      {y : AlgebraicClosure Work.ClassFieldTower.Kc |
        y ^ 2 = algebraMap Work.ClassFieldTower.Kc (AlgebraicClosure Work.ClassFieldTower.Kc) x}) :=
    isGalois_adjoin_sqrt x
  exact inferInstance

end Work.ShafarevichKoch
