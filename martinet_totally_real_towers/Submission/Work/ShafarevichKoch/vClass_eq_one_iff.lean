import Mathlib
import Submission.Work.ShafarevichKoch.Defs
import Submission.Work.ShafarevichKoch.SquareRoot
import Submission.Work.ShafarevichKoch.FracIdealOfUnit

/-!
# `Work.ShafarevichKoch.vClass_eq_one_iff`

**The kernel of the Kummer two-descent `vClass`.**

The Kummer two-descent class `vClass F x ∈ Cl(𝓞 F)` of `x ∈ V_∅` (`Defs.lean`) is trivial
exactly when `x` is a unit times a square in `Fˣ`:

`vClass F x = 1 ↔ ∃ u : 𝓞_Fˣ, ∃ y : Fˣ, x = u * y²`.

Equivalently, the sequence `1 → 𝓞_Fˣ/(𝓞_Fˣ)² → V_∅/Fˣ² → Cl(F)[2]` is exact at `V_∅/Fˣ²`, which
is the ingredient that turns `vClass` into an injection on `V_∅/Fˣ²` and hence gives Koch's
description of the maximal unramified exponent-`2` extension of `F` by Kummer theory.

## Proof

Recall (`Defs.lean`) that `vClass F x = ClassGroup.mk F J` for a square root `J` of the
principal fractional ideal `(x)`, which is unique by `squareRoot_unique`.

* If `x = u · y²` with `u` a unit of `𝓞 F`, then `J = (y)` by uniqueness of square roots, and the
  class of a *principal* fractional ideal is trivial: `classGroup_mk_fracIdealOf_eq_one`.
* Conversely, if `ClassGroup.mk F J = 1` then `J` is principal, `J = (z)` with `z ≠ 0`
  (`ClassGroup.mk_eq_one_iff` composed with `Submodule.isPrincipal_iff` and
  `FractionalIdeal.isPrincipal_iff`).  From `J · J = (x)` we get `(z · z) = (x)` in the group of
  fractional ideals, and two elements generating the same principal fractional ideal differ by a
  unit of `𝓞 F` (`FractionalIdeal.spanSingleton_eq_spanSingleton`); thus `x = u · z²` with
  `u : 𝓞_Fˣ`, and `z ≠ 0` exhibits `z` as an element of `Fˣ`.
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

/-- **The class group of a principal fractional ideal is trivial.**  The ideal class of
`FracIdealOf F y = (y)` is `1` for every `y : Fˣ`. -/
theorem classGroup_mk_fracIdealOf_eq_one (F : Type*) [Field F] [NumberField F] (y : Fˣ) :
    ClassGroup.mk F (FracIdealOf F y) = 1 := by
  rw [ClassGroup.mk_eq_one_iff]
  rw [Submodule.isPrincipal_iff]
  refine ⟨(y : F), ?_⟩
  rw [← FractionalIdeal.coe_spanSingleton (nonZeroDivisors (𝓞 F)), ← coe_toPrincipalIdeal]
  rfl

theorem vClass_eq_one_iff (F : Type*) [Field F] [NumberField F]
    (x : Work.ShafarevichKoch.VTwo F) :
    Work.ShafarevichKoch.vClass F x = 1 ↔ ∃ (u : Work.ShafarevichKoch.RingUnit F) (y : Fˣ),
      (x : Fˣ) = Work.ShafarevichKoch.unitEmbed F u * y ^ 2 := by
  constructor
  · -- `vClass F x = 1` forces the chosen square root of `(x)` to be principal, `J = (z)`.
    intro h
    obtain ⟨J, hJ1, hJ2⟩ : ∃ J : IdealUnit F,
        ClassGroup.mk F J = 1 ∧ J * J = FracIdealOf F x.1 := ⟨_, h, vClass_spec F x⟩
    have hprin : (J : Submodule (𝓞 F) F).IsPrincipal := ClassGroup.mk_eq_one_iff.mp hJ1
    obtain ⟨z, hz⟩ : ∃ z : F, (J : Submodule (𝓞 F) F) = Submodule.span (𝓞 F) {z} :=
      (Submodule.isPrincipal_iff _).mp hprin
    have hJz : (J : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) =
        FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) z := by
      rw [← FractionalIdeal.coeToSubmodule_inj, FractionalIdeal.coe_spanSingleton, hz]
    -- `J` is a nonzero fractional ideal, so its generator `z` is nonzero.
    have hz0 : z ≠ 0 := by
      intro h0
      have hJ0 : (J : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) = 0 := by
        rw [hJz, h0, FractionalIdeal.spanSingleton_zero]
      exact Units.ne_zero J hJ0
    -- `J · J = (x)` becomes `(z · z) = (x)`.
    have hsq : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (z * z) =
        FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) ((x : Fˣ) : F) := by
      have h1 : (J : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
          * (J : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) =
          FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) ((x : Fˣ) : F) := by
        rw [← Units.val_mul, hJ2, FracIdealOf, coe_toPrincipalIdeal]
      rw [hJz, FractionalIdeal.spanSingleton_mul_spanSingleton] at h1
      exact h1
    -- Two elements with the same principal fractional ideal differ by a unit of `𝓞 F`.
    obtain ⟨w, hw⟩ := FractionalIdeal.spanSingleton_eq_spanSingleton.mp hsq
    refine ⟨w, Units.mk0 z hz0, ?_⟩
    apply Units.ext
    rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mk0, ← hw, Units.smul_def,
      Algebra.smul_def]
    simp only [unitEmbed_coe, pow_two]
  · -- `x = u · y²`: then `(y)` is a square root of `(x)`, and its class is trivial.
    rintro ⟨u, y, hxy⟩
    have huniq : Classical.choose (x.property : IsSquareFracIdeal F (FracIdealOf F x.1))
        = FracIdealOf F y := by
      apply squareRoot_unique F
      refine (vClass_spec F x).trans ?_
      have h1 : FracIdealOf F x.1 = FracIdealOf F (unitEmbed F u) * FracIdealOf F (y ^ 2) := by
        rw [← FracIdealOf_mul, hxy]
      rw [h1, fracIdealOf_unitEmbed, one_mul, pow_two, FracIdealOf_mul]
    rw [vClass, huniq]
    exact classGroup_mk_fracIdealOf_eq_one F y

end Work.ShafarevichKoch
