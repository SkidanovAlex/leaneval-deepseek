import Mathlib
import Submission.Work.ShafarevichKoch.RelationBound
import Submission.Work.ShafarevichKoch.count_map_eq
import Submission.Work.ShafarevichKoch.exists_sq_eq_of_forall_even_count
import Submission.Work.ShafarevichKoch.exists_integral_mul_square
import Submission.Work.ShafarevichKoch.FracIdealOfUnit
import Submission.Work.ClassFieldTower.exists_ideal_sq_of_unramified

/-!
# `Work.ShafarevichKoch.mem_VTwo_of_unramified`

**Every element of `Fˣ` that becomes a square in an unramified Galois extension of `F` lies in
Koch's group `V_∅ = VTwo F`.**

If `L/F` is a finite Galois extension of number fields whose relative different is the unit ideal
(`differentIdeal (𝓞 F) (𝓞 L) = ⊤`, i.e. `L/F` is unramified at every finite place) and `x : Fˣ`
has a square root `z ∈ L`, then the principal fractional ideal `(x)` of `𝓞 F` is a square, i.e.
`x ∈ VTwo F`.

This is the "easy half" of the Kummer two-descent: the Kummer radical `V_∅` of the maximal
unramified exponent-`2` extension of `F` consists precisely of the classes of elements that become
squares in the maximal unramified extension.

## Proof

Choose `x' ∈ 𝓞 F`, `x' ≠ 0` and `y ∈ Fˣ` with `x' = x · y²` (`exists_integral_mul_square`); then
`(x) = (x') · (y)⁻²`, so it suffices to see that the integral ideal `(x') = Ideal.span {x'}` is a
square.  The element `z · y ∈ L` is a square root of `x'`, so
`Work.ClassFieldTower.exists_ideal_sq_of_unramified` (unramifiedness forces even valuations)
produces an integral ideal `I` with `I * I = Ideal.span {x'}`.  Mapping this through
`Ideal → FractionalIdeal → IdealUnit` and writing `(x') = FracIdealOf F (unit x')` exhibits
`(x) = (unit x') · (y)⁻²` as a product of squares in the group of invertible fractional ideals.
-/

open scoped Classical nonZeroDivisors NumberField
open NumberField

noncomputable section

namespace Work.ShafarevichKoch

/-- The principal fractional ideal of an element `a : 𝓞 F`, regarded as an element of `F`, is the
extension of the integral ideal `(a) = Ideal.span {a}`. -/
theorem coe_fracIdealOf_algebraMap (F : Type*) [Field F] [NumberField F]
    (a : 𝓞 F) (ha : (algebraMap (𝓞 F) F a) ≠ 0) :
    ((FracIdealOf F (Units.mk0 (algebraMap (𝓞 F) F a) ha) : IdealUnit F) :
        FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
      = ((Ideal.span {a} : Ideal (𝓞 F)) :
          FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := by
  rw [FracIdealOf, coe_toPrincipalIdeal, Units.val_mk0,
    FractionalIdeal.coeIdeal_span_singleton]

theorem mem_VTwo_of_unramified (F L : Type*) [Field F] [NumberField F] [Field L] [NumberField L]
    [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    (x : Fˣ) (z : L) (hz : z * z = algebraMap F L (x : F))
    (hur : differentIdeal (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers L) = ⊤) :
    x ∈ Work.ShafarevichKoch.VTwo F := by
  classical
  -- write `x` as an integral element modulo a square
  obtain ⟨x', hx'0, y, hy⟩ := exists_integral_mul_square F x
  have hyF : (algebraMap (𝓞 F) F x') = (x : F) * ((y : F)) ^ 2 := hy
  have hxa_ne : (algebraMap (𝓞 F) F x') ≠ 0 := by
    rw [hyF]; exact mul_ne_zero (Units.ne_zero x) (pow_ne_zero 2 (Units.ne_zero y))
  -- `x'` is a square in `L`, with square root `z * y`
  have hsq : ∃ b : L, b * b = algebraMap F L ((x' : 𝓞 F) : F) := by
    refine ⟨z * algebraMap F L (y : F), ?_⟩
    have h1 : (z * algebraMap F L (y : F)) * (z * algebraMap F L (y : F))
        = (z * z) * (algebraMap F L (y : F)) ^ 2 := by ring
    have h2 : (z * z) * (algebraMap F L (y : F)) ^ 2
        = algebraMap F L ((x : F) * (y : F) ^ 2) := by
      rw [hz, ← map_pow, ← map_mul]
    exact h1.trans (h2.trans (congrArg (algebraMap F L) hyF.symm))
  -- unramifiedness forces the principal ideal `(x')` to be a square of an integral ideal
  obtain ⟨I, hI⟩ :=
    Work.ClassFieldTower.exists_ideal_sq_of_unramified (K := F) (L := L) x' hx'0 hur hsq
  -- nonvanishing bookkeeping
  have hspan_ne : Ideal.span {x'} ≠ ⊥ := fun h => hx'0 (Ideal.span_singleton_eq_bot.mp h)
  have hspan0 : ((Ideal.span {x'} : Ideal (𝓞 F)) :
      FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr hspan_ne
  have hI0 : I ≠ ⊥ := by
    intro h0
    have h : Ideal.span {x'} = ⊥ := by rw [← hI, h0, Ideal.bot_mul]
    exact hspan_ne h
  have hIco0 : (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr hI0
  -- `(x')` is the principal fractional ideal of the unit `x' ∈ F`, and it is a square
  have hA : FracIdealOf F (Units.mk0 (algebraMap (𝓞 F) F x') hxa_ne)
      = Units.mk0 ((Ideal.span {x'} : Ideal (𝓞 F)) :
          FractionalIdeal (nonZeroDivisors (𝓞 F)) F) hspan0 := by
    refine Units.ext ?_
    rw [Units.val_mk0]
    exact coe_fracIdealOf_algebraMap F x' hxa_ne
  have hsq1 : IsSquareFracIdeal F
      (FracIdealOf F (Units.mk0 (algebraMap (𝓞 F) F x') hxa_ne)) := by
    rw [hA]
    refine ⟨Units.mk0 (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) hIco0, ?_⟩
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_mk0, Units.val_mk0, ← FractionalIdeal.coeIdeal_mul, hI]
  -- `x = x' / y ^ 2` as units of `F`
  have hxu : x = Units.mk0 (algebraMap (𝓞 F) F x') hxa_ne * (y ^ 2)⁻¹ := by
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, Units.val_mk0]
    rw [eq_comm, mul_inv_eq_iff_eq_mul₀ (pow_ne_zero 2 (Units.ne_zero y))]
    exact hyF
  -- hence `(x)` is a product of squares
  have hfac : FracIdealOf F x
      = FracIdealOf F (Units.mk0 (algebraMap (𝓞 F) F x') hxa_ne)
        * (FracIdealOf F y * FracIdealOf F y)⁻¹ := by
    rw [hxu, FracIdealOf_mul, FracIdealOf_inv,
      show FracIdealOf F (y ^ 2) = FracIdealOf F y * FracIdealOf F y by
        rw [pow_two, FracIdealOf_mul]]
  show IsSquareFracIdeal F (FracIdealOf F x)
  rw [hfac]
  exact isSquareFracIdeal_mul F hsq1 (isSquareFracIdeal_inv F ⟨FracIdealOf F y, rfl⟩)

end Work.ShafarevichKoch
