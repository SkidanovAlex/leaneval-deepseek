import Mathlib
import Submission.NK.NUV2.RouteC.cup_pow

/-!
# The valuation of the `H⁰ × H²` cup product with `a ∈ Fˣ` (Route C, the character formula)

For a finite Galois extension `E / F` of local fields (here: `F = Q.adicCompletion K`,
`E = q.adicCompletion L` for `q | Q`), the class `a ∪ c ∈ H²(Gal(E/F), Eˣ)` of the `H⁰ × H²` cup
product with `a ∈ Fˣ` (the coefficient change `powHom a`, `RouteC/cup_pow.lean`) is mapped by the
valuation `ord_* : H²(Gal(E/F), Eˣ) → H²(Gal(E/F), ℤ)` to `ord(a) · c`.  On the cochain level this
is the statement proved here:

`powHom a ≫ valSeqG = ord a • 𝟙`,

where `ord a = log (v (a))` is the valuation of `a` (an integer).  It is the computation behind the
surjectivity of the Artin map in the character formula (`ord_*(π ∪ c) = c` for a uniformiser `π`).
-/

open CategoryTheory
open scoped WithZero

namespace NK.NUV2.RouteC

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- The valuation of the cup product with `a`: `ord_*(a ∪ c) = ord(a) · c`, in the form
`powHom a ≫ valSeqG = ord a • 𝟙` of morphisms of `Rep ℤ Gal(L_q/K_Q)`. -/
theorem powHom_comp_valSeqG
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    (h1 : q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1)
    (a : (Q.adicCompletion K)ˣ) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    powHom (F := Q.adicCompletion K) (E := q.adicCompletion L) a ≫ valSeqG Q q hq h1
      = (WithZero.log (Valued.v (R := q.adicCompletion L)
          (algebraMap (Q.adicCompletion K) (q.adicCompletion L) (a : Q.adicCompletion K)))) •
        (𝟙 (valSeqTriv K L Q q hq)) := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  -- the valuation sequence on an element of the units representation
  have hval : ∀ x : Additive (q.adicCompletion L)ˣ,
      (valSeqG Q q hq h1).hom.toLinearMap x
        = WithZero.log (Valued.v (R := q.adicCompletion L)
            (((Additive.toMul x : (q.adicCompletion L)ˣ)) : q.adicCompletion L)) :=
    fun _ => rfl
  -- the cup product with `a` on an integer `n`
  have hpow : ∀ n : ℤ,
      (powHom (F := Q.adicCompletion K) (E := q.adicCompletion L) a).hom.toLinearMap n
        = n • (Additive.ofMul (Units.map
            (algebraMap (Q.adicCompletion K) (q.adicCompletion L)).toMonoidHom a) :
              Additive (q.adicCompletion L)ˣ) := by
    intro n
    unfold powHom
    simp only [Rep.hom_ofHom]
    rfl
  -- the valuation of a unit
  have hval : ∀ x : Additive (q.adicCompletion L)ˣ,
      (valSeqG Q q hq h1).hom.toLinearMap x
        = WithZero.log (Valued.v (R := q.adicCompletion L)
            (((Additive.toMul x : (q.adicCompletion L)ˣ)) : q.adicCompletion L)) :=
    fun _ => rfl
  -- the cup product with `a`, as a change of coefficients
  have hpow : ∀ n : ℤ,
      (powHom (F := Q.adicCompletion K) (E := q.adicCompletion L) a).hom.toLinearMap n
        = n • (Additive.ofMul (Units.map
            (algebraMap (Q.adicCompletion K) (q.adicCompletion L)).toMonoidHom a) :
              Additive (q.adicCompletion L)ˣ) := by
    intro n
    unfold powHom
    simp only [Rep.hom_ofHom]
    rfl
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro n
  show (valSeqG Q q hq h1).hom.toLinearMap
      ((powHom (F := Q.adicCompletion K) (E := q.adicCompletion L) a).hom.toLinearMap n)
    = (WithZero.log (Valued.v (R := q.adicCompletion L)
        (algebraMap (Q.adicCompletion K) (q.adicCompletion L) (a : Q.adicCompletion K)))) • n
  -- both sides are `ℤ`-linear in `n`, so it suffices to compare them at `n = 1`
  rw [show n = n • (1 : ℤ) from (mul_one n).symm]
  rw [map_zsmul]
  rw [map_zsmul]
  rw [show (valSeqG Q q hq h1).hom.toLinearMap
        ((powHom (F := Q.adicCompletion K) (E := q.adicCompletion L) a).hom.toLinearMap 1)
      = WithZero.log (Valued.v (R := q.adicCompletion L)
          (algebraMap (Q.adicCompletion K) (q.adicCompletion L) (a : Q.adicCompletion K))) from by
    rw [hpow 1, one_smul]
    exact hval (Additive.ofMul (Units.map
      (algebraMap (Q.adicCompletion K) (q.adicCompletion L)).toMonoidHom a))]
  simp
  ring

end NK.NUV2.RouteC
