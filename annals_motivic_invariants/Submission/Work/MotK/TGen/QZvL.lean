import Mathlib
import Submission.Work.MotK.TGen.ThetaSTDefs
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotK.TGen

/-- `ZvL a b h` is the ruling line `T ↦ rv a b h + T · rw a b h` of the fibre of the twisted quadro
map `kleinTwP` over the chart point: its `i`-th component is the affine polynomial
`C (rv a b h i) * X + C (rw a b h i)` in the ruling parameter `T = Polynomial.X`.

The identity `QZvL` records that this line lies on the `T`-invariant quadric `kleinTwQ`: because
`kleinTwQ` is a quadratic form in `y`, substituting `y = rv + T·rw` gives
`kleinTwQ rv + T·kleinTwBilin rv rw + T²·kleinTwQ rw`, and all three of
`kleinTwQ rv`, `kleinTwBilin rv rw`, `kleinTwQ rw` vanish (they are explicit rational identities in
`a, b, h, x₀, x₁, x₂` with denominators only in `a` and `b`).

The computation is carried out in the fraction field of `K[x₀,x₁,x₂][T]`, which is injective into
`Polynomial (MvPolynomial (Fin 3) K)`, so that `field_simp` may clear the denominators `a, b` and
`ring` may close the resulting polynomial identity. -/
theorem QZvL (K : Type) [Field K] (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    Work.MotK.kleinTwQ (Polynomial.C (MvPolynomial.C a)) (Polynomial.C (MvPolynomial.C b))
      (Polynomial.C (MvPolynomial.C h)) (ZvL a b h) = 0 := by
  have ha' : algebraMap K (FractionRing (Polynomial (MvPolynomial (Fin 3) K))) a ≠ 0 := by
    intro h0
    exact ha ((algebraMap K (FractionRing (Polynomial (MvPolynomial (Fin 3) K)))).injective
      (by rw [h0, map_zero]))
  have hb' : algebraMap K (FractionRing (Polynomial (MvPolynomial (Fin 3) K))) b ≠ 0 := by
    intro h0
    exact hb ((algebraMap K (FractionRing (Polynomial (MvPolynomial (Fin 3) K)))).injective
      (by rw [h0, map_zero]))
  apply IsFractionRing.injective (Polynomial (MvPolynomial (Fin 3) K))
    (FractionRing (Polynomial (MvPolynomial (Fin 3) K)))
  simp only [Work.MotK.kleinTwQ, Work.MotK.kleinTwP0, ZvL,
    Work.MotK.TwCensus.rv, Work.MotK.TwCensus.rw,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
    Fin.isValue,
    map_mul, map_add, map_sub, map_pow, map_neg, map_zero, map_one, map_div₀,
    Polynomial.C_eq_algebraMap, MvPolynomial.C_eq_algebraMap,
    ← IsScalarTower.algebraMap_apply]
  field_simp [hb', ha']
  first | refl_ring1 | ring

end Work.MotK.TGen
