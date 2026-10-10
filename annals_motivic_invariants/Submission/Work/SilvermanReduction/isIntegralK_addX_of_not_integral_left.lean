import Mathlib
import Submission.Work.SilvermanReduction.Basic
import Submission.Work.SilvermanReduction.Helpers
import Submission.Work.SilvermanReduction.val_y_lt_sq_of_equation

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option maxHeartbeats 1600000

open scoped WithZero

namespace Work.SilvermanReduction

section Helpers

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- A sum of two elements of valuation at most `c` has valuation at most `c`. -/
lemma val_add_le_of_le {a b : K} {c : ℤᵐ⁰} (ha : val R K a ≤ c) (hb : val R K b ≤ c) :
    val R K (a + b) ≤ c :=
  Valuation.map_add_le (val R K) ha hb

/-- A difference of two elements of valuation at most `c` has valuation at most `c`. -/
lemma val_sub_le_of_le {a b : K} {c : ℤᵐ⁰} (ha : val R K a ≤ c) (hb : val R K b ≤ c) :
    val R K (a - b) ≤ c :=
  Valuation.map_sub_le (val R K) ha hb

/-- Multiplying an integral element on the left does not increase the valuation. -/
lemma val_mul_le_of_le_one_left {w z : K} (hw : val R K w ≤ 1) :
    val R K (w * z) ≤ val R K z := by
  rw [Valuation.map_mul]
  calc val R K w * val R K z ≤ 1 * val R K z := mul_le_mul_left hw (val R K z)
    _ = val R K z := one_mul _

/-- Multiplying an integral element on the right does not increase the valuation. -/
lemma val_mul_le_of_le_one_right {w z : K} (hw : val R K w ≤ 1) :
    val R K (z * w) ≤ val R K z := by
  rw [Valuation.map_mul]
  calc val R K z * val R K w ≤ val R K z * 1 := mul_le_mul_right hw (val R K z)
    _ = val R K z := mul_one _

/-- The element `2` is integral at the place. -/
lemma isIntegralK_two : IsIntegralK R K (2 : K) := by
  simpa only [map_ofNat] using (IsIntegralK.of_algebraMap (R := R) (K := K) (2 : R))

end Helpers

theorem isIntegralK_addX_of_not_integral_left {K : Type*} [Field K] [DecidableEq K]
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra R K] [IsFractionRing R K]
    {W : WeierstrassCurve.Affine K} [W.IsIntegral R] {x y u v : K}
    (h : W.Equation x y) (h' : W.Equation u v) (hx : 1 < Work.SilvermanReduction.val R K x)
    (hu : Work.SilvermanReduction.val R K u ≤ 1) (hv : Work.SilvermanReduction.val R K v ≤ 1)
    (hy : Work.SilvermanReduction.val R K y <
      Work.SilvermanReduction.val R K x * Work.SilvermanReduction.val R K x)
    (hne : x ≠ u) :
    Work.SilvermanReduction.IsIntegralK R K (W.addX x u (W.slope x u y v)) := by
  show Work.SilvermanReduction.val R K (W.addX x u (W.slope x u y v)) ≤ 1
  have hux : val R K u < val R K x := lt_of_le_of_lt hu hx
  have hsub : val R K (x - u) = val R K x :=
    Valuation.map_sub_eq_of_lt_left (val R K) hux
  have hsq : val R K ((x - u) ^ 2) = val R K x * val R K x := by
    rw [Valuation.map_pow, hsub, pow_two]
  have hN := addX_mul_sq (W := W) hne h h'
  have hxx1 : (1 : ℤᵐ⁰) ≤ val R K x := le_of_lt hx
  have hxx2 : val R K x ≤ val R K x * val R K x :=
    le_mul_of_one_le_left (show (0 : ℤᵐ⁰) ≤ val R K x from zero_le) hxx1
  have h1xx : (1 : ℤᵐ⁰) ≤ val R K x * val R K x := one_le_mul hxx1 hxx1
  -- term-by-term bounds for the numerator of the chord identity
  have ht1 : val R K (x ^ 2 * u) ≤ val R K x * val R K x := by
    calc val R K (x ^ 2 * u) ≤ val R K (x ^ 2) := val_mul_le_of_le_one_right hu
      _ = val R K x * val R K x := by rw [Valuation.map_pow, pow_two]
  have ht2 : val R K (x * u ^ 2) ≤ val R K x * val R K x := by
    calc val R K (x * u ^ 2) ≤ val R K x :=
          val_mul_le_of_le_one_right (IsIntegralK.pow hu 2)
      _ ≤ val R K x * val R K x := hxx2
  have ht3 : val R K (2 * W.a₂ * x * u) ≤ val R K x * val R K x := by
    calc val R K (2 * W.a₂ * x * u) ≤ val R K (2 * W.a₂ * x) :=
          val_mul_le_of_le_one_right hu
      _ ≤ val R K x := val_mul_le_of_le_one_left (IsIntegralK.mul isIntegralK_two isIntegralK_a₂)
      _ ≤ val R K x * val R K x := hxx2
  have ht4 : val R K (W.a₄ * (x + u)) ≤ val R K x * val R K x := by
    calc val R K (W.a₄ * (x + u)) ≤ val R K (x + u) := val_mul_le_of_le_one_left isIntegralK_a₄
      _ ≤ val R K x := Valuation.map_add_le (val R K) le_rfl (le_trans hu hxx1)
      _ ≤ val R K x * val R K x := hxx2
  have ht5 : val R K (2 * W.a₆) ≤ val R K x * val R K x :=
    le_trans (IsIntegralK.mul isIntegralK_two isIntegralK_a₆) h1xx
  have ht6 : val R K (W.a₁ * (x * v + u * y)) ≤ val R K x * val R K x := by
    have hxv : val R K (x * v) ≤ val R K x * val R K x :=
      le_trans (val_mul_le_of_le_one_right hv) hxx2
    have huy : val R K (u * y) ≤ val R K x * val R K x :=
      le_trans (val_mul_le_of_le_one_left hu) hy.le
    calc val R K (W.a₁ * (x * v + u * y)) ≤ val R K (x * v + u * y) :=
          val_mul_le_of_le_one_left isIntegralK_a₁
      _ ≤ val R K x * val R K x := val_add_le_of_le hxv huy
  have ht7 : val R K (W.a₃ * (y + v)) ≤ val R K x * val R K x :=
    le_trans (val_mul_le_of_le_one_left isIntegralK_a₃)
      (val_add_le_of_le hy.le (le_trans hv h1xx))
  have ht8 : val R K (2 * y * v) ≤ val R K x * val R K x := by
    calc val R K (2 * y * v) ≤ val R K (2 * y) := val_mul_le_of_le_one_right hv
      _ ≤ val R K y := val_mul_le_of_le_one_left isIntegralK_two
      _ ≤ val R K x * val R K x := hy.le
  have hNle : val R K (x ^ 2 * u + x * u ^ 2 + 2 * W.a₂ * x * u + W.a₄ * (x + u) + 2 * W.a₆
      - W.a₁ * (x * v + u * y) - W.a₃ * (y + v) - 2 * y * v)
      ≤ val R K x * val R K x :=
    val_sub_le_of_le
      (val_sub_le_of_le
        (val_sub_le_of_le
          (val_add_le_of_le
            (val_add_le_of_le
              (val_add_le_of_le (val_add_le_of_le ht1 ht2) ht3) ht4) ht5)
          ht6) ht7) ht8
  have hkey : val R K ((x - u) ^ 2) * val R K (W.addX x u (W.slope x u y v))
      ≤ val R K x * val R K x := by
    rw [← Valuation.map_mul, hN]
    exact hNle
  rw [hsq] at hkey
  have hpos : (0 : ℤᵐ⁰) < val R K x * val R K x :=
    mul_pos (lt_of_lt_of_le zero_lt_one hxx1) (lt_of_lt_of_le zero_lt_one hxx1)
  exact le_of_mul_le_mul_left (by simpa using hkey) hpos

end Work.SilvermanReduction
