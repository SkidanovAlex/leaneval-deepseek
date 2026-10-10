import Mathlib
import Submission.Work.MotK.TGen.ChartMaps
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotK.TGen.GdivNeZero` — the target divisor `Gdiv` of the T-twisted link is non-zero

`Gdiv a b h = FambT a b h * bwVec a b h 4` is the product of the target equation of the
T-twisted Crauder--Katz link and the denominator `ǧ₄` of the inverse chart map, both
dehomogenised on the affine chart `{v₀ = 0, v₄ = 1}` at the rational point `p = kleinPointT`.

We prove it is a non-zero polynomial by exhibiting two evaluation points:
* the origin `x = 0` of the chart, where `FambT` takes the value `a⁴b²h · (−a⁵b⁵h) ≠ 0`
  (both factors of `kleinTwGhomV` being non-zero there, by
  `eval_zero_bilinG` and `eval_zero_sdualV`);
* the point `x = (0,1,0)`, where `bwVec a b h 4` takes the value `a²b²h ≠ 0`.

Since `MvPolynomial (Fin 3) K` is a domain, both factors are non-zero and so is their
product.  (No characteristic restriction is needed.) -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Work.MotK.TGen

open MvPolynomial

variable {K : Type} [Field K]

/-- The first factor of `FambT` (the "`b(p, R w)`" term of the target equation `kleinTwGhomV`)
evaluated at the origin of the affine chart: since `kleinTwQ p = 0` and `kleinTwR` is
homogeneous of degree `3`, the only surviving terms give `a⁴b²h`. -/
theorem eval_zero_bilinG (a b h : K) (ha : a ≠ 0) (hh : h ≠ 0) :
    MvPolynomial.eval (fun _ : Fin 3 => (0 : K))
        (kleinTwBilin (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h) (pRa a b h)
          (kleinTwR (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h) (chart3 K)))
      = a ^ 4 * b ^ 2 * h := by
  simp only [kleinTwBilin, kleinTwQ, kleinTwP0, Pi.add_apply, map_add, map_sub, map_mul,
    map_pow, map_neg, MvPolynomial.eval_C, pRa_apply, kleinPointT, chart3,
    kleinTwR_four, kleinTwR_zero, kleinTwR_one, kleinTwR_two, kleinTwR_three,
    kleinTwR0, kleinTwR1, kleinTwR2, kleinTwR3, kleinTwR4]
  norm_num
  field_simp
  first | refl_ring1 | ring

/-- The second factor of `FambT` (the dual secant quintic `kleinTwSDualV`) evaluated at the
origin of the affine chart: only the monomial `(z₄)⁵ = 1` survives, giving `−(a⁵b⁵h)`. -/
theorem eval_zero_sdualV (a b h : K) :
    MvPolynomial.eval (fun _ : Fin 3 => (0 : K))
        (kleinTwSDualV (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h) (chart3 K))
      = -(a ^ 5 * b ^ 5 * h) := by
  simp only [kleinTwSDualV, map_add, map_sub, map_mul, map_pow, MvPolynomial.eval_C, chart3]
  norm_num

/-- The target equation `FambT` of the T-twisted link is a non-zero polynomial of the chart. -/
theorem fambT_ne_zero (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) :
    FambT a b h ≠ 0 := by
  intro hzero
  have h1 := congrArg (MvPolynomial.eval (fun _ : Fin 3 => (0 : K))) hzero
  simp only [map_zero] at h1
  simp only [FambT, kleinTwGhomV, map_mul] at h1
  rw [eval_zero_bilinG a b h ha hh, eval_zero_sdualV a b h] at h1
  have hA : a ^ 4 * b ^ 2 * h ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero 4 ha) (pow_ne_zero 2 hb)) hh
  have hB : -(a ^ 5 * b ^ 5 * h) ≠ 0 :=
    neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero (pow_ne_zero 5 ha) (pow_ne_zero 5 hb)) hh)
  exact (mul_ne_zero hA hB) h1

/-- The denominator `ǧ₄ = bwVec a b h 4` of the inverse chart map is a non-zero polynomial of
the chart: `bwVec a b h 4 = kleinTwR4(...)(chart3)` (since `p₄ = 0`), which at the point
`x = (0,1,0)` takes the value `a²b²h ≠ 0`. -/
theorem bwVec_four_ne_zero (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) :
    bwVec a b h 4 ≠ 0 := by
  intro hzero
  have h1 := congrArg
    (MvPolynomial.eval (fun j : Fin 3 => if j = 1 then (1 : K) else 0)) hzero
  simp only [map_zero] at h1
  simp only [bwVec, kleinTwPi, pRa_apply, kleinPointT, map_sub, map_mul, map_pow,
    MvPolynomial.eval_C, chart3, kleinTwR_four, kleinTwR4,
    kleinTwR_zero, kleinTwR0] at h1
  norm_num at h1
  rcases h1 with (h | h) | h
  · exact ha h
  · exact hb h
  · exact hh h

theorem GdivNeZero {K : Type} [Field K] (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) :
    Gdiv a b h ≠ 0 := by
  rw [show Gdiv a b h = FambT a b h * bwVec a b h 4 from rfl]
  exact mul_ne_zero (fambT_ne_zero a b h ha hb hh) (bwVec_four_ne_zero a b h ha hb hh)

end Work.MotK.TGen
