import Mathlib
import Submission.Work.MotK.LinkCertDefs
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Non-vanishing of the chart function `f̂₄` of the T-twisted Crauder–Katz link

The affine chart map of the T-twisted link is `f = kleinTwP ∘ kleinTwStereo`, read in the
affine charts `chartC = ![0, x₀, x₁, x₂, 1]` at the point `pointC = (1,0,1, b/(a·h), 0)` of the
twisted quadric.  Its dehomogenised components are the polynomials
`fhatC K a b h i ∈ K[x₀,x₁,x₂]` (`Submission/Work/MotK/LinkCertT.lean`).

This file proves that the component `f̂₄` — the denominator of the chart coordinates
`φ_j = f̂_{j+1}/f̂₄` (`phiCh`) and of the unit identities `UnitChartC` — does **not** vanish as a
polynomial, whenever `a·b·h ≠ 0`.

The proof is by evaluation: `f̂₄` is the quartic component `kleinTwP4` of the twisted Pfaffian
map, namely `-a·b·h·y₃² + a²·y₀·y₁ - b²·h·y₂·y₄` with `y = kleinTwStereo p v`, and at the point
`(x₀,x₁,x₂) = (0,1,0)` the stereographic coordinates specialise to
`y = (0, 0, -a·b, 0, -a·b)`, so that `f̂₄(0,1,0) = -a²·b⁴·h ≠ 0`.
-/

namespace Work.MotK.ChartAeval

open Work.MotK

/-- **The value of `f̂₄` at the rational point `(0,1,0)`.**  Evaluating the quartic component
of the T-twisted chart map at `x₀ = 0, x₁ = 1, x₂ = 0` gives `-a²·b⁴·h`: at that point the
stereographic coordinates are `y = (0, 0, -ab, 0, -ab)`, because the quadric value and the polar
form specialise to `0` and `ab` respectively. -/
theorem fhatC_four_eval (K : Type*) [Field K] (a b h : K) (ha : a ≠ 0) (hh : h ≠ 0) :
    MvPolynomial.eval (![0, 1, 0] : Fin 3 → K) (Work.MotK.fhatC K a b h 4) = -(a ^ 2 * b ^ 4 * h) := by
  rw [show Work.MotK.fhatC K a b h 4 =
      Work.MotK.kleinTwP4 (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
        (Work.MotK.kleinTwStereo (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
          (Work.MotK.pRaC K a b h) (Work.MotK.chartC K)) from rfl]
  simp only [Work.MotK.kleinTwP4, Work.MotK.kleinTwStereo, Work.MotK.kleinTwQ, Work.MotK.kleinTwBilin,
    Work.MotK.kleinTwP0, Work.MotK.pRaC, Work.MotK.pointC, Work.MotK.chartC,
    Pi.add_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.cons_val_succ,
    Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
    map_add, map_sub, map_mul, map_pow, map_neg, map_zero, map_one,
    MvPolynomial.eval_C, MvPolynomial.eval_X]
  field_simp
  first | refl_ring1 | ring

/-- **The chart denominator `f̂₄` is a non-zero polynomial.**  For `a, b, h ≠ 0` the quartic
component `f̂₄ ∈ K[x₀,x₁,x₂]` of the T-twisted chart map is not the zero polynomial; equivalently
it is a regular function not identically vanishing on the affine chart `𝔸³_K`. -/
theorem fhatC_four_ne_zero (K : Type*) [Field K] (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) :
    Work.MotK.fhatC K a b h 4 ≠ 0 := by
  intro hzero
  have h0 : MvPolynomial.eval (![0, 1, 0] : Fin 3 → K) (Work.MotK.fhatC K a b h 4) = 0 := by
    rw [hzero, map_zero]
  rw [fhatC_four_eval K a b h ha hh] at h0
  have hne : a ^ 2 * b ^ 4 * h ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero 2 ha) (pow_ne_zero 4 hb)) hh
  exact hne (neg_eq_zero.mp h0)

end Work.MotK.ChartAeval
