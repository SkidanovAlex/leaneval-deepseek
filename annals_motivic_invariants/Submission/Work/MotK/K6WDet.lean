/-
# `Work.MotK.K6WDet` — the `ZpgWMat` determinant and the K6 saturation leaf

This module repairs the outstanding `sorry` of the K6 refactor that blocks both

* `Work.MotK.LinkCertTGenInf` (via `STClass` → `ZTwistDiv` → `ZTwistChartFracMain` →
  `ZpgI4SatW` → `ZpgI4NormalForm` → `ZpgW4NonZeroDivMain`), and
* `Work.MotK.TGen.ZCWnzd` (via `ZCWDet`),

both of which need `zpgW4 a b h` to be a non-zero-divisor modulo the chart ideal `zpgI4 a b h`
of the twisted Klein curve.  The two inputs already proved elsewhere in the workspace are

* `Work.MotK.TGen.ZpgI4SpanMain`  — the five standard monomials span the chart ring over `K[X₃]`,
* `Work.MotK.TGen.ZpgI4StdIndependent` — they are independent modulo `zpgI4`,
* `Work.MotK.TGen.ZpgWMatMulMain` — `zpgWMat` is the multiplication matrix of `zpgW4`,

and the missing fourth input is `(zpgWMat a b h).det ≠ 0`, proved here.

## The determinant

`zpgWMat a b h` is a `5 × 5` matrix over `MvPolynomial (Fin 1) K = K[X₀]` in which every entry is
a monomial `C (cc j i) * (X 0) ^ (dd j i)` (`zcc`, `zdd` below).  Hence

`det = ∑ σ, ↑(σ.sign) • ∏ i, M (σ i) i`

and the `X₀`-degree of the term of `σ` is `∑ i, dd (σ i) i`, which is `≤ 10` for every `σ` and is
`10` for exactly one permutation `s1` (`dd_le`, `dd_eq`).  Therefore the coefficient of `X₀ ^ 10`
in the determinant is `(s1.sign) • ∏ i, cc (s1 i) i = -(a^10 * b^10 * h^14) ≠ 0`
(`coeff_det`), and the determinant is nonzero.  (Cross-checked with a CAS: for `(a,b,h) = (1,1,1)`
the determinant is `-X^10 - X^5`, for `(1,-1,1)` it is `-X^10 + 11 X^5 - 32`.)

Note that `Matrix.det_fin_four`/`det_fin_five` do not exist in this Mathlib and `decide` cannot
decide *polynomial* identities (there is no `DecidableEq K`), which is why the coefficient of the
top monomial — and not the full expansion — is computed.
-/
import Mathlib
import Submission.Work.MotK.TGen.ZpgI4W4NonZeroDiv
import Submission.Work.MotK.TGen.ZpgI4StdIndependent
import Submission.Work.MotK.TGen.ZpgI4SpanMain
import Submission.Work.MotK.TGen.ZpgWMatMulMain
import Submission.Work.Reflect.PolyId

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Work.MotK.K6WDet

open MvPolynomial
open Work.MotK.TGen

/-! ## The `X 0`-degrees and coefficients of the entries of `zpgWMat` -/

/-- The `X 0`-degree of each entry of `zpgWMat`.  The structurally zero entries get degree `0`, so
that the degree sum is bounded by `10` for *every* permutation. -/
def zdd : Matrix (Fin 5) (Fin 5) ℕ :=
  !![0,3,2,1,0;
     0,0,0,2,1;
     1,0,0,0,2;
     0,1,0,0,3;
     0,0,1,0,0]

/-- The coefficient (in `K`) of each entry of `zpgWMat`, so that
`zpgWMat a b h j i = C (zcc K a b h j i) * (X 0) ^ (zdd j i)` (`zpgWMat_entry`). -/
noncomputable def zcc (K : Type) [Field K] (a b h : K) : Matrix (Fin 5) (Fin 5) K :=
  !![0, a^2*b^2*h^4, b^5*h^2/a, a^2*b^2, b*(a^5-b^5)/(a^2*h^2);
     -((a^5-b^5)/b), 0, 0, a*b^3*h^2, -((a^10-3*a^5*b^5+b^10)/(a^3*b^3));
     a^3*b*h^2, (a^5-b^5)/a, 0, 0, h^2*(a^5-2*b^5)/b;
     0, -(a*h^2*(a^5-2*b^5)/b^2), -(b*(a^5-b^5)/a^2), 0, a^2*b^2*h^4;
     0, 0, -(a^2*b^2*h^2), -((a^5-b^5)/b), 0]

/-- The unique permutation maximising `σ ↦ ∑ i, zdd (σ i) i`. -/
def s1 : Equiv.Perm (Fin 5) where
  toFun i := ![(2 : Fin 5), 0, 4, 1, 3] i
  invFun i := ![(1 : Fin 5), 3, 0, 4, 2] i
  left_inv := by intro i; fin_cases i <;> decide
  right_inv := by intro i; fin_cases i <;> decide

theorem zpgWMat_entry (K : Type) [Field K] (a b h : K) (j i : Fin 5) :
    zpgWMat (K := K) a b h j i = C (zcc K a b h j i) * (X 0) ^ (zdd j i) := by
  fin_cases j <;> fin_cases i <;> simp [zpgWMat, zcc, zdd]

/-! ## The combinatorics of the degree matrix -/

theorem dd_le : ∀ σ : Equiv.Perm (Fin 5), ∑ i, zdd (σ i) i ≤ 10 := by decide

theorem dd_eq : ∀ σ : Equiv.Perm (Fin 5), ∑ i, zdd (σ i) i = 10 → σ = s1 := by decide

theorem dd_s1 : ∑ i, zdd (s1 i) i = 10 := by decide

theorem s1_sign : (s1.sign : ℤ) = 1 := by decide

theorem s1_zero : s1 0 = 2 := by decide
theorem s1_one : s1 1 = 0 := by decide
theorem s1_two : s1 2 = 4 := by decide
theorem s1_three : s1 3 = 1 := by decide
theorem s1_four : s1 4 = 3 := by decide

/-! ## The coefficient of `X 0 ^ 10` in the determinant -/

/-- Coefficient extraction commutes with `ℤ`-scalar multiplication (the scalar is the permutation
sign in `Matrix.det_apply`). -/
theorem coeff_zsmul (K : Type) [Field K] (m : Fin 1 →₀ ℕ) (n : ℤ)
    (p : MvPolynomial (Fin 1) K) : (n • p).coeff m = n • p.coeff m :=
  map_zsmul (MvPolynomial.coeffAddMonoidHom m) n p

/-- The `X 0 ^ 10`-coefficient of the product of the entries along a permutation is the product of
the coefficients if the degree sum is `10`, and `0` otherwise. -/
theorem coeff_prod (K : Type) [Field K] (a b h : K) (σ : Equiv.Perm (Fin 5)) :
    ((∏ i : Fin 5, zpgWMat (K := K) a b h (σ i) i).coeff (Finsupp.single (0 : Fin 1) 10))
      = if (∑ i, zdd (σ i) i) = 10 then (∏ i, zcc K a b h (σ i) i) else 0 := by
  have hprod : (∏ i : Fin 5, zpgWMat (K := K) a b h (σ i) i)
      = C (∏ i, zcc K a b h (σ i) i) * (X 0) ^ (∑ i, zdd (σ i) i) := by
    simp only [zpgWMat_entry]
    rw [Finset.prod_mul_distrib]
    congr 1
    · rw [← map_prod]
    · exact Finset.prod_pow_eq_pow_sum Finset.univ (fun i => zdd (σ i) i) (X 0)
  rw [hprod, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X_pow]
  by_cases h : (∑ i, zdd (σ i) i) = 10
  · rw [if_pos (by rw [h]), if_pos h, mul_one]
  · rw [if_neg (fun hc => h ((Finsupp.single_injective (0 : Fin 1)) hc)), if_neg h, mul_zero]

/-- **The coefficient of `X 0 ^ 10` in `(zpgWMat a b h).det` is `-(a^10 * b^10 * h^14)`.** -/
theorem coeff_det (K : Type) [Field K] (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) :
    (zpgWMat (K := K) a b h).det.coeff (Finsupp.single (0 : Fin 1) 10)
      = -(a ^ 10 * b ^ 10 * h ^ 14) := by
  rw [Matrix.det_apply, MvPolynomial.coeff_sum]
  simp only [Units.smul_def]
  rw [Finset.sum_eq_single s1]
  · rw [coeff_zsmul, coeff_prod, s1_sign, if_pos dd_s1]
    rw [Fin.prod_univ_five, s1_zero, s1_one, s1_two, s1_three, s1_four]
    simp [zcc]
    first | refl_ring1 | ring
  · intro σ _ hσ
    rw [coeff_zsmul, coeff_prod]
    rw [if_neg (fun h => hσ (dd_eq σ h)), zsmul_zero]
  · intro h
    exact absurd (Finset.mem_univ s1) h

/-- **`zpgWMat` has a nonzero determinant.** -/
theorem WDetNeZero (K : Type) [Field K] (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) :
    (zpgWMat (K := K) a b h).det ≠ 0 := by
  intro h0
  have hc := coeff_det K a b h ha hb hh
  rw [h0] at hc
  have h' : (-(a ^ 10 * b ^ 10 * h ^ 14) : K) = 0 := by simpa using hc.symm
  exact (neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero (pow_ne_zero 10 ha) (pow_ne_zero 10 hb))
    (pow_ne_zero 14 hh))) h'

/-! ## The saturation leaf -/

/-- **`zpgW4` is a non-zero-divisor modulo the chart ideal `zpgI4` of the twisted Klein curve.**
This is the `hkey` input of `Work.MotK.TGen.ZpgI4NormalForm`, hence the input of
`Work.MotK.TGen.ZpgI4SatW`. -/
theorem zpgI4W4NonZeroDiv (K : Type) [Field K] (a b h : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) (u : MvPolynomial (Fin 4) K)
    (hu : zpgW4 a b h * u ∈ zpgI4 a b h) : u ∈ zpgI4 a b h := by
  refine ZpgI4W4NonZeroDiv_of K a b h ?_ ?_ ?_ ?_ u hu
  · intro f
    obtain ⟨g, hg⟩ := ZpgI4SpanMain K a b h ha hb hh f
    exact ⟨g, by rw [zpgSum_eq]; simpa only [zpgEmb] using hg⟩
  · intro g hg i
    rw [zpgSum_eq] at hg
    simpa only [zpgEmb] using ZpgI4StdIndependent K a b h ha hb hh g hg i
  · exact ZpgWMatMulMain K a b h ha hb hh
  · exact WDetNeZero K a b h ha hb hh

end Work.MotK.K6WDet
