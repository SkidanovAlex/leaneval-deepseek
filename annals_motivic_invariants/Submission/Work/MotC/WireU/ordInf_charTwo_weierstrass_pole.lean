import Mathlib
import Submission.Work.Genus.Defs
import Submission.Work.Genus.OrderInf.ordInf_add_eq_of_lt
import Submission.Work.Genus.OrderInf.ordInf_pow
import Submission.Work.Genus.OrderInf.ordInf_C_mul
import Submission.Work.Genus.OrderInf.ordInf_aeval_of_neg
import Submission.Work.Genus.OrderInf.ordInf_mul
import Submission.Work.Genus.OrderInf.ordInf_polynomial
import Submission.Work.Genus.OrderInf.min_ordInf_le_ordInf_add

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotC.WireU

open Polynomial

/-- The order at infinity of a constant: a constant rational function has neither a zero nor a
pole at infinity (the value `0` is the `RatFunc.intDegree 0 = 0` convention). -/
private lemma ordInf_algebraMap_const {K : Type*} [Field K] (c : K) :
    Work.Genus.ordInf (algebraMap K (RatFunc K) c) = 0 := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp [Work.Genus.ordInf]
  · rw [Work.Genus.ordInf, RatFunc.algebraMap_eq_C, RatFunc.intDegree_C, neg_zero]

theorem ordInf_charTwo_weierstrass_pole {K : Type*} [Field K] [CharP K 2] (a₁ a₂ a₃ a₄ a₆ : K) {x y : RatFunc K}
    (h : y ^ 2 + algebraMap K (RatFunc K) a₁ * x * y + algebraMap K (RatFunc K) a₃ * y
      = x ^ 3 + algebraMap K (RatFunc K) a₂ * x ^ 2 + algebraMap K (RatFunc K) a₄ * x
        + algebraMap K (RatFunc K) a₆)
    (hx : Work.Genus.ordInf x < 0) :
    (2 : ℤ) ∣ Work.Genus.ordInf x ∧ 2 * Work.Genus.ordInf y = 3 * Work.Genus.ordInf x := by
  -- `x ≠ 0` since it has a pole at infinity.
  have hxne : x ≠ 0 := by
    intro h0
    rw [h0] at hx
    simp [Work.Genus.ordInf] at hx
  -- The cubic realizing the right-hand side of the Weierstrass equation.
  set F : Polynomial K := X ^ 3 + C a₂ * X ^ 2 + C a₄ * X + C a₆ with hF
  have hFaeval : Polynomial.aeval x F
      = x ^ 3 + algebraMap K (RatFunc K) a₂ * x ^ 2 + algebraMap K (RatFunc K) a₄ * x
        + algebraMap K (RatFunc K) a₆ := by
    rw [hF]; simp
  have hFdeg : F.natDegree = 3 := by
    rw [hF]
    have hle : (X ^ 3 + C a₂ * X ^ 2 + C a₄ * X + C a₆ : K[X]).natDegree ≤ 3 := by
      compute_degree!
    exact Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hle (by simp)
  -- The right-hand side has a pole of order exactly `3 * ordInf x` (the leading cubic term
  -- strictly dominates).
  have hRHS : Work.Genus.ordInf (x ^ 3 + algebraMap K (RatFunc K) a₂ * x ^ 2
        + algebraMap K (RatFunc K) a₄ * x + algebraMap K (RatFunc K) a₆)
      = 3 * Work.Genus.ordInf x := by
    rw [← hFaeval, Work.Genus.OrderInf.ordInf_aeval_of_neg (by rw [hFdeg]; norm_num) hxne hx,
      hFdeg]
    norm_num
  have hRHSne : (x ^ 3 + algebraMap K (RatFunc K) a₂ * x ^ 2 + algebraMap K (RatFunc K) a₄ * x
      + algebraMap K (RatFunc K) a₆) ≠ 0 := by
    intro h0
    have : Work.Genus.ordInf (x ^ 3 + algebraMap K (RatFunc K) a₂ * x ^ 2
        + algebraMap K (RatFunc K) a₄ * x + algebraMap K (RatFunc K) a₆) = 0 := by
      rw [h0]; simp [Work.Genus.ordInf]
    rw [hRHS] at this
    exact (ne_of_lt hx) (by linarith)
  -- The completed ordinate `w = a₁ x + a₃`, and `g = y + w`.
  set w : RatFunc K := algebraMap K (RatFunc K) a₁ * x + algebraMap K (RatFunc K) a₃ with hw
  set g : RatFunc K := y + w with hg
  -- The left-hand side of the Weierstrass equation factors as `y * g` (this needs no characteristic
  -- assumption).
  have hfactor : y * g = y ^ 2 + algebraMap K (RatFunc K) a₁ * x * y
      + algebraMap K (RatFunc K) a₃ * y := by
    rw [hg, hw]; ring
  -- hence `y * g` equals the (non-zero) right-hand side, so `y ≠ 0` and `g ≠ 0`.
  have hyg : y * g = x ^ 3 + algebraMap K (RatFunc K) a₂ * x ^ 2
      + algebraMap K (RatFunc K) a₄ * x + algebraMap K (RatFunc K) a₆ := by
    rw [hfactor]; exact h
  have hprodne : y * g ≠ 0 := by
    rw [hyg]; exact hRHSne
  have hy : y ≠ 0 := left_ne_zero_of_mul hprodne
  have hgne : g ≠ 0 := right_ne_zero_of_mul hprodne
  -- Multiplicativity of the order at infinity on the product `y * g = x³ + …`.
  have hpq : Work.Genus.ordInf y + Work.Genus.ordInf g = 3 * Work.Genus.ordInf x := by
    have h1 := Work.Genus.OrderInf.ordInf_mul hy hgne
    rw [hyg, hRHS] at h1
    exact h1.symm
  -- `y + g = w`, using characteristic two.
  have hygw : y + g = w := by
    rw [hg, hw]
    have hyy : y + y = 0 := CharTwo.add_self_eq_zero y
    rw [← add_assoc, hyy, zero_add]
  -- `w = a₁ x + a₃` has order at infinity at least that of `x`.
  have hw_ge : Work.Genus.ordInf x ≤ Work.Genus.ordInf w := by
    by_cases ha₁ : a₁ = 0
    · have hwv : w = algebraMap K (RatFunc K) a₃ := by
        rw [hw, ha₁, map_zero, zero_mul, zero_add]
      rw [hwv, ordInf_algebraMap_const]
      exact le_of_lt hx
    · rw [hw]
      have hlt : Work.Genus.ordInf (algebraMap K (RatFunc K) a₁ * x)
          < Work.Genus.ordInf (algebraMap K (RatFunc K) a₃) := by
        rw [Work.Genus.OrderInf.ordInf_C_mul ha₁ x, ordInf_algebraMap_const a₃]
        exact hx
      have hne1 : algebraMap K (RatFunc K) a₁ * x ≠ 0 := by
        intro h0
        have : Work.Genus.ordInf (algebraMap K (RatFunc K) a₁ * x) = 0 := by
          rw [h0]; simp [Work.Genus.ordInf]
        rw [Work.Genus.OrderInf.ordInf_C_mul ha₁ x] at this
        exact (ne_of_lt hx) this
      rw [Work.Genus.OrderInf.ordInf_add_eq_of_lt hne1 hlt,
        Work.Genus.OrderInf.ordInf_C_mul ha₁ x]
  -- Core: `ordInf y = ordInf g`.  Otherwise the smaller one is `≥ ordInf x` while the sum of the
  -- two is `3 * ordInf x`, which is impossible because `ordInf x < 0`.
  have hpq_eq : Work.Genus.ordInf y = Work.Genus.ordInf g := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have heq : Work.Genus.ordInf (y + g) = Work.Genus.ordInf y :=
        Work.Genus.OrderInf.ordInf_add_eq_of_lt hy hlt
      have hge : Work.Genus.ordInf x ≤ Work.Genus.ordInf y := by
        rw [← heq, hygw]; exact hw_ge
      linarith
    · have heq : Work.Genus.ordInf (y + g) = Work.Genus.ordInf g := by
        rw [add_comm y g]
        exact Work.Genus.OrderInf.ordInf_add_eq_of_lt hgne hlt
      have hge : Work.Genus.ordInf x ≤ Work.Genus.ordInf g := by
        rw [← heq, hygw]; exact hw_ge
      linarith
  have hkey : 2 * Work.Genus.ordInf y = 3 * Work.Genus.ordInf x := by
    rw [← hpq_eq] at hpq
    linarith
  exact ⟨⟨Work.Genus.ordInf y - Work.Genus.ordInf x, by linarith⟩, hkey⟩

end Work.MotC.WireU
