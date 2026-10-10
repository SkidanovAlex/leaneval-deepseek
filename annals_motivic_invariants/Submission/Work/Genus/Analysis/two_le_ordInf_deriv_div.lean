import Mathlib
import Submission.Work.Genus.Defs
import Submission.Work.Genus.OrderInf.ordInf_mul
import Submission.Work.Genus.OrderInf.ordInf_pow
import Submission.Work.Genus.OrderInf.ordInf_div
import Submission.Work.Genus.OrderInf.ordInf_C_mul
import Submission.Work.Genus.OrderInf.min_ordInf_le_ordInf_add
import Submission.Work.Genus.OrderInf.ordInf_add_eq_of_lt
import Submission.Work.Genus.OrderInf.ordInf_aeval_of_neg
import Submission.Work.Genus.OrderInf.ordInf_aeval_nonneg
import Submission.Work.Genus.OrderInf.ordInf_deriv_ge
import Submission.Work.Genus.OrderInf.two_le_ordInf_deriv
import Submission.Work.Genus.OrderInf.ordInf_polynomial
import Submission.Work.Genus.Deriv.deriv_aeval
import Submission.Work.Genus.Deriv.deriv_mul
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Genus.Analysis

/-- **Regularity of the pulled-back invariant differential at infinity.**  In the situation of
`Work.Genus.Analysis.ord_deriv_div_nonneg` (squarefree cubic `A` of degree `3`, `w ≠ 0`,
`A(x) = w²`, `deriv x ≠ 0`, characteristic `≠ 2`) one has `2 ≤ ordInf (deriv x / w)`: `(x'/w) dt` is
regular at infinity with a zero of order at least `2`.

Route: mirror the finite analysis with `ordInf` (the same case split, using
`ordInf_aeval_of_neg`, `ordInf_deriv_ge`, `two_le_ordInf_deriv`, `ordInf_div`), using the chain rule
as in `Work.Genus.Analysis.ord_deriv_div_nonneg`:
* `m := ordInf x < 0`: `ordInf (A(x)) = 3m`, `2 * ordInf w = 3m`, and
  `ordInf (deriv x) ≥ m + 1`, so `ordInf (deriv x / w) ≥ 1 - m/2 ≥ 2` (since `3m` is even and
  `m ≤ -2`).
* `ordInf x ≥ 0` and `ordInf w = 0`: `2 ≤ ordInf (deriv x)` (`two_le_ordInf_deriv`).
* `ordInf x ≥ 0` and `ordInf w = e > 0`: the Bezout argument forces `ordInf (A'(x)) ≤ 0` and
  `ordInf (deriv w) ≥ e + 1`, so `ordInf (deriv x) ≥ 2e + 1 ≥ e + 2`. -/
theorem two_le_ordInf_deriv_div {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) {A : Polynomial F}
    (hA : A.natDegree = 3) (hsq : IsCoprime A (Polynomial.derivative A)) {x w : RatFunc F}
    (hw : w ≠ 0) (hx' : Work.Genus.deriv x ≠ 0) (heq : Polynomial.aeval x A = w ^ 2) :
    2 ≤ Work.Genus.ordInf (Work.Genus.deriv x / w) := by
  -- `deriv x / w` is a quotient of two non-zero functions, so its order is the difference.
  have hdiv : Work.Genus.ordInf (Work.Genus.deriv x / w)
      = Work.Genus.ordInf (Work.Genus.deriv x) - Work.Genus.ordInf w :=
    Work.Genus.OrderInf.ordInf_div hx' hw
  by_cases hm : Work.Genus.ordInf x < 0
  · -- ### Case 1: `x` has a pole at infinity, `m = ordInf x < 0`.
    have hx0 : x ≠ 0 := by
      intro h0
      rw [h0] at hm
      simp [Work.Genus.ordInf] at hm
    have hAp : 0 < A.natDegree := by rw [hA]; norm_num
    -- `ordInf (A(x)) = 3 * ordInf x`
    have h1 : Work.Genus.ordInf (Polynomial.aeval x A) = 3 * Work.Genus.ordInf x := by
      rw [Work.Genus.OrderInf.ordInf_aeval_of_neg hAp hx0 hm, hA]
      norm_num
    -- `= ordInf (w ^ 2) = 2 * ordInf w`
    have h2eq : Work.Genus.ordInf (Polynomial.aeval x A) = 2 * Work.Genus.ordInf w := by
      rw [heq, Work.Genus.OrderInf.ordInf_pow hw 2]
      first | refl_ring1 | ring
    have h3 : (3 : ℤ) * Work.Genus.ordInf x = 2 * Work.Genus.ordInf w := by linarith
    -- `m` is even: `m = 2k` with `k = ordInf w - ordInf x`
    obtain ⟨k, hk⟩ : ∃ k : ℤ, Work.Genus.ordInf x = 2 * k :=
      ⟨Work.Genus.ordInf w - Work.Genus.ordInf x, by linarith⟩
    have hwk : Work.Genus.ordInf w = 3 * k := by linarith
    have hk1 : k ≤ -1 := by linarith
    -- differentiating increases the order at a pole: `ordInf (deriv x) ≥ ordInf x + 1`
    have h4 : Work.Genus.ordInf x + 1 ≤ Work.Genus.ordInf (Work.Genus.deriv x) :=
      Work.Genus.OrderInf.ordInf_deriv_ge hx0 hx'
    rw [hdiv]
    linarith
  · -- ### The remaining cases: `0 ≤ ordInf x`, so `w ^ 2 = A(x)` has non-negative order.
    have hmnn : 0 ≤ Work.Genus.ordInf x := not_lt.mp hm
    have hAle : 0 ≤ Work.Genus.ordInf (Polynomial.aeval x A) :=
      Work.Genus.OrderInf.ordInf_aeval_nonneg hmnn
    have hwne : 0 ≤ Work.Genus.ordInf w := by
      have h2eq : Work.Genus.ordInf (Polynomial.aeval x A) = 2 * Work.Genus.ordInf w := by
        rw [heq, Work.Genus.OrderInf.ordInf_pow hw 2]
        first | refl_ring1 | ring
      linarith
    rcases lt_or_eq_of_le hwne with hepos | hezero
    · -- ### Case 3: `e = ordInf w > 0`.
      -- Bezout: `u * A + v * A' = 1`, evaluated at `x`.
      obtain ⟨u, v, huv⟩ := hsq
      set U := Polynomial.aeval x u with hUdef
      set V := Polynomial.aeval x v with hVdef
      set Apr := Polynomial.aeval x (Polynomial.derivative A) with hAprdef
      have hbez : U * w ^ 2 + V * Apr = 1 := by
        have h := congrArg (Polynomial.aeval x) huv
        simp only [Polynomial.aeval_mul, Polynomial.aeval_add, Polynomial.aeval_one] at h
        rw [heq] at h
        exact h
      have hUnn : 0 ≤ Work.Genus.ordInf U :=
        Work.Genus.OrderInf.ordInf_aeval_nonneg (A := u) hmnn
      have hVnn : 0 ≤ Work.Genus.ordInf V :=
        Work.Genus.OrderInf.ordInf_aeval_nonneg (A := v) hmnn
      have h1ne : (1 : RatFunc F) ≠ 0 := one_ne_zero
      -- `V * Apr ≠ 0`: otherwise `U * w ^ 2 = 1` would have order `0`, while it is `≥ 2e > 0`.
      have hVA_ne : V * Apr ≠ 0 := by
        intro h0
        have hUw : U * w ^ 2 = 1 := by
          have h' := hbez
          rw [h0, add_zero] at h'
          exact h'
        have hUne : U ≠ 0 := by
          intro hU0
          rw [hU0, zero_mul] at hUw
          exact h1ne hUw.symm
        have h1 : Work.Genus.ordInf (U * w ^ 2) = 0 := by
          rw [hUw]; simp [Work.Genus.ordInf]
        have h2 : Work.Genus.ordInf (U * w ^ 2)
            = Work.Genus.ordInf U + 2 * Work.Genus.ordInf w := by
          rw [Work.Genus.OrderInf.ordInf_mul hUne (pow_ne_zero 2 hw),
            Work.Genus.OrderInf.ordInf_pow hw 2]
          first | refl_ring1 | ring
        omega
      -- `ordInf (V * Apr) = 0`: either `U * w ^ 2 = 0` and `V * Apr = 1`, or `U * w ^ 2 ≠ 0`
      -- has strictly positive order and `V * Apr = 1 - U * w ^ 2` keeps the minimal order `0`.
      have hVA_zero : Work.Genus.ordInf (V * Apr) = 0 := by
        by_cases hU : U * w ^ 2 = 0
        · have h' := hbez
          rw [hU, zero_add] at h'
          rw [h', show Work.Genus.ordInf (1 : RatFunc F) = 0 from by
            simp [Work.Genus.ordInf]]
        · have hUne : U ≠ 0 := by intro h0; exact hU (by rw [h0, zero_mul])
          have hpos : 0 < Work.Genus.ordInf (U * w ^ 2) := by
            rw [Work.Genus.OrderInf.ordInf_mul hUne (pow_ne_zero 2 hw),
              Work.Genus.OrderInf.ordInf_pow hw 2]
            omega
          have hneg : Work.Genus.ordInf (-(U * w ^ 2)) = Work.Genus.ordInf (U * w ^ 2) := by
            simp only [Work.Genus.ordInf, RatFunc.intDegree_neg]
          have hone : Work.Genus.ordInf (1 : RatFunc F) = 0 := by
            simp [Work.Genus.ordInf]
          have hlt : Work.Genus.ordInf (1 : RatFunc F) < Work.Genus.ordInf (-(U * w ^ 2)) := by
            rw [hneg, hone]; exact hpos
          have hVeq : V * Apr = 1 - U * w ^ 2 :=
            (eq_sub_iff_add_eq).mpr (by rw [add_comm]; exact hbez)
          rw [hVeq, sub_eq_add_neg,
            Work.Genus.OrderInf.ordInf_add_eq_of_lt h1ne hlt, hone]
      have hApr_le : Work.Genus.ordInf Apr ≤ 0 := by
        have hVne : V ≠ 0 := left_ne_zero_of_mul hVA_ne
        have hAprne : Apr ≠ 0 := right_ne_zero_of_mul hVA_ne
        have hmul := Work.Genus.OrderInf.ordInf_mul hVne hAprne
        rw [hVA_zero] at hmul
        omega
      have hApr_ne : Apr ≠ 0 := right_ne_zero_of_mul hVA_ne
      -- Chain rule: `A'(x) * x' = 2 w w'`.
      have hchain : Apr * Work.Genus.deriv x = 2 * w * Work.Genus.deriv w := by
        have h1 : Work.Genus.deriv (Polynomial.aeval x A)
            = Polynomial.aeval x (Polynomial.derivative A) * Work.Genus.deriv x :=
          Work.Genus.Deriv.deriv_aeval
        have h2 : Work.Genus.deriv (w ^ 2) = 2 * w * Work.Genus.deriv w := by
          rw [pow_two, Work.Genus.Deriv.deriv_mul]
          first | refl_ring1 | ring
        rw [← h1, heq, h2]
      have hdw : Work.Genus.deriv w ≠ 0 := by
        intro h0
        rw [h0, mul_zero] at hchain
        exact (mul_ne_zero hApr_ne hx') hchain
      have hchain_ord := Work.Genus.OrderInf.ordInf_mul hApr_ne hx'
      rw [hchain] at hchain_ord
      have h2r : (2 : RatFunc F) ≠ 0 := by
        rw [show (2 : RatFunc F) = RatFunc.C (2 : F) from (map_ofNat RatFunc.C 2).symm]
        simpa using RatFunc.C_injective.ne h2
      have h2w : Work.Genus.ordInf ((2 : RatFunc F) * w) = Work.Genus.ordInf w := by
        have hcast : algebraMap F (RatFunc F) (2 : F) = (2 : RatFunc F) := by
          rw [RatFunc.algebraMap_eq_C]
          exact map_ofNat RatFunc.C 2
        rw [← hcast]
        exact Work.Genus.OrderInf.ordInf_C_mul h2 w
      rw [Work.Genus.OrderInf.ordInf_mul (mul_ne_zero h2r hw) hdw, h2w] at hchain_ord
      have hdwge : Work.Genus.ordInf w + 1 ≤ Work.Genus.ordInf (Work.Genus.deriv w) :=
        Work.Genus.OrderInf.ordInf_deriv_ge hw hdw
      rw [hdiv]
      omega
    · -- ### Case 2: `e = ordInf w = 0`.
      have hx0 : x ≠ 0 := by
        intro h0
        exact hx' (by rw [h0]; simp [Work.Genus.deriv])
      have h2le : 2 ≤ Work.Genus.ordInf (Work.Genus.deriv x) :=
        Work.Genus.OrderInf.two_le_ordInf_deriv hx0 hx' hmnn
      rw [hdiv, ← hezero]
      linarith

end Work.Genus.Analysis
