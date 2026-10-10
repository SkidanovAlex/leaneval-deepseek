import Mathlib
import Submission.Work.MotAS.ASMinv
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Characteristic-`5` invertibility of the explicit Lagrange matrix `asMinv`

Part of the subproject `Submission/Work/MotAS` (`Work.MotAS`), node **AS-EQ**.

`asM w i j = (w + i)^j` is the Vandermonde matrix on the five nodes `w, w+1, …, w+4`, and
`asMinv w j i = δ_{j,0} - (w+i)^{4-j}` is the Lagrange interpolation matrix (see the header of
`Submission/Work/MotAS/ASMinv.lean`).  In a commutative ring of characteristic `5` they are
mutually inverse; this file proves `asM w * asMinv w = 1`.

The proof is the geometric-series computation of the entry

`(asM w * asMinv w) i k = 1 - Σ_{j=0}^{4} (w+i)^j (w+k)^{4-j}`,

together with `Σ_{j=0}^{4} (w+i)^j (w+k)^{4-j} = ((w+i) - (w+k))^4` (an identity that holds
exactly in characteristic `5`, where `5 · X = 0`), and the small characteristic-`5` computation
`((i-k))^4 = if i = k then 0 else 1` for `i, k : Fin 5`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace Work.MotAS

/-- In a ring of characteristic `5`, a natural number is congruent to its residue modulo `5`. -/
private lemma natCast_eq_mod5 {R : Type*} [CommRing R] (h5 : (5 : R) = 0) (n : ℕ) :
    ((n : ℕ) : R) = ((n % 5 : ℕ) : R) := by
  have h5' : ((5 : ℕ) : R) = 0 := h5
  conv_lhs => rw [← Nat.div_add_mod n 5]
  rw [Nat.cast_add, Nat.cast_mul, h5', zero_mul, zero_add]

/-- **Leaf case** `1 - ((i : R) - (k : R))^4 = if i = k then 1 else 0` for `i k : Fin 5` in
characteristic `5`; equivalently `((i - k : R))^4 = if i = k then 0 else 1`.

For `i ≠ k` the difference `i - k` is (up to sign) one of `1,2,3,4`, whose fourth powers are
`1,16,81,256 ≡ 1 (mod 5)`. -/
private lemma one_sub_fourth_sub {R : Type*} [CommRing R] (h5 : (5 : R) = 0) (i k : Fin 5) :
    1 - (((i : ℕ) : R) - ((k : ℕ) : R))^4 = if i = k then (1 : R) else 0 := by
  by_cases h : i = k
  · subst h; simp
  · rw [ite_eq_right h]
    have hd : (((i : ℕ) : R) - ((k : ℕ) : R))^4 = 1 := by
      fin_cases i <;> fin_cases k <;>
        first
          | exact absurd rfl h
          | · norm_num
              try (rw [← Nat.cast_ofNat, natCast_eq_mod5 h5]; norm_num)
    rw [hd]; ring

theorem asM_mul_asMinv {R : Type*} [CommRing R] (h5 : (5 : R) = 0) (w : R) :
    Work.MotAS.asM w * Work.MotAS.asMinv w = (1 : Matrix (Fin 5) (Fin 5) R) := by
  ext i k
  simp only [Matrix.mul_apply, Matrix.one_apply, Work.MotAS.asM, Work.MotAS.asMinv, Matrix.of_apply]
  -- `(asM w * asMinv w) i k = 1 - Σ_{j} (w+i)^j (w+k)^{4-j}`: split the delta term off the sum.
  have hstep : ∀ j : Fin 5,
      (w + ((i : ℕ) : R)) ^ (j : ℕ) *
          ((if (j : ℕ) = 0 then (1 : R) else 0) - (w + ((k : ℕ) : R)) ^ (4 - (j : ℕ)))
        = (w + ((i : ℕ) : R)) ^ (j : ℕ) * (if (j : ℕ) = 0 then (1 : R) else 0)
          - (w + ((i : ℕ) : R)) ^ (j : ℕ) * (w + ((k : ℕ) : R)) ^ (4 - (j : ℕ)) := by
    intro j; rw [mul_sub]
  simp only [hstep, Finset.sum_sub_distrib]
  -- The delta part of the sum is `1`.
  have hdelta :
      (∑ j : Fin 5, (w + ((i : ℕ) : R)) ^ (j : ℕ) * (if (j : ℕ) = 0 then (1 : R) else 0))
        = 1 := by
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
    norm_num
  -- The remaining part is `((w+i) - (w+k))^4` in characteristic `5`.
  have hS : (∑ j : Fin 5, (w + ((i : ℕ) : R)) ^ (j : ℕ) * (w + ((k : ℕ) : R)) ^ (4 - (j : ℕ)))
      = ((w + ((i : ℕ) : R)) - (w + ((k : ℕ) : R)))^4 := by
    have hexp :
        (∑ j : Fin 5, (w + ((i : ℕ) : R)) ^ (j : ℕ) * (w + ((k : ℕ) : R)) ^ (4 - (j : ℕ)))
          = (w + ((i : ℕ) : R))^4 + (w + ((i : ℕ) : R))^3 * (w + ((k : ℕ) : R))
            + (w + ((i : ℕ) : R))^2 * (w + ((k : ℕ) : R))^2
            + (w + ((i : ℕ) : R)) * (w + ((k : ℕ) : R))^3 + (w + ((k : ℕ) : R))^4 := by
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
      norm_num
      first | refl_ring1 | ring
    rw [hexp]
    have hlin : ((w + ((i : ℕ) : R)) - (w + ((k : ℕ) : R)))^4
        = (w + ((i : ℕ) : R))^4 + (w + ((i : ℕ) : R))^3 * (w + ((k : ℕ) : R))
          + (w + ((i : ℕ) : R))^2 * (w + ((k : ℕ) : R))^2
          + (w + ((i : ℕ) : R)) * (w + ((k : ℕ) : R))^3 + (w + ((k : ℕ) : R))^4
          + 5 * ((w + ((i : ℕ) : R))^2 * (w + ((k : ℕ) : R))^2
              - (w + ((i : ℕ) : R))^3 * (w + ((k : ℕ) : R))
              - (w + ((i : ℕ) : R)) * (w + ((k : ℕ) : R))^3) := by ring
    rw [hlin, h5, zero_mul, add_zero]
  rw [hdelta, hS]
  have hdv : (w + ((i : ℕ) : R)) - (w + ((k : ℕ) : R)) = ((i : ℕ) : R) - ((k : ℕ) : R) := by ring
  rw [hdv]
  exact one_sub_fourth_sub h5 i k

end Work.MotAS
