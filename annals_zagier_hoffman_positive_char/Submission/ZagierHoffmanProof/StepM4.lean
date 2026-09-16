import Submission.ZagierHoffmanProof.ThakurDeg4
import Submission.ZagierHoffmanProof.ThakurDeg2

set_option autoImplicit false
set_option maxHeartbeats 8000000

open Polynomial RatFunc
open scoped BigOperators WithZero
open WithZero

/-!
# Step M4: valuation bookkeeping for the level recursion of the power sums

This module begins the formalisation of Thakur's *level* recursion for the power sums
(`S_{d+1}(k) = − Σ_{j : q−1 ∣ j} C(−k,j) t^{−k−j} S_d(k+j)`, Thakur, *Power sums ...*,
§3.2), which refines the crude bound `v (P_d k) ≤ v (P_1 k)^d` of `ThakurDeg4.v_P_le`.

The first ingredients recorded here are the exact valuations of the nonzero constants and
of the powers of `X` inside the completion at infinity, together with the general
"valuation of a finite sum is at most the maximum" principle in the ordered value group
`ℤᵐ⁰`.
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

section Constants

/-- A nonzero constant of `F` has valuation `1` inside the completion at infinity. -/
lemma v_cst_of_ne_zero {a : F} (ha : a ≠ 0) : Valued.v (cst F a) = 1 := by
  rw [cst, cstHom, RingHom.comp_apply, toK]
  have h : (algebraMap F (RatFunc F)) a ≠ 0 := by simpa using ha
  rw [v_toK F _ h, RatFunc.algebraMap_eq_C, RatFunc.intDegree_C, WithZero.exp_zero]

/-- `v (X^n) = exp n` in the completion at infinity. -/
lemma v_coe_X_pow (n : ℕ) :
    Valued.v ((((Polynomial.X ^ n : F[X]) : RatFunc F))
      : RatFunc.CompletionAtInfty F) = exp (n : ℤ) := by
  have hp : (Polynomial.X ^ n : F[X]) ≠ 0 := pow_ne_zero n Polynomial.X_ne_zero
  rw [inftyValued_v_polynomial F _ hp, Polynomial.natDegree_X_pow]

/-- The inverse-power form: `v ((X^n)^{-1}) = exp (−n)`. -/
lemma v_coe_X_pow_inv (n : ℕ) :
    Valued.v (((((Polynomial.X ^ n : F[X]) : RatFunc F))
      : RatFunc.CompletionAtInfty F))⁻¹ = exp (-(n : ℤ)) := by
  have hp : (Polynomial.X ^ n : F[X]) ≠ 0 := pow_ne_zero n Polynomial.X_ne_zero
  have h : ((((Polynomial.X ^ n : F[X]) : RatFunc F)) : RatFunc.CompletionAtInfty F) ≠ 0 := by
    intro hzero
    have := inftyValued_v_polynomial F _ hp
    rw [hzero, map_zero] at this
    exact (WithZero.exp_ne_zero) this.symm
  rw [Valuation.map_inv, v_coe_X_pow F n]
  exact (WithZero.exp_neg (n : ℤ)).symm

end Constants

section Sums

/-- The valuation of a finite sum is (in `ℤᵐ⁰`) at most the maximum of the valuational
bounds of its terms. -/
lemma v_finset_sum_le {ι : Type*} (s : Finset ι) (f : ι → RatFunc.CompletionAtInfty F)
    {B : ℤᵐ⁰} (h : ∀ i ∈ s, Valued.v (f i) ≤ B) :
    Valued.v (∑ i ∈ s, f i) ≤ B := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      refine le_trans (Valuation.map_add_le_max' (self := Valued.v) _ _) (max_le ?_ ?_)
      · exact h a (Finset.mem_insert_self a s)
      · refine ih ?_
        intro i hi
        exact h i (Finset.mem_insert_of_mem hi)

end Sums

end ZagierHoffmanPositiveChar
