import Mathlib
import Submission.Work.MotAS.ASMinv

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `asMinv w * asM w = 1` in characteristic `5`

Part of the subproject `Submission/Work/MotAS` (`Work.MotAS`), node **AS-EQ**
(`Work.MotAS.twistFieldAS_eq`).

`asM w i j = (w+i)^j` is the Vandermonde matrix in the five nodes `w, w+1, …, w+4`, and
`asMinv w j i = δ_{j,0} - (w+i)^{4-j}` is its explicit inverse (Lagrange interpolation), valid over
any commutative ring of characteristic `5`.  This file proves the right-inverse identity
`asMinv w * asM w = 1`; the left-inverse identity `asM w * asMinv w = 1` is the sibling node
`Submission/Work/MotAS/asM_mul_asMinv.lean`.

The whole content is the evaluation of the power sums

`∑_{i=0}^{4} (w+i)^n = 0` for `n ∈ {0,1,2,3,5,6,7}` and `= -1` for `n ∈ {4,8}`

in characteristic `5` (the entries of the product only involve the exponents `0 ≤ n ≤ 8`).  They
are proved as explicit polynomial identities in `ℤ[w]` in which the non-constant part is a multiple
of `5`, plus the characteristic-`5` relation `4 = -1`.
-/

set_option autoImplicit false

namespace Work.MotAS

variable {R : Type*} [CommRing R]

/-- In characteristic `5` one has `4 = -1`. -/
private lemma four_eq_neg_one (h5 : (5 : R) = 0) : (4 : R) = -(1 : R) := by
  have h : (4 : R) + 1 = 0 := by
    have : (4 : R) + 1 = (5 : R) := by norm_num
    rw [this, h5]
  exact eq_neg_iff_add_eq_zero.mpr h

/-- **The five power sums of `0,1,2,3,4` in characteristic `5`.**  For `n ≤ 8`,
`∑_{i=0}^{4} (w+i)^n` vanishes unless `n ∈ {4,8}`, in which case it equals `-1`. -/
private lemma sum_pow_five (h5 : (5 : R) = 0) (w : R) (n : ℕ) (hn : n ≤ 8) :
    (∑ i : Fin 5, (w + (i : ℕ))^n) = if n = 4 ∨ n = 8 then (-1 : R) else 0 := by
  have h4 := four_eq_neg_one h5
  interval_cases n
  · have h : (∑ i : Fin 5, (w + (i : ℕ))^0) = 0 := by
      rw [Fin.sum_univ_five]; norm_num; exact h5
    rw [h]; norm_num
  · have h : (∑ i : Fin 5, (w + (i : ℕ))^1) = 5 * (w + 2) := by
      rw [Fin.sum_univ_five]; norm_num; ring
    rw [h, h5, zero_mul]; norm_num
  · have h : (∑ i : Fin 5, (w + (i : ℕ))^2) = 5 * (w^2 + 4*w + 6) := by
      rw [Fin.sum_univ_five]; norm_num; ring
    rw [h, h5, zero_mul]; norm_num
  · have h : (∑ i : Fin 5, (w + (i : ℕ))^3) = 5 * (w^3 + 6*w^2 + 18*w + 20) := by
      rw [Fin.sum_univ_five]; norm_num; ring
    rw [h, h5, zero_mul]; norm_num
  · have h : (∑ i : Fin 5, (w + (i : ℕ))^4) = 5 * (w^4 + 8*w^3 + 36*w^2 + 80*w + 70) + 4 := by
      rw [Fin.sum_univ_five]; norm_num; ring
    rw [h, h5, zero_mul, zero_add, h4]; norm_num
  · have h : (∑ i : Fin 5, (w + (i : ℕ))^5)
        = 5 * (w^5 + 10*w^4 + 60*w^3 + 200*w^2 + 354*w + 260) := by
      rw [Fin.sum_univ_five]; norm_num; ring
    rw [h, h5, zero_mul]; norm_num
  · have h : (∑ i : Fin 5, (w + (i : ℕ))^6)
        = 5 * (w^6 + 12*w^5 + 90*w^4 + 400*w^3 + 1062*w^2 + 1560*w + 978) := by
      rw [Fin.sum_univ_five]; norm_num; ring
    rw [h, h5, zero_mul]; norm_num
  · have h : (∑ i : Fin 5, (w + (i : ℕ))^7)
        = 5 * (w^7 + 14*w^6 + 126*w^5 + 700*w^4 + 2478*w^3 + 5460*w^2 + 6846*w + 3740) := by
      rw [Fin.sum_univ_five]; norm_num; ring
    rw [h, h5, zero_mul]; norm_num
  · have h : (∑ i : Fin 5, (w + (i : ℕ))^8)
        = 5 * (w^8 + 16*w^7 + 168*w^6 + 1120*w^5 + 4956*w^4 + 14560*w^3 + 27384*w^2
            + 29920*w + 14470) + 4 := by
      rw [Fin.sum_univ_five]; norm_num; ring
    rw [h, h5, zero_mul, zero_add, h4]; norm_num

/-- Entrywise form of the product: the `(j,k)` entry of `asMinv w * asM w` is the difference of
the two power sums `δ_{j,0}·∑_i (w+i)^k` and `∑_i (w+i)^{4-j+k}`. -/
private lemma entry_eq (w : R) (j k : Fin 5) :
    (∑ i : Fin 5, Work.MotAS.asMinv w j i * Work.MotAS.asM w i k)
      = (if (j:ℕ) = 0 then (1:R) else 0) * (∑ i : Fin 5, (w + (i:ℕ))^(k:ℕ))
        - ∑ i : Fin 5, (w + (i:ℕ))^(4 - (j:ℕ) + (k:ℕ)) := by
  calc (∑ i : Fin 5, Work.MotAS.asMinv w j i * Work.MotAS.asM w i k)
      = ∑ i : Fin 5, ((if (j:ℕ) = 0 then (1:R) else 0) * (w + (i:ℕ))^(k:ℕ)
          - (w + (i:ℕ))^(4 - (j:ℕ) + (k:ℕ))) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        simp only [Work.MotAS.asMinv, Work.MotAS.asM, Matrix.of_apply]
        rw [sub_mul, ← pow_add]
    _ = (if (j:ℕ) = 0 then (1:R) else 0) * (∑ i : Fin 5, (w + (i:ℕ))^(k:ℕ))
          - ∑ i : Fin 5, (w + (i:ℕ))^(4 - (j:ℕ) + (k:ℕ)) := by
        rw [Finset.sum_sub_distrib, Finset.mul_sum]

/-- The arithmetic core: with the power sums replaced by their values `0`/`-1`, the `(j,k)` entry
of `asMinv w * asM w` is the Kronecker delta. -/
private lemma entry_arith (j k : Fin 5) :
    (if (j:ℕ) = 0 then (1:R) else 0) * (if ((k:ℕ) = 4 ∨ (k:ℕ) = 8) then (-1:R) else 0)
      - (if (4 - (j:ℕ) + (k:ℕ)) = 4 ∨ (4 - (j:ℕ) + (k:ℕ)) = 8 then (-1:R) else 0)
      = if j = k then (1:R) else 0 := by
  fin_cases j <;> fin_cases k <;> norm_num

theorem asMinv_mul_asM {R : Type*} [CommRing R] (h5 : (5 : R) = 0) (w : R) :
    Work.MotAS.asMinv w * Work.MotAS.asM w = (1 : Matrix (Fin 5) (Fin 5) R) := by
  ext j k
  rw [Matrix.mul_apply, Matrix.one_apply]
  rw [entry_eq w j k]
  have hk : (∑ i : Fin 5, (w + (i:ℕ))^(k:ℕ))
      = if (k:ℕ) = 4 ∨ (k:ℕ) = 8 then (-1:R) else 0 :=
    sum_pow_five h5 w (k:ℕ) (by have h := k.isLt; omega)
  have hm : (∑ i : Fin 5, (w + (i:ℕ))^(4 - (j:ℕ) + (k:ℕ)))
      = if (4 - (j:ℕ) + (k:ℕ)) = 4 ∨ (4 - (j:ℕ) + (k:ℕ)) = 8 then (-1:R) else 0 :=
    sum_pow_five h5 w _ (by have hj := j.isLt; have hk := k.isLt; omega)
  rw [hk, hm]
  exact entry_arith j k

end Work.MotAS
