import Mathlib
import Submission.Work.Pure.pure_facts

namespace Work.A14D

open Submission.CDTPlan
open PowerSeries
open scoped BigOperators

/-!
# `Work.A14D.pure_dclosed_spec`

The per-index unfolding of `Work.Pure.dclosed : DClosed pureB`, with the existential
witnesses instantiated to the concrete polynomials `Work.Pure.dq` and `Work.Pure.dA`.

`DClosed` is a `Prop`-valued existential, so the data extracted from `dclosed`
(`dclosed.1`, `dclosed.2.2.1`) is only propositionally, not definitionally, equal to
`Work.Pure.dq` / `Work.Pure.dA`. Hence the identity is reproved here for the concrete
witnesses, by replaying the seven `fin_cases` goals of the proof of `Work.Pure.dclosed`
(file `Submission/Work/Pure/pure_facts.lean`).

The lemmas `relation_B1…B7`, `dq_coe` are reused from `Work.Pure`; the private helper
lemmas `pB0…pB6`, `coe2`, `coe4` of that file are not importable and are reproduced here.
-/

private lemma coe2 : (((2 : Polynomial ℚ)) : PowerSeries ℚ) = (2 : PowerSeries ℚ) := by
  rw [show ((2 : Polynomial ℚ)) = Polynomial.C 2 from rfl, Polynomial.coe_C]; rfl

private lemma coe4 : (((4 : Polynomial ℚ)) : PowerSeries ℚ) = (4 : PowerSeries ℚ) := by
  rw [show ((4 : Polynomial ℚ)) = Polynomial.C 4 from rfl, Polynomial.coe_C]; rfl

private lemma pB0 : pureB (0 : Fin 7) = B1 := rfl
private lemma pB1 : pureB (1 : Fin 7) = B2 := rfl
private lemma pB2 : pureB (2 : Fin 7) = B3 := rfl
private lemma pB3 : pureB (3 : Fin 7) = B4 := rfl
private lemma pB4 : pureB (4 : Fin 7) = B5 := rfl
private lemma pB5 : pureB (5 : Fin 7) = B6 := rfl
private lemma pB6 : pureB (6 : Fin 7) = B7 := rfl

-- This is the per-index unfolding of `Work.Pure.dclosed : DClosed pureB`, but with the
-- existential witnesses *instantiated* to the concrete polynomials `Work.Pure.dq` and
-- `Work.Pure.dA`.
theorem pure_dclosed_spec (i : Fin 7) :
    (Work.Pure.dq : PowerSeries ℚ) * PowerSeries.derivative (R := ℚ) (Submission.CDTPlan.pureB i)
      = ∑ j : Fin 7, (Work.Pure.dA i j : PowerSeries ℚ) * Submission.CDTPlan.pureB j := by
  fin_cases i
  · change (Work.Pure.dq : PowerSeries ℚ) * (PowerSeries.derivative (R := ℚ)) B1
      = ∑ j : Fin 7, (((Work.Pure.dA (0 : Fin 7) j : Polynomial ℚ)) : PowerSeries ℚ) * pureB j
    rw [Fin.sum_univ_seven]
    simp only [Work.Pure.dA, pB0, pB1, pB2, pB3, pB4, pB5, pB6, B1, PowerSeries.derivative_one,
      Polynomial.coe_zero, zero_mul, mul_zero, add_zero, zero_add]
    norm_num
  · change (Work.Pure.dq : PowerSeries ℚ) * (PowerSeries.derivative (R := ℚ)) B2
      = ∑ j : Fin 7, (((Work.Pure.dA (1 : Fin 7) j : Polynomial ℚ)) : PowerSeries ℚ) * pureB j
    rw [Fin.sum_univ_seven]
    simp only [Work.Pure.dA, pB0, pB1, pB2, pB3, pB4, pB5, pB6]
    norm_num
    try simp only [Polynomial.coe_mul, Polynomial.coe_sub, Polynomial.coe_pow,
      Polynomial.coe_zero, Polynomial.coe_neg, zero_mul, mul_zero, add_zero, zero_add, B1, mul_one]
    rw [coe2, coe4]
    rw [Work.Pure.dq_coe]
    linear_combination Work.Pure.relation_B2
  · change (Work.Pure.dq : PowerSeries ℚ) * (PowerSeries.derivative (R := ℚ)) B3
      = ∑ j : Fin 7, (((Work.Pure.dA (2 : Fin 7) j : Polynomial ℚ)) : PowerSeries ℚ) * pureB j
    rw [Fin.sum_univ_seven]
    simp only [Work.Pure.dA, pB0, pB1, pB2, pB3, pB4, pB5, pB6]
    norm_num
    try simp only [Polynomial.coe_mul, Polynomial.coe_sub, Polynomial.coe_pow,
      Polynomial.coe_zero, Polynomial.coe_neg, zero_mul, mul_zero, add_zero, zero_add, B1, mul_one]
    rw [coe2, coe4]
    rw [Work.Pure.dq_coe]
    linear_combination Work.Pure.relation_B3
  · change (Work.Pure.dq : PowerSeries ℚ) * (PowerSeries.derivative (R := ℚ)) B4
      = ∑ j : Fin 7, (((Work.Pure.dA (3 : Fin 7) j : Polynomial ℚ)) : PowerSeries ℚ) * pureB j
    rw [Fin.sum_univ_seven]
    simp only [Work.Pure.dA, pB0, pB1, pB2, pB3, pB4, pB5, pB6]
    norm_num
    try simp only [Polynomial.coe_mul, Polynomial.coe_sub, Polynomial.coe_pow,
      Polynomial.coe_zero, Polynomial.coe_neg, zero_mul, mul_zero, add_zero, zero_add, B1, mul_one]
    rw [coe2, coe4]
    rw [Work.Pure.dq_coe]
    linear_combination Work.Pure.relation_B4
  · change (Work.Pure.dq : PowerSeries ℚ) * (PowerSeries.derivative (R := ℚ)) B5
      = ∑ j : Fin 7, (((Work.Pure.dA (4 : Fin 7) j : Polynomial ℚ)) : PowerSeries ℚ) * pureB j
    rw [Fin.sum_univ_seven]
    simp only [Work.Pure.dA, pB0, pB1, pB2, pB3, pB4, pB5, pB6]
    norm_num
    try simp only [Polynomial.coe_mul, Polynomial.coe_sub, Polynomial.coe_pow,
      Polynomial.coe_zero, Polynomial.coe_neg, zero_mul, mul_zero, add_zero, zero_add, B1, mul_one]
    rw [coe2, coe4]
    rw [Work.Pure.dq_coe]
    linear_combination Work.Pure.relation_B5
  · change (Work.Pure.dq : PowerSeries ℚ) * (PowerSeries.derivative (R := ℚ)) B6
      = ∑ j : Fin 7, (((Work.Pure.dA (5 : Fin 7) j : Polynomial ℚ)) : PowerSeries ℚ) * pureB j
    rw [Fin.sum_univ_seven]
    simp only [Work.Pure.dA, pB0, pB1, pB2, pB3, pB4, pB5, pB6]
    norm_num
    try simp only [Polynomial.coe_mul, Polynomial.coe_sub, Polynomial.coe_pow,
      Polynomial.coe_zero, Polynomial.coe_neg, zero_mul, mul_zero, add_zero, zero_add, B1, mul_one]
    rw [coe2, coe4]
    rw [Work.Pure.dq_coe]
    linear_combination Work.Pure.relation_B6
  · change (Work.Pure.dq : PowerSeries ℚ) * (PowerSeries.derivative (R := ℚ)) B7
      = ∑ j : Fin 7, (((Work.Pure.dA (6 : Fin 7) j : Polynomial ℚ)) : PowerSeries ℚ) * pureB j
    rw [Fin.sum_univ_seven]
    simp only [Work.Pure.dA, pB0, pB1, pB2, pB3, pB4, pB5, pB6]
    norm_num
    try simp only [Polynomial.coe_mul, Polynomial.coe_sub, Polynomial.coe_pow,
      Polynomial.coe_zero, Polynomial.coe_neg, zero_mul, mul_zero, add_zero, zero_add, B1, mul_one]
    rw [coe2, coe4]
    rw [Work.Pure.dq_coe]
    linear_combination Work.Pure.relation_B7

end Work.A14D
