import Mathlib
import Submission.Work.LinnikBurgess.lf_defs
import Submission.Work.LinnikBurgess.critN_shifts

namespace Work.LinnikBurgess

open scoped BigOperators

/-- In any `ZMod N`, the sum of the inverses of three units times their product is the sum of the
three pairwise products.  This is the "cleared of inverses" form of `∑_l 1/v_l = A₂/A₃`. -/
lemma zmod_sum_inv_mul_prod {N : ℕ} (v : Fin 3 → ZMod N) (hv : ∀ l, IsUnit (v l)) :
    (∑ l : Fin 3, (v l)⁻¹) * (∏ l : Fin 3, v l)
      = v 0 * v 1 + v 0 * v 2 + v 1 * v 2 := by
  have h0 := ZMod.inv_mul_of_unit (v 0) (hv 0)
  have h1 := ZMod.inv_mul_of_unit (v 1) (hv 1)
  have h2 := ZMod.inv_mul_of_unit (v 2) (hv 2)
  rw [Fin.sum_univ_three, Fin.prod_univ_three]
  linear_combination h0 * (v 1 * v 2) + h1 * (v 0 * v 2) + h2 * (v 0 * v 1)

/-- The product of the lifts of `y + a l` is the lift of `sh3 y a`. -/
lemma prod_shift_cast (N : ℕ) (y : ℕ) (a : Fin 3 → ℕ) :
    (∏ l : Fin 3, (((y + a l : ℕ) : ZMod N))) = ((sh3 y a : ℕ) : ZMod N) := by
  rw [Fin.prod_univ_three, sh3]
  push_cast
  ring

/-- The sum of the three pairwise products of the lifts of `y + a l` is the lift of `sh2 y a`. -/
lemma sum_pair_cast (N : ℕ) (y : ℕ) (a : Fin 3 → ℕ) :
    (((y + a 0 : ℕ) : ZMod N) * ((y + a 1 : ℕ) : ZMod N)
      + ((y + a 0 : ℕ) : ZMod N) * ((y + a 2 : ℕ) : ZMod N)
      + ((y + a 1 : ℕ) : ZMod N) * ((y + a 2 : ℕ) : ZMod N))
      = ((sh2 y a : ℕ) : ZMod N) := by
  rw [sh2]
  push_cast
  ring

/-- In `ZMod (p ^ e)`, the first defect of Lemma A is the Wronskian divided by `f_a f_b`, cleared of
inverses: `D₁(y) · (f_a(y) f_b(y)) = N(y)`, where `N = critN a b` is the Wronskian and `y` is a unit
at `p` (so every `y + a l`, `y + b l` is invertible).

Hints: for a unit `u : (ZMod (p^e))ˣ` one has `(↑u)⁻¹ = ↑u⁻¹` (`ZMod.inv_coe_unit`), so it suffices
to prove the group identity `(∑_l v_l⁻¹) * ∏_l v_l = ∏_{l≠0} v_l + ∏_{l≠1} v_l + ∏_{l≠2} v_l` in
`(ZMod (p^e))ˣ` for `v l` the unit `y + a l` (`ZMod.isUnit_iff_coprime`, `IsUnit.unit`), i.e.
`∑_l (y + a_l)⁻¹ = sh2 y a * (sh3 y a)⁻¹`; subtract the `b`-analogue and use
`critN_eval_shift : (critN a b).eval y = sh2 y a * sh3 y b - sh3 y a * sh2 y b`. -/
theorem defect1_mul_Uval {p e : ℕ} [Fact p.Prime] (a b : Fin 3 → ℕ) {y : ℕ}
    (hy : UnitAt p y a b) :
    defect1 p e a b y * (((Uval y a b : ℕ)) : ZMod (p ^ e))
      = (((critN a b).eval (y : ℤ) : ℤ) : ZMod (p ^ e)) := by
  have hp : p.Prime := Fact.out
  -- every `y + a l` and `y + b l` is a unit modulo `p ^ e`
  have hunit_a : ∀ l : Fin 3, IsUnit (((y + a l : ℕ) : ZMod (p ^ e))) := by
    intro l
    exact (ZMod.isUnit_iff_coprime (y + a l) (p ^ e)).mpr
      (((hp.coprime_iff_not_dvd.mpr (hy l).1).symm).pow_right e)
  have hunit_b : ∀ l : Fin 3, IsUnit (((y + b l : ℕ) : ZMod (p ^ e))) := by
    intro l
    exact (ZMod.isUnit_iff_coprime (y + b l) (p ^ e)).mpr
      (((hp.coprime_iff_not_dvd.mpr (hy l).2).symm).pow_right e)
  -- `∑_l (y + a_l)⁻¹ · ∏_l (y + a_l) = sh2 y a`
  have ha := zmod_sum_inv_mul_prod (fun l : Fin 3 => ((y + a l : ℕ) : ZMod (p ^ e))) hunit_a
  have hb := zmod_sum_inv_mul_prod (fun l : Fin 3 => ((y + b l : ℕ) : ZMod (p ^ e))) hunit_b
  have ha' : (∑ l : Fin 3, (((y + a l : ℕ) : ZMod (p ^ e)))⁻¹)
        * ((sh3 y a : ℕ) : ZMod (p ^ e)) = ((sh2 y a : ℕ) : ZMod (p ^ e)) := by
    rw [← prod_shift_cast, ← sum_pair_cast]
    exact ha
  have hb' : (∑ l : Fin 3, (((y + b l : ℕ) : ZMod (p ^ e)))⁻¹)
        * ((sh3 y b : ℕ) : ZMod (p ^ e)) = ((sh2 y b : ℕ) : ZMod (p ^ e)) := by
    rw [← prod_shift_cast, ← sum_pair_cast]
    exact hb
  -- unfold the defect, the product and the Wronskian and push the casts
  rw [defect1, Uval, critN_eval_shift, Nat.cast_mul]
  have hint : ((((sh2 y a : ℤ) * (sh3 y b : ℤ) - (sh3 y a : ℤ) * (sh2 y b : ℤ) : ℤ)) : ZMod (p ^ e))
      = ((sh2 y a : ℕ) : ZMod (p ^ e)) * ((sh3 y b : ℕ) : ZMod (p ^ e))
        - ((sh3 y a : ℕ) : ZMod (p ^ e)) * ((sh2 y b : ℕ) : ZMod (p ^ e)) := by
    push_cast
    ring
  rw [hint]
  linear_combination ha' * ((sh3 y b : ℕ) : ZMod (p ^ e))
    - hb' * ((sh3 y a : ℕ) : ZMod (p ^ e))

end Work.LinnikBurgess
