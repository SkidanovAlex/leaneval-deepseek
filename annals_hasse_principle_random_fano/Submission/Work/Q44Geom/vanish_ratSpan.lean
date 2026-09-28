import Mathlib
import Submission.Work.Q44Geom.Setup
import Submission.Work.HP.Q44Setup
import Submission.Work.Q44Geom.sat_span
import Submission.Work.Q44Geom.formOf_eval

/-!
# `Work.Q44Geom.vanish_ratSpan`

A quartic form `f₄₄ c` that vanishes at every lattice point of `L ⊆ ℤ⁵` vanishes on the
whole `ℚ`-span `ratSpan L` of `L`.

The argument is "clear denominators, then use homogeneity".  If `b ∈ ratSpan L`, then by
`mem_ratSpan_iff'` (from `sat_span`) there is a nonzero `n : ℤ` with
`n • b = toRatLM w` for some `w ∈ L`.  Since `c` vanishes at `w`, the rational polynomial
`f₄₄ c` vanishes at `toRatLM w = n • b`; by homogeneity of degree `4`,
`0 = eval (n • b) (f₄₄ c) = n⁴ · eval b (f₄₄ c)`, and `n ≠ 0` gives the claim.
-/

set_option autoImplicit false
noncomputable section

namespace Work.Q44Geom

open MvPolynomial

/-- Evaluating the quartic `f44 c` at a rational point `b` agrees with the
coefficient-vector evaluation `formEval`. -/
lemma f44_eval_rat (c : Work.HP.Mon 4 4 → ℤ) (b : Fin 5 → ℚ) :
    MvPolynomial.eval b (Work.Q44Geom.f44 c) = Work.HP.formEval 4 4 c b := by
  rw [Work.Q44Geom.f44, ← MvPolynomial.aeval_eq_eval, Work.HP.aeval_formOf]

/-- `formEval` is homogeneous of degree `d`: scaling the point by `N : ℤ` scales the value
by `(N : ℚ) ^ d`. -/
lemma formEval_zsmul (d n : ℕ) (a : Work.HP.Mon d n → ℤ) (N : ℤ) (b : Fin (n + 1) → ℚ) :
    Work.HP.formEval d n a (N • b) = (N : ℚ) ^ d * Work.HP.formEval d n a b := by
  unfold Work.HP.formEval
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hv : Work.HP.veronese d n (N • b) m = (N : ℚ) ^ d * Work.HP.veronese d n b m := by
    unfold Work.HP.veronese
    simp only [Pi.smul_apply, zsmul_eq_mul, mul_pow, Finset.prod_mul_distrib,
      Finset.prod_pow_eq_pow_sum, m.2]
  rw [hv]
  ring

theorem vanish_ratSpan (c : Work.HP.Mon 4 4 → ℤ) (L : Submodule ℤ (Fin 5 → ℤ))
    (hc : c ∈ Work.HP.vanishOn L) {b : Fin 5 → ℚ} (hb : b ∈ Work.Q44Geom.ratSpan L) :
    MvPolynomial.eval b (Work.Q44Geom.f44 c) = 0 := by
  -- clear denominators: some nonzero integer multiple of `b` is the image of a lattice vector
  obtain ⟨n, hn, hmem⟩ := (Work.Q44Geom.mem_ratSpan_iff' L b).mp hb
  rw [Submodule.mem_map] at hmem
  obtain ⟨w, hwL, hw⟩ := hmem
  -- `c` vanishes at the lattice point `w`, hence at its rational image
  have hvan : Work.HP.formEval (R := ℤ) 4 4 c w = 0 :=
    (Work.HP.mem_vanishOn (L := L) (a := c)).mp hc ⟨w, hwL⟩
  have hz : Work.HP.formEval (R := ℚ) 4 4 c (n • b) = 0 := by
    have h1 : MvPolynomial.eval (n • b) (Work.Q44Geom.f44 c) = 0 := by
      rw [← hw, Work.Q44Geom.formOf_eval, hvan]
      norm_num
    rwa [f44_eval_rat] at h1
  -- homogeneity of degree 4
  rw [formEval_zsmul] at hz
  have hnq : (n : ℚ) ^ 4 ≠ 0 := pow_ne_zero 4 (by exact_mod_cast hn)
  rw [f44_eval_rat]
  exact (mul_eq_zero.mp hz).resolve_left hnq

end Work.Q44Geom
