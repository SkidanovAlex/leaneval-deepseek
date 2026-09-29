import Mathlib
import Submission.Work.C17.exp2_defs

/-!
# Multiplicativity of the two-term local expansion `Exp2`

If `f = x^e·(l + m·x + O(x²))` and `g = x^{e'}·(l' + m'·x + O(x²))` at `x = 0`, then

`f·g = x^{e+e'}·(l·l' + (m·l' + l·m')·x + O(x²))`.

No non-vanishing hypothesis on the leading coefficients is needed (this is the whole point of
`Exp2` as opposed to `Lead2At`).
-/

namespace Work.C17

open Commons.FieldTheory.RatFunc

noncomputable section

theorem exp2_mul {f g : RatFunc ℚ} {e e' : ℤ} {l m l' m' : ℚ}
    (hf : Exp2 f e l m) (hg : Exp2 g e' l' m') :
    Exp2 (f * g) (e + e') (l * l') (m * l' + l * m') := by
  unfold Exp2 at hf hg ⊢
  set c : RatFunc ℚ := algebraMap ℚ (RatFunc ℚ) l + algebraMap ℚ (RatFunc ℚ) m * xQ with hc
  set d : RatFunc ℚ := algebraMap ℚ (RatFunc ℚ) l' + algebraMap ℚ (RatFunc ℚ) m' * xQ with hd
  have hcreg : Reg c := by rw [hc]; exact reg_add (reg_rat l) (reg_mul (reg_rat m) reg_X)
  have hdreg : Reg d := by rw [hd]; exact reg_add (reg_rat l') (reg_mul (reg_rat m') reg_X)
  have heq : (f * g) * xQ ^ (-(e + e')) - algebraMap ℚ (RatFunc ℚ) (l * l')
      - algebraMap ℚ (RatFunc ℚ) (m * l' + l * m') * xQ
      = ((f * xQ ^ (-e) - c) * (g * xQ ^ (-e') - d) + (f * xQ ^ (-e) - c) * d)
        + (c * (g * xQ ^ (-e') - d) + algebraMap ℚ (RatFunc ℚ) (m * m') * xQ ^ 2) := by
    rw [hc, hd]
    simp only [map_mul, map_add]
    rw [neg_add, zpow_add₀ xQ_ne_zero]
    ring
  have hA : (2 : WithTop ℤ) ≤ ordAtT (0 : ℚ) (f * xQ ^ (-e) - c) := by
    rw [hc]
    simpa only [sub_sub] using hf
  have hB : (2 : WithTop ℤ) ≤ ordAtT (0 : ℚ) (g * xQ ^ (-e') - d) := by
    rw [hd]
    simpa only [sub_sub] using hg
  have hx2 : (2 : WithTop ℤ) ≤ ordAtT (0 : ℚ) ((xQ : RatFunc ℚ) ^ 2) := by
    rw [ordAtT_pow (0 : ℚ) xQ_ne_zero 2, ordAtT_xQ]; norm_num
  rw [heq]
  refine ordAtT_add_ge' ?_ ?_
  · refine ordAtT_add_ge' ?_ ?_
    · have h := ordAtT_mul_ge hA hB
      exact le_trans (withTop_coe_le_coe_int (by norm_num : (2 : ℤ) ≤ 4)) h
    · have h := ordAtT_mul_ge (j := 2) (k := 0) hA hdreg
      simpa using h
  · refine ordAtT_add_ge' ?_ ?_
    · have h := ordAtT_mul_ge (j := 0) (k := 2) hcreg hB
      simpa using h
    · have h := ordAtT_mul_ge (j := 0) (k := 2) (reg_rat (m * m')) hx2
      simpa using h

end

end Work.C17
