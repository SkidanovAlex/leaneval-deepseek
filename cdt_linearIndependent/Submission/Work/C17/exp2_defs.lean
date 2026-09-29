import Mathlib
import Submission.Work.C17.lead_defs
import Submission.Work.C17.lead_api
import Submission.CDT.RatFuncDeriv
import Submission.CDT.DerivOrderAt

/-!
# Two-term local expansions without a non-vanishing leading coefficient

`Lead2At f e l m` (see `Submission.Work.C17.lead_defs`) records the local expansion
`f = x^e·(l + m·x + O(x²))` at `x = 0` *and* the requirement `l ≠ 0`.  When adding two such
expansions at the same order, or when shifting an expansion to a lower order, the leading
coefficient of the result can legitimately vanish, so `Lead2At` is not closed under these
operations.

`Exp2 f e l m` is the same expansion condition *without* the requirement `l ≠ 0`:

`Exp2 f e l m := (2 : WithTop ℤ) ≤ ordAtT 0 (f·x^{-e} − l − m·x)`,

so that `Lead2At f e l m ↔ l ≠ 0 ∧ Exp2 f e l m`.  This file sets up the bookkeeping
(closing `Exp2` under addition, negation, subtraction, multiplication by constants and
shifting the order down by one), and the extraction of a `LeadAt` from the difference of
two `Lead2At`'s with equal order and leading coefficient.
-/

namespace Work.C17

open Commons.FieldTheory.RatFunc

noncomputable section

/-- `f = x^e·(l + m·x + O(x²))` at `x = 0`, with no requirement on `l`. -/
def Exp2 (f : RatFunc ℚ) (e : ℤ) (l m : ℚ) : Prop :=
  (2 : WithTop ℤ) ≤ ordAtT (0 : ℚ)
    (f * xQ ^ (-e) - algebraMap ℚ (RatFunc ℚ) l - algebraMap ℚ (RatFunc ℚ) m * xQ)

theorem lead2At_iff_exp2 {f : RatFunc ℚ} {e : ℤ} {l m : ℚ} :
    Lead2At f e l m ↔ l ≠ 0 ∧ Exp2 f e l m := Iff.rfl

theorem Lead2At.to_exp2 {f : RatFunc ℚ} {e : ℤ} {l m : ℚ} (h : Lead2At f e l m) :
    Exp2 f e l m := h.2

theorem Exp2.to_Lead2At {f : RatFunc ℚ} {e : ℤ} {l m : ℚ} (h : Exp2 f e l m) (hl : l ≠ 0) :
    Lead2At f e l m := ⟨hl, h⟩

theorem Exp2.to_LeadAt {f : RatFunc ℚ} {e : ℤ} {l m : ℚ} (h : Exp2 f e l m) (hl : l ≠ 0) :
    LeadAt f e l := (h.to_Lead2At hl).to_LeadAt

theorem Exp2.add {f g : RatFunc ℚ} {e : ℤ} {l m l' m' : ℚ} (hf : Exp2 f e l m)
    (hg : Exp2 g e l' m') : Exp2 (f + g) e (l + l') (m + m') := by
  have heq : (f + g) * xQ ^ (-e) - algebraMap ℚ (RatFunc ℚ) (l + l')
      - algebraMap ℚ (RatFunc ℚ) (m + m') * xQ
      = (f * xQ ^ (-e) - algebraMap ℚ (RatFunc ℚ) l - algebraMap ℚ (RatFunc ℚ) m * xQ)
        + (g * xQ ^ (-e) - algebraMap ℚ (RatFunc ℚ) l' - algebraMap ℚ (RatFunc ℚ) m' * xQ) := by
    rw [map_add, map_add]; ring
  unfold Exp2 at hf hg ⊢
  rw [heq]
  exact ordAtT_add_ge' hf hg

theorem Exp2.neg {f : RatFunc ℚ} {e : ℤ} {l m : ℚ} (h : Exp2 f e l m) :
    Exp2 (-f) e (-l) (-m) := by
  have h1 : (-f) * xQ ^ (-e) - algebraMap ℚ (RatFunc ℚ) (-l) - algebraMap ℚ (RatFunc ℚ) (-m) * xQ
      = -(f * xQ ^ (-e) - algebraMap ℚ (RatFunc ℚ) l - algebraMap ℚ (RatFunc ℚ) m * xQ) := by
    rw [map_neg, map_neg]; ring
  unfold Exp2 at h ⊢
  rw [h1, ordAtT_neg]
  exact h

theorem Exp2.sub {f g : RatFunc ℚ} {e : ℤ} {l m l' m' : ℚ} (hf : Exp2 f e l m)
    (hg : Exp2 g e l' m') : Exp2 (f - g) e (l - l') (m - m') := by
  have h := Exp2.add hf (Exp2.neg hg)
  simpa [sub_eq_add_neg] using h

theorem exp2_rat (c : ℚ) : Exp2 (algebraMap ℚ (RatFunc ℚ) c) 0 c 0 := by
  unfold Exp2
  have h : algebraMap ℚ (RatFunc ℚ) c * xQ ^ (-(0 : ℤ)) - algebraMap ℚ (RatFunc ℚ) c
      - algebraMap ℚ (RatFunc ℚ) 0 * xQ = 0 := by
    rw [map_zero, zero_mul, sub_zero, neg_zero, zpow_zero, mul_one, sub_self]
  rw [h, ordAtT_zero]; exact le_top

/-- Shifting a two-term expansion one order down: `f = x^e(l + mx + O(x²))` implies
`f = x^{e-1}(0 + l·x + O(x²))`. -/
theorem Exp2.shift {f : RatFunc ℚ} {e : ℤ} {l m : ℚ} (h : Exp2 f e l m) :
    Exp2 f (e - 1) 0 l := by
  unfold Exp2 at h ⊢
  have hx : (xQ : RatFunc ℚ) ≠ 0 := xQ_ne_zero
  have h1 : f * xQ ^ (-(e - 1)) - algebraMap ℚ (RatFunc ℚ) 0 - algebraMap ℚ (RatFunc ℚ) l * xQ
      = xQ * (f * xQ ^ (-e) - algebraMap ℚ (RatFunc ℚ) l - algebraMap ℚ (RatFunc ℚ) m * xQ)
        + algebraMap ℚ (RatFunc ℚ) m * xQ ^ 2 := by
    have hz : xQ ^ (-(e - 1)) = xQ ^ (-e) * xQ := by
      rw [show (-(e - 1) : ℤ) = -e + 1 by ring, zpow_add₀ hx, zpow_one]
    rw [map_zero, sub_zero, hz]; ring
  rw [h1]
  refine ordAtT_add_ge' (j := 2) ?_ ?_
  · have hxq : ((1 : ℤ) : WithTop ℤ) ≤ ordAtT (0 : ℚ) (xQ : RatFunc ℚ) := by
      rw [ordAtT_xQ]; norm_num
    have hmul := ordAtT_mul_ge (a := (xQ : RatFunc ℚ))
      (b := f * xQ ^ (-e) - algebraMap ℚ (RatFunc ℚ) l - algebraMap ℚ (RatFunc ℚ) m * xQ)
      (j := 1) (k := 2) hxq h
    exact le_trans (withTop_coe_le_coe_int (by norm_num : (2 : ℤ) ≤ 3)) hmul
  · rcases eq_or_ne m 0 with hm | hm
    · rw [hm, map_zero, zero_mul, ordAtT_zero]; exact le_top
    · have hmne : algebraMap ℚ (RatFunc ℚ) m ≠ 0 := fun hh =>
        hm ((algebraMap ℚ (RatFunc ℚ)).injective (by rw [hh, map_zero]))
      rw [ordAtT_mul (0 : ℚ) hmne (pow_ne_zero 2 xQ_ne_zero),
        ordAtT_rat hm, ordAtT_pow (0 : ℚ) xQ_ne_zero 2, ordAtT_xQ]
      norm_num

/-- **Difference of two expansions with the same order and leading coefficient.**
If `f = x^e(l + mx + O(x²))` and `g = x^e(l + m'x + O(x²))` with `m ≠ m'`, then
`f - g = x^{e+1}((m - m') + O(x))`. -/
theorem leadAt_sub_of_lead2At {f g : RatFunc ℚ} {e : ℤ} {l m m' : ℚ}
    (hf : Lead2At f e l m) (hg : Lead2At g e l m') (h : m ≠ m') :
    LeadAt (f - g) (e + 1) (m - m') := by
  have hf2 : Exp2 f e l m := hf.2
  have hg2 : Exp2 g e l m' := hg.2
  set A : RatFunc ℚ :=
    (f * xQ ^ (-e) - algebraMap ℚ (RatFunc ℚ) l - algebraMap ℚ (RatFunc ℚ) m * xQ) / xQ ^ 2
    with hA
  set B : RatFunc ℚ :=
    (g * xQ ^ (-e) - algebraMap ℚ (RatFunc ℚ) l - algebraMap ℚ (RatFunc ℚ) m' * xQ) / xQ ^ 2
    with hB
  have hAreg : Reg A := by rw [hA]; exact reg_div_xQ_sq hf2
  have hBreg : Reg B := by rw [hB]; exact reg_div_xQ_sq hg2
  have hxA : xQ ^ 2 * A = f * xQ ^ (-e) - algebraMap ℚ (RatFunc ℚ) l - algebraMap ℚ (RatFunc ℚ) m * xQ := by
    rw [hA, div_eq_mul_inv, ← mul_assoc,
      mul_comm (xQ ^ 2) (f * xQ ^ (-e) - algebraMap ℚ (RatFunc ℚ) l - algebraMap ℚ (RatFunc ℚ) m * xQ),
      mul_inv_cancel_right₀ (pow_ne_zero 2 xQ_ne_zero)]
  have hxB : xQ ^ 2 * B = g * xQ ^ (-e) - algebraMap ℚ (RatFunc ℚ) l - algebraMap ℚ (RatFunc ℚ) m' * xQ := by
    rw [hB, div_eq_mul_inv, ← mul_assoc,
      mul_comm (xQ ^ 2) (g * xQ ^ (-e) - algebraMap ℚ (RatFunc ℚ) l - algebraMap ℚ (RatFunc ℚ) m' * xQ),
      mul_inv_cancel_right₀ (pow_ne_zero 2 xQ_ne_zero)]
  have hsub : (f - g) * xQ ^ (-e) - algebraMap ℚ (RatFunc ℚ) (m - m') * xQ = xQ ^ 2 * (A - B) := by
    rw [mul_sub, hxA, hxB, map_sub]; ring
  have hx : (xQ : RatFunc ℚ) ≠ 0 := xQ_ne_zero
  have hz : (xQ : RatFunc ℚ) * xQ ^ (-(e + 1)) = xQ ^ (-e) := by
    have h1 : (xQ : RatFunc ℚ) * xQ ^ (-(e + 1)) = xQ ^ (1 : ℤ) * xQ ^ (-(e + 1)) := by
      rw [zpow_one]
    rw [h1, ← zpow_add₀ hx, show (1 : ℤ) + -(e + 1) = -e by ring]
  have hX : (xQ : RatFunc ℚ) * ((f - g) * xQ ^ (-(e + 1))) = (f - g) * xQ ^ (-e) := by
    rw [← mul_assoc, mul_comm (xQ : RatFunc ℚ) (f - g), mul_assoc, hz]
  have h1 : xQ * ((f - g) * xQ ^ (-(e + 1)) - algebraMap ℚ (RatFunc ℚ) (m - m'))
      = (f - g) * xQ ^ (-e) - algebraMap ℚ (RatFunc ℚ) (m - m') * xQ := by
    rw [mul_sub, hX]
    ring
  have heq : (f - g) * xQ ^ (-(e + 1)) - algebraMap ℚ (RatFunc ℚ) (m - m') = xQ * (A - B) := by
    refine mul_left_cancel₀ hx ?_
    rw [h1, hsub]; ring
  refine ⟨sub_ne_zero.mpr h, ?_⟩
  rw [heq]
  have hAB : Reg (A - B) := reg_sub hAreg hBreg
  rcases eq_or_ne (A - B) 0 with h0 | h0
  · rw [h0, mul_zero, ordAtT_zero]; exact le_top
  · rw [ordAtT_mul (0 : ℚ) hx h0, ordAtT_xQ]
    rw [Reg] at hAB
    exact le_add_of_nonneg_right hAB

end

end Work.C17
