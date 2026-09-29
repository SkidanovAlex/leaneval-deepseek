import Mathlib
import Submission.Work.Cert.ACSlit.Shadow
import Submission.Work.APsi.defs

/-!
# Reading off the `SlitW` flags (`sokB`, `sokM`, `sokW`, `suseE`)

The checker `Work.Cert.ACSlit.sokM` etc. are conjunctions of `decide (…)`; these lemmas expose them
as ordinary propositions.  Also `(sQp …).r = 3`.
-/

namespace Work.Cert.ACSlit
open Work.Cert

/-- `mu a 0 = 0`. -/
lemma mu_zero_right (a : ℤ) : mu a 0 = 0 := by
  simp only [mu, fdiv, Int.mul_zero, neg_zero]
  rw [show Int.ediv 0 S = 0 from by decide]; ring

/-- the radius of `sQp` is the constant `3`. -/
lemma sQp_r (A B2 E C1 G8 A2 ror roi : ℤ) (st : Work.Cert.St) (w : Work.Cert.SlitW) :
    (sQp A B2 E C1 G8 A2 ror roi st w).r = 3 := by
  simp only [sQp, bsub, bmul, bK, sC, mu_zero_right]
  norm_num

/-- `0 ≤ (sQp …).r`. -/
lemma sQp_r_nonneg (A B2 E C1 G8 A2 ror roi : ℤ) (st : Work.Cert.St) (w : Work.Cert.SlitW) :
    0 ≤ (sQp A B2 E C1 G8 A2 ror roi st w).r := by rw [sQp_r]; norm_num

/-- the `sokM` flag, exposed. -/
lemma sokM_spec (A B2 E C1 G8 A2 ror roi : ℤ) (st : Work.Cert.St) (w : Work.Cert.SlitW)
    (h : sokM A B2 E C1 G8 A2 ror roi st w = true) :
    (0 ≤ w.D)
    ∧ ((sfp A B2 E C1 G8 A2 ror roi st w).x * (sfp A B2 E C1 G8 A2 ror roi st w).x
        + (sfp A B2 E C1 G8 A2 ror roi st w).y * (sfp A B2 E C1 G8 A2 ror roi st w).y
        ≤ w.D * w.D)
    ∧ (0 ≤ w.cU) ∧ (st.cr * st.cr + st.ci * st.ci ≤ w.cU * w.cU)
    ∧ (0 ≤ w.qU) ∧ ((sQ A B2 E C1 G8 A2 ror roi st w).x * (sQ A B2 E C1 G8 A2 ror roi st w).x
        + (sQ A B2 E C1 G8 A2 ror roi st w).y * (sQ A B2 E C1 G8 A2 ror roi st w).y
        ≤ w.qU * w.qU)
    ∧ (0 ≤ w.qL) ∧ (w.qL * w.qL
        ≤ (sQ A B2 E C1 G8 A2 ror roi st w).x * (sQ A B2 E C1 G8 A2 ror roi st w).x
        + (sQ A B2 E C1 G8 A2 ror roi st w).y * (sQ A B2 E C1 G8 A2 ror roi st w).y)
    ∧ (0 ≤ w.qpU) ∧ ((sQp A B2 E C1 G8 A2 ror roi st w).x * (sQp A B2 E C1 G8 A2 ror roi st w).x
        + (sQp A B2 E C1 G8 A2 ror roi st w).y * (sQp A B2 E C1 G8 A2 ror roi st w).y
        ≤ w.qpU * w.qpU)
    ∧ (0 ≤ w.m1U) ∧ ((st.cr - S) * (st.cr - S) + st.ci * st.ci ≤ w.m1U * w.m1U) := by
  simp only [sokM, Bool.and_eq_true, decide_eq_true_eq] at h
  tauto

/-- the `sokB` flag, exposed. -/
lemma sokB_spec (A B2 E C1 G8 A2 ror roi : ℤ) (st : Work.Cert.St) (w : Work.Cert.SlitW)
    (h : sokB A B2 E C1 G8 A2 ror roi st w = true) :
    (0 < w.sr) ∧ (0 ≤ (sQ A B2 E C1 G8 A2 ror roi st w).r)
    ∧ (0 ≤ (sden A B2 E C1 G8 A2 ror roi st w).r)
    ∧ ((sden A B2 E C1 G8 A2 ror roi st w).r < w.L1)
    ∧ (w.L1 * w.L1 ≤ (sden A B2 E C1 G8 A2 ror roi st w).x * (sden A B2 E C1 G8 A2 ror roi st w).x
        + (sden A B2 E C1 G8 A2 ror roi st w).y * (sden A B2 E C1 G8 A2 ror roi st w).y)
    ∧ (0 ≤ (ss A B2 E C1 G8 A2 ror roi st w).r)
    ∧ ((ss A B2 E C1 G8 A2 ror roi st w).r < w.Ls)
    ∧ (w.Ls * w.Ls ≤ (ss A B2 E C1 G8 A2 ror roi st w).x * (ss A B2 E C1 G8 A2 ror roi st w).x
        + (ss A B2 E C1 G8 A2 ror roi st w).y * (ss A B2 E C1 G8 A2 ror roi st w).y)
    ∧ (0 < w.cL)
    ∧ (w.cL * w.cL ≤ st.cr * st.cr + st.ci * st.ci) := by
  simp only [sokB, bsqrtOK, binvOK, Bool.and_eq_true, decide_eq_true_eq] at h
  tauto

/-- the `suseE` flag, exposed. -/
lemma suseE_spec (A B2 E C1 G8 A2 ror roi : ℤ) (st : Work.Cert.St) (w : Work.Cert.SlitW)
    (h : suseE A B2 E C1 G8 A2 ror roi st w = true) :
    (0 < sQlo A B2 E C1 G8 A2 ror roi st w) ∧ (0 < swlo A B2 E C1 G8 A2 ror roi st w) := by
  simp only [suseE, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h

/-- the `sokW` flag, exposed (assuming `suseE`). -/
lemma sokW_spec (A B2 E C1 G8 A2 ror roi : ℤ) (st : Work.Cert.St) (w : Work.Cert.SlitW)
    (h : sokW A B2 E C1 G8 A2 ror roi st w = true)
    (huse : suseE A B2 E C1 G8 A2 ror roi st w = true) :
    (0 < w.sL) ∧ (w.sL * w.sL ≤ sQlo A B2 E C1 G8 A2 ror roi st w * S)
    ∧ (0 ≤ w.sH) ∧ (sQhi A B2 E C1 G8 A2 ror roi st w * S ≤ w.sH * w.sH) := by
  simp only [sokW, huse, Bool.not_true, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at h
  tauto

/-- `cIn st` is the ball centre `cx st.cr st.ci`. -/
lemma cIn_eq (st : Work.Cert.St) : cIn st = cx st.cr st.ci := rfl

end Work.Cert.ACSlit
