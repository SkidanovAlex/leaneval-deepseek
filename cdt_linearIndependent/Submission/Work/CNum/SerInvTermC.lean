import Mathlib
import Submission.Work.CNum.SerUpDefs
import Submission.Work.CNum.LogUpMSpecPos
import Submission.Work.CNum.SerInvTerm
import Submission.Work.CNum.ShiLower

/-!
# `Work.CNum.SerInvTermC` — per-term soundness of the countdown-shaped series term

`Work.CNum.serAuxB` evaluates the `n`-th term of the logarithmic series by the mantissa
`shi x y σ e n px py pe sg`, whose `ρ`-coefficient is `n + 1`.  The certificate is written with a
*countdown* index: at the `k`-th step of the recursion the state `SerInv` is the one of exponent
`k + 1`, while the coefficient carried along is `SERM - k`.  The auxiliary quantity `sTc` records
the corresponding series term

  `sTc x y e k = log (‖1 + c^{k+1}‖ + (SERM - k) · R^k · ρ)`,

and this file proves the matching per-term soundness statement: `sTc` is bounded above by
`logUpM (shi x y σ e (SERM - 1 - k) px py pe sg)`, whose `ρ`-coefficient
`(SERM - 1 - k) + 1 = SERM - k` is exactly the countdown coefficient.

The proof follows `Work.CNum.SerInvTerm`: the state invariant gives `‖c^{k+1} - p‖ ≤ m2r pe` and
`R^k ≤ m2r sg`, so

* `‖1 + c^{k+1}‖ ≤ m2r (nrmUp (SC+px) py) + m2r pe` (triangle inequality + `NrmUpSpec`),
* `(SERM-k)·R^k·ρ ≤ m2r ((SERM-k) · mulU e sg)` (`le_mulU`),

and the right-hand side is exactly the mantissa `shi` at the countdown index, up to the slack `4`.
The numerical side conditions `1 ≤ shi` and `shi ≤ 2^60` needed by `Work.CNum.LogUpMSpec_pos`
are obtained from index-general versions proved below; `ShiLower`/`shi_upper` cannot be used
directly because they require the invariant at the *same* index as the mantissa.
-/

namespace Work.CNum

open Work.ANum

/-! ## Index arithmetic for the countdown index -/

/-- The countdown index `SERM - 1 - k` is still a valid series index. -/
lemma sERRM_sub_one_sub_lt {k : ℕ} (hk : k < SERM) : SERM - 1 - k < SERM := by omega

/-- The `ρ`-coefficient at the countdown index `SERM - 1 - k` is `SERM - k`. -/
lemma sERRM_sub_one_sub_cast {k : ℕ} (hk : k < SERM) :
    (((SERM - 1 - k : ℕ) : ℤ) + 1) = ((SERM - k : ℕ) : ℤ) := by
  have hN : SERM - 1 - k + 1 = SERM - k := by omega
  have h2 : (((SERM - 1 - k : ℕ) : ℤ) + 1) = (((SERM - 1 - k + 1 : ℕ)) : ℤ) := by
    rw [Nat.cast_add, Nat.cast_one]
  rw [h2, hN]

/-- The countdown coefficient is at most `44`. -/
lemma sERRM_sub_one_sub_le {k : ℕ} (hk : k < SERM) :
    (((SERM - 1 - k : ℕ) : ℤ) + 1) ≤ 44 := by
  rw [sERRM_sub_one_sub_cast hk]
  have h : (SERM - k : ℕ) ≤ 44 := by
    have h' : SERM - k ≤ SERM := Nat.sub_le SERM k
    simpa [SERM] using h'
  exact_mod_cast h

/-! ## Index-general numerical bounds for `shi`

`Work.CNum.ShiLower` and `Work.CNum.shi_upper` bound `shi` at the index at which the state
invariant `SerInv` is known.  The countdown term needs the bound at a *different* index, so we
redo the two numerical arguments with the index kept general: `shi` is
`nrmUp (SC+px) py + pe + (j+1)·mulU e sg + 4`, and only the size of the coefficient `j+1` matters.
-/

/-- `shi` is at least `1` as soon as `pe ≥ 0` and `mulU e sg ≥ 0`. -/
lemma shi_ge_one_of {x y e σ : ℤ} {j : ℕ} {px py pe sg : ℤ}
    (hpe : 0 ≤ pe) (hmul : 0 ≤ mulU e sg) : 1 ≤ shi x y σ e j px py pe sg := by
  have hnrm : 1 ≤ nrmUp (SC + px) py := by simp only [nrmUp, sqUp]; omega
  have hk1 : (0:ℤ) ≤ (j:ℤ) + 1 := by positivity
  have h : 0 ≤ ((j:ℤ) + 1) * mulU e sg := mul_nonneg hk1 hmul
  simp only [shi]; linarith

/-- `shi ≤ 2^60` as soon as the index coefficient is `≤ 44` and the four numerical bounds
`nrmUp ≤ 2^36`, `pe ≤ 3·SC`, `0 ≤ mulU e sg`, `mulU e sg < 2^32` hold. -/
lemma shi_le_2_60_of {x y e σ : ℤ} {j : ℕ} {px py pe sg : ℤ}
    (hj : (j:ℤ) + 1 ≤ 44) (hx34 : (SC + px).natAbs ≤ 2 ^ 34) (hy34 : py.natAbs ≤ 2 ^ 34)
    (hpe : pe ≤ 3 * SC) (hmul0 : 0 ≤ mulU e sg) (hmul32 : mulU e sg < 2 ^ 32) :
    shi x y σ e j px py pe sg ≤ 2 ^ 60 := by
  have hnrm : nrmUp (SC + px) py ≤ 2 ^ 36 := nrmUp_le hx34 hy34
  have hk1 : (0:ℤ) ≤ (j:ℤ) + 1 := by positivity
  have hprod2 : ((j:ℤ) + 1) * mulU e sg ≤ 44 * 2 ^ 32 := by nlinarith
  have hSC : SC = 2 ^ 30 := by norm_num [SC]
  simp only [shi]
  nlinarith

/-- The numerical data supplied by the state invariant (at *any* index) that is needed to bound
`shi` at another index: `mulU e sg` is nonnegative and `< 2^32`, `pe ≤ 3·SC`, and
`nrmUp (SC+px) py ≤ 2^36`. -/
lemma serInv_shi_data {x y e σ : ℤ} {k : ℕ} {px py pe sg : ℤ} (he : 0 ≤ e)
    (hσlt : m2r σ < 1) (hRσ : srad x y e ≤ m2r σ) (h : SerInv x y e σ k px py pe sg) :
    0 ≤ mulU e sg ∧ mulU e sg < 2 ^ 32 ∧ pe ≤ 3 * SC
      ∧ nrmUp (SC + px) py ≤ 2 ^ 36 := by
  obtain ⟨hpe0, hpe3, hsgk, hsg2, herr, hx34, hy34⟩ := h
  have he0 : 0 ≤ m2r e := m2r_nonneg_NrmSpec he
  have hsrad0 : 0 ≤ srad x y e := by
    simp only [srad]; linarith [norm_nonneg (spt x y), he0]
  -- `sg ≥ 0`, from `srad^k ≤ m2r sg` and `srad ≥ 0`
  have hsg0 : 0 ≤ sg := (m2r_nonneg_iff sg).mp (le_trans (pow_nonneg hsrad0 k) hsgk)
  have hpe : pe ≤ 3 * SC := by
    by_contra hc
    have hlt : 3 * SC < pe := lt_of_not_ge hc
    have h' := m2r_lt hlt
    rw [m2r_mul_SC'] at h'
    norm_num at h'
    linarith
  have he_lt : e < SC := by
    have hle : m2r e ≤ srad x y e := by simp only [srad]; linarith [norm_nonneg (spt x y)]
    have h1 : m2r e < 1 := lt_of_le_of_lt (le_trans hle hRσ) hσlt
    by_contra hc
    have hc' : SC ≤ e := le_of_not_gt hc
    have h2 : (1:ℝ) ≤ m2r e := by have h' := m2r_le hc'; rwa [m2r_SC] at h'
    linarith
  have hsg_le : sg ≤ 2 * SC := by
    by_contra hc
    have hc' : 2 * SC < sg := lt_of_not_ge hc
    have h' := m2r_lt hc'
    rw [m2r_two] at h'
    linarith
  have hmul32 : mulU e sg < 2 ^ 32 := by
    have h1 := mulU_mul_SC_lt e sg
    have hSC : SC = 2 ^ 30 := by norm_num [SC]
    have he1 : e ≤ SC - 1 := by omega
    have hprod : e * sg ≤ (SC - 1) * (2 * SC) := mul_le_mul he1 hsg_le hsg0 (by omega)
    have h2 : mulU e sg * SC < 2 ^ 32 * SC := by nlinarith
    exact lt_of_mul_lt_mul_right h2 SC_pos.le
  have hmul0 : 0 ≤ mulU e sg := by
    have hprod : 0 ≤ e * sg := mul_nonneg he hsg0
    have h1 : Int.ediv (-(e * sg)) SC ≤ 0 := by
      have hle : -(e * sg) ≤ 0 := by linarith
      exact nonpos_of_mul_nonpos_left (le_trans (Int.ediv_mul_le (-(e * sg)) SC_ne_zero) hle) SC_pos
    simp only [mulU]; linarith
  exact ⟨hmul0, hmul32, hpe, nrmUp_le hx34 hy34⟩

/-! ## The analytic core -/

/-- **The analytic core of `SerInvTermC`.**  Under the state invariant `SerInv` at step `k`
(with `k < SERM`), the `k`-th countdown-shaped argument of the logarithmic series is bounded by
the mantissa `shi` at index `SERM - 1 - k`. -/
lemma sTc_arg_le {x y e σ : ℤ} {k : ℕ} {px py pe sg : ℤ} (hk : k < SERM) (he : 0 ≤ e)
    (h : SerInv x y e σ k px py pe sg) :
    ‖(1:ℂ) + spt x y ^ (k+1)‖ + ((SERM - k : ℕ) : ℝ) * srad x y e ^ k * m2r e
      ≤ m2r (shi x y σ e (SERM - 1 - k) px py pe sg) := by
  obtain ⟨hpe0, hpe3, hsgk, hsg2, herr, hx34, hy34⟩ := h
  have he0 : 0 ≤ m2r e := m2r_nonneg_NrmSpec he
  -- rewrite the mantissa at the countdown index with the explicit coefficient `SERM - k`
  have hsi : shi x y σ e (SERM - 1 - k) px py pe sg
      = nrmUp (SC + px) py + pe + ((SERM - k : ℕ) : ℤ) * mulU e sg + 4 := by
    simp only [shi]
    rw [sERRM_sub_one_sub_cast hk]
  -- `‖1 + c^{k+1}‖ ≤ ‖1 + p‖ + ‖c^{k+1} - p‖ ≤ nrmUp (SC+px) py + pe`
  have hnorm : ‖(1:ℂ) + spt x y ^ (k+1)‖ ≤ m2r (nrmUp (SC + px) py) + m2r pe := by
    have h1 : (1:ℂ) + spt x y ^ (k+1) = spt (SC + px) py + (spt x y ^ (k+1) - spt px py) := by
      rw [← spt_one_add]; ring
    rw [h1]
    have h2 := norm_add_le (spt (SC + px) py) (spt x y ^ (k+1) - spt px py)
    have h3 : ‖spt (SC + px) py‖ ≤ m2r (nrmUp (SC + px) py) := NrmUpSpec hx34 hy34
    linarith
  -- `R^k · ρ ≤ m2r sg · m2r e ≤ m2r (mulU e sg)`
  have hmul : srad x y e ^ k * m2r e ≤ m2r (mulU e sg) := by
    calc srad x y e ^ k * m2r e ≤ m2r sg * m2r e := mul_le_mul_of_nonneg_right hsgk he0
      _ ≤ m2r (mulU sg e) := le_mulU sg e
      _ = m2r (mulU e sg) := by rw [mulU_comm e sg]
  have hterm : ((SERM - k : ℕ) : ℝ) * srad x y e ^ k * m2r e
      ≤ m2r (((SERM - k : ℕ) : ℤ) * mulU e sg) := by
    have hN0 : (0:ℝ) ≤ ((SERM - k : ℕ) : ℝ) := Nat.cast_nonneg _
    calc ((SERM - k : ℕ) : ℝ) * srad x y e ^ k * m2r e
        = ((SERM - k : ℕ) : ℝ) * (srad x y e ^ k * m2r e) := by ring
      _ ≤ ((SERM - k : ℕ) : ℝ) * m2r (mulU e sg) := mul_le_mul_of_nonneg_left hmul hN0
      _ = m2r (((SERM - k : ℕ) : ℤ) * mulU e sg) := by rw [m2r_mul_int']; push_cast; ring
  have hsum : (m2r (nrmUp (SC + px) py) + m2r pe) + m2r (((SERM - k : ℕ) : ℤ) * mulU e sg)
      ≤ m2r (nrmUp (SC + px) py + pe + ((SERM - k : ℕ) : ℤ) * mulU e sg + 4) := by
    simp only [m2r_add]
    have h4 : (0:ℝ) ≤ m2r (4:ℤ) := m2r_nonneg_NrmSpec (by norm_num)
    linarith
  rw [hsi]
  linarith

/-- The countdown-shaped argument of the logarithmic series is strictly positive: the same
argument as `Work.CNum.log_arg_pos` (`‖c‖ < 1` gives `‖1 + c^{k+1}‖ > 0`), the extra
coefficient `SERM - k` being nonnegative. -/
lemma sTc_arg_pos {x y e : ℤ} (he : 0 ≤ e) (hR : srad x y e < 1) (k : ℕ) :
    0 < ‖(1:ℂ) + spt x y ^ (k+1)‖ + ((SERM - k : ℕ) : ℝ) * srad x y e ^ k * m2r e := by
  have he0 : 0 ≤ m2r e := m2r_nonneg_NrmSpec he
  have hs0 : 0 ≤ srad x y e := by
    simp only [srad]; linarith [norm_nonneg (spt x y), he0]
  have hc1 : ‖spt x y‖ < 1 := by
    have hle : ‖spt x y‖ ≤ srad x y e := by simp only [srad]; linarith [he0]
    linarith
  have hz : ‖spt x y ^ (k+1)‖ < 1 := by
    rw [norm_pow]
    calc ‖spt x y‖ ^ (k+1) ≤ ‖spt x y‖ ^ 1 :=
          pow_le_pow_of_le_one (norm_nonneg _) hc1.le (by omega)
      _ = ‖spt x y‖ := pow_one _
      _ < 1 := hc1
  have hA : 0 < ‖(1:ℂ) + spt x y ^ (k+1)‖ := by
    have h2 : (1:ℝ) ≤ ‖(1:ℂ) + spt x y ^ (k+1)‖ + ‖spt x y ^ (k+1)‖ := by
      have h := norm_add_le ((1:ℂ) + spt x y ^ (k+1)) (-(spt x y ^ (k+1)))
      have hL : ((1:ℂ) + spt x y ^ (k+1)) + -(spt x y ^ (k+1)) = 1 := by ring
      rw [hL, norm_one, norm_neg] at h
      exact h
    linarith
  have hN : 0 ≤ ((SERM - k : ℕ) : ℝ) * srad x y e ^ k * m2r e :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hs0 k)) he0
  linarith

/-! ## The assignment -/

/-- **The assignment.**  Each countdown-shaped term of the logarithmic series is bounded above by
the mantissa `shi` of the certificate evaluated at the countdown index. -/
theorem SerInvTermC {x y e σ : ℤ} (he : 0 ≤ e) (hσlt : Work.ANum.m2r σ < 1)
    (hRσ : Work.CNum.srad x y e ≤ Work.ANum.m2r σ) {k : ℕ} (hk : k < Work.CNum.SERM)
    {px py pe sg : ℤ} (h : Work.CNum.SerInv x y e σ k px py pe sg) :
    Work.CNum.sTc x y e k
      ≤ Work.ANum.m2r (Work.CNum.logUpM (Work.CNum.shi x y σ e (Work.CNum.SERM - 1 - k)
          px py pe sg)) := by
  have harg : ‖(1:ℂ) + spt x y ^ (k+1)‖ + ((SERM - k : ℕ) : ℝ) * srad x y e ^ k * m2r e
      ≤ m2r (shi x y σ e (SERM - 1 - k) px py pe sg) := sTc_arg_le hk he h
  have hpos : 0 < ‖(1:ℂ) + spt x y ^ (k+1)‖ + ((SERM - k : ℕ) : ℝ) * srad x y e ^ k * m2r e :=
    sTc_arg_pos he (lt_of_le_of_lt hRσ hσlt) k
  obtain ⟨hmul0, hmul32, hpeSC, -⟩ := serInv_shi_data he hσlt hRσ h
  have h1 : (1:ℤ) ≤ shi x y σ e (SERM - 1 - k) px py pe sg := shi_ge_one_of h.1 hmul0
  have h2 : shi x y σ e (SERM - 1 - k) px py pe sg ≤ 2 ^ 60 :=
    shi_le_2_60_of (sERRM_sub_one_sub_le hk) h.2.2.2.2.2.1 h.2.2.2.2.2.2 hpeSC hmul0 hmul32
  simp only [sTc, scoef]
  exact LogUpMSpec_pos h1 h2 harg hpos

end Work.CNum
