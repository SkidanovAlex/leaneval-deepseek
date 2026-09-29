import Mathlib
import Submission.Work.CNum.SerUpDefs
import Submission.Work.CNum.LogUpMSpecPos
import Submission.Work.CNum.NrmSpec
import Submission.Work.CNum.LgInfra
import Submission.Work.CNum.ShiLower

/-!
# `Work.CNum.SerInvTerm` — per-term soundness of the `serUp` logarithmic series

The certificate `Work.CNum.serUp` bounds `log ‖h w‖` by the series

  `log 256 + log R + 24 Σ_{n < SERM} log (‖1 + c^{n+1}‖ + (n+1) R^n ρ) + tail`,

and `Work.CNum.serAuxB` evaluates the `n`-th term by the mantissa

  `shi x y σ e n px py pe sg = nrmUp (SC+px) py + pe + (n+1)·mulU e sg + 4`.

This file proves that this mantissa is a valid upper bound for the `n`-th term of the
series, given the recursion invariant `Work.CNum.SerInv`: writing `c = (x+iy)/SC` for the
centre of the ball, `p = (px+iy)/SC` for the tracked approximation of `c^{k+1}`,
`ρ = m2r e` for the radius and `R = ‖c‖ + ρ = srad x y e`, the invariant gives

* `‖c^{k+1} - p‖ ≤ m2r pe` (`≤ 3`),
* `R^k ≤ m2r sg ≤ 2`,
* `|SC+px|, |py| ≤ 2^34` (so that `NrmUpSpec` applies to the mantissa `(SC+px, py)`),

and the term is bounded by

  `‖1 + c^{k+1}‖ + (k+1) R^k ρ ≤ (m2r (nrmUp (SC+px) py) + m2r pe) + (k+1)·m2r (mulU e sg)`.

The two numerical side conditions `1 ≤ shi` and `shi ≤ 2^60` needed by
`Work.CNum.LogUpMSpec_pos` are provided by `Work.CNum.ShiLower` (proved by a colleague) and by
`Work.CNum.shi_upper` below.
-/

namespace Work.CNum

open Work.ANum

/-- `(1 : ℂ) + (px + i·py)/SC = ((SC+px) + i·py)/SC`: the mantissa pair `(SC+px, py)` is the
translation of the point `p` by `1`. -/
lemma spt_one_add (px py : ℤ) : (1:ℂ) + spt px py = spt (SC + px) py := by
  have hSC : ((SC:ℤ) : ℂ) ≠ 0 := by norm_num [SC]
  unfold spt
  push_cast
  rw [eq_div_iff hSC]
  field_simp
  ring

/-- `mulU` is symmetric in its two arguments. -/
lemma mulU_comm (a b : ℤ) : mulU a b = mulU b a := by
  simp only [mulU, mul_comm a b]

/-- **The analytic core of `SerInvTerm`.**  Under the state invariant `SerInv` at step `k`,
the `k`-th argument of the logarithmic series is bounded by the mantissa `shi`. -/
lemma sT_arg_le {x y e σ : ℤ} {k : ℕ} {px py pe sg : ℤ} (he : 0 ≤ e)
    (h : SerInv x y e σ k px py pe sg) :
    ‖(1:ℂ) + spt x y ^ (k+1)‖ + ((k:ℝ)+1) * srad x y e ^ k * m2r e
      ≤ m2r (shi x y σ e k px py pe sg) := by
  obtain ⟨hpe0, hpe3, hsgk, hsg2, herr, hx34, hy34⟩ := h
  have he0 : 0 ≤ m2r e := m2r_nonneg_NrmSpec he
  have hR0 : 0 ≤ srad x y e := by
    simp only [srad]; linarith [norm_nonneg (spt x y), he0]
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
  have hterm : ((k:ℝ)+1) * srad x y e ^ k * m2r e ≤ m2r (((k:ℤ)+1) * mulU e sg) := by
    have hk0 : (0:ℝ) ≤ (k:ℝ)+1 := by positivity
    calc ((k:ℝ)+1) * srad x y e ^ k * m2r e
        = ((k:ℝ)+1) * (srad x y e ^ k * m2r e) := by ring
      _ ≤ ((k:ℝ)+1) * m2r (mulU e sg) := mul_le_mul_of_nonneg_left hmul hk0
      _ = m2r (((k:ℤ)+1) * mulU e sg) := by
            rw [m2r_mul_int']; push_cast; ring
  have h4 : (0:ℝ) ≤ m2r (4:ℤ) := by simp only [m2r]; exact div_nonneg (by norm_num) SC_posR.le
  have hsum : (m2r (nrmUp (SC + px) py) + m2r pe) + m2r (((k:ℤ)+1) * mulU e sg)
      ≤ m2r (nrmUp (SC + px) py + pe + ((k:ℤ)+1) * mulU e sg + 4) := by
    simp only [m2r_add]
    linarith
  simp only [shi]
  linarith

/-- The argument of the logarithmic series is strictly positive: `‖c‖ ≤ R < 1` forces
`c^{k+1} ≠ -1`. -/
lemma log_arg_pos {x y e : ℤ} (he : 0 ≤ e) (hR : srad x y e < 1) (k : ℕ) :
    0 < ‖(1:ℂ) + spt x y ^ (k+1)‖ + ((k:ℝ)+1) * srad x y e ^ k * m2r e := by
  have he0 : (0:ℝ) ≤ m2r e := m2r_nonneg_NrmSpec he
  have hR0 : (0:ℝ) ≤ srad x y e := by
    simp only [srad]; linarith [norm_nonneg (spt x y), he0]
  have hc1 : ‖spt x y‖ < 1 := by
    have : ‖spt x y‖ ≤ srad x y e := by simp only [srad]; linarith
    linarith
  have hz : ‖spt x y ^ (k+1)‖ < 1 := by
    rw [norm_pow]
    calc ‖spt x y‖ ^ (k+1) ≤ ‖spt x y‖ ^ 1 :=
          pow_le_pow_of_le_one (norm_nonneg _) hc1.le (by omega)
      _ = ‖spt x y‖ := pow_one _
      _ < 1 := hc1
  have hmain : 0 < ‖(1:ℂ) + spt x y ^ (k+1)‖ := by
    have h2 : (1:ℝ) ≤ ‖(1:ℂ) + spt x y ^ (k+1)‖ + ‖spt x y ^ (k+1)‖ := by
      have h := norm_add_le ((1:ℂ) + spt x y ^ (k+1)) (-(spt x y ^ (k+1)))
      have hL : ((1:ℂ) + spt x y ^ (k+1)) + -(spt x y ^ (k+1)) = 1 := by ring
      rw [hL, norm_one, norm_neg] at h
      exact h
    linarith
  have h2 : 0 ≤ ((k:ℝ)+1) * srad x y e ^ k * m2r e := by positivity
  linarith

/-! ## The numerical side conditions for `LogUpMSpec_pos` -/

/-- Ceiling-rounded product: `mulU a b · SC < a·b + SC` (the standard `⌈a·b/SC⌉·SC < a·b + SC`). -/
lemma mulU_mul_SC_lt (a b : ℤ) : mulU a b * SC < a * b + SC := by
  have h := Int.mul_ediv_add_emod (-(a * b)) SC
  have hlt := Int.emod_lt_of_pos (-(a * b)) SC_pos
  set q := Int.ediv (-(a * b)) SC with hq
  set em := (-(a * b)) % SC with hem
  have h1 : q * SC + em = -(a * b) := by
    rw [hq, mul_comm (Int.ediv (-(a * b)) SC) SC]
    exact h
  have h3 : mulU a b = -q := by simp only [mulU, hq]
  rw [h3]
  linarith

/-- `nrmUp x y ≤ 2^36` whenever `|x|, |y| ≤ 2^34` (the `< 2^70` regime of `IsqrtSpec`). -/
lemma nrmUp_le {x y : ℤ} (hx : x.natAbs ≤ 2 ^ 34) (hy : y.natAbs ≤ 2 ^ 34) :
    nrmUp x y ≤ 2 ^ 36 := by
  obtain ⟨hlt, hval⟩ := natAbs_sq_add hx hy
  have hkey : isqrt (x.natAbs ^ 2 + y.natAbs ^ 2) + 1 ≤ 2 ^ 36 := by
    by_contra hc
    have hc' : 2 ^ 36 ≤ isqrt (x.natAbs ^ 2 + y.natAbs ^ 2) := by omega
    have h1 := (IsqrtSpec (x.natAbs ^ 2 + y.natAbs ^ 2) (by rw [← hval]; exact hlt)).1
    have hsum : x.natAbs ^ 2 + y.natAbs ^ 2 < 2 ^ 70 := by
      have a := Nat.pow_le_pow_left hx 2
      have b := Nat.pow_le_pow_left hy 2
      omega
    have hchain : 2 ^ 70 ≤ x.natAbs ^ 2 + y.natAbs ^ 2 :=
      le_trans (by norm_num) (le_trans (Nat.mul_le_mul hc' hc') h1)
    omega
  simp only [nrmUp, sqUp]
  rw [hval]
  exact_mod_cast hkey

/-- `shi` is at most `2^60`: it is a sum of a norm bound (`< 2^36`), an accumulated error
(`≤ 3·SC`), `(k+1) ≤ 44` copies of a product bound (`< 2^32`) and the constant `4`.  Here the
hypothesis `srad x y e ≤ m2r σ < 1` is what bounds `e < SC` (and hence `mulU e sg < 2^32`). -/
lemma shi_upper {x y e σ : ℤ} (he : 0 ≤ e) (hσlt : m2r σ < 1) (hRσ : srad x y e ≤ m2r σ)
    {k : ℕ} (hk : k < SERM) {px py pe sg : ℤ} (h : SerInv x y e σ k px py pe sg) :
    shi x y σ e k px py pe sg ≤ 2 ^ 60 := by
  obtain ⟨hpe0, hpe3, hsgk, hsg2, herr, hx34, hy34⟩ := h
  have he0 : (0:ℝ) ≤ m2r e := m2r_nonneg_NrmSpec he
  have hsrad0 : (0:ℝ) ≤ srad x y e := by
    simp only [srad]; linarith [norm_nonneg (spt x y)]
  have hsg0 : 0 ≤ sg := by
    have h' : 0 ≤ m2r sg := le_trans (pow_nonneg hsrad0 k) hsgk
    exact (m2r_nonneg_iff sg).mp h'
  have hpe : pe ≤ 3 * SC := by
    by_contra hc
    have hlt : 3 * SC < pe := lt_of_not_ge hc
    have h' := m2r_lt hlt
    rw [m2r_mul_SC'] at h'
    norm_num at h'
    linarith
  have he_lt : e < SC := by
    have h1 : m2r e < 1 := by
      have hle : m2r e ≤ srad x y e := by simp only [srad]; linarith [norm_nonneg (spt x y)]
      exact lt_of_le_of_lt (le_trans hle hRσ) hσlt
    by_contra hc
    have hc' : SC ≤ e := le_of_not_gt hc
    have h2 : (1:ℝ) ≤ m2r e := by
      have h' := m2r_le hc'
      rwa [m2r_SC] at h'
    linarith
  have hsg_le : sg ≤ 2 * SC := by
    by_contra hc
    have hc' : 2 * SC < sg := lt_of_not_ge hc
    have h' := m2r_lt hc'
    rw [m2r_two] at h'
    linarith
  have hSC : SC = 2 ^ 30 := by norm_num [SC]
  have hmul32 : mulU e sg < 2 ^ 32 := by
    have h1 := mulU_mul_SC_lt e sg
    have he1 : e ≤ SC - 1 := by omega
    have hprod : e * sg ≤ (SC - 1) * (2 * SC) :=
      mul_le_mul he1 hsg_le hsg0 (by omega)
    have h2 : mulU e sg * SC < 2 ^ 32 * SC := by nlinarith
    exact lt_of_mul_lt_mul_right h2 SC_pos.le
  have hk44 : (k : ℤ) + 1 ≤ 44 := by
    have h' : k < 44 := by simpa [SERM] using hk
    omega
  have hmulU0 : 0 ≤ mulU e sg := by
    have h' : 0 ≤ m2r e * m2r sg := mul_nonneg he0 (le_trans (pow_nonneg hsrad0 k) hsgk)
    have h2 := le_trans h' (le_mulU e sg)
    exact (m2r_nonneg_iff (mulU e sg)).mp h2
  have hprod2 : ((k:ℤ)+1) * mulU e sg ≤ 44 * 2 ^ 32 := by nlinarith
  have hnrm : nrmUp (SC + px) py ≤ 2 ^ 36 := nrmUp_le hx34 hy34
  simp only [shi]
  nlinarith

/-- **The assignment.**  Each term of the logarithmic series is bounded above by the
mantissa `shi` of the certificate. -/
theorem SerInvTerm {x y e σ : ℤ} (he : 0 ≤ e) (hσlt : Work.ANum.m2r σ < 1) (hRσ : Work.CNum.srad x y e ≤ Work.ANum.m2r σ) {k : ℕ} (hk : k < Work.CNum.SERM) {px py pe sg : ℤ} (h : Work.CNum.SerInv x y e σ k px py pe sg) : Work.CNum.sT x y e k ≤ Work.ANum.m2r (Work.CNum.logUpM (Work.CNum.shi x y σ e k px py pe sg)) := by
  have harg := sT_arg_le (x := x) (y := y) (e := e) (σ := σ) (k := k) he h
  have hpos := log_arg_pos (x := x) (y := y) (e := e) he (lt_of_le_of_lt hRσ hσlt) k
  have h1 : 1 ≤ shi x y σ e k px py pe sg := ShiLower he hσlt hRσ hk h
  have h2 : shi x y σ e k px py pe sg ≤ 2 ^ 60 := shi_upper he hσlt hRσ hk h
  simp only [Work.CNum.sT]
  exact LogUpMSpec_pos h1 h2 harg hpos

end Work.CNum
