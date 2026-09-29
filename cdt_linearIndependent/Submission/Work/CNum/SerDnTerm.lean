import Mathlib
import Submission.Work.CNum.SerDnDefs
import Submission.Work.CNum.NrmSpec
import Submission.Work.CNum.IsqrtSpec
import Submission.Work.CNum.LgInfra
import Submission.Work.ANum.norm_pow_succ_sub_pow_succ_le

/-!
# `Work.CNum.SerDnTerm` — per-term soundness of the `serDn` logarithmic series

`Work.CNum.serDn x y e` lower-bounds `log ‖h w‖` (`h = Submission.CDTPlan.hauptH`) for every
`w` in the ball of centre `c = (x+iy)/SC` and radius `ρ = m2r e` by evaluating

  `log 256 + log ‖c‖ + 24 Σ_{k < SERM} log (‖1 + c^{k+1}‖ - (SERM-k) ρ R^k) - 24·(tail)`,
  `R = ‖c‖ + ρ`,

term by term; the `k`-th mantissa is `sdLo σ e (SERM-k) s` where `s` is the state of the
recursion after `k` steps.

This file proves that the mantissa `sdLo σ e (SERM-k) s` is a legitimate *lower* bound: writing
`p = (px + i py)/SC` for the tracked approximation of `c^{k+1}`, the invariant `SDInv` gives
`‖c^{k+1} - p‖ ≤ m2r pe`, `R^k ≤ m2r sg ≤ 2` and `|SC+px|, |py| ≤ 2^34`, whence

* `sdLo σ e (SERM-k) s ≥ 1` (positivity: `R ≤ m2r σ ≤ 79/100` keeps `1 + c^{k+1}` at distance
  `1 - 79/100` from the origin, and the errors are `≤ 2/100 + 44·(2·10⁻⁶ + 1/SC)`),
* `sdLo σ e (SERM-k) s ≤ 2^60`,
* `m2r (sdLo σ e (SERM-k) s) ≤ ‖1 + w^{k+1}‖ + (2k+1-SERM)·ρ·R^k`: this is the term-by-term
  estimate used by `SerDnSpec`, tight in the sense that for `k` near `SERM` the extra term
  `(2k+1-SERM) ρ R^k` is precisely the slack which `SerDnNum` sums up.
-/

namespace Work.CNum

open Work.ANum

/-! ## Elementary helpers -/

private lemma m2r_one_int : m2r (1 : ℤ) = 1 / (SC : ℝ) := by simp [m2r]

private lemma nrmUp_eq_nrmDn_add_one (x y : ℤ) : nrmUp x y = nrmDn x y + 1 := by
  simp only [nrmUp, nrmDn, sqUp, sqDn]
  push_cast
  ring

private lemma spt_one_add (px py : ℤ) : (1:ℂ) + spt px py = spt (SC + px) py := by
  have hSC : ((SC:ℤ) : ℂ) ≠ 0 := by norm_num [SC]
  unfold spt
  push_cast
  rw [eq_div_iff hSC]
  field_simp
  ring

/-- Ceiling-rounded product: `mulU a b · SC < a·b + SC`. -/
private lemma mulU_mul_SC_lt (a b : ℤ) : mulU a b * SC < a * b + SC := by
  have h := Int.ediv_mul_add_emod (-(a * b)) SC
  have hlt := Int.emod_lt_of_pos (-(a * b)) SC_pos
  set q := Int.ediv (-(a * b)) SC with hq
  set em := (-(a * b)) % SC with hem
  have h1 : q * SC + em = -(a * b) := by
    rw [hq, hem]
    exact h
  have h3 : mulU a b = -q := by simp only [mulU, hq]
  rw [h3]
  linarith

private lemma m2r_mulU_lt (a b : ℤ) : m2r (mulU a b) < m2r a * m2r b + 1 / (SC : ℝ) := by
  have hlt := mulU_mul_SC_lt a b
  have hR : ((mulU a b : ℤ) : ℝ) * (SC:ℝ) < ((a * b : ℤ) : ℝ) + (SC:ℝ) := by
    exact_mod_cast hlt
  have h1 : ((mulU a b : ℤ) : ℝ) < ((a * b : ℤ) : ℝ) / (SC:ℝ) + 1 := by
    have h := div_lt_div_of_pos_right hR SC_posR
    rwa [mul_div_cancel_right₀ _ (ne_of_gt SC_posR), add_div, div_self (ne_of_gt SC_posR)] at h
  have h2 : m2r (mulU a b) < (((a * b : ℤ) : ℝ) / (SC:ℝ) + 1) / (SC:ℝ) := by
    have h := div_lt_div_of_pos_right h1 SC_posR
    simpa only [m2r] using h
  have h3 : (((a * b : ℤ) : ℝ) / (SC:ℝ) + 1) / (SC:ℝ) = m2r a * m2r b + 1 / (SC:ℝ) := by
    simp only [m2r]
    rw [add_div, div_div, div_mul_div_comm]
    push_cast
    ring
  linarith

/-- `nrmUp x y ≤ 2^36` whenever `|x|, |y| ≤ 2^34` (the `< 2^70` regime of `IsqrtSpec`). -/
private lemma nrmUp_le {x y : ℤ} (hx : x.natAbs ≤ 2 ^ 34) (hy : y.natAbs ≤ 2 ^ 34) :
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

/-! ## The analytic core -/

private lemma serDnTerm_core {x y e σ : ℤ} {w : ℂ} {k : ℕ} {px py pe sg : ℤ}
    (he : 0 ≤ e) (he1 : m2r e ≤ 1 / 10 ^ 6) (hσ1 : m2r σ ≤ 79 / 100)
    (hRσ : srad x y e ≤ m2r σ) (hw : ‖w - spt x y‖ ≤ m2r e) (hk : k < SERM)
    (hpe0 : 0 ≤ pe) (hpe : m2r pe ≤ 1 / 100) (hsgk : srad x y e ^ k ≤ m2r sg)
    (hsg2 : m2r sg ≤ 2) (herr : ‖spt x y ^ (k + 1) - spt px py‖ ≤ m2r pe)
    (hx34 : Int.natAbs (SC + px) ≤ 2 ^ 34) (hy34 : Int.natAbs py ≤ 2 ^ 34) :
    1 ≤ sdLo σ e ((SERM - k : ℕ) : ℤ) ⟨px, py, pe, sg⟩ ∧
      sdLo σ e ((SERM - k : ℕ) : ℤ) ⟨px, py, pe, sg⟩ ≤ 2 ^ 60 ∧
      m2r (sdLo σ e ((SERM - k : ℕ) : ℤ) ⟨px, py, pe, sg⟩) ≤
        ‖(1 : ℂ) + w ^ (k + 1)‖ +
          (2 * (k : ℝ) + 1 - SERM) * m2r e * srad x y e ^ k := by
  have he0 : (0:ℝ) ≤ m2r e := m2r_nonneg_NrmSpec he
  have hR0 : (0:ℝ) ≤ srad x y e := by
    simp only [srad]; linarith [norm_nonneg (spt x y), he0]
  have hR1 : srad x y e ≤ 79 / 100 := le_trans hRσ hσ1
  have hc_le : ‖spt x y‖ ≤ srad x y e := by simp only [srad]; linarith
  -- unfold the mantissa
  have hsd : m2r (sdLo σ e ((SERM - k : ℕ) : ℤ) ⟨px, py, pe, sg⟩)
      = m2r (nrmDn (SC + px) py) - m2r pe - ((SERM - k : ℕ) : ℝ) * m2r (mulU e sg)
        - m2r 4 := by
    simp only [sdLo, m2r_sub, m2r_mul_int']
    push_cast
    ring
  have h4z : (0:ℝ) ≤ m2r (4:ℤ) := by
    simp only [m2r]
    exact div_nonneg (by norm_num) SC_posR.le
  -- the norm of the tracked point `1 + p` vs `1 + c^(k+1)`
  have hnorm_pt : ‖spt (SC + px) py‖ = ‖(1:ℂ) + spt px py‖ := by rw [spt_one_add]
  have herr' : ‖spt px py - spt x y ^ (k + 1)‖ ≤ m2r pe := by
    rw [norm_sub_rev]; exact herr
  -- (A) upper bound for `nrmDn (SC+px) py`
  have hA : m2r (nrmDn (SC + px) py) ≤ ‖(1:ℂ) + spt x y ^ (k + 1)‖ + m2r pe := by
    have hnd : m2r (nrmDn (SC + px) py) ≤ ‖(1:ℂ) + spt px py‖ := by
      rw [spt_one_add]
      have h := NrmDnSpec (x := SC + px) (y := py) hx34 hy34
      simpa only [spt] using h
    have hsplit : (1:ℂ) + spt px py
        = ((1:ℂ) + spt x y ^ (k+1)) + (spt px py - spt x y ^ (k+1)) := by ring
    have h2 : ‖(1:ℂ) + spt px py‖ ≤ ‖(1:ℂ) + spt x y ^ (k+1)‖ + m2r pe := by
      rw [hsplit]
      have h3 := norm_add_le ((1:ℂ) + spt x y ^ (k+1)) (spt px py - spt x y ^ (k+1))
      linarith
    linarith
  -- (B) `‖1 + c^(k+1)‖ ≤ ‖1 + w^(k+1)‖ + (k+1) R^k ρ`
  have hB : ‖(1:ℂ) + spt x y ^ (k + 1)‖ ≤ ‖(1:ℂ) + w ^ (k + 1)‖
      + ((k:ℝ) + 1) * srad x y e ^ k * m2r e := by
    have hcw : ‖spt x y - w‖ ≤ m2r e := by rw [norm_sub_rev]; exact hw
    have hwyl : ‖w‖ ≤ srad x y e := by
      have h2 : ‖w‖ ≤ ‖w - spt x y‖ + ‖spt x y‖ := by
        have h := norm_add_le (w - spt x y) (spt x y)
        have heq : (w - spt x y) + spt x y = w := by ring
        rwa [heq] at h
      have h3 : ‖w - spt x y‖ + ‖spt x y‖ ≤ m2r e + ‖spt x y‖ := by linarith
      have h4 : m2r e + ‖spt x y‖ = srad x y e := by simp only [srad]; ring
      linarith
    have hpow := norm_pow_succ_sub_pow_succ_le (x := spt x y) (y := w)
      (r := srad x y e) hc_le hwyl k
    have hsplit : (1:ℂ) + spt x y ^ (k+1)
        = ((1:ℂ) + w ^ (k+1)) + (spt x y ^ (k+1) - w ^ (k+1)) := by ring
    have h3 : ‖spt x y ^ (k+1) - w ^ (k+1)‖ ≤ ((k:ℝ) + 1) * srad x y e ^ k * m2r e := by
      calc ‖spt x y ^ (k+1) - w ^ (k+1)‖
          ≤ ((k:ℝ) + 1) * srad x y e ^ k * ‖spt x y - w‖ := hpow
        _ ≤ ((k:ℝ) + 1) * srad x y e ^ k * m2r e := by
            have h1 : (0:ℝ) ≤ ((k:ℝ) + 1) * srad x y e ^ k := by positivity
            exact mul_le_mul_of_nonneg_left hcw h1
    rw [hsplit]
    have h4 := norm_add_le ((1:ℂ) + w ^ (k+1)) (spt x y ^ (k+1) - w ^ (k+1))
    linarith
  -- (C) the error term
  have hC : ((SERM - k : ℕ) : ℝ) * (m2r e * srad x y e ^ k)
      ≤ ((SERM - k : ℕ) : ℝ) * m2r (mulU e sg) := by
    have h1 : m2r e * srad x y e ^ k ≤ m2r (mulU e sg) := by
      calc m2r e * srad x y e ^ k ≤ m2r e * m2r sg :=
            mul_le_mul_of_nonneg_left hsgk he0
        _ ≤ m2r (mulU e sg) := le_mulU e sg
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  -- the coefficient identity
  have hcoef : (2 * (k:ℝ) + 1 - SERM) * m2r e * srad x y e ^ k
      = ((k:ℝ) + 1) * m2r e * srad x y e ^ k
        - ((SERM - k : ℕ) : ℝ) * (m2r e * srad x y e ^ k) := by
    have hk' : k ≤ SERM := le_of_lt hk
    have hcast : ((SERM - k : ℕ) : ℝ) = (SERM:ℝ) - (k:ℝ) := by
      push_cast [Nat.cast_sub hk']
      ring
    rw [hcast]; ring
  refine ⟨?_, ?_, ?_⟩
  · -- positivity
    have hlow_nrm : (21:ℝ)/100 - m2r pe - 1/SC ≤ m2r (nrmDn (SC + px) py) := by
      have hup : ‖spt (SC + px) py‖ ≤ m2r (nrmDn (SC + px) py) + 1 / (SC:ℝ) := by
        have h := NrmUpSpec (x := SC + px) (y := py) hx34 hy34
        have h' : m2r (nrmUp (SC + px) py) = m2r (nrmDn (SC + px) py) + 1 / (SC:ℝ) := by
          rw [nrmUp_eq_nrmDn_add_one, m2r_add, m2r_one_int]
        simpa only [spt, h'] using h
      have hge1 : 1 - srad x y e ≤ ‖(1:ℂ) + spt x y ^ (k+1)‖ := by
        have hle : ‖spt x y ^ (k+1)‖ ≤ srad x y e := by
          rw [norm_pow]
          calc ‖spt x y‖ ^ (k+1) ≤ ‖spt x y‖ ^ 1 :=
                pow_le_pow_of_le_one (norm_nonneg _) (by linarith : ‖spt x y‖ ≤ 1) (by omega)
            _ = ‖spt x y‖ := pow_one _
            _ ≤ srad x y e := hc_le
        have h2 : (1:ℝ) ≤ ‖(1:ℂ) + spt x y^(k+1)‖ + ‖spt x y^(k+1)‖ := by
          have h := norm_add_le ((1:ℂ) + spt x y^(k+1)) (-(spt x y^(k+1)))
          have hL : ((1:ℂ) + spt x y^(k+1)) + -(spt x y^(k+1)) = 1 := by ring
          rw [hL, norm_one, norm_neg] at h
          exact h
        linarith
      have hlow : 1 - 79/100 - m2r pe ≤ ‖spt (SC + px) py‖ := by
        rw [hnorm_pt]
        have h3 : (1:ℝ) - 79/100 ≤ ‖(1:ℂ) + spt x y ^ (k+1)‖ := by linarith
        have h4 : ‖(1:ℂ) + spt px py‖ ≥ ‖(1:ℂ) + spt x y^(k+1)‖ - m2r pe := by
          have h := norm_sub_le ((1:ℂ) + spt px py) (spt px py - spt x y^(k+1))
          have heq : ((1:ℂ) + spt px py) - (spt px py - spt x y^(k+1))
              = (1:ℂ) + spt x y^(k+1) := by ring
          rw [heq, norm_sub_rev] at h
          linarith
        linarith
      linarith
    have hprod : ((SERM - k : ℕ) : ℝ) * m2r (mulU e sg) ≤ 44 * (2/10^6 + 1/(SC:ℝ)) := by
      have hle44 : ((SERM - k : ℕ) : ℝ) ≤ 44 := by
        have h : (SERM - k : ℕ) ≤ 44 := by simp only [SERM]; omega
        exact_mod_cast h
      have hq : m2r (mulU e sg) ≤ 2/10^6 + 1/(SC:ℝ) := by
        have h1 := (m2r_mulU_lt e sg).le
        have h2 : m2r e * m2r sg ≤ (1/10^6) * 2 :=
          mul_le_mul he1 hsg2 (le_trans (pow_nonneg hR0 k) hsgk) (by norm_num)
        linarith
      have hq0 : 0 ≤ m2r (mulU e sg) := by
        have h1 : 0 ≤ m2r e * m2r sg :=
          mul_nonneg he0 (le_trans (pow_nonneg hR0 k) hsgk)
        linarith [le_mulU e sg]
      exact mul_le_mul hle44 hq hq0 (by norm_num)
    have hm4 : m2r (4:ℤ) = 4/(SC:ℝ) := by
      simp only [m2r]; push_cast; ring
    have hnum : (0:ℝ) < 21/100 - 2/100 - 1/SC - 44 * (2/10^6 + 1/SC) - 4/SC := by
      have hSCv : (SC:ℝ) = 2^30 := by norm_num [SC]
      rw [hSCv]; norm_num
    have key : (0:ℝ) < m2r (sdLo σ e ((SERM - k : ℕ) : ℤ) ⟨px, py, pe, sg⟩) := by
      rw [hsd]
      nlinarith [hlow_nrm, hpe, hprod, h4z, hnum, hm4]
    have hpos : 0 < sdLo σ e ((SERM - k : ℕ) : ℤ) ⟨px, py, pe, sg⟩ :=
      (m2r_pos_iff _).mp key
    omega
  · -- upper bound
    have hnrmUp : nrmUp (SC + px) py ≤ 2 ^ 36 := nrmUp_le hx34 hy34
    have hnd : nrmDn (SC + px) py ≤ 2 ^ 60 := by
      have h := hnrmUp
      rw [nrmUp_eq_nrmDn_add_one] at h
      linarith
    have hmulU0 : 0 ≤ mulU e sg := by
      have h1 : 0 ≤ m2r e * m2r sg :=
        mul_nonneg he0 (le_trans (pow_nonneg hR0 k) hsgk)
      exact (m2r_nonneg_iff _).mp (le_trans h1 (le_mulU e sg))
    have hmz0 : 0 ≤ ((SERM - k : ℕ) : ℤ) := by positivity
    simp only [sdLo]
    nlinarith [hnd, hpe0, hmulU0, hmz0]
  · -- the term estimate
    rw [hsd, hcoef]
    nlinarith [hA, hB, hC, h4z]

theorem SerDnTerm {x y e σ : ℤ} {w : ℂ} {k : ℕ} {s : Work.CNum.SD} (he : 0 ≤ e) (he1 : Work.ANum.m2r e ≤ 1 / 10 ^ 6) (hσ1 : Work.ANum.m2r σ ≤ 79 / 100) (hRσ : Work.CNum.srad x y e ≤ Work.ANum.m2r σ) (hw : ‖w - Work.CNum.spt x y‖ ≤ Work.ANum.m2r e) (hk : k < Work.CNum.SERM) (h : Work.CNum.SDInv x y e σ k s) : 1 ≤ Work.CNum.sdLo σ e ((Work.CNum.SERM - k : ℕ) : ℤ) s ∧ Work.CNum.sdLo σ e ((Work.CNum.SERM - k : ℕ) : ℤ) s ≤ 2 ^ 60 ∧ Work.ANum.m2r (Work.CNum.sdLo σ e ((Work.CNum.SERM - k : ℕ) : ℤ) s) ≤ ‖(1 : ℂ) + w ^ (k + 1)‖ + (2 * (k : ℝ) + 1 - Work.CNum.SERM) * Work.ANum.m2r e * Work.CNum.srad x y e ^ k := by
  obtain ⟨px, py, pe, sg⟩ := s
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact serDnTerm_core he he1 hσ1 hRσ hw hk h1 h2 h3 h4 h5 h6 h7

end Work.CNum
