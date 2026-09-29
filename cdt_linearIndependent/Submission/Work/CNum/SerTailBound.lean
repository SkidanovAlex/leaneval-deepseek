import Mathlib
import Submission.Work.CNum.SerUpDefs
import Submission.Work.CNum.LgInfra

/-!
# `Work.CNum.SerTailBound` — the geometric tail of the `serUp` series

`Work.CNum.serUp x y e` bounds `log ‖h w‖` on the ball of centre `(x + iy)/SC` and radius
`m2r e` by

  `log 256 + log R + 24 Σ_{n < SERM} T_n + 24 · (geometric tail)`,

where `R = srad x y e = ‖spt x y‖ + m2r e` is the series variable and `σ` is a mantissa with
`R ≤ m2r σ < 1` (the certificate runs the series in the variable `σ`, whose rounded powers are
computed by `powM true σ`).  The tail is bounded by

  `R^(SERM+1)/(1-R) ≤ σ^(SERM+1)/(1-σ)`.

This file proves that bound, together with the elementary nonnegativity lemmas for the
rounding primitives `mulU`, `divUz`, `powM` that it needs.

* `σ^(SERM+1)/(1-σ) ≤ m2r (divUz (SC · powM true σ (SERM+1)) (SC - σ))`
  (`powM_true_ge` plus the ceiling-division soundness `divUz_ge`);
* the two remaining summands of the mantissa expression are nonnegative, so they may be
  discarded (`m2r` is monotone).
-/

namespace Work.CNum

open Work.ANum

/-- `mulU a b = ⌈a·b/SC⌉` is nonnegative when `a, b ≥ 0`. -/
lemma mulU_nonneg {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ mulU a b := by
  simp only [mulU]
  have hab : 0 ≤ a * b := Int.mul_nonneg ha hb
  have h1 : Int.ediv (-(a * b)) SC ≤ Int.ediv 0 SC :=
    Int.ediv_le_ediv (c := SC) SC_pos (show -(a * b) ≤ 0 by omega)
  have h2 : Int.ediv (0 : ℤ) SC = 0 := Int.zero_ediv SC
  have h : Int.ediv (-(a * b)) SC ≤ 0 := by linarith
  exact neg_nonneg.mpr h

/-- `divUz a b = ⌈a/b⌉` is nonnegative when `a ≥ 0` and `b > 0`. -/
lemma divUz_nonneg {a b : ℤ} (ha : 0 ≤ a) (hb : 0 < b) : 0 ≤ divUz a b := by
  simp only [divUz]
  have h1 : Int.ediv (-a) b ≤ Int.ediv 0 b :=
    Int.ediv_le_ediv (c := b) hb (show -a ≤ 0 by omega)
  have h2 : Int.ediv (0 : ℤ) b = 0 := Int.zero_ediv b
  have h : Int.ediv (-a) b ≤ 0 := by linarith
  exact neg_nonneg.mpr h

/-- The rounded power `powM true q` of a nonnegative mantissa is nonnegative. -/
lemma powM_true_nonneg {q : ℤ} (hq : 0 ≤ q) (m : ℕ) : 0 ≤ powM true q m := by
  induction m with
  | zero => simp [powM]; exact SC_pos.le
  | succ m ih =>
      have h1 : powM true q (m + 1) = mulU (powM true q m) q := by
        simp only [powM, if_true]
      rw [h1]
      exact mulU_nonneg ih hq

theorem SerTailBound {x y e σ : ℤ} (he : 0 ≤ e) (hσlt : Work.ANum.m2r σ < 1) (hRσ : Work.CNum.srad x y e ≤ Work.ANum.m2r σ) : Work.CNum.srad x y e ^ (Work.CNum.SERM + 1) / (1 - Work.CNum.srad x y e) ≤ Work.ANum.m2r (Work.CNum.divUz (Work.ANum.SC * Work.CNum.powM true σ (Work.CNum.SERM + 1)) (Work.ANum.SC - σ) + Work.CNum.divUz (Work.ANum.SC * Work.CNum.mulU e ((Work.CNum.SERM + 1) * Work.CNum.powM true σ Work.CNum.SERM)) ((Work.ANum.SC - σ) * (Work.ANum.SC - σ)) + 4) := by
  have henn : 0 ≤ m2r e := m2r_nonneg_NrmSpec he
  have hRnn : 0 ≤ srad x y e := by
    simp only [srad]
    exact add_nonneg (norm_nonneg _) henn
  have hσnn : 0 ≤ m2r σ := le_trans hRnn hRσ
  have hRlt : srad x y e < 1 := lt_of_le_of_lt hRσ hσlt
  have hdenR : 0 < 1 - srad x y e := by linarith
  have hdenσ : 0 < 1 - m2r σ := by linarith
  -- Step 1: `R ↦ m2r σ` for the series variable.
  have hstep1 : srad x y e ^ (SERM + 1) / (1 - srad x y e) ≤
      (m2r σ) ^ (SERM + 1) / (1 - m2r σ) := by
    rw [div_le_div_iff₀ hdenR hdenσ]
    exact mul_le_mul (pow_le_pow_left₀ hRnn hRσ _) (by linarith) hdenσ.le (pow_nonneg hσnn _)
  have hσZ : 0 ≤ σ := (m2r_nonneg_iff σ).mp hσnn
  have hSCσ : σ < SC := by
    by_contra h
    have h2 : SC ≤ σ := not_lt.mp h
    have h3 := m2r_le h2
    rw [m2r_SC] at h3
    linarith
  have hd : 0 < SC - σ := by omega
  -- Step 2: `σ^(SERM+1)/(1-σ)` is dominated by the first tail summand.
  have hP : (m2r σ) ^ (SERM + 1) ≤ m2r (powM true σ (SERM + 1)) := powM_true_ge hσnn _
  have hnum : (m2r σ) ^ (SERM + 1) * (SC : ℝ) ≤ m2r (SC * powM true σ (SERM + 1)) := by
    rw [mul_comm (SC : ℤ) (powM true σ (SERM + 1)), m2r_mul_int]
    exact mul_le_mul_of_nonneg_right hP SC_posR.le
  have hstep2 : (m2r σ) ^ (SERM + 1) * (SC : ℝ) / ((SC - σ : ℤ) : ℝ) ≤
      m2r (divUz (SC * powM true σ (SERM + 1)) (SC - σ)) := by
    have h1 : (m2r σ) ^ (SERM + 1) * (SC : ℝ) / ((SC - σ : ℤ) : ℝ) ≤
        m2r (SC * powM true σ (SERM + 1)) / ((SC - σ : ℤ) : ℝ) :=
      div_le_div_of_nonneg_right hnum (by exact_mod_cast hd.le)
    exact le_trans h1 (divUz_ge hd _)
  have heq : (m2r σ) ^ (SERM + 1) * (SC : ℝ) / ((SC - σ : ℤ) : ℝ) =
      (m2r σ) ^ (SERM + 1) / (1 - m2r σ) := by
    have hcast : ((SC - σ : ℤ) : ℝ) = (SC : ℝ) * m2r (SC - σ) := by
      rw [← Iv.m2r_mul_SC (SC - σ)]; ring
    rw [hcast, m2r_sub, m2r_SC]
    rw [mul_comm ((m2r σ) ^ (SERM + 1)) (SC : ℝ)]
    exact mul_div_mul_left _ _ (ne_of_gt SC_posR)
  have hkey : (m2r σ) ^ (SERM + 1) / (1 - m2r σ) ≤
      m2r (divUz (SC * powM true σ (SERM + 1)) (SC - σ)) := by
    rw [← heq]; exact hstep2
  -- Step 3: the two remaining summands are nonnegative, hence can be dropped.
  have hP44 : 0 ≤ powM true σ SERM := powM_true_nonneg hσZ SERM
  have h45 : (0 : ℤ) ≤ ((SERM + 1 : ℕ) : ℤ) := Int.natCast_nonneg _
  have hB1 : 0 ≤ ((SERM + 1 : ℕ) : ℤ) * powM true σ SERM := Int.mul_nonneg h45 hP44
  have hB2 : 0 ≤ mulU e (((SERM + 1 : ℕ) : ℤ) * powM true σ SERM) := mulU_nonneg he hB1
  have hB3 : 0 ≤ SC * mulU e (((SERM + 1 : ℕ) : ℤ) * powM true σ SERM) :=
    Int.mul_nonneg SC_pos.le hB2
  have hB4 : 0 < (SC - σ) * (SC - σ) := Int.mul_pos hd hd
  have hB : 0 ≤ divUz (SC * mulU e (((SERM + 1 : ℕ) : ℤ) * powM true σ SERM))
      ((SC - σ) * (SC - σ)) := divUz_nonneg hB3 hB4
  have hmono : divUz (SC * powM true σ (SERM + 1)) (SC - σ) ≤
      divUz (SC * powM true σ (SERM + 1)) (SC - σ) +
        divUz (SC * mulU e (((SERM + 1 : ℕ) : ℤ) * powM true σ SERM))
          ((SC - σ) * (SC - σ)) + 4 := by
    omega
  exact le_trans hstep1 (le_trans hkey (m2r_le hmono))

end Work.CNum
