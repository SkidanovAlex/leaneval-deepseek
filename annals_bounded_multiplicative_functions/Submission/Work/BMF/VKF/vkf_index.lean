import Mathlib
import Submission.Work.BMF.VKF.defs
import Submission.Work.BMF.vkford_H_lower2

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.VKF

/-- Ford's saving index, after the two Stechkin excesses are paid for, is at least `1/(dDλ²)`:

`(H − (Δ₁+Δ₂)μ)/(2rs) ≥ 1/(10⁹·λ²)`.

Route: `H = dHidx N lam ≥ λ²/10` (`Work.BMF.vkford_H_lower2`, whose hypotheses
`λ ≤ h ≤ λ+1`, `2λ+1 ≤ g ≤ 6λ+1`, `2/5 ≤ μ ≤ 41/100` are all among the assumptions), while
`(Δ₁+Δ₂)μ ≤ 2·(λ²/50)·(41/100) < λ²/20`, so `H − (Δ₁+Δ₂)μ ≥ λ²/20`; and
`2rs ≤ 2·(310λ²)(205λ²) = 1.271·10⁵λ⁴`, whence the quotient is `≥ 3.9·10⁻⁷/λ² ≥ 1/(10⁹λ²)`. -/
theorem vkf_index (N lam : ℝ) (hN : 2 ≤ N) (hlogN : 70 ≤ Real.log N) (hlam : 13 / 5 ≤ lam)
    (hh : lam ≤ ((Work.BMF.VKF.dH lam : ℕ) : ℝ))
    (hh2 : ((Work.BMF.VKF.dH lam : ℕ) : ℝ) ≤ lam + 1)
    (hg1 : 2 * lam + 1 ≤ ((Work.BMF.VKF.dG lam : ℕ) : ℝ))
    (hg2 : ((Work.BMF.VKF.dG lam : ℕ) : ℝ) ≤ 6 * lam + 1)
    (hmu1 : 2 / 5 ≤ Work.BMF.VKF.dMu N) (hmu2 : Work.BMF.VKF.dMu N ≤ 41 / 100)
    (hd1 : Work.BMF.VKF.dDelta1 lam ≤ lam ^ 2 / 50)
    (hd2 : Work.BMF.VKF.dDelta2 lam ≤ lam ^ 2 / 50)
    (hr : 300 * lam ^ 2 ≤ ((Work.BMF.VKF.dR lam : ℕ) : ℝ))
    (hs : 200 * lam ^ 2 ≤ ((Work.BMF.VKF.dS lam : ℕ) : ℝ))
    (hr2 : ((Work.BMF.VKF.dR lam : ℕ) : ℝ) ≤ 310 * lam ^ 2)
    (hs2 : ((Work.BMF.VKF.dS lam : ℕ) : ℝ) ≤ 205 * lam ^ 2) :
    1 / (Work.BMF.VKF.dD * lam ^ 2) ≤
      (Work.BMF.VKF.dHidx N lam
          - (Work.BMF.VKF.dDelta1 lam + Work.BMF.VKF.dDelta2 lam) * Work.BMF.VKF.dMu N)
        / (2 * ((Work.BMF.VKF.dR lam : ℕ) : ℝ) * ((Work.BMF.VKF.dS lam : ℕ) : ℝ)) := by
  have hlam0 : (0 : ℝ) < lam := by linarith
  -- Ford's saving index is at least `λ²/10`.
  have hH_low : lam ^ 2 / 10 ≤ Work.BMF.VKF.dHidx N lam := by
    have h := Work.BMF.vkford_H_lower2 (Work.BMF.VKF.dH lam) (Work.BMF.VKF.dG lam)
      (Work.BMF.VKF.dMu N) (Work.BMF.VKF.dMu N) lam
      (by linarith) hh hh2 hg1 hg2 hmu1 hmu1 (by linarith)
    simpa [Work.BMF.VKF.dHidx] using h
  -- The Stechkin excesses cost at most `λ²/20`.
  have hmul : (Work.BMF.VKF.dDelta1 lam + Work.BMF.VKF.dDelta2 lam) * Work.BMF.VKF.dMu N
      ≤ lam ^ 2 / 20 := by
    have hsum : Work.BMF.VKF.dDelta1 lam + Work.BMF.VKF.dDelta2 lam ≤ lam ^ 2 / 25 := by
      linarith
    have hmu0 : (0 : ℝ) ≤ Work.BMF.VKF.dMu N := by linarith
    have h1 : (Work.BMF.VKF.dDelta1 lam + Work.BMF.VKF.dDelta2 lam) * Work.BMF.VKF.dMu N
        ≤ (lam ^ 2 / 25) * (41 / 100) := mul_le_mul hsum hmu2 hmu0 (by positivity)
    nlinarith [h1, sq_nonneg lam]
  -- Hence the numerator is at least `λ²/20`.
  have hnum : lam ^ 2 / 20 ≤ Work.BMF.VKF.dHidx N lam
      - (Work.BMF.VKF.dDelta1 lam + Work.BMF.VKF.dDelta2 lam) * Work.BMF.VKF.dMu N := by
    linarith [hH_low, hmul]
  have hRpos : (0 : ℝ) < ((Work.BMF.VKF.dR lam : ℕ) : ℝ) := by nlinarith [hr, sq_nonneg lam]
  have hSpos : (0 : ℝ) < ((Work.BMF.VKF.dS lam : ℕ) : ℝ) := by nlinarith [hs, sq_nonneg lam]
  have hden_pos : (0 : ℝ) < 2 * ((Work.BMF.VKF.dR lam : ℕ) : ℝ) * ((Work.BMF.VKF.dS lam : ℕ) : ℝ) :=
    by positivity
  -- The denominator is at most `2·310·205·λ⁴`.
  have hden_le : 2 * ((Work.BMF.VKF.dR lam : ℕ) : ℝ) * ((Work.BMF.VKF.dS lam : ℕ) : ℝ)
      ≤ 127100 * lam ^ 4 := by
    have hR0 : (0 : ℝ) ≤ ((Work.BMF.VKF.dR lam : ℕ) : ℝ) := Nat.cast_nonneg _
    have hS0 : (0 : ℝ) ≤ ((Work.BMF.VKF.dS lam : ℕ) : ℝ) := Nat.cast_nonneg _
    nlinarith [hr2, hs2, hR0, hS0, sq_nonneg lam]
  have hAD : (1 / (Work.BMF.VKF.dD * lam ^ 2))
        * (2 * ((Work.BMF.VKF.dR lam : ℕ) : ℝ) * ((Work.BMF.VKF.dS lam : ℕ) : ℝ))
      ≤ lam ^ 2 / 20 := by
    have h1 : (1 / (Work.BMF.VKF.dD * lam ^ 2))
          * (2 * ((Work.BMF.VKF.dR lam : ℕ) : ℝ) * ((Work.BMF.VKF.dS lam : ℕ) : ℝ))
        ≤ (1 / (Work.BMF.VKF.dD * lam ^ 2)) * (127100 * lam ^ 4) :=
      mul_le_mul_of_nonneg_left hden_le (by
        apply div_nonneg one_pos.le
        exact (mul_pos Work.BMF.VKF.dD_pos (pow_pos hlam0 2)).le)
    have h2 : (1 / (Work.BMF.VKF.dD * lam ^ 2)) * (127100 * lam ^ 4)
        = 127100 * lam ^ 2 / Work.BMF.VKF.dD := by
      field_simp
    have h3 : (127100 : ℝ) * lam ^ 2 / Work.BMF.VKF.dD ≤ lam ^ 2 / 20 := by
      have hdD : Work.BMF.VKF.dD = (10 : ℝ) ^ 9 := by norm_num [Work.BMF.VKF.dD]
      rw [hdD, div_le_iff₀ (by norm_num : (0 : ℝ) < (10 : ℝ) ^ 9)]
      nlinarith [sq_nonneg lam]
    linarith
  rw [le_div_iff₀ hden_pos]
  linarith [hAD, hnum]

end Work.BMF.VKF
