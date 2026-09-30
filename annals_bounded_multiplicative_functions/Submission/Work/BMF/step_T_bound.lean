import Mathlib
import Submission.Work.BMF.adi_descent
import Submission.Work.BMF.step_tval_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

open Polynomial Finset

/-- The coefficient `T_j` extracted at level `j = s.j` obeys the bound `CTc · N^{j+1}`
imposed at every level of the descent.

This is the content of `step_tval_bound` (`|T_j| ≤ 2π A (j+1) j^{j+1} C₀ N (x/L)^j`)
together with `A ≤ Alev k C₀ 0`, `x/L ≤ C₀ N` and `j ≤ k`. -/
theorem Tval_le_CTc (p : ADIPar) (s : DSt) (hp : ADIHyp p) (hs : DInv p s) (hj : 1 ≤ s.j) :
    |Tval p s| ≤ CTc p.k p.C₀ * p.N ^ (s.j + 1) := by
  have hstv := step_tval_bound p s hp hs hj
  obtain ⟨hjk, -, -, -, -, -, -, hAlev, -, -, -, -⟩ := hs
  obtain ⟨hC₀, -, hL2, hN100, -, hx, -, hxNL, -, -, -, -⟩ := hp
  have hC₀pos : 0 < p.C₀ := lt_of_lt_of_le zero_lt_one hC₀
  have hLpos : 0 < p.L := by linarith
  have hNpos : 0 < p.N := by
    have h1 : (1 : ℝ) ≤ p.C₀ ^ 4 := one_le_pow₀ hC₀
    nlinarith
  have hA0 : 0 ≤ Alev p.k p.C₀ 0 := Alev_nonneg p.k p.C₀ hC₀ (Nat.zero_le p.k)
  have hA : s.A ≤ Alev p.k p.C₀ 0 := le_trans hAlev (Alev_le_zero p.k p.C₀ hC₀ hjk)
  have hjR : (0 : ℝ) ≤ (s.j : ℝ) := Nat.cast_nonneg _
  have hjkR : (s.j : ℝ) ≤ (p.k : ℝ) := by exact_mod_cast hjk
  have hk1R : (1 : ℝ) ≤ (p.k : ℝ) := by
    have h : 1 ≤ p.k := le_trans hj hjk
    exact_mod_cast h
  have hxL0 : 0 ≤ p.x / p.L := div_nonneg hx.le hLpos.le
  have hNpow0 : (0 : ℝ) ≤ p.N ^ (s.j + 1) := pow_nonneg hNpos.le _
  have hpow0 : (0 : ℝ) ≤ (s.j : ℝ) ^ (s.j + 1) := pow_nonneg hjR _
  have hxLpow0 : (0 : ℝ) ≤ (p.x / p.L) ^ s.j := pow_nonneg hxL0 _
  -- the coefficient factor appearing in `step_tval_bound` is nonnegative
  have hcoef0 : 0 ≤ ((s.j : ℝ) + 1) * (s.j : ℝ) ^ (s.j + 1) * p.C₀ * p.N *
      (p.x / p.L) ^ s.j :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by linarith) hpow0) hC₀pos.le) hNpos.le)
      hxLpow0
  -- Step 1: replace the sup bound `s.A` by the level-`0` bound `Alev k C₀ 0`
  have hstep1 : |Tval p s| ≤
      2 * Real.pi * Alev p.k p.C₀ 0 * ((s.j : ℝ) + 1) * (s.j : ℝ) ^ (s.j + 1) * p.C₀ * p.N *
        (p.x / p.L) ^ s.j := by
    have h2π : (0 : ℝ) ≤ 2 * Real.pi := by positivity
    have h1 : 2 * Real.pi * s.A ≤ 2 * Real.pi * Alev p.k p.C₀ 0 :=
      mul_le_mul_of_nonneg_left hA h2π
    calc |Tval p s| ≤ 2 * Real.pi * s.A * ((s.j : ℝ) + 1) * (s.j : ℝ) ^ (s.j + 1) * p.C₀ *
          p.N * (p.x / p.L) ^ s.j := hstv
      _ = (2 * Real.pi * s.A) * (((s.j : ℝ) + 1) * (s.j : ℝ) ^ (s.j + 1) * p.C₀ * p.N *
            (p.x / p.L) ^ s.j) := by ring
      _ ≤ (2 * Real.pi * Alev p.k p.C₀ 0) * (((s.j : ℝ) + 1) * (s.j : ℝ) ^ (s.j + 1) * p.C₀ *
            p.N * (p.x / p.L) ^ s.j) := mul_le_mul_of_nonneg_right h1 hcoef0
      _ = 2 * Real.pi * Alev p.k p.C₀ 0 * ((s.j : ℝ) + 1) * (s.j : ℝ) ^ (s.j + 1) * p.C₀ * p.N *
            (p.x / p.L) ^ s.j := by ring
  -- Step 2: use `x / L ≤ C₀ * N`
  have hxLle : p.x / p.L ≤ p.C₀ * p.N := by
    rw [div_le_iff₀ hLpos]
    nlinarith [hxNL]
  have hpowL : (p.x / p.L) ^ s.j ≤ (p.C₀ * p.N) ^ s.j :=
    pow_le_pow_left₀ hxL0 hxLle s.j
  have hN2 : p.N * (p.C₀ * p.N) ^ s.j = p.C₀ ^ s.j * p.N ^ (s.j + 1) := by
    rw [mul_pow, pow_succ]
    ring
  have hstep2 : 2 * Real.pi * Alev p.k p.C₀ 0 * ((s.j : ℝ) + 1) * (s.j : ℝ) ^ (s.j + 1) * p.C₀ *
        p.N * (p.x / p.L) ^ s.j ≤
      2 * Real.pi * Alev p.k p.C₀ 0 * ((s.j : ℝ) + 1) * (s.j : ℝ) ^ (s.j + 1) *
        (p.C₀ * (p.C₀ ^ s.j * p.N ^ (s.j + 1))) := by
    have hM : 0 ≤ 2 * Real.pi * Alev p.k p.C₀ 0 * ((s.j : ℝ) + 1) * (s.j : ℝ) ^ (s.j + 1) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hA0) (by linarith)) hpow0
    have hinner : p.C₀ * (p.N * (p.x / p.L) ^ s.j) ≤ p.C₀ * (p.C₀ ^ s.j * p.N ^ (s.j + 1)) := by
      have h1 : p.N * (p.x / p.L) ^ s.j ≤ p.N * (p.C₀ * p.N) ^ s.j :=
        mul_le_mul_of_nonneg_left hpowL hNpos.le
      have h2 : p.C₀ * (p.N * (p.x / p.L) ^ s.j) ≤ p.C₀ * (p.N * (p.C₀ * p.N) ^ s.j) :=
        mul_le_mul_of_nonneg_left h1 hC₀pos.le
      rw [hN2] at h2
      exact h2
    calc 2 * Real.pi * Alev p.k p.C₀ 0 * ((s.j : ℝ) + 1) * (s.j : ℝ) ^ (s.j + 1) * p.C₀ * p.N *
          (p.x / p.L) ^ s.j
        = (2 * Real.pi * Alev p.k p.C₀ 0 * ((s.j : ℝ) + 1) * (s.j : ℝ) ^ (s.j + 1)) *
            (p.C₀ * (p.N * (p.x / p.L) ^ s.j)) := by ring
      _ ≤ (2 * Real.pi * Alev p.k p.C₀ 0 * ((s.j : ℝ) + 1) * (s.j : ℝ) ^ (s.j + 1)) *
            (p.C₀ * (p.C₀ ^ s.j * p.N ^ (s.j + 1))) := mul_le_mul_of_nonneg_left hinner hM
  -- Step 3: compare the level-`s.j` factor with the level-`p.k` factor
  have hpowj : (s.j : ℝ) ^ (s.j + 1) ≤ (p.k : ℝ) ^ (p.k + 1) :=
    le_trans (pow_le_pow_left₀ hjR hjkR (s.j + 1))
      (pow_le_pow_right₀ hk1R (by omega : s.j + 1 ≤ p.k + 1))
  have hC0j : p.C₀ ^ s.j ≤ p.C₀ ^ p.k := pow_le_pow_right₀ hC₀ hjk
  have hKK : ((s.j : ℝ) + 1) * (s.j : ℝ) ^ (s.j + 1) * (p.C₀ * p.C₀ ^ s.j) ≤
      ((p.k : ℝ) + 1) * (p.k : ℝ) ^ (p.k + 1) * (p.C₀ * p.C₀ ^ p.k) := by
    have h1 : ((s.j : ℝ) + 1) * (s.j : ℝ) ^ (s.j + 1) ≤
        ((p.k : ℝ) + 1) * (p.k : ℝ) ^ (p.k + 1) :=
      mul_le_mul (by linarith) hpowj hpow0 (by linarith)
    have h2 : p.C₀ * p.C₀ ^ s.j ≤ p.C₀ * p.C₀ ^ p.k :=
      mul_le_mul_of_nonneg_left hC0j hC₀pos.le
    exact mul_le_mul h1 h2 (mul_nonneg hC₀pos.le (pow_nonneg hC₀pos.le _)) (by positivity)
  have hAll : (((s.j : ℝ) + 1) * (s.j : ℝ) ^ (s.j + 1) * (p.C₀ * p.C₀ ^ s.j)) * p.N ^ (s.j + 1) ≤
      (((p.k : ℝ) + 1) * (p.k : ℝ) ^ (p.k + 1) * (p.C₀ * p.C₀ ^ p.k)) * p.N ^ (s.j + 1) :=
    mul_le_mul_of_nonneg_right hKK hNpow0
  have hstep3 : 2 * Real.pi * Alev p.k p.C₀ 0 * ((s.j : ℝ) + 1) * (s.j : ℝ) ^ (s.j + 1) *
        (p.C₀ * (p.C₀ ^ s.j * p.N ^ (s.j + 1))) ≤
      2 * Real.pi * Alev p.k p.C₀ 0 * ((p.k : ℝ) + 1) * (p.k : ℝ) ^ (p.k + 1) *
        (p.C₀ * p.C₀ ^ p.k) * p.N ^ (s.j + 1) := by
    have h2πA : 0 ≤ 2 * Real.pi * Alev p.k p.C₀ 0 := mul_nonneg (by positivity) hA0
    calc 2 * Real.pi * Alev p.k p.C₀ 0 * ((s.j : ℝ) + 1) * (s.j : ℝ) ^ (s.j + 1) *
          (p.C₀ * (p.C₀ ^ s.j * p.N ^ (s.j + 1)))
        = (2 * Real.pi * Alev p.k p.C₀ 0) *
            ((((s.j : ℝ) + 1) * (s.j : ℝ) ^ (s.j + 1) * (p.C₀ * p.C₀ ^ s.j)) * p.N ^ (s.j + 1)) := by
          ring
      _ ≤ (2 * Real.pi * Alev p.k p.C₀ 0) *
            ((((p.k : ℝ) + 1) * (p.k : ℝ) ^ (p.k + 1) * (p.C₀ * p.C₀ ^ p.k)) * p.N ^ (s.j + 1)) :=
          mul_le_mul_of_nonneg_left hAll h2πA
      _ = 2 * Real.pi * Alev p.k p.C₀ 0 * ((p.k : ℝ) + 1) * (p.k : ℝ) ^ (p.k + 1) *
            (p.C₀ * p.C₀ ^ p.k) * p.N ^ (s.j + 1) := by ring
  have hCTc : 2 * Real.pi * Alev p.k p.C₀ 0 * ((p.k : ℝ) + 1) * (p.k : ℝ) ^ (p.k + 1) *
        (p.C₀ * p.C₀ ^ p.k) * p.N ^ (s.j + 1) = CTc p.k p.C₀ * p.N ^ (s.j + 1) := by
    unfold CTc CT1
    rw [pow_succ (p.k : ℝ) p.k]
    ring
  exact hstep1.trans (hstep2.trans (hstep3.trans (le_of_eq hCTc)))

theorem step_T_bound (p : ADIPar) (s : DSt) (hp : ADIHyp p) (hs : DInv p s) (hj : 1 ≤ s.j) :
    ∀ m ∈ Finset.Icc s.j p.k, |(dstep p s).T m| ≤ CTc p.k p.C₀ * p.N ^ (m + 1) := by
  intro m hm
  rw [Finset.mem_Icc] at hm
  obtain ⟨hmj, hmk⟩ := hm
  have hTv := Tval_le_CTc p s hp hs hj
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hTbd, -⟩ := hs
  rw [dstep_T]
  by_cases h : m = s.j
  · subst h
    rw [Function.update_self]
    exact hTv
  · rw [Function.update_of_ne h]
    exact hTbd m (Finset.mem_Icc.mpr ⟨by omega, hmk⟩)

end Work.BMF
