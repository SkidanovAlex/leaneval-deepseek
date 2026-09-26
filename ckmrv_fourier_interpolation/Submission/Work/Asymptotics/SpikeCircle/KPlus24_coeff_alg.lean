import Mathlib
import Submission.Work.Residues.KPlusAux

noncomputable section

namespace Work.Asymptotics.SpikeCircle

open Work.Residues.KPlusAux

set_option maxHeartbeats 8000000

/-- The four `d = 24` coefficient combinations `N0f, N2f, M0f, M2f` are each `O(m)` when the
modular-form values are `m`-close to `1` and `h` is bounded by `Hh`.

This is purely algebraic: each expression is rewritten as a combination of the `O(m)`
quantities `Qf = e₄³ - e₆²`, `Uf = e₂e₆ - e₄²`, the cancelling combination
`e₄·Pf + Qf = O(m²)`, and an explicit `h`-coefficient, and the elementary bounds
`‖Qf‖ ≤ 10 m`, `‖Uf‖ ≤ 6 m`, `‖e₄ Pf + Qf‖ ≤ 60 m²` are applied. -/
theorem KPlus24_coeff_alg {e2 e4 e6 h : ℂ} {m Hh : ℝ} (hm : 0 ≤ m) (hm1 : m ≤ 1)
    (h2 : ‖e2 - 1‖ ≤ m) (h4 : ‖e4 - 1‖ ≤ m) (h6 : ‖e6 - 1‖ ≤ m)
    (hh : ‖h‖ ≤ Hh) (hHh : 0 ≤ Hh) :
    ‖Work.Residues.KPlusAux.N0f e2 e4 e6 h‖ ≤ (600 + 400 * Hh) * m ∧
    ‖Work.Residues.KPlusAux.N2f e2 e4 e6 h‖ ≤ (600 + 400 * Hh) * m ∧
    ‖Work.Residues.KPlusAux.M0f e2 e4 e6 h‖ ≤ (600 + 400 * Hh) * m ∧
    ‖Work.Residues.KPlusAux.M2f e2 e4 e6 h‖ ≤ (600 + 400 * Hh) * m := by
  have hKe : m * 1 ≤ 1 := by simpa using hm1
  have hm2 : m ^ 2 ≤ m := by nlinarith [hm, hm1]
  have h2' : ‖e2 - 1‖ ≤ m * 1 := by simpa using h2
  have h4' : ‖e4 - 1‖ ≤ m * 1 := by simpa using h4
  have h6' : ‖e6 - 1‖ ≤ m * 1 := by simpa using h6
  -- basic bounds coming from the library
  have hQf : ‖Qf e4 e6‖ ≤ 10 * m := by
    have h := norm_Qf_le (K := m) (e := 1) hKe h4' h6'
    simpa using h
  have hUf : ‖Uf e2 e4 e6‖ ≤ 6 * m := by
    have h := norm_Uf_le (K := m) (e := 1) hKe h2' h4' h6'
    simpa using h
  have hPfQ : ‖e4 * Pf e2 e4 e6 + Qf e4 e6‖ ≤ 60 * m ^ 2 := by
    have h := norm_e4Pf_plus_Qf_le (K := m) (e := 1) hKe h2' h4' h6'
    simpa using h
  -- norm control of the elementary factors
  have he2 : ‖e2‖ ≤ 2 := norm_le_two h2 hm1
  have he4 : ‖e4‖ ≤ 2 := norm_le_two h4 hm1
  have he6 : ‖e6‖ ≤ 2 := norm_le_two h6 hm1
  have hS2 : ‖e2 ^ 2 * e4 * e6‖ ≤ 16 := by
    simp only [norm_mul, norm_pow]
    have h1 : ‖e2‖ ^ 2 ≤ 4 := by nlinarith [norm_nonneg e2, he2]
    have ha : ‖e2‖ ^ 2 * ‖e4‖ ≤ 4 * 2 := mul_le_mul h1 he4 (norm_nonneg e4) (by norm_num)
    have hb : ‖e2‖ ^ 2 * ‖e4‖ * ‖e6‖ ≤ 4 * 2 * 2 :=
      mul_le_mul ha he6 (norm_nonneg e6) (by norm_num)
    linarith [hb]
  have hS4 : ‖e4 ^ 2 * e6‖ ≤ 8 := by
    simp only [norm_mul, norm_pow]
    have h1 : ‖e4‖ ^ 2 ≤ 4 := by nlinarith [norm_nonneg e4, he4]
    have ha : ‖e4‖ ^ 2 * ‖e6‖ ≤ 4 * 2 := mul_le_mul h1 he6 (norm_nonneg e6) (by norm_num)
    linarith [ha]
  have hS24 : ‖2 * e2 * e4 * e6‖ ≤ 16 := by
    simp only [norm_mul, Complex.norm_ofNat]
    have ha : 2 * ‖e2‖ ≤ 2 * 2 := mul_le_mul_of_nonneg_left he2 (by norm_num)
    have hb : 2 * ‖e2‖ * ‖e4‖ ≤ 2 * 2 * 2 := mul_le_mul ha he4 (norm_nonneg e4) (by norm_num)
    have hc : 2 * ‖e2‖ * ‖e4‖ * ‖e6‖ ≤ 2 * 2 * 2 * 2 :=
      mul_le_mul hb he6 (norm_nonneg e6) (by norm_num)
    linarith [hc]
  have hu5 : ‖(5 : ℂ) * e2 - 6‖ ≤ 6 := by
    have h1 : (5 : ℂ) * e2 - 6 = (5 : ℂ) * (e2 - 1) + (-1) := by ring
    rw [h1]
    have h2' : ‖(5 : ℂ) * (e2 - 1)‖ ≤ 5 * m := by
      rw [norm_mul, Complex.norm_ofNat]
      exact mul_le_mul_of_nonneg_left h2 (by norm_num)
    calc ‖(5 : ℂ) * (e2 - 1) + (-1 : ℂ)‖ ≤ ‖(5 : ℂ) * (e2 - 1)‖ + ‖(-1 : ℂ)‖ :=
          norm_add_le _ _
      _ ≤ 5 * m + 1 := by rw [norm_neg, norm_one]; linarith
      _ ≤ 6 := by linarith
  have hu67 : ‖(6 : ℂ) - 7 * e2‖ ≤ 8 := by
    have h1 : (6 : ℂ) - 7 * e2 = (-1 : ℂ) + -(7 * (e2 - 1)) := by ring
    rw [h1]
    have h2'' : ‖(7 : ℂ) * (e2 - 1)‖ ≤ 7 * m := by
      rw [norm_mul, Complex.norm_ofNat]
      exact mul_le_mul_of_nonneg_left h2 (by norm_num)
    have h2n : ‖-(7 * (e2 - 1))‖ ≤ 7 * m := by rw [norm_neg]; exact h2''
    calc ‖(-1 : ℂ) + -(7 * (e2 - 1))‖ ≤ ‖(-1 : ℂ)‖ + ‖-(7 * (e2 - 1))‖ := norm_add_le _ _
      _ ≤ 1 + 7 * m := by rw [norm_neg, norm_one]; linarith
      _ ≤ 8 := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- N0f
    have hid : N0f e2 e4 e6 h
        = 6 * (e4 * Pf e2 e4 e6 + Qf e4 e6) + (5 * e2 - 6) * Qf e4 e6
          + (e2 ^ 2 * e4 * e6 * Qf e4 e6) * h := by
      simp only [N0f, Pf, Qf]; ring
    rw [hid]
    have hX : ‖(6 : ℂ) * (e4 * Pf e2 e4 e6 + Qf e4 e6)‖ ≤ 6 * (60 * m ^ 2) := by
      rw [norm_mul, Complex.norm_ofNat]
      exact mul_le_mul_of_nonneg_left hPfQ (by norm_num)
    have hY : ‖(5 * e2 - 6) * Qf e4 e6‖ ≤ 6 * (10 * m) :=
      norm_mul_le_mul hu5 hQf (by norm_num)
    have hQfac : ‖e2 ^ 2 * e4 * e6 * Qf e4 e6‖ ≤ 16 * (10 * m) :=
      norm_mul_le_mul hS2 hQf (by norm_num)
    have hZ : ‖(e2 ^ 2 * e4 * e6 * Qf e4 e6) * h‖ ≤ (16 * (10 * m)) * Hh :=
      norm_mul_le_mul hQfac hh (by positivity)
    have t := norm_add_le
      ((6 : ℂ) * (e4 * Pf e2 e4 e6 + Qf e4 e6) + (5 * e2 - 6) * Qf e4 e6)
      ((e2 ^ 2 * e4 * e6 * Qf e4 e6) * h)
    have t' := norm_add_le ((6 : ℂ) * (e4 * Pf e2 e4 e6 + Qf e4 e6))
      ((5 * e2 - 6) * Qf e4 e6)
    nlinarith [t, t', hX, hY, hZ, hm, hm2, hHh]
  · -- N2f
    have hid : N2f e2 e4 e6 h
        = -(6 * (e4 * Pf e2 e4 e6 + Qf e4 e6)) + (6 - 7 * e2) * Qf e4 e6
          + (e4 ^ 2 * e6 * Qf e4 e6) * h := by
      simp only [N2f, Pf, Qf]; ring
    rw [hid]
    have hX : ‖(6 : ℂ) * (e4 * Pf e2 e4 e6 + Qf e4 e6)‖ ≤ 6 * (60 * m ^ 2) := by
      rw [norm_mul, Complex.norm_ofNat]
      exact mul_le_mul_of_nonneg_left hPfQ (by norm_num)
    have hXn : ‖-(6 * (e4 * Pf e2 e4 e6 + Qf e4 e6))‖ ≤ 6 * (60 * m ^ 2) := by
      rw [norm_neg]; exact hX
    have hY : ‖(6 - 7 * e2) * Qf e4 e6‖ ≤ 8 * (10 * m) :=
      norm_mul_le_mul hu67 hQf (by norm_num)
    have hQfac : ‖e4 ^ 2 * e6 * Qf e4 e6‖ ≤ 8 * (10 * m) :=
      norm_mul_le_mul hS4 hQf (by norm_num)
    have hZ : ‖(e4 ^ 2 * e6 * Qf e4 e6) * h‖ ≤ (8 * (10 * m)) * Hh :=
      norm_mul_le_mul hQfac hh (by positivity)
    have t := norm_add_le
      (-(6 * (e4 * Pf e2 e4 e6 + Qf e4 e6)) + (6 - 7 * e2) * Qf e4 e6)
      ((e4 ^ 2 * e6 * Qf e4 e6) * h)
    have t' := norm_add_le (-(6 * (e4 * Pf e2 e4 e6 + Qf e4 e6)))
      ((6 - 7 * e2) * Qf e4 e6)
    nlinarith [t, t', hXn, hY, hZ, hm, hm2, hHh]
  · -- M0f
    have hid : M0f e2 e4 e6 h
        = 12 * (e4 * Uf e2 e4 e6) + 5 * Qf e4 e6
          + (2 * e2 * e4 * e6 * Qf e4 e6) * h := by
      simp only [M0f, Uf, Qf]; ring
    rw [hid]
    have hUfac : ‖e4 * Uf e2 e4 e6‖ ≤ 2 * (6 * m) :=
      norm_mul_le_mul he4 hUf (by norm_num)
    have hX : ‖(12 : ℂ) * (e4 * Uf e2 e4 e6)‖ ≤ 12 * (2 * (6 * m)) := by
      rw [norm_mul, Complex.norm_ofNat]
      exact mul_le_mul_of_nonneg_left hUfac (by norm_num)
    have hY : ‖(5 : ℂ) * Qf e4 e6‖ ≤ 5 * (10 * m) := by
      rw [norm_mul, Complex.norm_ofNat]
      exact mul_le_mul_of_nonneg_left hQf (by norm_num)
    have hQfac : ‖2 * e2 * e4 * e6 * Qf e4 e6‖ ≤ 16 * (10 * m) :=
      norm_mul_le_mul hS24 hQf (by norm_num)
    have hZ : ‖(2 * e2 * e4 * e6 * Qf e4 e6) * h‖ ≤ (16 * (10 * m)) * Hh :=
      norm_mul_le_mul hQfac hh (by positivity)
    have t := norm_add_le
      ((12 : ℂ) * (e4 * Uf e2 e4 e6) + (5 : ℂ) * Qf e4 e6)
      ((2 * e2 * e4 * e6 * Qf e4 e6) * h)
    have t' := norm_add_le ((12 : ℂ) * (e4 * Uf e2 e4 e6)) ((5 : ℂ) * Qf e4 e6)
    nlinarith [t, t', hX, hY, hZ, hm, hHh]
  · -- M2f
    have hid : M2f e2 e4 e6 h
        = -((12 : ℂ) * (e4 * Uf e2 e4 e6)) + (-((7 : ℂ) * Qf e4 e6)) := by
      simp only [M2f, Uf, Qf]; ring
    rw [hid]
    have hUfac : ‖e4 * Uf e2 e4 e6‖ ≤ 2 * (6 * m) :=
      norm_mul_le_mul he4 hUf (by norm_num)
    have hX : ‖(12 : ℂ) * (e4 * Uf e2 e4 e6)‖ ≤ 12 * (2 * (6 * m)) := by
      rw [norm_mul, Complex.norm_ofNat]
      exact mul_le_mul_of_nonneg_left hUfac (by norm_num)
    have hXn : ‖-((12 : ℂ) * (e4 * Uf e2 e4 e6))‖ ≤ 12 * (2 * (6 * m)) := by
      rw [norm_neg]; exact hX
    have hY : ‖(7 : ℂ) * Qf e4 e6‖ ≤ 7 * (10 * m) := by
      rw [norm_mul, Complex.norm_ofNat]
      exact mul_le_mul_of_nonneg_left hQf (by norm_num)
    have hYn : ‖-((7 : ℂ) * Qf e4 e6)‖ ≤ 7 * (10 * m) := by
      rw [norm_neg]; exact hY
    have t := norm_add_le (-((12 : ℂ) * (e4 * Uf e2 e4 e6))) (-((7 : ℂ) * Qf e4 e6))
    nlinarith [t, hXn, hYn, hm, hHh]

end Work.Asymptotics.SpikeCircle
