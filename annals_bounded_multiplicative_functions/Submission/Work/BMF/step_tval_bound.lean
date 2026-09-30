import Mathlib
import Submission.Work.BMF.adi_descent
import Submission.Work.BMF.adi_basic
import Submission.Work.BMF.top_coeff_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

open Polynomial Finset
theorem step_tval_bound (p : ADIPar) (s : DSt) (hp : ADIHyp p) (hs : DInv p s) (hj : 1 ≤ s.j) :
    |Tval p s| ≤ 2 * Real.pi * s.A * ((s.j : ℝ) + 1) * (s.j : ℝ) ^ (s.j + 1) *
      p.C₀ * p.N * (p.x / p.L) ^ s.j := by
  obtain ⟨hjk, hPdeg, hEdeg, hGdeg, hrel, hEbd, hA0, hAlev, hInt, hP0eq, hTbd, hmu⟩ := hs
  obtain ⟨hC₀, hP0deg, hL2, hN, hQm, hx, hNL, hxNL, hb1, hba, hcomp, hcomp2⟩ := hp
  have hL0 : 0 < p.L := by linarith
  have ha0 : 0 < (p.a : ℝ) := by
    have : 0 < p.a := by omega
    exact_mod_cast this
  have hj0 : 0 < s.j := by omega
  have hQpos : 0 < ((qj p.a p.b s.j : ℕ) : ℝ) := by
    exact_mod_cast qj_pos p.a p.b s.j hba hj0
  have hQne : ((qj p.a p.b s.j : ℕ) : ℝ) ≠ 0 := ne_of_gt hQpos
  have hane : (p.a : ℝ) ≠ 0 := ne_of_gt ha0
  have hLne : p.L ≠ 0 := ne_of_gt hL0
  have hjne : (s.j : ℝ) ≠ 0 := by
    exact_mod_cast (by omega : s.j ≠ 0)
  -- Absolute-value normal form of `Tval`.
  have hAbsEq : |Tval p s| =
      2 * Real.pi * (s.j : ℝ) * p.x ^ (s.j) * |s.E.coeff s.j| /
        ((qj p.a p.b s.j : ℕ) : ℝ) := by
    rw [Tval, abs_mul, abs_mul, abs_mul, abs_mul]
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi),
      abs_of_nonneg (Nat.cast_nonneg s.j),
      abs_pow, abs_neg, abs_one, one_pow,
      abs_of_nonneg (pow_nonneg (le_of_lt hx) _),
      abs_div, abs_of_pos hQpos]
    ring
  -- The bounded-interval hypothesis needed by `top_coeff_bound`.
  have hbd : ∀ t ∈ Set.Icc (p.x / (p.a : ℝ)) (p.x / (p.a : ℝ) + p.L / (p.a : ℝ)),
      |s.E.eval t| ≤ s.A := by
    intro t ht
    refine hEbd t ?_
    obtain ⟨h1, h2⟩ := ht
    refine ⟨h1, ?_⟩
    have : (p.x + p.L) / (p.a : ℝ) = p.x / (p.a : ℝ) + p.L / (p.a : ℝ) := by ring
    rw [this]; exact h2
  have hlam : 0 < p.L / (p.a : ℝ) := div_pos hL0 ha0
  have htc := top_coeff_bound (j := s.j) (e := s.E) hEdeg (A := s.A)
      (t0 := p.x / (p.a : ℝ)) (lam := p.L / (p.a : ℝ)) hlam hA0 hbd
  -- Reduction of the `a^j / q_j` factor.
  have hAj : (p.a : ℝ) ^ (s.j) / ((qj p.a p.b s.j : ℕ) : ℝ) ≤ p.C₀ * p.N := by
    have hC0pos : (0 : ℝ) < p.C₀ := by linarith
    have hN0 : (0 : ℝ) < p.N := by
      have : (1 : ℝ) ≤ p.C₀ ^ 4 := one_le_pow₀ hC₀
      nlinarith
    have hCN : 0 < p.C₀ * p.N := mul_pos hC0pos hN0
    have hlow := qj_lower p.a p.b s.j (by omega) hC₀ hN hcomp hba
    rw [div_le_iff₀ hQpos]
    rw [div_le_iff₀ hCN] at hlow
    nlinarith
  calc |Tval p s|
      = 2 * Real.pi * (s.j : ℝ) * p.x ^ (s.j) * |s.E.coeff s.j| /
          ((qj p.a p.b s.j : ℕ) : ℝ) := hAbsEq
    _ ≤ 2 * Real.pi * (s.j : ℝ) * p.x ^ (s.j) *
          (s.A * ((s.j : ℝ) + 1) * (s.j : ℝ) ^ (s.j) / (p.L / (p.a : ℝ)) ^ (s.j)) /
          ((qj p.a p.b s.j : ℕ) : ℝ) := by
        apply div_le_div_of_nonneg_right _ hQpos.le
        apply mul_le_mul_of_nonneg_left htc
        positivity
    _ = 2 * Real.pi * s.A * ((s.j : ℝ) + 1) * (s.j : ℝ) ^ (s.j + 1) * (p.x / p.L) ^ (s.j) *
          ((p.a : ℝ) ^ (s.j) / ((qj p.a p.b s.j : ℕ) : ℝ)) := by
        rw [div_pow, div_pow, pow_succ]
        field_simp
    _ ≤ 2 * Real.pi * s.A * ((s.j : ℝ) + 1) * (s.j : ℝ) ^ (s.j + 1) * (p.x / p.L) ^ (s.j) *
          (p.C₀ * p.N) := by
        apply mul_le_mul_of_nonneg_left hAj
        positivity
    _ = 2 * Real.pi * s.A * ((s.j : ℝ) + 1) * (s.j : ℝ) ^ (s.j + 1) * p.C₀ * p.N *
          (p.x / p.L) ^ (s.j) := by ring

end Work.BMF
