import Mathlib
import Submission.Work.BMF.adi_descent
import Submission.Work.BMF.top_coeff_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The bound `|T_j| ≤ CTc k C₀ · N^{j+1}` for the coefficient extracted by the ADI descent

At each level `s.j` of the one-sided ADI descent (`Submission.Work.BMF.adi_descent`), the
coefficient `Tval p s = 2π j (-1)^{j-1} x^j · (coeff_j E)/q_j` peeled off the polynomial is
bounded by the constant `CTc p.k p.C₀` times `N^{j+1}`.

The proof combines:
* the sup-norm bound `|E| ≤ s.A` on the interval `[x/a, (x+L)/a]` (from `DInv`) with the
  Lagrange-interpolation top-coefficient estimate `top_coeff_bound`, giving
  `|coeff_j E| ≤ s.A (j+1) j^j (a/L)^j`;
* the comparability `a^j / q_j ≤ C₀ N` derived from the proved `qj_lower`;
* `x/L ≤ C₀ N` from `ADIHyp`, and `s.A ≤ Alev k C₀ 0`;
* elementary power comparisons `j^{j+1} ≤ k^{k+1}`, `C₀^{j+1} ≤ C₀^{k+1}` for `j ≤ k`, `C₀ ≥ 1`.
-/

namespace Work.BMF

open Polynomial Finset

theorem abs_Tval_le (p : ADIPar) (s : DSt) (hp : ADIHyp p) (hs : DInv p s) (hj : 1 ≤ s.j) :
    |Tval p s| ≤ CTc p.k p.C₀ * p.N ^ (s.j + 1) := by
  obtain ⟨hjk, -, hEdeg, -, -, hEbd, hA0, hAlev, -, -, -, -⟩ := hs
  obtain ⟨hC₀, -, hL2, hN100, -, hx, -, hxNL, -, hba, hcomp, -⟩ := hp
  have hL0 : 0 < p.L := by linarith
  have ha0 : 0 < (p.a : ℝ) := by
    have : 0 < p.a := by omega
    exact_mod_cast this
  have hj0 : 0 < s.j := by omega
  have hQpos : 0 < ((qj p.a p.b s.j : ℕ) : ℝ) := by
    exact_mod_cast qj_pos p.a p.b s.j hba hj0
  have hC₀pos : 0 < p.C₀ := lt_of_lt_of_le zero_lt_one hC₀
  have hNpos : 0 < p.N := by
    have : (1 : ℝ) ≤ p.C₀ ^ 4 := one_le_pow₀ hC₀
    nlinarith
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
    have hCN : 0 < p.C₀ * p.N := mul_pos hC₀pos hNpos
    have hlow := qj_lower p.a p.b s.j (by omega) hC₀ hN100 hcomp hba
    rw [div_le_iff₀ hQpos]
    rw [div_le_iff₀ hCN] at hlow
    nlinarith
  -- The intermediate bound with the `(x/L)^j` factor.
  have hstv : |Tval p s| ≤
      2 * Real.pi * s.A * ((s.j : ℝ) + 1) * (s.j : ℝ) ^ (s.j + 1) * (p.x / p.L) ^ s.j *
        (p.C₀ * p.N) := by
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
  have hA0lev : 0 ≤ Alev p.k p.C₀ 0 := Alev_nonneg p.k p.C₀ hC₀ (Nat.zero_le p.k)
  have hA : s.A ≤ Alev p.k p.C₀ 0 := le_trans hAlev (Alev_le_zero p.k p.C₀ hC₀ hjk)
  have hjR : (0 : ℝ) ≤ (s.j : ℝ) := Nat.cast_nonneg _
  have hjkR : (s.j : ℝ) ≤ (p.k : ℝ) := by exact_mod_cast hjk
  have hk1R : (1 : ℝ) ≤ (p.k : ℝ) := by
    have : 1 ≤ p.k := le_trans hj hjk
    exact_mod_cast this
  have hxL0 : 0 ≤ p.x / p.L := div_nonneg hx.le hL0.le
  have hxLle : p.x / p.L ≤ p.C₀ * p.N := by
    rw [div_le_iff₀ hL0]
    nlinarith [hxNL]
  -- Step 1: replace `s.A` by the level-`0` bound `Alev k C₀ 0`.
  have hstep1 : |Tval p s| ≤ 2 * Real.pi * Alev p.k p.C₀ 0 * ((s.j : ℝ) + 1) *
        (s.j : ℝ) ^ (s.j + 1) * (p.x / p.L) ^ s.j * (p.C₀ * p.N) := by
    refine le_trans hstv ?_
    have hcoef0 : (0 : ℝ) ≤ ((s.j : ℝ) + 1) * (s.j : ℝ) ^ (s.j + 1) * (p.x / p.L) ^ s.j *
        (p.C₀ * p.N) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by linarith) (pow_nonneg hjR _))
        (pow_nonneg hxL0 _)) (mul_nonneg hC₀pos.le hNpos.le)
    calc 2 * Real.pi * s.A * ((s.j : ℝ) + 1) * (s.j : ℝ) ^ (s.j + 1) * (p.x / p.L) ^ s.j *
          (p.C₀ * p.N)
        = (2 * Real.pi * s.A) * (((s.j : ℝ) + 1) * (s.j : ℝ) ^ (s.j + 1) * (p.x / p.L) ^ s.j *
            (p.C₀ * p.N)) := by ring
      _ ≤ (2 * Real.pi * Alev p.k p.C₀ 0) * (((s.j : ℝ) + 1) * (s.j : ℝ) ^ (s.j + 1) *
            (p.x / p.L) ^ s.j * (p.C₀ * p.N)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hA (by positivity)) hcoef0
      _ = 2 * Real.pi * Alev p.k p.C₀ 0 * ((s.j : ℝ) + 1) * (s.j : ℝ) ^ (s.j + 1) *
            (p.x / p.L) ^ s.j * (p.C₀ * p.N) := by ring
  -- Step 2: `(x/L)^j · (C₀ N) ≤ C₀^{j+1} N^{j+1}`.
  have hstep2 : 2 * Real.pi * Alev p.k p.C₀ 0 * ((s.j : ℝ) + 1) * (s.j : ℝ) ^ (s.j + 1) *
        (p.x / p.L) ^ s.j * (p.C₀ * p.N) ≤ 2 * Real.pi * Alev p.k p.C₀ 0 *
        ((s.j : ℝ) + 1) * (s.j : ℝ) ^ (s.j + 1) * (p.C₀ ^ (s.j + 1) * p.N ^ (s.j + 1)) := by
    have hpL : (p.x / p.L) ^ s.j ≤ (p.C₀ * p.N) ^ s.j := pow_le_pow_left₀ hxL0 hxLle s.j
    have hinner : (p.x / p.L) ^ s.j * (p.C₀ * p.N) ≤ p.C₀ ^ (s.j + 1) * p.N ^ (s.j + 1) := by
      calc (p.x / p.L) ^ s.j * (p.C₀ * p.N) ≤ (p.C₀ * p.N) ^ s.j * (p.C₀ * p.N) :=
            mul_le_mul_of_nonneg_right hpL (mul_nonneg hC₀pos.le hNpos.le)
        _ = (p.C₀ * p.N) ^ (s.j + 1) := (pow_succ (p.C₀ * p.N) s.j).symm
        _ = p.C₀ ^ (s.j + 1) * p.N ^ (s.j + 1) := by rw [mul_pow]
    have hM2 : (0 : ℝ) ≤ 2 * Real.pi * Alev p.k p.C₀ 0 * ((s.j : ℝ) + 1) *
        (s.j : ℝ) ^ (s.j + 1) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hA0lev) (by linarith)) (pow_nonneg hjR _)
    calc 2 * Real.pi * Alev p.k p.C₀ 0 * ((s.j : ℝ) + 1) * (s.j : ℝ) ^ (s.j + 1) *
          (p.x / p.L) ^ s.j * (p.C₀ * p.N)
        = (2 * Real.pi * Alev p.k p.C₀ 0 * ((s.j : ℝ) + 1) * (s.j : ℝ) ^ (s.j + 1)) *
            ((p.x / p.L) ^ s.j * (p.C₀ * p.N)) := by ring
      _ ≤ (2 * Real.pi * Alev p.k p.C₀ 0 * ((s.j : ℝ) + 1) * (s.j : ℝ) ^ (s.j + 1)) *
            (p.C₀ ^ (s.j + 1) * p.N ^ (s.j + 1)) := mul_le_mul_of_nonneg_left hinner hM2
      _ = 2 * Real.pi * Alev p.k p.C₀ 0 * ((s.j : ℝ) + 1) * (s.j : ℝ) ^ (s.j + 1) *
            (p.C₀ ^ (s.j + 1) * p.N ^ (s.j + 1)) := by ring
  -- Step 3: compare the level-`s.j` factor with the level-`p.k` factor.
  have hpowj : (s.j : ℝ) ^ (s.j + 1) ≤ (p.k : ℝ) ^ (p.k + 1) :=
    le_trans (pow_le_pow_left₀ hjR hjkR (s.j + 1)) (pow_le_pow_right₀ hk1R (by omega))
  have hpowC : p.C₀ ^ (s.j + 1) ≤ p.C₀ ^ (p.k + 1) := pow_le_pow_right₀ hC₀ (by omega)
  have hK : ((s.j : ℝ) + 1) * (s.j : ℝ) ^ (s.j + 1) * p.C₀ ^ (s.j + 1) ≤
      ((p.k : ℝ) + 1) * (p.k : ℝ) ^ (p.k + 1) * p.C₀ ^ (p.k + 1) := by
    have h1 : ((s.j : ℝ) + 1) * (s.j : ℝ) ^ (s.j + 1) ≤
        ((p.k : ℝ) + 1) * (p.k : ℝ) ^ (p.k + 1) :=
      mul_le_mul (by linarith) hpowj (pow_nonneg hjR _) (by linarith)
    calc ((s.j : ℝ) + 1) * (s.j : ℝ) ^ (s.j + 1) * p.C₀ ^ (s.j + 1)
        ≤ ((p.k : ℝ) + 1) * (p.k : ℝ) ^ (p.k + 1) * p.C₀ ^ (s.j + 1) :=
          mul_le_mul_of_nonneg_right h1 (pow_nonneg hC₀pos.le _)
      _ ≤ ((p.k : ℝ) + 1) * (p.k : ℝ) ^ (p.k + 1) * p.C₀ ^ (p.k + 1) :=
          mul_le_mul_of_nonneg_left hpowC (mul_nonneg (by linarith) (pow_nonneg (Nat.cast_nonneg p.k) _))
  -- Step 4: assemble and identify `CTc`.
  have hFin : |Tval p s| ≤ 2 * Real.pi * Alev p.k p.C₀ 0 * ((p.k : ℝ) + 1) *
        (p.k : ℝ) ^ (p.k + 1) * p.C₀ ^ (p.k + 1) * p.N ^ (s.j + 1) := by
    have hNpow : (0 : ℝ) ≤ p.N ^ (s.j + 1) := pow_nonneg hNpos.le _
    calc |Tval p s| ≤ 2 * Real.pi * Alev p.k p.C₀ 0 * ((s.j : ℝ) + 1) * (s.j : ℝ) ^ (s.j + 1) *
          (p.C₀ ^ (s.j + 1) * p.N ^ (s.j + 1)) := hstep1.trans hstep2
      _ = (2 * Real.pi * Alev p.k p.C₀ 0) *
            (((s.j : ℝ) + 1) * (s.j : ℝ) ^ (s.j + 1) * p.C₀ ^ (s.j + 1)) * p.N ^ (s.j + 1) := by
          ring
      _ ≤ (2 * Real.pi * Alev p.k p.C₀ 0) *
            (((p.k : ℝ) + 1) * (p.k : ℝ) ^ (p.k + 1) * p.C₀ ^ (p.k + 1)) * p.N ^ (s.j + 1) := by
          apply mul_le_mul_of_nonneg_right _ hNpow
          exact mul_le_mul_of_nonneg_left hK (mul_nonneg (by positivity) hA0lev)
      _ = 2 * Real.pi * Alev p.k p.C₀ 0 * ((p.k : ℝ) + 1) * (p.k : ℝ) ^ (p.k + 1) *
            p.C₀ ^ (p.k + 1) * p.N ^ (s.j + 1) := by ring
  have hCTc : 2 * Real.pi * Alev p.k p.C₀ 0 * ((p.k : ℝ) + 1) * (p.k : ℝ) ^ (p.k + 1) *
        p.C₀ ^ (p.k + 1) * p.N ^ (s.j + 1) = CTc p.k p.C₀ * p.N ^ (s.j + 1) := by
    unfold CTc CT1
    rw [pow_succ p.C₀ p.k, pow_succ ((p.k : ℝ)) p.k]
    ring
  exact hFin.trans (le_of_eq hCTc)

end Work.BMF
