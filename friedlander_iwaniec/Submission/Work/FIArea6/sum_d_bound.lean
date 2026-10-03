import Mathlib
import Submission.Work.FIArea6.pair_phi_helpers

/-!
# `Work.FIArea6.sum_d_bound`

The elementary modulus sum in the `d`-exchange of the `Φ`-weighted pair average:

`∑_{d ≤ D} (φ(d)/d) · 3(2(⌈4πθN⌉₊/(4d) + 1) + 1) ≤ 105 (θN + 1) log(2 + N)`,

where `D = Dmod Pa = ⌈πθN⌉₊ + 1` and `T = ⌈4πθN⌉₊`.

Since `φ(d)/d ≤ 1`, each summand is at most `3T/(2d) + 9`; the harmonic estimate
`∑_{d ≤ D} 1/d ≤ 1 + log D`, the ceiling estimates `T ≤ 4πθN + 1`, `D ≤ πθN + 2`,
`log D ≤ log 4 + log(2 + N)` (using `θ ≤ 1` and `π < 4`) and the numerical inputs
`π < 3.15`, `log 4 ≤ 7/5`, `1 ≤ log(2+N)` then give the stated constant `105`.
-/

namespace Work.FIArea6

open Finset
open scoped BigOperators

noncomputable section

private lemma sum_d_bound_log_three : (1 : ℝ) ≤ Real.log 3 := by
  have h := Real.log_lt_log (Real.exp_pos 1) Real.exp_one_lt_three
  rw [Real.log_exp] at h
  exact h.le

/-- The numerical core: for `A, L ≥ 0, ≥ 1`,
`(6πA + 3/2)(1 + log 4 + L) + 9(πA + 2) ≤ 105(A + 1)L`. -/
private lemma sum_d_bound_num (A L : ℝ) (hA : 0 ≤ A) (hL : 1 ≤ L) :
    (6 * Real.pi * A + 3 / 2) * (1 + Real.log 4 + L) + 9 * (Real.pi * A + 2)
      ≤ 105 * (A + 1) * L := by
  have hpi : Real.pi < 3.15 := Real.pi_lt_d2
  have hq : Real.log 4 ≤ 7 / 5 := by
    rw [Real.log_four_eq]
    nlinarith [Real.log_two_lt_d9]
  have hq0 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have h1 : 6 * Real.pi * A + 3 / 2 ≤ 19 * A + 2 := by nlinarith [hpi, hA]
  have h2 : 1 + Real.log 4 + L ≤ 12 / 5 + L := by linarith
  have h1' : (0 : ℝ) ≤ 19 * A + 2 := by linarith
  have h2' : (0 : ℝ) ≤ 1 + Real.log 4 + L := by linarith
  have h3 : (6 * Real.pi * A + 3 / 2) * (1 + Real.log 4 + L)
      ≤ (19 * A + 2) * (12 / 5 + L) := mul_le_mul h1 h2 h2' h1'
  have h4 : 9 * (Real.pi * A + 2) ≤ 9 * (3.15 * A + 2) := by nlinarith [hpi, hA]
  have h5 : (19 * A + 2) * (12 / 5 + L) + 9 * (3.15 * A + 2) ≤ 105 * (A + 1) * L := by
    nlinarith
  linarith [h3, h4, h5]

theorem sum_d_bound (Pa : Work.FITop.Params) :
    (∑ d ∈ Finset.Icc 1 (Work.FIArea6.Dmod Pa),
        (Nat.totient d : ℝ) / (d : ℝ)
          * (3 * (2 * ((⌈4 * Real.pi * Pa.θ * Pa.N⌉₊ : ℝ) / (4*(d:ℝ)) + 1) + 1)))
      ≤ 105 * (Pa.θ * Pa.N + 1) * Real.log (2 + Pa.N) := by
  set T : ℕ := ⌈4 * Real.pi * Pa.θ * Pa.N⌉₊ with hT
  set D : ℕ := Work.FIArea6.Dmod Pa with hD
  have hθ1 : Pa.θ ≤ 1 := theta_le_one Pa
  have hN0 : (0 : ℝ) ≤ Pa.N := le_trans zero_le_one Pa.hN1
  have hA0 : (0 : ℝ) ≤ Pa.θ * Pa.N := mul_nonneg Pa.hθ0.le hN0
  have hAN : Pa.θ * Pa.N ≤ Pa.N := mul_le_of_le_one_left hN0 hθ1
  -- ceiling estimates
  have hTb : (T : ℝ) ≤ 4 * Real.pi * Pa.θ * Pa.N + 1 := by
    rw [hT]
    have hnn : (0 : ℝ) ≤ 4 * Real.pi * Pa.θ * Pa.N :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) Real.pi_pos.le)
        Pa.hθ0.le) hN0
    have := Nat.ceil_lt_add_one hnn
    linarith
  have hDb : (D : ℝ) ≤ Real.pi * Pa.θ * Pa.N + 2 := by
    rw [hD]; unfold Work.FIArea6.Dmod
    have hnn : (0 : ℝ) ≤ Real.pi * Pa.θ * Pa.N :=
      mul_nonneg (mul_nonneg Real.pi_pos.le Pa.hθ0.le) hN0
    have := Nat.ceil_lt_add_one hnn
    push_cast
    linarith
  have hD1 : 1 ≤ D := by rw [hD]; unfold Work.FIArea6.Dmod; omega
  have hDpos : (0 : ℝ) < (D : ℝ) := by
    have h1 : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD1
    linarith
  -- `log D ≤ log 4 + log (2 + N)`
  have hlogD : Real.log (D : ℝ) ≤ Real.log 4 + Real.log (2 + Pa.N) := by
    have hle : (D : ℝ) ≤ 4 * (Pa.θ * Pa.N + 2) := by
      have hpi4 : Real.pi ≤ 4 := Real.pi_lt_four.le
      nlinarith [hDb, hA0, hpi4]
    have hA2 : (0 : ℝ) < Pa.θ * Pa.N + 2 := by linarith
    calc Real.log (D : ℝ) ≤ Real.log (4 * (Pa.θ * Pa.N + 2)) := Real.log_le_log hDpos hle
      _ = Real.log 4 + Real.log (Pa.θ * Pa.N + 2) := Real.log_mul (by norm_num) (ne_of_gt hA2)
      _ ≤ Real.log 4 + Real.log (2 + Pa.N) :=
          add_le_add (le_refl _) (Real.log_le_log hA2 (by linarith))
  have hL1 : (1 : ℝ) ≤ Real.log (2 + Pa.N) :=
    le_trans sum_d_bound_log_three
      (Real.log_le_log (by norm_num) (by linarith [Pa.hN1]))
  -- harmonic estimate
  have hharm : (∑ d ∈ Finset.Icc 1 D, (1 : ℝ) / (d : ℝ)) ≤ 1 + Real.log (D : ℝ) := by
    have h_eq : (∑ k ∈ Finset.Icc 1 D, (1 : ℝ) / (k : ℝ)) = (harmonic D : ℝ) := by
      rw [harmonic_eq_sum_Icc, Rat.cast_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Rat.cast_inv]
      simp
    rw [h_eq]
    exact harmonic_le_one_add_log D
  calc
    (∑ d ∈ Finset.Icc 1 D,
        (Nat.totient d : ℝ) / (d : ℝ)
          * (3 * (2 * ((T : ℝ) / (4*(d:ℝ)) + 1) + 1)))
      ≤ ∑ d ∈ Finset.Icc 1 D, (3 * (T : ℝ) / (2 * (d : ℝ)) + 9) := by
        apply Finset.sum_le_sum
        intro d hd
        have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
        have hd0 : (0 : ℝ) < (d : ℝ) := by
          have : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd1
          linarith
        have hphi : (Nat.totient d : ℝ) / (d : ℝ) ≤ 1 := by
          rw [div_le_one hd0]
          exact_mod_cast Nat.totient_le d
        have hb : (0 : ℝ) ≤ 3 * (2 * ((T : ℝ) / (4*(d:ℝ)) + 1) + 1) := by positivity
        calc (Nat.totient d : ℝ) / (d : ℝ) * (3 * (2 * ((T : ℝ)/(4*(d:ℝ))+1)+1))
            ≤ 1 * (3 * (2 * ((T : ℝ)/(4*(d:ℝ))+1)+1)) := mul_le_mul_of_nonneg_right hphi hb
          _ = 3 * (T : ℝ) / (2 * (d : ℝ)) + 9 := by
              rw [one_mul]
              have hd0' : (d : ℝ) ≠ 0 := ne_of_gt hd0
              field_simp
              ring
    _ = 3 * (T : ℝ) / 2 * (∑ d ∈ Finset.Icc 1 D, (1:ℝ)/(d:ℝ)) + 9 * (D : ℝ) := by
        rw [Finset.sum_add_distrib]
        have hcard : (Finset.Icc 1 D).card = D := by rw [Nat.card_Icc]; omega
        rw [Finset.sum_const, hcard, nsmul_eq_mul]
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d hd
        have hd0 : (d : ℝ) ≠ 0 := by
          have h1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
          have h2 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast h1
          have : (0 : ℝ) < (d : ℝ) := by linarith
          exact ne_of_gt this
        field_simp
        ring
    _ ≤ 3 * (T : ℝ) / 2 * (1 + Real.log (D : ℝ)) + 9 * (D : ℝ) := by
        have h := mul_le_mul_of_nonneg_left hharm (by positivity : (0:ℝ) ≤ 3 * (T:ℝ) / 2)
        linarith
    _ ≤ (6 * Real.pi * (Pa.θ * Pa.N) + 3 / 2) * (1 + Real.log 4 + Real.log (2 + Pa.N))
          + 9 * (Real.pi * (Pa.θ * Pa.N) + 2) := by
        have h1 : 3 * (T : ℝ) / 2 ≤ 6 * Real.pi * (Pa.θ * Pa.N) + 3 / 2 := by nlinarith [hTb]
        have h2 : 1 + Real.log (D : ℝ) ≤ 1 + Real.log 4 + Real.log (2 + Pa.N) := by linarith
        have h2' : (0 : ℝ) ≤ 1 + Real.log (D : ℝ) := by
          have : (0 : ℝ) ≤ Real.log (D : ℝ) := Real.log_nonneg (by exact_mod_cast hD1)
          linarith
        have hb : (0 : ℝ) ≤ 6 * Real.pi * (Pa.θ * Pa.N) + 3 / 2 := by
          have h1' : (0 : ℝ) ≤ 6 * Real.pi * (Pa.θ * Pa.N) :=
            mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) hA0
          linarith
        have h3 : 3 * (T : ℝ) / 2 * (1 + Real.log (D : ℝ))
            ≤ (6 * Real.pi * (Pa.θ * Pa.N) + 3 / 2) * (1 + Real.log 4 + Real.log (2 + Pa.N)) :=
          mul_le_mul h1 h2 h2' hb
        have h4 : 9 * (D : ℝ) ≤ 9 * (Real.pi * (Pa.θ * Pa.N) + 2) := by nlinarith [hDb]
        linarith [h3, h4]
    _ ≤ 105 * (Pa.θ * Pa.N + 1) * Real.log (2 + Pa.N) :=
        sum_d_bound_num (Pa.θ * Pa.N) (Real.log (2 + Pa.N)) hA0 hL1

end

end Work.FIArea6
