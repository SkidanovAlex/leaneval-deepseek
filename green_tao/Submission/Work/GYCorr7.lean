import Submission.Work.GYCorr6
import Submission.Work.GYCount

/-!
# The box-average upper bound for the correlation system (Green–Tao (GY2-est))

This file reduces the box-average estimate of Green–Tao's Proposition GY2 to
* the divisor-sum main term (`hmain`, proved from `mainSum_eq_logR_corr` + `G1u_zero_bound`),
* the elementary error estimate `errBd ≤ ε·P^a` (`errBd_le` of `GYCount`), and
* the residue-class counting (`countBox_abs_bound` of `GYCount`).

The result is an **upper** bound (no absolute value), which is all the correlation condition
needs.
-/

open Finset
open scoped BigOperators

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

namespace GYMaj
namespace Corr

open GYMaj.BoxAvg
open Commons.NumberTheory.Sieve

variable {a : ℕ}

/-- The box-data of the correlation box-average reduction. -/
structure CorrBoxData (k R W : ℕ) (a : ℕ) (δ : Fin a → ℤ) (l r : Fin 1 → ℤ) : Prop where
  ha1 : 1 ≤ a
  haK : a ≤ k * 2 ^ (k - 1)
  hside : ∀ j, (R : ℤ) ^ (10 * a) ≤ r j - l j
  hpos : ∀ x ∈ box l r, ∀ i, 0 < theta W (Ac a) δ x i
  hΔ0 : Delta δ ≠ 0

/-- The constant multiplying the `Δ`-primes in the main term. -/
noncomputable def Kc (a : ℕ) : ℝ := Real.exp (Cc a * (∑' n : ℕ, (n : ℝ) ^ (-(4 / 3 : ℝ))))

/-- The `Δ`-factor of the main term. -/
noncomputable def LamD (a : ℕ) (δ : Fin a → ℤ) : ℝ :=
  ∏ q ∈ (Delta δ).primeFactors, (1 + (q : ℝ) ^ (-(1 / 2 : ℝ))) ^ (Da a)

lemma Kc_pos (a : ℕ) : 0 < Kc a := Real.exp_pos _

lemma one_le_LamD (a : ℕ) (δ : Fin a → ℤ) : 1 ≤ LamD a δ := by
  rw [LamD]
  refine Finset.one_le_prod (fun q _ => ?_)
  have h1 : (1 : ℝ) ≤ 1 + (q : ℝ) ^ (-(1 / 2 : ℝ)) := by
    have := Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ (q : ℝ)) (-(1 / 2 : ℝ))
    linarith
  exact Real.one_le_rpow h1 (Da_nonneg a)

/-- **The box-average upper bound for the correlation system.** -/
theorem boxAvgCorr_ub (k R W : ℕ) (ε : ℝ) (hR : 3 ≤ R) (hRk : 3 * k ≤ R) (hW : 1 ≤ W)
    (hε : 0 < ε)
    (hsmall : 6 * (3 * (k : ℝ)) * (Real.log (R : ℝ)) ^ (k * 2 ^ (k - 1)) ≤ ε * (R : ℝ) ^ 6)
    (herr : ∀ (a : ℕ) (δ : Fin a → ℤ) (l r : Fin 1 → ℤ), CorrBoxData k R W a δ l r →
      errBd R W (Ac a) δ l r
        ≤ (ε / 2) * ((W : ℝ) * Real.log (R : ℝ) / (Nat.totient W : ℝ)) ^ a)
    (hmain : ∀ (a : ℕ) (δ : Fin a → ℤ) (l r : Fin 1 → ℤ), CorrBoxData k R W a δ l r →
      mainSum R W (Ac a) δ
        ≤ (1 + ε / 2) * ((W : ℝ) * Real.log (R : ℝ) / (Nat.totient W : ℝ)) ^ a
            * (Kc a * LamD a δ)) :
    ∀ (a : ℕ) (δ : Fin a → ℤ) (l r : Fin 1 → ℤ), CorrBoxData k R W a δ l r →
      (sideProd l r)⁻¹ * boxSum R W (Ac a) δ l r
        ≤ (1 + ε) * ((W : ℝ) * Real.log (R : ℝ) / (Nat.totient W : ℝ)) ^ a
            * (Kc a * LamD a δ) := by
  intro a δ l r hD
  obtain ⟨ha1, haK, hside, hpos, hΔ0⟩ := hD
  have hD' : CorrBoxData k R W a δ l r := ⟨ha1, haK, hside, hpos, hΔ0⟩
  have hW0 : 0 < W := by omega
  have hφpos : (0 : ℝ) < (Nat.totient W : ℝ) :=
    Nat.cast_pos.mpr (Nat.totient_pos.mpr hW0)
  have hR1 : 1 ≤ R := by omega
  have hRpos : (0 : ℝ) < (R : ℝ) := by exact_mod_cast (by omega : 0 < R)
  have hL0 : 0 ≤ Real.log (R : ℝ) := Real.log_nonneg (by exact_mod_cast hR1)
  have hP0 : 0 ≤ (W : ℝ) * Real.log (R : ℝ) / (Nat.totient W : ℝ) := by positivity
  set Pc : ℝ := (W : ℝ) * Real.log (R : ℝ) / (Nat.totient W : ℝ) with hP
  have hS : 0 < sideProd l r := by
    rw [sideProd]
    refine Finset.prod_pos (fun j _ => ?_)
    have h1 : (1 : ℤ) ≤ (R : ℤ) ^ (10 * a) :=
      one_le_pow₀ (by exact_mod_cast hR1 : (1 : ℤ) ≤ (R : ℤ))
    have h2 : (0 : ℤ) < r j - l j := lt_of_lt_of_le (by norm_num) (le_trans h1 (hside j))
    exact_mod_cast h2
  have hcount : ∀ d ∈ P (m := a) R, ∀ e ∈ P (m := a) R,
      |((countBox W (Ac a) δ l r d e : ℕ) : ℝ) - sideProd l r * rho W (Ac a) δ d e|
        ≤ sideProd l r * rho W (Ac a) δ d e * Efac d e l r := by
    intro d hd e he
    simp only [P, Fintype.mem_piFinset] at hd he
    have hd1 : ∀ i, 1 ≤ d i := fun i => (Finset.mem_Icc.mp (hd i)).1
    have hdR : ∀ i, d i ≤ R := fun i => (Finset.mem_Icc.mp (hd i)).2
    have he1 : ∀ i, 1 ≤ e i := fun i => (Finset.mem_Icc.mp (he i)).1
    have heR : ∀ i, e i ≤ R := fun i => (Finset.mem_Icc.mp (he i)).2
    have hN : ∀ j, (Ddd d e : ℤ) ≤ r j - l j := by
      intro j
      have h1 : (Ddd d e : ℤ) ≤ ((R : ℤ)) ^ (2 * a) := by
        have h := Ddd_le d e hd1 he1 hdR heR
        exact_mod_cast h
      have h2 : ((R : ℤ)) ^ (2 * a) ≤ ((R : ℤ)) ^ (10 * a) :=
        pow_le_pow_right₀ (by exact_mod_cast hR1 : (1 : ℤ) ≤ (R : ℤ)) (by omega)
      linarith [hside j]
    exact countBox_abs_bound W (Ac a) δ l r d e hd1 he1 hpos hN
  have hle := BoxAvg.box_sum_le_main (m := a) (t := 1) R W (Ac a) δ l r hpos hS hcount
  have he := herr a δ l r hD'
  have hm := hmain a δ l r hD'
  have hKc : 1 ≤ Kc a := by
    rw [Kc]
    exact Real.one_le_exp (mul_nonneg (Cc_nonneg a)
      (tsum_nonneg (fun n => Real.rpow_nonneg (by positivity) _)))
  have hKL : 1 ≤ Kc a * LamD a δ := by nlinarith [hKc, one_le_LamD a δ]
  have hK0 : (0 : ℝ) ≤ Kc a * LamD a δ := le_trans zero_le_one hKL
  have habs : (sideProd l r)⁻¹ * boxSum R W (Ac a) δ l r - mainSum R W (Ac a) δ
      ≤ errBd R W (Ac a) δ l r := by
    have h1 := (abs_le.mp hle).2
    linarith
  have hrw : (sideProd l r)⁻¹ * boxSum R W (Ac a) δ l r
      ≤ mainSum R W (Ac a) δ + errBd R W (Ac a) δ l r := by linarith
  have hPa : (0 : ℝ) ≤ Pc ^ a := pow_nonneg hP0 a
  calc (sideProd l r)⁻¹ * boxSum R W (Ac a) δ l r
      ≤ mainSum R W (Ac a) δ + errBd R W (Ac a) δ l r := hrw
    _ ≤ (1 + ε / 2) * Pc ^ a * (Kc a * LamD a δ) + (ε / 2) * Pc ^ a := by linarith [hm, he]
    _ ≤ (1 + ε / 2) * Pc ^ a * (Kc a * LamD a δ)
          + (ε / 2) * Pc ^ a * (Kc a * LamD a δ) := by
        have h2 : (ε / 2) * Pc ^ a ≤ (ε / 2) * Pc ^ a * (Kc a * LamD a δ) :=
          le_mul_of_one_le_right (by positivity) hKL
        linarith [h2]
    _ = (1 + ε) * Pc ^ a * (Kc a * LamD a δ) := by ring

end Corr
end GYMaj
