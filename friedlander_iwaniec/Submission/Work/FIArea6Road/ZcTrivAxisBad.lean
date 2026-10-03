/-
# `Submission.Work.FIArea6Road.ZcTrivAxisBad`

The bad-prime correction `G_d(s) = ∏_{p ∣ 4d}(1 - p^{-s})(1 - χ₄(p)p^{-s})` of the trivial-`ψ`
regime is bounded below on `Re s ≥ 1/2`: `‖G_d(s)⁻¹‖ ≤ K·d` with an absolute constant `K`.

Each factor is bounded by the corresponding prime for odd `p` (the `p = 2` factor by the constant
`4`), and `∏_{p ∣ d} p ≤ d`.
-/
import Mathlib
import Submission.Work.FIArea6Hecke.R.AxisLogDefs

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIArea6Road

open Finset

noncomputable section

/-! ## Elementary estimates -/

/-- `∏_{p ∣ n} p ≤ n` for `n ≥ 1` (the radical of `n` divides `n`). -/
lemma zcT_prod_primeFactors_le_self (n : ℕ) (hn : 1 ≤ n) :
    ∏ p ∈ n.primeFactors, (p : ℝ) ≤ (n : ℝ) := by
  have hnat : ∏ p ∈ n.primeFactors, p ≤ n :=
    Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd n)
  calc ∏ p ∈ n.primeFactors, (p : ℝ)
      = ((∏ p ∈ n.primeFactors, p : ℕ) : ℝ) :=
        (Nat.cast_prod (fun p : ℕ => p) n.primeFactors).symm
    _ ≤ (n : ℝ) := by exact_mod_cast hnat

/-- `2^{-1/2} ≤ 3/4`, hence `(1 - 2^{-1/2})^{-1} ≤ 4`. -/
lemma zcT_inv_one_sub_two_rpow_half_le_four :
    (1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)))⁻¹ ≤ 4 := by
  have hsq : ((2 : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 = 1 / 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hnn : (0 : ℝ) ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (by norm_num) _
  have hle : (2 : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 3 / 4 := by
    nlinarith [hsq, hnn, sq_nonneg ((2 : ℝ) ^ (-(1 / 2 : ℝ)) - 3 / 4)]
  have hpos : 0 < 1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)) := by linarith
  have hquot : (1 : ℝ) / 4 ≤ 1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)) := by linarith
  have h := (inv_le_inv₀ hpos (by norm_num : (0 : ℝ) < 1 / 4)).mpr hquot
  rwa [show ((1 : ℝ) / 4)⁻¹ = 4 by norm_num] at h

/-- `(1 - p^{-1/2})^{-2} ≤ p` for `p ≥ 4`. -/
lemma zcT_inv_sq_le_self {p : ℝ} (hp : 4 ≤ p) :
    ((1 - p ^ (-(1 / 2 : ℝ)))⁻¹) ^ 2 ≤ p := by
  have hp0 : 0 < p := by linarith
  have hle : p ^ (-(1 / 2 : ℝ)) = (Real.sqrt p)⁻¹ := by
    rw [Real.rpow_neg (le_of_lt hp0), Real.sqrt_eq_rpow]
  rw [hle]
  have hsq : (2 : ℝ) ≤ Real.sqrt p := by
    have h := Real.sqrt_le_sqrt hp
    rwa [show Real.sqrt (4 : ℝ) = 2 from by norm_num] at h
  have h1 : (1 : ℝ) ≤ Real.sqrt p - 1 := by linarith
  have hsub : 1 - (Real.sqrt p)⁻¹ = (Real.sqrt p - 1) / Real.sqrt p := by
    field_simp
  rw [hsub, inv_div, div_pow]
  rw [div_le_iff₀ (pow_pos (by linarith : (0 : ℝ) < Real.sqrt p - 1) 2)]
  have hge1 : (1 : ℝ) ≤ (Real.sqrt p - 1) ^ 2 := by
    have h := pow_le_pow_left₀ (show (0 : ℝ) ≤ 1 by norm_num) h1 2
    simpa using h
  have hmul := mul_le_mul_of_nonneg_left hge1 (le_of_lt hp0)
  have hsq' := Real.sq_sqrt (le_of_lt hp0)
  nlinarith [hmul, hsq']

/-- `(1 - p^{-1})^{-1} ≤ p` for `p ≥ 2`. -/
lemma zcT_inv_one_sub_inv_le_self {p : ℝ} (hp : 2 ≤ p) :
    (1 - p ^ (-1 : ℝ))⁻¹ ≤ p := by
  rw [Real.rpow_neg_one]
  have hp0 : 0 < p := by linarith
  have h1 : 1 < p := by linarith
  have hden : 0 < 1 - p⁻¹ := by
    have := inv_lt_one_of_one_lt₀ h1
    linarith
  rw [inv_le_iff_one_le_mul₀ hden]
  have hmul : p * (1 - p⁻¹) = p - 1 := by
    rw [mul_sub, mul_one, mul_inv_cancel₀ (ne_of_gt hp0)]
  rw [hmul]
  linarith

/-- `1 - p^{-1/2} ≤ ‖1 - p^{-s}‖` for `p ≥ 1` and `Re s ≥ 1/2`. -/
lemma zcT_one_sub_rpow_half_le_norm {p : ℕ} (hp : 0 < p) {s : ℂ}
    (hs : (1 / 2 : ℝ) ≤ s.re) :
    1 - (p : ℝ) ^ (-(1 / 2 : ℝ)) ≤ ‖(1 : ℂ) - (p : ℂ) ^ (-s)‖ := by
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hnorm : ‖(p : ℂ) ^ (-s)‖ = (p : ℝ) ^ (-s.re) := by
    rw [Complex.norm_natCast_cpow_of_pos hp (-s), Complex.neg_re]
  have h1 := norm_sub_norm_le (1 : ℂ) ((p : ℂ) ^ (-s))
  rw [norm_one, hnorm] at h1
  have h2 : (p : ℝ) ^ (-s.re) ≤ (p : ℝ) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
  linarith

/-- `1 - p^{-1/2} > 0` for `p > 1`. -/
lemma zcT_one_sub_rpow_half_pos {p : ℕ} (hp : 1 < p) :
    0 < 1 - (p : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have h : (p : ℝ) ^ (-(1 / 2 : ℝ)) < (p : ℝ) ^ (0 : ℝ) :=
    Real.rpow_lt_rpow_of_exponent_lt hp1 (by norm_num)
  rw [Real.rpow_zero] at h
  linarith

/-! ## The per-prime bound -/

/-- **The per-prime bound.**  For a prime `p` and `Re s ≥ 1/2` the reciprocal of the `p`-factor of
`axisBadPoly` is at most `p` (at most `4` for `p = 2`). -/
lemma zcT_axisBad_factor_inv_le (p : ℕ) (hpp : p.Prime) {s : ℂ} (hs : (1 / 2 : ℝ) ≤ s.re) :
    ‖((1 - (p : ℂ) ^ (-s)) * (1 - Work.FIArea6Hecke.R.axisChi4 p * (p : ℂ) ^ (-s)))⁻¹‖
      ≤ (if p = 2 then (4 : ℝ) else (p : ℝ)) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.pos
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.one_lt
  have hAhalf : 1 - (p : ℝ) ^ (-(1 / 2 : ℝ)) ≤ ‖(1 : ℂ) - (p : ℂ) ^ (-s)‖ :=
    zcT_one_sub_rpow_half_le_norm hpp.pos hs
  have hAhalfpos : 0 < 1 - (p : ℝ) ^ (-(1 / 2 : ℝ)) := zcT_one_sub_rpow_half_pos hpp.one_lt
  have hApos : 0 < ‖(1 : ℂ) - (p : ℂ) ^ (-s)‖ := lt_of_lt_of_le hAhalfpos hAhalf
  have hAinv : (‖(1 : ℂ) - (p : ℂ) ^ (-s)‖)⁻¹
      ≤ (1 - (p : ℝ) ^ (-(1 / 2 : ℝ)))⁻¹ := (inv_le_inv₀ hApos hAhalfpos).mpr hAhalf
  by_cases hp2 : p = 2
  · subst hp2
    rw [if_pos rfl]
    have hchi0 : Work.FIArea6Hecke.R.axisChi4 2 = 0 :=
      Work.FIArea6Hecke.R.axisChi4_eq_zero_of_even ⟨1, by norm_num⟩
    rw [hchi0, zero_mul, sub_zero, mul_one, norm_inv]
    exact le_trans hAinv zcT_inv_one_sub_two_rpow_half_le_four
  · rw [if_neg hp2]
    have hmod2 : p % 2 ≠ 0 := by
      intro h
      have h2 : 2 ∣ p := Nat.dvd_of_mod_eq_zero h
      rcases (Nat.dvd_prime hpp).mp h2 with h1 | h1
      · exact absurd h1 (by norm_num)
      · exact hp2 h1.symm
    have hval := Work.FIArea6Hecke.R.axisChi4_eq_if p
    rw [if_neg hmod2] at hval
    by_cases hmod : p % 4 = 1
    · rw [if_pos hmod] at hval
      rw [hval, one_mul]
      have h4p : 4 ≤ p := by
        have hdecomp : p = p / 4 * 4 + p % 4 := by
          rw [mul_comm]
          exact (Nat.div_add_mod p 4).symm
        rw [hmod] at hdecomp
        rcases Nat.eq_zero_or_pos (p / 4) with h | h
        · rw [h] at hdecomp
          simp at hdecomp
          exact (hpp.ne_one hdecomp).elim
        · nlinarith [hdecomp, h]
      have hsq : (1 - (p : ℂ) ^ (-s)) * (1 - (p : ℂ) ^ (-s))
          = ((1 : ℂ) - (p : ℂ) ^ (-s)) ^ 2 := by ring
      rw [hsq, norm_inv, norm_pow]
      calc ((‖(1 : ℂ) - (p : ℂ) ^ (-s)‖) ^ 2)⁻¹
          = ((‖(1 : ℂ) - (p : ℂ) ^ (-s)‖)⁻¹) ^ 2 := by rw [← inv_pow]
        _ ≤ ((1 - (p : ℝ) ^ (-(1 / 2 : ℝ)))⁻¹) ^ 2 :=
              pow_le_pow_left₀ (inv_nonneg.mpr (norm_nonneg _)) hAinv 2
        _ ≤ (p : ℝ) := zcT_inv_sq_le_self (by exact_mod_cast h4p)
    · rw [if_neg hmod] at hval
      rw [hval]
      have hfac : (1 - (p : ℂ) ^ (-s)) * (1 - (-1 : ℂ) * (p : ℂ) ^ (-s))
          = 1 - ((p : ℂ) ^ (-s)) ^ 2 := by ring
      rw [hfac, norm_inv]
      have hnormB : ‖(p : ℂ) ^ (-s)‖ = (p : ℝ) ^ (-s.re) := by
        rw [Complex.norm_natCast_cpow_of_pos hpp.pos (-s), Complex.neg_re]
      have hnormB2 : ‖((p : ℂ) ^ (-s)) ^ 2‖ = (p : ℝ) ^ (-2 * s.re) := by
        rw [norm_pow, hnormB, ← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hp0)]
        ring_nf
      have hle1 : 1 - (p : ℝ) ^ (-2 * s.re) ≤ ‖(1 : ℂ) - ((p : ℂ) ^ (-s)) ^ 2‖ := by
        have h := norm_sub_norm_le (1 : ℂ) (((p : ℂ) ^ (-s)) ^ 2)
        rw [norm_one, hnormB2] at h
        linarith
      have hT : (p : ℝ) ^ (-2 * s.re) ≤ (p : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (le_of_lt hp1) (by linarith)
      have hden : 0 < 1 - (p : ℝ) ^ (-1 : ℝ) := by
        rw [Real.rpow_neg_one]
        have : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp1
        linarith
      have hlo : 0 < 1 - (p : ℝ) ^ (-2 * s.re) := by linarith
      have hposn : 0 < ‖(1 : ℂ) - ((p : ℂ) ^ (-s)) ^ 2‖ := lt_of_lt_of_le hlo hle1
      calc (‖(1 : ℂ) - ((p : ℂ) ^ (-s)) ^ 2‖)⁻¹
          ≤ (1 - (p : ℝ) ^ (-2 * s.re))⁻¹ := (inv_le_inv₀ hposn hlo).mpr hle1
        _ ≤ (1 - (p : ℝ) ^ (-1 : ℝ))⁻¹ := (inv_le_inv₀ hlo hden).mpr (by linarith)
        _ ≤ (p : ℝ) := zcT_inv_one_sub_inv_le_self (by exact_mod_cast hpp.two_le)

/-! ## The main bound -/

theorem ZcTrivAxisBad :
    ∃ K : ℝ, 0 < K ∧ ∀ d : ℕ, 1 ≤ d → ∀ s : ℂ, (1 / 2 : ℝ) ≤ s.re →
      ‖(Work.FIArea6Hecke.R.axisBadPoly d s)⁻¹‖ ≤ K * (d : ℝ) := by
  refine ⟨4, by norm_num, ?_⟩
  intro d hd s hs
  have hmem2 : 2 ∈ (4 * d).primeFactors := by
    rw [Nat.mem_primeFactors]
    exact ⟨Nat.prime_two, ⟨2 * d, by ring⟩, by omega⟩
  have herase : (4 * d).primeFactors.erase 2 ⊆ d.primeFactors := by
    intro p hp
    rw [Finset.mem_erase, Nat.mem_primeFactors] at hp
    obtain ⟨hp2, hpp, hpdvd, -⟩ := hp
    rw [Nat.mem_primeFactors]
    refine ⟨hpp, ?_, by omega⟩
    have h1 : p ∣ 2 * (2 * d) := by
      simpa [show 4 * d = 2 * (2 * d) by ring] using hpdvd
    rcases hpp.dvd_mul.mp h1 with h | h
    · rcases (Nat.dvd_prime Nat.prime_two).mp h with h1 | h1
      · exact absurd h1 hpp.ne_one
      · exact absurd h1 hp2
    · rcases hpp.dvd_mul.mp h with h2 | h2
      · rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h3 | h3
        · exact absurd h3 hpp.ne_one
        · exact absurd h3 hp2
      · exact h2
  have hfac : ∀ p ∈ (4 * d).primeFactors,
      ‖((1 - (p : ℂ) ^ (-s)) * (1 - Work.FIArea6Hecke.R.axisChi4 p * (p : ℂ) ^ (-s)))⁻¹‖
        ≤ (if p = 2 then (4 : ℝ) else (p : ℝ)) :=
    fun p hp => zcT_axisBad_factor_inv_le p (Nat.prime_of_mem_primeFactors hp) hs
  have hprod : ‖(Work.FIArea6Hecke.R.axisBadPoly d s)⁻¹‖
      = ∏ p ∈ (4 * d).primeFactors,
          ‖((1 - (p : ℂ) ^ (-s)) * (1 - Work.FIArea6Hecke.R.axisChi4 p * (p : ℂ) ^ (-s)))⁻¹‖ := by
    rw [Work.FIArea6Hecke.R.axisBadPoly, ← Finset.prod_inv_distrib, norm_prod]
  rw [hprod]
  refine le_trans (Finset.prod_le_prod₀ (fun p _ => norm_nonneg _) hfac) ?_
  rw [← Finset.prod_erase_mul (4 * d).primeFactors
    (fun p => (if p = 2 then (4 : ℝ) else (p : ℝ))) hmem2]
  rw [if_pos rfl]
  have h1 : ∏ p ∈ (4 * d).primeFactors.erase 2, (if p = 2 then (4 : ℝ) else (p : ℝ))
      = ∏ p ∈ (4 * d).primeFactors.erase 2, (p : ℝ) := by
    refine Finset.prod_congr rfl fun p hp => ?_
    exact if_neg (Finset.mem_erase.mp hp).1
  rw [h1]
  have h2 : ∏ p ∈ (4 * d).primeFactors.erase 2, (p : ℝ) ≤ ∏ p ∈ d.primeFactors, (p : ℝ) :=
    Finset.prod_le_prod_of_subset_of_one_le₀ herase (fun p _ => by positivity)
      (fun p hp _ => by
        have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
        exact_mod_cast hpp.one_le)
  have h3 : ∏ p ∈ d.primeFactors, (p : ℝ) ≤ (d : ℝ) := zcT_prod_primeFactors_le_self d hd
  linarith

end

end Work.FIArea6Road
