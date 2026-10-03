/-
# `Work.FIChain.Etwo_le_at_07` — the `E₂` estimate (9.12) at the `⌈x^{7/10}⌉` cutoff

This is the `D₇`-analogue of `Submission.ASP.FI_Etwo_le`: the companion's §9 estimate `(9.12)`
for the `E₂`-part of the §9 error term, but for the *larger* modulus cutoff
`D₇(x) = ⌈x^{7/10}⌉` rather than `Rcut x = ⌊x^{11/16}⌋`.

The proof is the one of `FI_Etwo_le` with the modulus `D` kept general: the only place where `D`
enters is the `g`-part `EtwoG FIa FIg t D (L+1) t`, which `Submission.ASP.EtwoG_FIa_le` bounds
uniformly for every `1 ≤ D ≤ x`, and the `A`-part of `E₂`, bounded by `Submission.ASP.Etwo_le`
via Cauchy–Schwarz with the two `D`-independent inputs `hX` (the `τ³`-weighted square-divisor
count, made to vanish by taking the split point `Y = t.sqrt`) and
`hS1 = Submission.ASP.FI_Ad_sqrt_le β` (which only needs `Rcut x ≤ t`).

The general-`D` form is recorded as `Etwo_le_generalD`; the requested statement
`Etwo_le_at_07` is then the instance `D = ⌈x^{7/10}⌉`, using
`Rcut x ≤ ⌈x^{7/10}⌉ ≤ x` for large `x`.
-/
import Mathlib
import Submission.Work.FIChain.Defs
import Submission.ASP.S40
import Submission.ASP.S31
import Submission.ASP.S22
import Submission.ASP.S21
import Submission.ASP.S35
import Submission.ASP.S36
import Submission.ASP.S34
import Submission.ASP.S33
import Submission.ASP.S32
import Submission.ASP.S9b
import Submission.ASP.S9d
import Submission.ASP.S37
import Submission.ASP_R3

namespace Work.FIChain

open Finset
open Submission.ASP
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

set_option maxHeartbeats 4000000

/-! ### The general-modulus form of `(9.12)` -/

/-- **Companion §9, the `E₂` estimate (9.12), with a general modulus cutoff `D`**: for every
`1 ≤ D ≤ x` and every `t` with `Rcut x ≤ t ≤ x`, the `ν > L` part of the §9 error term is
`≪ A(x)(log x)^{−λ}`, given the `τ³`-weighted `S₂ ≪ A(x)(log x)^{B₂}` with `B₂ ≤ 2λ` and that
`(log x)^{8λ+100} ≤ L`. -/
theorem Etwo_le_generalD (B2 C2 lam : ℝ) (hC2 : 0 < C2) (hB2 : 0 ≤ B2)
    (hcomp : B2 ≤ 2 * lam) (X2 : ℕ)
    (hS2 : ∀ x : ℕ, X2 ≤ x → ∀ t : ℕ, 2 ≤ t → t ≤ x →
      (∑ n ∈ Finset.Icc 1 t, FIa n * ((n.divisors.card : ℝ)) ^ (3 : ℕ))
        ≤ C2 * (Submission.Aseq x : ℝ) * (Real.log x) ^ B2) :
    ∃ X₀ : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ x : ℕ, X₀ ≤ x → ∀ t D L : ℕ,
      2 ≤ t → t ≤ x → Submission.Rcut x ≤ t → 1 ≤ D → D ≤ x →
      1 ≤ L → L < t.sqrt →
      (L + 1) ^ 2 < Submission.X2Y4R3.R3cut x →
      (Real.log x) ^ (8 * lam + 100) ≤ (L : ℝ) →
      Etwo FIa FIg t D L
        ≤ C * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lam) := by
  obtain ⟨Cg, hCg, hGle⟩ := EtwoG_FIa_le
  set lamm : ℝ := B2 + 2 * lam + 10 with hlammdef
  set β : ℝ := 71 + 4 * lamm with hβdef
  have hβ71 : (71 : ℝ) ≤ β := by rw [hβdef]; linarith
  have hlamm0 : (0 : ℝ) ≤ lamm := by rw [hlammdef]; linarith
  have hβ0 : (0 : ℝ) ≤ β := le_trans (by norm_num) hβ71
  obtain ⟨Xlim, Clim, hClim, hAd⟩ := FI_Ad_sqrt_le β hβ71
  -- thresholds
  obtain ⟨Y1, -, hY1⟩ :=
    Commons.Analysis.ExpLog.const_mul_log_add_two_pow_le_rpow_threshold_nat
      (K := (1 : ℝ)) (by norm_num) (n := ⌈2 * β⌉₊) (r := (1 : ℝ) / 60) (by norm_num)
  obtain ⟨Y2, -, hY2⟩ :=
    Commons.Analysis.ExpLog.const_mul_log_add_two_pow_le_rpow_threshold_nat
      (K := 2 * Real.sqrt 2) (by positivity) (n := 0) (r := (1 : ℝ) / 480) (by norm_num)
  obtain ⟨Y3, -, hY3⟩ :=
    Commons.Analysis.ExpLog.const_mul_log_add_two_pow_le_rpow_threshold_nat
      (K := 16) (by norm_num) (n := 0) (r := (1 : ℝ) / 60) (by norm_num)
  obtain ⟨Y4, -, hY4⟩ :=
    Commons.Analysis.ExpLog.const_mul_log_add_two_pow_le_rpow_threshold_nat
      (K := 2 ^ (45 : ℕ)) (by positivity) (n := 40) (r := (1 : ℝ) / 2) (by norm_num)
  obtain ⟨Y6, -, hY6⟩ :=
    Commons.Analysis.ExpLog.const_mul_log_add_two_pow_le_rpow_threshold_nat
      (K := 9) (by norm_num) (n := 0) (r := (7 : ℝ) / 10) (by norm_num)
  obtain ⟨Y5, -, hY5⟩ :=
    Commons.Analysis.ExpLog.const_mul_log_add_two_pow_le_rpow_threshold_nat
      (K := Real.exp ((2 : ℝ) ^ (45 : ℕ))) (by positivity) (n := 0) (r := 1) (by norm_num)
  have hlam3 : (3 * lam + 100) ≥ (46 : ℝ) := by
    have := hcomp
    nlinarith [hB2, hcomp]
  refine ⟨max (max (max Xlim (max Y1 Y2)) (max Y3 (max Y4 Y5))) (max (max Y6 129) X2),
    (1 + Real.sqrt (Clim * C2) + Cg * (2 : ℝ) ^ (37 : ℕ)) * 8, by positivity,
    fun x hx t D L ht htx hDt hD1 hDx hL1 hLt hLsq hLbig => ?_⟩
  have hle := hx
  have hAX : max Xlim (max Y1 Y2)
      ≤ max (max (max Xlim (max Y1 Y2)) (max Y3 (max Y4 Y5))) (max (max Y6 129) X2) :=
    le_trans (le_max_left _ _) (le_max_left _ _)
  have hBY : max Y3 (max Y4 Y5)
      ≤ max (max (max Xlim (max Y1 Y2)) (max Y3 (max Y4 Y5))) (max (max Y6 129) X2) :=
    le_trans (le_max_right _ _) (le_max_left _ _)
  have hxXlim : Xlim ≤ x := le_trans (le_trans (le_max_left _ _) hAX) hle
  have hxY1 : Y1 ≤ x :=
    le_trans (le_trans (le_trans (le_max_left Y1 Y2) (le_max_right Xlim _)) hAX) hle
  have hxY2 : Y2 ≤ x :=
    le_trans (le_trans (le_trans (le_max_right Y1 Y2) (le_max_right Xlim _)) hAX) hle
  have hxY3 : Y3 ≤ x := le_trans (le_trans (le_max_left _ _) hBY) hle
  have hxY4 : Y4 ≤ x :=
    le_trans (le_trans (le_trans (le_max_left Y4 Y5) (le_max_right Y3 _)) hBY) hle
  have hxY5 : Y5 ≤ x :=
    le_trans (le_trans (le_trans (le_max_right Y4 Y5) (le_max_right Y3 _)) hBY) hle
  have hx128 : 128 ≤ x :=
    le_trans (by norm_num : (128 : ℕ) ≤ 129)
      (le_trans (le_max_right Y6 129)
        (le_trans (le_max_left (max Y6 129) X2) (le_trans (le_max_right _ _) hle)))
  have hxY6 : Y6 ≤ x :=
    le_trans (le_max_left Y6 129)
      (le_trans (le_max_left (max Y6 129) X2) (le_trans (le_max_right _ _) hle))
  have hxX2 : X2 ≤ x :=
    le_trans (le_max_right (max Y6 129) X2) (le_trans (le_max_right _ _) hle)
  have hx1 : 1 ≤ x := by omega
  have hx0 : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 1) hx1)
  have hxR1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx1
  have htxR : (t : ℝ) ≤ (x : ℝ) := by exact_mod_cast htx
  have ht1 : 1 ≤ t := le_trans (by norm_num : 1 ≤ 2) ht
  have ht4' : 4 ≤ t := le_trans (four_le_Rcut (le_trans (by norm_num : 64 ≤ 128) hx128)) hDt
  have htR0 : (0 : ℝ) < (t : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 1) ht1)
  have ht4 : (4 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht4'
  have hL0 : (0 : ℝ) < (L : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 1) hL1)
  have hL1R : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL1
  have hxR2 : (2 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (le_trans (by norm_num : 2 ≤ 128) hx128)
  have hlogx1 : (1 : ℝ) ≤ Real.log x := by
    have hx3 : (3 : ℝ) ≤ (x : ℝ) := by
      exact_mod_cast (le_trans (by norm_num : 3 ≤ 128) hx128)
    have he : Real.exp 1 ≤ (x : ℝ) := by linarith [Real.exp_one_lt_three]
    have h := Real.log_le_log (Real.exp_pos 1) he
    rwa [Real.log_exp] at h
  have hlogx0 : (0 : ℝ) < Real.log x := lt_of_lt_of_le zero_lt_one hlogx1
  have hlogadd1 : (1 : ℝ) ≤ Real.log ((x : ℝ) + 2) := by
    have h5 : Real.exp 1 ≤ (x : ℝ) + 2 := by linarith [Real.exp_one_lt_three]
    have h := Real.log_le_log (Real.exp_pos 1) h5
    rwa [Real.log_exp] at h
  have hlogt1 : (1 : ℝ) ≤ Real.log ((t : ℝ) + 2) := by
    have h3 : (3 : ℝ) ≤ (t : ℝ) + 2 := by linarith [ht4]
    have he : Real.exp 1 ≤ (t : ℝ) + 2 := by linarith [Real.exp_one_lt_three]
    have h := Real.log_le_log (Real.exp_pos 1) he
    rwa [Real.log_exp] at h
  have hlogt_le : Real.log ((t : ℝ) + 2) ≤ Real.log ((x : ℝ) + 2) :=
    Real.log_le_log (by positivity) (by linarith)
  -- threshold consequences
  have h2sqrt2 : 2 * Real.sqrt 2 ≤ (x : ℝ) ^ ((1 : ℝ) / 480) := by
    have h := hY2 x hxY2
    simpa using h
  have h4pow : (16 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 60) := by
    have h := hY3 x hxY3
    simpa using h
  have h45log : ((2 : ℝ) ^ (45 : ℕ)) ≤ Real.log x := by
    have h := hY5 x hxY5
    simp only [pow_zero, mul_one] at h
    have h2 : Real.log (Real.exp ((2 : ℝ) ^ (45 : ℕ))) ≤ Real.log x :=
      Real.log_le_log (Real.exp_pos _) (by simpa using h)
    rwa [Real.log_exp] at h2
  have hlog2le : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hxR2
  have hpow45 : ((2 : ℝ) ^ (45 : ℕ)) * (Real.log x) ^ (45 : ℕ) ≤ (Real.log x) ^ (46 : ℕ) := by
    have h1 : (2 : ℝ) ^ (45 : ℕ) ≤ Real.log x := h45log
    calc ((2 : ℝ) ^ (45 : ℕ)) * (Real.log x) ^ (45 : ℕ)
        ≤ (Real.log x) * (Real.log x) ^ (45 : ℕ) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = (Real.log x) ^ (46 : ℕ) := by ring
  -- `(log(x+2))^{2β} ≤ x^{1/60}`
  have hthr : (Real.log ((x : ℝ) + 2)) ^ (2 * β) ≤ (x : ℝ) ^ ((1 : ℝ) / 60) := by
    have h2 := hY1 x hxY1
    have h3 : (Real.log ((x : ℝ) + 2)) ^ (2 * β)
        ≤ (Real.log ((x : ℝ) + 2)) ^ (⌈2 * β⌉₊ : ℕ) := by
      have h4 := Real.rpow_le_rpow_of_exponent_le hlogadd1 (Nat.le_ceil (2 * β))
      rwa [Real.rpow_natCast] at h4
    linarith
  have hlogβx : (Real.log ((x : ℝ) + 2)) ^ β ≤ (x : ℝ) ^ ((1 : ℝ) / 120) := by
    have h2 : ((Real.log ((x : ℝ) + 2)) ^ β) ^ 2 = (Real.log ((x : ℝ) + 2)) ^ (2 * β) := by
      rw [← Real.rpow_natCast ((Real.log ((x : ℝ) + 2)) ^ β) 2,
        ← Real.rpow_mul (le_trans zero_le_one hlogadd1)]
      congr 1
      ring
    have h3 : ((Real.log ((x : ℝ) + 2)) ^ β) ^ 2 ≤ (x : ℝ) ^ ((1 : ℝ) / 60) := by
      rw [h2]; exact hthr
    have h4 : (x : ℝ) ^ ((1 : ℝ) / 60) = ((x : ℝ) ^ ((1 : ℝ) / 120)) ^ 2 := by
      rw [← Real.rpow_natCast ((x : ℝ) ^ ((1 : ℝ) / 120)) 2, ← Real.rpow_mul hx0.le]
      congr 1
      norm_num
    rw [h4] at h3
    have hA0 : (0 : ℝ) ≤ (Real.log ((x : ℝ) + 2)) ^ β := Real.rpow_nonneg (by linarith) _
    have hB0 : (0 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 120) := Real.rpow_nonneg hx0.le _
    nlinarith [h3, hA0, hB0]
  -- the split point
  set v : ℝ := (t : ℝ) ^ ((1 : ℝ) / 3) * (Real.log ((t : ℝ) + 2)) ^ β with hvdef
  set ν₀ : ℕ := ⌈v⌉₊ with hν₀def
  set ν₁ : ℕ := max L ν₀ with hν₁def
  have hv0 : 0 ≤ v := mul_nonneg (Real.rpow_nonneg htR0.le _) (Real.rpow_nonneg (by positivity) _)
  have hν₀low : v ≤ (ν₀ : ℝ) := Nat.le_ceil v
  have hLν₁ : L ≤ ν₁ := le_max_left _ _
  have hν₀ν₁ : ν₀ ≤ ν₁ := le_max_right _ _
  -- `v ≤ x^{41/120}` and `v² ≤ x^{41/60}`
  have hv_le : v ≤ (x : ℝ) ^ ((41 : ℝ) / 120) := by
    have h1 : (Real.log ((t : ℝ) + 2)) ^ β ≤ (x : ℝ) ^ ((1 : ℝ) / 120) :=
      le_trans (Real.rpow_le_rpow (le_trans zero_le_one hlogt1) hlogt_le hβ0) hlogβx
    have h2 : v ≤ (t : ℝ) ^ ((1 : ℝ) / 3) * (x : ℝ) ^ ((1 : ℝ) / 120) := by
      rw [hvdef]
      exact mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg htR0.le _)
    have h3 : (t : ℝ) ^ ((1 : ℝ) / 3) * (x : ℝ) ^ ((1 : ℝ) / 120)
        ≤ (x : ℝ) ^ ((1 : ℝ) / 3) * (x : ℝ) ^ ((1 : ℝ) / 120) :=
      mul_le_mul_of_nonneg_right (Real.rpow_le_rpow htR0.le htxR (by norm_num))
        (Real.rpow_nonneg hx0.le _)
    have h4 : (x : ℝ) ^ ((1 : ℝ) / 3) * (x : ℝ) ^ ((1 : ℝ) / 120) = (x : ℝ) ^ ((41 : ℝ) / 120) := by
      rw [← Real.rpow_add hx0]; congr 1; norm_num
    linarith
  have hv_sq_le : v ^ 2 ≤ (x : ℝ) ^ ((41 : ℝ) / 60) := by
    rw [hvdef]
    have h1 : ((t : ℝ) ^ ((1 : ℝ) / 3) * (Real.log ((t : ℝ) + 2)) ^ β) ^ 2
        = (t : ℝ) ^ ((2 : ℝ) / 3) * ((Real.log ((t : ℝ) + 2)) ^ β) ^ 2 := by
      rw [mul_pow, ← Real.rpow_natCast ((t : ℝ) ^ ((1 : ℝ) / 3)) 2, ← Real.rpow_mul htR0.le]
      congr 2
      norm_num
    rw [h1]
    have h2 : ((Real.log ((t : ℝ) + 2)) ^ β) ^ 2 ≤ ((x : ℝ) ^ ((1 : ℝ) / 120)) ^ 2 :=
      pow_le_pow_left₀ (by positivity)
        (le_trans (Real.rpow_le_rpow (le_trans zero_le_one hlogt1) hlogt_le hβ0) hlogβx) 2
    have h3 : ((x : ℝ) ^ ((1 : ℝ) / 120)) ^ 2 = (x : ℝ) ^ ((1 : ℝ) / 60) := by
      rw [← Real.rpow_natCast ((x : ℝ) ^ ((1 : ℝ) / 120)) 2, ← Real.rpow_mul hx0.le]
      congr 1
      norm_num
    have h4 : (t : ℝ) ^ ((2 : ℝ) / 3) ≤ (x : ℝ) ^ ((2 : ℝ) / 3) :=
      Real.rpow_le_rpow htR0.le htxR (by norm_num)
    calc (t : ℝ) ^ ((2 : ℝ) / 3) * ((Real.log ((t : ℝ) + 2)) ^ β) ^ 2
        ≤ (x : ℝ) ^ ((2 : ℝ) / 3) * (x : ℝ) ^ ((1 : ℝ) / 60) :=
          mul_le_mul h4 (le_trans h2 (le_of_eq h3)) (by positivity)
            (Real.rpow_nonneg hx0.le _)
      _ = (x : ℝ) ^ ((41 : ℝ) / 60) := by
          rw [← Real.rpow_add hx0]; congr 1; norm_num
  -- `ν₀ ≤ t.sqrt`
  have hx64' : 64 ≤ x := le_trans (by norm_num : 64 ≤ 128) hx128
  have hν₀_sqrt : ν₀ ≤ t.sqrt := by
    -- `x^{41/120} ≤ t^{1/2}/2`
    have h4 : (x : ℝ) ^ ((11 : ℝ) / 16) / 2 ≤ (t : ℝ) :=
      le_trans (half_rpow_le_Rcut hx64') (by exact_mod_cast hDt)
    have h5 : ((x : ℝ) ^ ((11 : ℝ) / 16) / 2) ^ ((1 : ℝ) / 2) ≤ (t : ℝ) ^ ((1 : ℝ) / 2) :=
      Real.rpow_le_rpow (by positivity) h4 (by norm_num)
    have h6 : ((x : ℝ) ^ ((11 : ℝ) / 16) / 2) ^ ((1 : ℝ) / 2)
        = (x : ℝ) ^ ((11 : ℝ) / 32) / Real.sqrt 2 := by
      rw [Real.div_rpow (by positivity) (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_eq_rpow,
        ← Real.rpow_mul hx0.le]
      congr 1
      norm_num
    rw [h6] at h5
    have h7 : (x : ℝ) ^ ((41 : ℝ) / 120) ≤ (x : ℝ) ^ ((11 : ℝ) / 32) / (2 * Real.sqrt 2) := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.sqrt 2)]
      have h8 : (x : ℝ) ^ ((11 : ℝ) / 32)
          = (x : ℝ) ^ ((41 : ℝ) / 120) * (x : ℝ) ^ ((1 : ℝ) / 480) := by
        rw [← Real.rpow_add hx0]; congr 1; norm_num
      rw [h8]
      exact mul_le_mul_of_nonneg_left h2sqrt2 (Real.rpow_nonneg hx0.le _)
    have h9 : (x : ℝ) ^ ((11 : ℝ) / 32) / (2 * Real.sqrt 2)
        ≤ (t : ℝ) ^ ((1 : ℝ) / 2) / 2 := by
      have h10 : (x : ℝ) ^ ((11 : ℝ) / 32) / (2 * Real.sqrt 2)
          = (x : ℝ) ^ ((11 : ℝ) / 32) / Real.sqrt 2 / 2 := by ring
      rw [h10]
      linarith [h5]
    have h11 : v ≤ (t : ℝ) ^ ((1 : ℝ) / 2) / 2 := le_trans hv_le (le_trans h7 h9)
    have h12 : (ν₀ : ℝ) < v + 1 := Nat.ceil_lt_add_one hv0
    have h13 : (ν₀ : ℝ) ^ 2 < (t : ℝ) := by
      have h14 : (t : ℝ) ^ ((1 : ℝ) / 2) / 2 + 1 ≤ (t : ℝ) ^ ((1 : ℝ) / 2) := by
        have h15 : (2 : ℝ) ≤ (t : ℝ) ^ ((1 : ℝ) / 2) := by
          have h16 : (4 : ℝ) ^ ((1 : ℝ) / 2) ≤ (t : ℝ) ^ ((1 : ℝ) / 2) :=
            Real.rpow_le_rpow (by norm_num) ht4 (by norm_num)
          have h17 : (4 : ℝ) ^ ((1 : ℝ) / 2) = 2 := by norm_num
          linarith
        linarith
      have h18 : ((t : ℝ) ^ ((1 : ℝ) / 2)) ^ 2 = (t : ℝ) := by
        rw [← Real.rpow_natCast ((t : ℝ) ^ ((1 : ℝ) / 2)) 2, ← Real.rpow_mul htR0.le]
        norm_num
      nlinarith [h12, h11, h14, h18, sq_nonneg ((t : ℝ) ^ ((1 : ℝ) / 2) - 1)]
    rw [Nat.le_sqrt]
    have h19 : (ν₀ * ν₀ : ℕ) = ν₀ ^ 2 := by ring
    rw [h19]
    exact_mod_cast le_of_lt h13
  -- `ν₀² < R3cut x`
  have hν₀_sq : (ν₀ : ℝ) ^ 2 < (Submission.X2Y4R3.R3cut x : ℝ) := by
    have h1 : v ^ 2 ≤ (Submission.X2Y4R3.R3cut x : ℝ) / 8 := by
      have h3 : (x : ℝ) ^ ((7 : ℝ) / 10) - 1 < (Submission.X2Y4R3.R3cut x : ℝ) := by
        rw [Submission.X2Y4R3.R3cut]
        have h6 : (1 : ℝ) ≤ (Real.log x) ^ ((2 : ℝ) ^ 25) :=
          Real.one_le_rpow hlogx1 (by norm_num)
        have h7 : (x : ℝ) ^ ((7 : ℝ) / 10)
            ≤ (x : ℝ) ^ ((7 : ℝ) / 10) * (Real.log x) ^ ((2 : ℝ) ^ 25) := by
          calc (x : ℝ) ^ ((7 : ℝ) / 10) = (x : ℝ) ^ ((7 : ℝ) / 10) * 1 := by ring
            _ ≤ (x : ℝ) ^ ((7 : ℝ) / 10) * (Real.log x) ^ ((2 : ℝ) ^ 25) :=
                mul_le_mul_of_nonneg_left h6 (Real.rpow_nonneg hx0.le _)
        have h8 := Nat.lt_floor_add_one
          ((x : ℝ) ^ ((7 : ℝ) / 10) * (Real.log x) ^ ((2 : ℝ) ^ 25))
        push_cast at h8
        linarith
      have h8 : (x : ℝ) ^ ((41 : ℝ) / 60) * 16 ≤ (x : ℝ) ^ ((7 : ℝ) / 10) := by
        calc (x : ℝ) ^ ((41 : ℝ) / 60) * 16
            ≤ (x : ℝ) ^ ((41 : ℝ) / 60) * (x : ℝ) ^ ((1 : ℝ) / 60) :=
              mul_le_mul_of_nonneg_left h4pow (Real.rpow_nonneg hx0.le _)
          _ = (x : ℝ) ^ ((7 : ℝ) / 10) := by
              rw [← Real.rpow_add hx0]; congr 1; norm_num
      have h10 : (2 : ℝ) ≤ (x : ℝ) ^ ((7 : ℝ) / 10) := by
        have h11 : (2 : ℝ) ≤ (64 : ℝ) ^ ((7 : ℝ) / 10) := two_le_rpow_seven_tenths (by norm_num)
        exact le_trans h11 (Real.rpow_le_rpow (by norm_num) (by exact_mod_cast hx64') (by norm_num))
      have h9''' : (8 : ℝ) * (x : ℝ) ^ ((41 : ℝ) / 60) ≤ (x : ℝ) ^ ((7 : ℝ) / 10) - 1 := by
        have h12 : (8 : ℝ) * (x : ℝ) ^ ((41 : ℝ) / 60)
            = ((x : ℝ) ^ ((41 : ℝ) / 60) * 16) / 2 := by ring
        rw [h12]
        linarith [h8, h10]
      have h9'' : (8 : ℝ) * (x : ℝ) ^ ((41 : ℝ) / 60)
          ≤ (Submission.X2Y4R3.R3cut x : ℝ) := le_trans h9''' (le_of_lt h3)
      have h9' : (x : ℝ) ^ ((41 : ℝ) / 60)
          ≤ (Submission.X2Y4R3.R3cut x : ℝ) / 8 := by
        rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 8)]
        simpa [mul_comm] using h9''
      linarith [h9', hv_sq_le]
    have hA8 : (8 : ℝ) ≤ (Submission.X2Y4R3.R3cut x : ℝ) := by
      rw [Submission.X2Y4R3.R3cut]
      have h13 : (9 : ℝ) ≤ (x : ℝ) ^ ((7 : ℝ) / 10) := by
        have h14 := hY6 x hxY6
        simpa using h14
      have h15 : (1 : ℝ) ≤ (Real.log x) ^ ((2 : ℝ) ^ 25) :=
        Real.one_le_rpow hlogx1 (by norm_num)
      have h16 : (9 : ℝ) ≤ (x : ℝ) ^ ((7 : ℝ) / 10) * (Real.log x) ^ ((2 : ℝ) ^ 25) :=
        le_trans h13 (le_mul_of_one_le_right (Real.rpow_nonneg hx0.le _) h15)
      have h17 := Nat.lt_floor_add_one ((x : ℝ) ^ ((7 : ℝ) / 10) * (Real.log x) ^ ((2 : ℝ) ^ 25))
      push_cast at h17
      have h18 : (8 : ℝ) ≤ ((⌊(x : ℝ) ^ ((7 : ℝ) / 10)
          * (Real.log x) ^ ((2 : ℝ) ^ 25)⌋₊ : ℕ) : ℝ) := by linarith
      exact_mod_cast h18
    exact ceil_sq_lt hA8 hv0 h1
  -- `ν₁` bounds
  have hν₁_sqrt : ν₁ ≤ t.sqrt := by
    rw [hν₁def]
    exact max_le (le_of_lt hLt) hν₀_sqrt
  have hν₁_sq : ν₁ ^ 2 < Submission.X2Y4R3.R3cut x := by
    rw [hν₁def]
    have hmax : max L ν₀ ^ 2 = max (L ^ 2) (ν₀ ^ 2) := by
      rcases le_total L ν₀ with h | h
      · rw [max_eq_right h, max_eq_right (pow_le_pow_left₀ (Nat.zero_le L) h 2)]
      · rw [max_eq_left h, max_eq_left (pow_le_pow_left₀ (Nat.zero_le ν₀) h 2)]
    rw [hmax]
    refine max_lt ?_ ?_
    · exact lt_of_lt_of_le (by nlinarith : L ^ 2 < (L + 1) ^ 2) (le_of_lt hLsq)
    · have h4 : ((ν₀ ^ 2 : ℕ) : ℝ) = (ν₀ : ℝ) ^ 2 := by push_cast; ring
      have h5 : ((ν₀ ^ 2 : ℕ) : ℝ) < (Submission.X2Y4R3.R3cut x : ℝ) := by
        rw [h4]; exact hν₀_sq
      exact_mod_cast h5
  -- the `(log x)^{(β-71)/4} ≤ √L` comparison
  have hexp_le : (β - 71) / 4 ≤ 4 * lam + 50 := by
    rw [hβdef, hlammdef]
    linarith [hcomp, hB2]
  have hLbsqrt : (Real.log x) ^ ((β - 71) / 4) ≤ Real.sqrt (L : ℝ) := by
    have h1 : (Real.log x) ^ (4 * lam + 50) ≤ Real.sqrt (L : ℝ) := by
      rw [Real.le_sqrt (Real.rpow_nonneg hlogx0.le _) (Nat.cast_nonneg L)]
      have h2 : ((Real.log x) ^ (4 * lam + 50)) ^ 2 = (Real.log x) ^ (8 * lam + 100) := by
        rw [← Real.rpow_natCast ((Real.log x) ^ (4 * lam + 50)) 2,
          ← Real.rpow_mul hlogx0.le]
        congr 1
        ring
      rw [h2]; exact hLbig
    exact le_trans (Real.rpow_le_rpow_of_exponent_le hlogx1 hexp_le) h1
  -- apply `FI_Ad_sqrt_le`
  have hS1 : (∑ ν ∈ ((Finset.Icc (L + 1) t.sqrt).filter Squarefree), Ad FIa (ν ^ 2) t)
      ≤ Clim * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lamm) := by
    have h := hAd x hxXlim t L ν₁ ht htx hDt hL1 hLν₁ hν₁_sqrt hν₁_sq
      (le_trans hν₀low (by exact_mod_cast hν₀ν₁)) hLbsqrt
    rwa [show (β - 71) / 4 = lamm from by rw [hβdef]; ring] at h
  -- the `X`-term vanishes
  have hsq0 : ∀ n ∈ Finset.Icc 1 t, sqdvCount n (t.sqrt + 1) t = 0 := by
    intro n hn
    rw [sqdvCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro ν hν hdvd
    rw [Finset.mem_filter] at hν
    obtain ⟨hν1, _⟩ := hν
    obtain ⟨hν1a, hν1b⟩ := Finset.mem_Icc.mp hν1
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hn2 : n ≤ t := (Finset.mem_Icc.mp hn).2
    have h2 : ν ^ 2 ≤ n := Nat.le_of_dvd (by omega) hdvd
    have h3 : t < (t.sqrt + 1) ^ 2 := by
      have h4 : t < t.sqrt.succ * t.sqrt.succ := Nat.lt_succ_sqrt t
      have h5 : t.sqrt.succ = t.sqrt + 1 := rfl
      rw [h5] at h4
      simpa [pow_two] using h4
    have h6 : (t.sqrt + 1) ^ 2 ≤ ν ^ 2 := Nat.pow_le_pow_left hν1a 2
    omega
  have hX0 : (∑ n ∈ Finset.Icc 1 t, ((n.divisors.card : ℝ)) ^ (3 : ℕ)
      * (sqdvCount n (t.sqrt + 1) t : ℝ)) ≤ 0 := by
    have hzero : (∑ n ∈ Finset.Icc 1 t, ((n.divisors.card : ℝ)) ^ (3 : ℕ)
        * (sqdvCount n (t.sqrt + 1) t : ℝ)) = 0 := by
      refine Finset.sum_eq_zero (fun n hn => ?_)
      rw [hsq0 n hn, Nat.cast_zero, mul_zero]
    rw [hzero]
  -- apply `Etwo_le`
  have hE := Etwo_le FIa FIg (fun n => FIa_nonneg n) t (D) L t.sqrt
    (by omega) hLt (Nat.sqrt_le_self t) hX0 hS1 (hS2 x hxX2 t (by omega) htx)
    (hGle x t (D) L (by omega) htx hD1 hDx hL1)
  -- the final assembly
  have hS1nn : (0 : ℝ) ≤ Clim * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lamm) := by positivity
  have hS2nn : (0 : ℝ) ≤ C2 * (Submission.Aseq x : ℝ) * (Real.log x) ^ B2 := by positivity
  have hsqrt0 : Real.sqrt (0 : ℝ) = 0 := Real.sqrt_zero
  have hA2nn : (0 : ℝ) ≤ ∑ n ∈ Finset.Icc 1 t, FIa n ^ 2 :=
    Finset.sum_nonneg (fun n _ => sq_nonneg _)
  have hstep : Etwo FIa FIg t (D) L ≤ Real.sqrt (Clim * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lamm)) * Real.sqrt (C2 * (Submission.Aseq x : ℝ) * (Real.log x) ^ B2) + Cg * (Submission.Aseq x : ℝ) * (Real.log ((x : ℝ) + 2)) ^ 5 * (Real.log ((L : ℝ) + 2)) ^ 32 / (L : ℝ) := by
    refine le_trans hE (le_of_eq ?_)
    rw [Real.sqrt_zero, mul_zero, add_zero]
  -- bound the two terms
  have hterm1 : Real.sqrt (Clim * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lamm))
        * Real.sqrt (C2 * (Submission.Aseq x : ℝ) * (Real.log x) ^ B2)
      ≤ Real.sqrt (Clim * C2) * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lam) := by
    have hS1nn : (0 : ℝ) ≤ Clim * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lamm) := by positivity
    have hS2nn : (0 : ℝ) ≤ C2 * (Submission.Aseq x : ℝ) * (Real.log x) ^ B2 := by positivity
    rw [(Real.sqrt_mul hS1nn (C2 * (Submission.Aseq x : ℝ) * (Real.log x) ^ B2)).symm]
    have hprod : Clim * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lamm)
          * (C2 * (Submission.Aseq x : ℝ) * (Real.log x) ^ B2)
        = Clim * C2 * (Submission.Aseq x : ℝ) ^ 2 * (Real.log x) ^ (B2 - lamm) := by
      have h1 : (Real.log x) ^ (-lamm) * (Real.log x) ^ B2 = (Real.log x) ^ (B2 - lamm) := by
        rw [← Real.rpow_add hlogx0]; ring_nf
      rw [← h1]; ring
    rw [hprod]
    have hA0 : (0 : ℝ) ≤ Clim * C2 := by positivity
    have hB0 : (0 : ℝ) ≤ (Submission.Aseq x : ℝ) ^ 2 := by positivity
    have hC0 : (0 : ℝ) ≤ (Real.log x) ^ (B2 - lamm) := by positivity
    rw [show Clim * C2 * (Submission.Aseq x : ℝ) ^ 2 * (Real.log x) ^ (B2 - lamm)
        = Clim * C2 * ((Submission.Aseq x : ℝ) ^ 2 * (Real.log x) ^ (B2 - lamm)) from by ring]
    rw [Real.sqrt_mul hA0 ((Submission.Aseq x : ℝ) ^ 2 * (Real.log x) ^ (B2 - lamm)),
      Real.sqrt_mul hB0 ((Real.log x) ^ (B2 - lamm)), Real.sqrt_sq (Nat.cast_nonneg _)]
    have hCsqrt : Real.sqrt ((Real.log x) ^ (B2 - lamm)) = (Real.log x) ^ ((B2 - lamm) / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hlogx0.le]
      congr 1
      ring
    rw [hCsqrt]
    have hexp : (B2 - lamm) / 2 ≤ -lam := by
      rw [hlammdef]
      ring_nf
      linarith
    have hgoal : (Real.log x) ^ ((B2 - lamm) / 2) ≤ (Real.log x) ^ (-lam) :=
      Real.rpow_le_rpow_of_exponent_le hlogx1 hexp
    refine le_trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hgoal (Nat.cast_nonneg _)) (Real.sqrt_nonneg _)) (le_of_eq ?_)
    ring
  have hterm2 : Cg * (Submission.Aseq x : ℝ) * (Real.log ((x : ℝ) + 2)) ^ 5
        * (Real.log ((L : ℝ) + 2)) ^ 32 / (L : ℝ)
      ≤ Cg * (2 : ℝ) ^ (37 : ℕ) * ((Submission.Aseq x : ℝ) * (Real.log x) ^ (-lam)) := by
    have hlog2 : Real.log ((x : ℝ) + 2) ≤ 2 * Real.log x := by
      have h13 : Real.log ((x : ℝ) + 2) ≤ Real.log (2 * (x : ℝ)) :=
        Real.log_le_log (by positivity) (by linarith)
      rw [Real.log_mul (by norm_num) hx0.ne'] at h13
      linarith [Real.log_two_lt_d9]
    have hlogL : Real.log ((L : ℝ) + 2) ≤ 2 * Real.log x := by
      have h14 : (L : ℝ) + 2 ≤ (x : ℝ) + 2 := by
        have h15 : (L : ℝ) ≤ (t : ℝ) :=
          le_trans (le_of_lt (by exact_mod_cast hLt)) (Nat.cast_le.mpr (Nat.sqrt_le_self t))
        have h16 : (t : ℝ) ≤ (x : ℝ) := by exact_mod_cast htx
        linarith
      exact le_trans (Real.log_le_log (by positivity) h14) hlog2
    have hL2 : (0 : ℝ) ≤ Real.log ((L : ℝ) + 2) := Real.log_nonneg (by linarith)
    have hx2 : (0 : ℝ) ≤ Real.log ((x : ℝ) + 2) := Real.log_nonneg (by linarith)
    have hxl : (0 : ℝ) ≤ 2 * Real.log x := by linarith
    have h5b : (Real.log ((x : ℝ) + 2)) ^ 5 ≤ (2 * Real.log x) ^ 5 :=
      pow_le_pow_left₀ hx2 hlog2 5
    have h32b : (Real.log ((L : ℝ) + 2)) ^ 32 ≤ (2 * Real.log x) ^ 32 :=
      pow_le_pow_left₀ hL2 hlogL 32
    have hprod : (Real.log ((x : ℝ) + 2)) ^ 5 * (Real.log ((L : ℝ) + 2)) ^ 32
        ≤ (2 * Real.log x) ^ 37 :=
      le_trans (mul_le_mul h5b h32b (pow_nonneg hL2 32) (pow_nonneg hxl 5))
        (le_of_eq (by rw [← pow_add]))
    have h2nn : (0 : ℝ) ≤ (2 * Real.log x) ^ 37 := pow_nonneg hxl 37
    have h2pow : (2 * Real.log x) ^ 37 = (2 : ℝ) ^ 37 * (Real.log x) ^ 37 := by rw [mul_pow]
    have hClog : (0 : ℝ) ≤ Cg * (Submission.Aseq x : ℝ) := by positivity
    have hLinv : (1 : ℝ) / (L : ℝ) ≤ (Real.log x) ^ (-(4 * lam + 100)) := by
      have h1 : (Real.log x) ^ (4 * lam + 100) ≤ (L : ℝ) :=
        le_trans (Real.rpow_le_rpow_of_exponent_le hlogx1 (by linarith [hB2, hcomp])) hLbig
      have h2 : (0 : ℝ) < (Real.log x) ^ (4 * lam + 100) := Real.rpow_pos_of_pos hlogx0 _
      rw [one_div, Real.rpow_neg hlogx0.le]
      exact (inv_le_inv₀ hL0 h2).mpr h1
    have hLpos' : (0 : ℝ) ≤ 1 / (L : ℝ) := by positivity
    have hstep1 : Cg * (Submission.Aseq x : ℝ) * (Real.log ((x : ℝ) + 2)) ^ 5
          * (Real.log ((L : ℝ) + 2)) ^ 32 / (L : ℝ)
        = Cg * (Submission.Aseq x : ℝ)
          * ((Real.log ((x : ℝ) + 2)) ^ 5 * (Real.log ((L : ℝ) + 2)) ^ 32) * (1 / (L : ℝ)) := by
      rw [div_eq_mul_one_div]; ring
    have hstep2 : Cg * (Submission.Aseq x : ℝ)
          * ((Real.log ((x : ℝ) + 2)) ^ 5 * (Real.log ((L : ℝ) + 2)) ^ 32) * (1 / (L : ℝ))
        ≤ Cg * (Submission.Aseq x : ℝ)
          * ((2 * Real.log x) ^ 37 * (Real.log x) ^ (-(4 * lam + 100))) := by
      refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_left
        (mul_le_mul hprod hLinv hLpos' h2nn) hClog)
      ring
    have hstep3 : Cg * (Submission.Aseq x : ℝ)
          * ((2 * Real.log x) ^ 37 * (Real.log x) ^ (-(4 * lam + 100)))
        = Cg * (2 : ℝ) ^ 37 * (Submission.Aseq x : ℝ)
          * ((Real.log x) ^ (37 : ℕ) * (Real.log x) ^ (-(4 * lam + 100))) := by
      rw [h2pow]; ring
    have h37 : (Real.log x) ^ (37 : ℕ) * (Real.log x) ^ (-(4 * lam + 100))
        ≤ (Real.log x) ^ (-lam) := by
      rw [← Real.rpow_natCast (Real.log x) 37, ← Real.rpow_add hlogx0]
      refine Real.rpow_le_rpow_of_exponent_le hlogx1 ?_
      have hc := hcomp
      push_cast
      linarith [hB2, hc]
    have h17 : (0 : ℝ) ≤ Cg * (2 : ℝ) ^ 37 := by positivity
    have h17b : (0 : ℝ) ≤ Cg * (2 : ℝ) ^ 37 * (Submission.Aseq x : ℝ) := by positivity
    have hstep4 : Cg * (2 : ℝ) ^ 37 * (Submission.Aseq x : ℝ)
          * ((Real.log x) ^ (37 : ℕ) * (Real.log x) ^ (-(4 * lam + 100)))
        ≤ Cg * (2 : ℝ) ^ 37 * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lam) :=
      mul_le_mul_of_nonneg_left h37 h17b
    have hstep5 : Cg * (2 : ℝ) ^ 37 * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lam)
        = Cg * (2 : ℝ) ^ (37 : ℕ) * ((Submission.Aseq x : ℝ) * (Real.log x) ^ (-lam)) := by ring
    exact le_trans (le_of_eq hstep1) (le_trans hstep2 (le_trans (le_of_eq hstep3)
      (le_trans hstep4 (le_of_eq hstep5))))
  refine le_trans hstep ?_
  refine le_trans (add_le_add hterm1 hterm2) ?_
  have hA0 : (0 : ℝ) ≤ (Submission.Aseq x : ℝ) := Nat.cast_nonneg _
  have h20 : (0 : ℝ) ≤ (Real.log x) ^ (-lam) := by positivity
  have hQ : (0 : ℝ) ≤ (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lam) := mul_nonneg hA0 h20
  have h21 : (0 : ℝ) ≤ Real.sqrt (Clim * C2) := Real.sqrt_nonneg _
  have h22 : (0 : ℝ) ≤ Cg * (2 : ℝ) ^ (37 : ℕ) := by positivity
  nlinarith [hQ, h21, h22]

/-! ### The elementary comparisons of the cutoffs -/

/-- `⌈x^{7/10}⌉ ≤ x` for `x ≥ 1`. -/
theorem ceil_rpow_710_le_self {x : ℕ} (hx : 1 ≤ x) :
    ⌈(x : ℝ) ^ ((7 : ℝ) / 10)⌉₊ ≤ x := by
  refine Nat.ceil_le.mpr ?_
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  calc (x : ℝ) ^ ((7 : ℝ) / 10) ≤ (x : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
    _ = (x : ℝ) := Real.rpow_one _

/-- `Rcut x = ⌊x^{11/16}⌋ ≤ ⌈x^{7/10}⌉` for `x ≥ 2`. -/
theorem Rcut_le_ceil_rpow_710 {x : ℕ} (hx : 2 ≤ x) :
    Submission.Rcut x ≤ ⌈(x : ℝ) ^ ((7 : ℝ) / 10)⌉₊ := by
  have hx0 : (0 : ℝ) ≤ (x : ℝ) := Nat.cast_nonneg _
  have hx1 : (1 : ℝ) < (x : ℝ) := by exact_mod_cast hx
  rw [Submission.Rcut]
  have h1 : ((⌊(x : ℝ) ^ ((11 : ℝ) / 16)⌋₊ : ℕ) : ℝ) ≤ (x : ℝ) ^ ((11 : ℝ) / 16) :=
    Nat.floor_le (Real.rpow_nonneg hx0 _)
  have h2 : (x : ℝ) ^ ((11 : ℝ) / 16) < (x : ℝ) ^ ((7 : ℝ) / 10) :=
    Real.rpow_lt_rpow_of_exponent_lt hx1 (by norm_num)
  have h3 : (x : ℝ) ^ ((7 : ℝ) / 10) ≤ ((⌈(x : ℝ) ^ ((7 : ℝ) / 10)⌉₊ : ℕ) : ℝ) :=
    Nat.le_ceil _
  have hlt : ((⌊(x : ℝ) ^ ((11 : ℝ) / 16)⌋₊ : ℕ) : ℝ)
      < ((⌈(x : ℝ) ^ ((7 : ℝ) / 10)⌉₊ : ℕ) : ℝ) := by linarith
  exact Nat.le_of_lt (by exact_mod_cast hlt)

/-- `1 ≤ ⌈x^{7/10}⌉` for `x ≥ 1`. -/
theorem one_le_ceil_rpow_710 {x : ℕ} (hx : 1 ≤ x) :
    1 ≤ ⌈(x : ℝ) ^ ((7 : ℝ) / 10)⌉₊ := by
  refine Nat.one_le_ceil_iff.mpr ?_
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have h0 : (0 : ℝ) < (x : ℝ) := lt_of_lt_of_le zero_lt_one hx1
  exact Real.rpow_pos_of_pos h0 _

/-! ### The requested instance `D = ⌈x^{7/10}⌉` -/

theorem Etwo_le_at_07 (B2 C2 lam : ℝ) (hC2 : 0 < C2) (hB2 : 0 ≤ B2) (hcomp : B2 ≤ 2 * lam) (X2 : ℕ)
    (hS2 : ∀ x : ℕ, X2 ≤ x → ∀ t : ℕ, 2 ≤ t → t ≤ x →
      (∑ n ∈ Finset.Icc 1 t, Submission.ASP.FIa n * ((n.divisors.card : ℝ)) ^ (3 : ℕ))
        ≤ C2 * (Submission.Aseq x : ℝ) * (Real.log (x : ℝ)) ^ B2) :
    ∃ X₀ : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ x : ℕ, X₀ ≤ x → ∀ t : ℕ, ∀ L : ℕ,
      2 ≤ t → t ≤ x → ⌈(x : ℝ) ^ ((7 : ℝ) / 10)⌉₊ ≤ t → 1 ≤ L → L < t.sqrt →
      (L + 1) ^ 2 < Submission.X2Y4R3.R3cut x →
      (Real.log (x : ℝ)) ^ (8 * lam + 100) ≤ (L : ℝ) →
      Submission.ASP.Etwo Submission.ASP.FIa Submission.ASP.FIg t (⌈(x : ℝ) ^ ((7 : ℝ) / 10)⌉₊) L
        ≤ C * (Submission.Aseq x : ℝ) * (Real.log (x : ℝ)) ^ (-lam) := by
  obtain ⟨Xg, C, hC, hgen⟩ :=
    Etwo_le_generalD B2 C2 lam hC2 hB2 hcomp X2 hS2
  refine ⟨max Xg 2, C, hC, ?_⟩
  intro x hx t L ht2 htx hDt hL1 hLt hLsq hLbig
  have hxg : Xg ≤ x := by omega
  have hx2 : 2 ≤ x := by omega
  have hx1 : 1 ≤ x := by omega
  have hRt : Submission.Rcut x ≤ t :=
    le_trans (Rcut_le_ceil_rpow_710 hx2) hDt
  have hD1 : 1 ≤ ⌈(x : ℝ) ^ ((7 : ℝ) / 10)⌉₊ := one_le_ceil_rpow_710 hx1
  have hDx : ⌈(x : ℝ) ^ ((7 : ℝ) / 10)⌉₊ ≤ x := ceil_rpow_710_le_self hx1
  exact hgen x hxg t ⌈(x : ℝ) ^ ((7 : ℝ) / 10)⌉₊ L ht2 htx hRt hD1 hDx hL1 hLt hLsq hLbig


end

end Work.FIChain
