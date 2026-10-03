/-
# `Work.FIChain.rtildeFull_D7_le` — `(R′)` for `ã` at the cut-off `D₇(x) = ⌈x^{7/10}⌉`

The `τ⁰`-weighted `(R′)`-estimate for the honest remainder `r̃_full = r̃ + A·gtail` of the
squarefree-supported sequence `ã`, at the modulus cut-off `⌈x^{7/10}⌉` (rather than
`Rcut x = ⌊x^{11/16}⌋` of `Submission.ASP.S38`).

The proof is the one of `Submission.ASP.FI_rtildeFull_sum_le` with the modulus kept general:
the §9 split point is taken *polylogarithmic*, `L = ⌈(log x)^M⌉`, so that

* `D₇·L² + 1 ≤ x^{141/200}` — the hypothesis of the `E₁`-input `Eone_le_at_07`;
* `(log x)^{8λ+100} ≤ L` — the hypothesis of the `E₂`-input `Etwo_le_at_07`;
* `D₇ ≤ m` (from the statement) makes the `τ⁰`-`ν`-sum `T` (`Submission.ASP.FIr_T_le`) and the
  density tail (`Submission.ASP.FI_gtail_sum_le`) applicable;

the assembly is `Submission.ASP.Rtilde_sum_le_signed_of_inputs` + `RtildeFull_sum_le`, and the
last term is absorbed into `A(x)(log x)^{-λ}` by `poly_tail_le` (the power `x^{7/10}` still beats
`A(x) ≍ x^{3/4}`).

It contains no unfinished proofs and no additional assumptions.
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
import Submission.Work.FIChain.Eone_le_at_07
import Submission.Work.FIChain.Etwo_le_at_07

set_option maxHeartbeats 3200000

namespace Work.FIChain

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The §9 split point `L = ⌈(log x)^M⌉` of the `D₇`-assembly. -/
def Llog (M : ℝ) (x : ℕ) : ℕ := ⌈(Real.log (x : ℝ)) ^ M⌉₊

/-- Thresholds for the split point `L = ⌈(log x)^M⌉` at the cut-off `D₇(x) = ⌈x^{7/10}⌉`:
`(L+1)² ≤ D₇ - 1`, `D₇·L² + 1 ≤ x^{141/200}`, `(log x)^M ≤ L` and `(L+1)² < R3cut x`. -/
theorem exists_Llog_thresholds (M : ℝ) (hM : 0 ≤ M) :
    ∃ X : ℕ, ∀ x : ℕ, X ≤ x →
      1 ≤ Llog M x ∧
      2 ≤ ⌈(x : ℝ) ^ ((7 : ℝ) / 10)⌉₊ ∧
      (Llog M x + 1) ^ 2 + 1 ≤ ⌈(x : ℝ) ^ ((7 : ℝ) / 10)⌉₊ ∧
      ((⌈(x : ℝ) ^ ((7 : ℝ) / 10)⌉₊ * (Llog M x) ^ 2 : ℕ) : ℝ) + 1
        ≤ (x : ℝ) ^ ((141 : ℝ) / 200) ∧
      (Real.log (x : ℝ)) ^ M ≤ (Llog M x : ℝ) ∧
      (Llog M x + 1) ^ 2 < Submission.X2Y4R3.R3cut x := by
  obtain ⟨X₁, -, hT₁⟩ := Commons.Analysis.ExpLog.const_mul_log_pow_le_rpow_threshold
    (K := (10 : ℝ)) (n := 2 * ⌈M⌉₊) (r := (7 : ℝ) / 10) (by norm_num) (by norm_num)
  obtain ⟨X₂, -, hT₂⟩ := Commons.Analysis.ExpLog.const_mul_log_pow_le_rpow_threshold
    (K := (9 : ℝ)) (n := 2 * ⌈M⌉₊) (r := (1 : ℝ) / 200) (by norm_num) (by norm_num)
  refine ⟨max (max ⌈X₁⌉₊ ⌈X₂⌉₊) 100 + 1, fun x hx => ?_⟩
  have hxX₁ : X₁ ≤ (x : ℝ) :=
    le_trans (Nat.le_ceil X₁) (by exact_mod_cast (by omega : ⌈X₁⌉₊ ≤ x))
  have hxX₂ : X₂ ≤ (x : ℝ) :=
    le_trans (Nat.le_ceil X₂) (by exact_mod_cast (by omega : ⌈X₂⌉₊ ≤ x))
  have hx100 : 100 ≤ x := by omega
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (by omega : 1 ≤ x)
  have hx0 : (0 : ℝ) < (x : ℝ) := by linarith
  have hx3 : (3 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (by omega : 3 ≤ x)
  have hlog1 : (1 : ℝ) ≤ Real.log x :=
    le_trans Submission.ASP.one_le_log_three (Real.log_le_log (by norm_num) hx3)
  have hlog0 : (0 : ℝ) < Real.log x := lt_of_lt_of_le zero_lt_one hlog1
  set V : ℝ := (Real.log x) ^ (⌈M⌉₊ : ℕ) with hV
  set Y : ℝ := (Real.log x) ^ (2 * ⌈M⌉₊) with hY
  have hV1 : (1 : ℝ) ≤ V := one_le_pow₀ hlog1
  have hVY : V ^ 2 = Y := by
    rw [hV, hY, pow_two, ← pow_add]
    congr 1
    omega
  have huM : (Real.log x) ^ M ≤ V := by
    rw [hV, ← Real.rpow_natCast (Real.log x) ⌈M⌉₊]
    exact Real.rpow_le_rpow_of_exponent_le hlog1 (Nat.le_ceil M)
  have hu1 : (1 : ℝ) ≤ (Real.log x) ^ M := Real.one_le_rpow hlog1 hM
  have hLub : (Llog M x : ℝ) ≤ (Real.log x) ^ M + 1 := by
    rw [Llog]
    exact le_of_lt (Nat.ceil_lt_add_one (Real.rpow_nonneg hlog0.le M))
  have hL0 : (0 : ℝ) ≤ (Llog M x : ℝ) := Nat.cast_nonneg _
  have hL_ubV : (Llog M x : ℝ) ≤ 2 * V := by linarith
  have hL1 : 1 ≤ Llog M x := by
    rw [Llog]
    exact Nat.one_le_ceil_iff.mpr (lt_of_lt_of_le zero_lt_one hu1)
  have hTL1 : 10 * Y ≤ (x : ℝ) ^ ((7 : ℝ) / 10) := hT₁ (x : ℝ) hxX₁
  have hTL2 : 9 * Y ≤ (x : ℝ) ^ ((1 : ℝ) / 200) := hT₂ (x : ℝ) hxX₂
  have hY1 : (1 : ℝ) ≤ Y := by rw [← hVY]; nlinarith [hV1]
  have hD7_2r : (2 : ℝ) ≤ (x : ℝ) ^ ((7 : ℝ) / 10) := by
    have h64 : (2 : ℝ) ≤ (64 : ℝ) ^ ((7 : ℝ) / 10) :=
      Submission.ASP.two_le_rpow_seven_tenths (by norm_num)
    have hmono : (64 : ℝ) ^ ((7 : ℝ) / 10) ≤ (x : ℝ) ^ ((7 : ℝ) / 10) :=
      Real.rpow_le_rpow (by norm_num) (by exact_mod_cast (by omega : 64 ≤ x)) (by norm_num)
    linarith
  have hD7_2 : 2 ≤ ⌈(x : ℝ) ^ ((7 : ℝ) / 10)⌉₊ := by
    exact_mod_cast (le_trans hD7_2r (Nat.le_ceil _))
  -- `(L+1)² + 1 ≤ x^{7/10}`
  have hsq_le : ((Llog M x : ℝ) + 1) ^ 2 + 1 ≤ (x : ℝ) ^ ((7 : ℝ) / 10) := by
    have h2 : ((Llog M x : ℝ) + 1) ^ 2 ≤ 9 * Y := by
      have h0 : (0 : ℝ) ≤ (Llog M x : ℝ) + 1 := by positivity
      have h3 : ((Llog M x : ℝ) + 1) ^ 2 ≤ (2 * V + 1) ^ 2 := by nlinarith [hL_ubV, h0]
      have h4 : (2 * V + 1) ^ 2 ≤ 9 * V ^ 2 := by nlinarith [hV1]
      rw [hVY] at h4
      linarith
    linarith [h2, hTL1, hY1]
  have hsqD7 : (Llog M x + 1) ^ 2 + 1 ≤ ⌈(x : ℝ) ^ ((7 : ℝ) / 10)⌉₊ := by
    have h2 : ((((Llog M x + 1) ^ 2 + 1 : ℕ)) : ℝ)
        ≤ ((⌈(x : ℝ) ^ ((7 : ℝ) / 10)⌉₊ : ℕ) : ℝ) := by
      push_cast
      exact le_trans hsq_le (Nat.le_ceil _)
    exact_mod_cast h2
  -- the `E₁` threshold `D₇·L² + 1 ≤ x^{141/200}`
  have hv : ((⌈(x : ℝ) ^ ((7 : ℝ) / 10)⌉₊ * (Llog M x) ^ 2 : ℕ) : ℝ) + 1
      ≤ (x : ℝ) ^ ((141 : ℝ) / 200) := by
    have hcast : ((⌈(x : ℝ) ^ ((7 : ℝ) / 10)⌉₊ * (Llog M x) ^ 2 : ℕ) : ℝ)
        = (⌈(x : ℝ) ^ ((7 : ℝ) / 10)⌉₊ : ℝ) * ((Llog M x : ℝ) ^ 2) := by
      push_cast; ring
    rw [hcast]
    have hD7ub : (⌈(x : ℝ) ^ ((7 : ℝ) / 10)⌉₊ : ℝ) ≤ 2 * (x : ℝ) ^ ((7 : ℝ) / 10) := by
      have h := Nat.ceil_lt_add_one (Real.rpow_nonneg hx0.le ((7 : ℝ) / 10))
      have h2 : (1 : ℝ) ≤ (x : ℝ) ^ ((7 : ℝ) / 10) := Real.one_le_rpow hx1 (by norm_num)
      linarith
    have hLsq : (Llog M x : ℝ) ^ 2 ≤ 4 * Y := by
      have h3 : (2 * V) ^ 2 = 4 * V ^ 2 := by ring
      rw [hVY] at h3
      nlinarith [hL_ubV, h3, hL0]
    have h8Y : 8 * Y + 1 ≤ (x : ℝ) ^ ((1 : ℝ) / 200) := by
      have h1 : (1 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 200) := Real.one_le_rpow hx1 (by norm_num)
      linarith [hTL2]
    have hx710 : (1 : ℝ) ≤ (x : ℝ) ^ ((7 : ℝ) / 10) := Real.one_le_rpow hx1 (by norm_num)
    have hx7nn : (0 : ℝ) ≤ (x : ℝ) ^ ((7 : ℝ) / 10) := le_trans zero_le_one hx710
    have hstep : (⌈(x : ℝ) ^ ((7 : ℝ) / 10)⌉₊ : ℝ) * (Llog M x : ℝ) ^ 2
        ≤ 8 * ((x : ℝ) ^ ((7 : ℝ) / 10) * Y) := by
      calc (⌈(x : ℝ) ^ ((7 : ℝ) / 10)⌉₊ : ℝ) * (Llog M x : ℝ) ^ 2
          ≤ (2 * (x : ℝ) ^ ((7 : ℝ) / 10)) * (4 * Y) :=
            mul_le_mul hD7ub hLsq (by positivity) (by positivity)
        _ = 8 * ((x : ℝ) ^ ((7 : ℝ) / 10) * Y) := by ring
    calc (⌈(x : ℝ) ^ ((7 : ℝ) / 10)⌉₊ : ℝ) * (Llog M x : ℝ) ^ 2 + 1
        ≤ 8 * ((x : ℝ) ^ ((7 : ℝ) / 10) * Y) + 1 := by linarith
      _ ≤ 8 * ((x : ℝ) ^ ((7 : ℝ) / 10) * Y) + (x : ℝ) ^ ((7 : ℝ) / 10) := by linarith
      _ = (x : ℝ) ^ ((7 : ℝ) / 10) * (8 * Y + 1) := by ring
      _ ≤ (x : ℝ) ^ ((7 : ℝ) / 10) * (x : ℝ) ^ ((1 : ℝ) / 200) :=
          mul_le_mul_of_nonneg_left h8Y hx7nn
      _ = (x : ℝ) ^ ((141 : ℝ) / 200) := by
          rw [← Real.rpow_add hx0]
          congr 1
          norm_num
  have hlogL : (Real.log x) ^ M ≤ (Llog M x : ℝ) := by
    rw [Llog]
    exact Nat.le_ceil _
  have hR3 : (Llog M x + 1) ^ 2 < Submission.X2Y4R3.R3cut x := by
    have h5 : (1 : ℝ) ≤ (Real.log x) ^ ((2 : ℝ) ^ 25) := Real.one_le_rpow hlog1 (by norm_num)
    have hx7nn : (0 : ℝ) ≤ (x : ℝ) ^ ((7 : ℝ) / 10) := Real.rpow_nonneg hx0.le _
    have h6 : (x : ℝ) ^ ((7 : ℝ) / 10)
        ≤ (x : ℝ) ^ ((7 : ℝ) / 10) * (Real.log x) ^ ((2 : ℝ) ^ 25) := by
      have h := mul_le_mul_of_nonneg_left h5 hx7nn
      simpa using h
    have h7 : ((((Llog M x + 1) ^ 2 + 1 : ℕ)) : ℝ)
        ≤ (x : ℝ) ^ ((7 : ℝ) / 10) * (Real.log x) ^ ((2 : ℝ) ^ 25) := by
      push_cast
      exact le_trans hsq_le h6
    have h8 : (Llog M x + 1) ^ 2 + 1 ≤ Submission.X2Y4R3.R3cut x := by
      rw [Submission.X2Y4R3.R3cut]
      exact Nat.le_floor h7
    omega
  exact ⟨hL1, hD7_2, hsqD7, hv, hlogL, hR3⟩


/-- **The `τ⁰`-weighted `(R′)` for the honest remainder of `ã` at the cut-off `D₇ = ⌈x^{7/10}⌉`.** -/
theorem rtilde_D7_le (lam : ℝ) : ∃ X₀ : ℕ, ∃ C : ℝ, 0 < C ∧
    ∀ x : ℕ, X₀ ≤ x → ∀ m : ℕ, ⌈(x : ℝ) ^ ((7 : ℝ) / 10)⌉₊ ≤ m → m ≤ x →
    (∑ d ∈ (Finset.Icc 1 ⌈(x : ℝ) ^ ((7 : ℝ) / 10)⌉₊).filter Squarefree,
        |Submission.ASP.rtilde Submission.ASP.FIr Submission.ASP.FIgtil d m|)
      ≤ C * (Submission.Aseq x : ℝ) * (Real.log (x : ℝ)) ^ (-lam) := by
  obtain ⟨C2, B2, X2, hC2, hcube⟩ := Submission.ASP.sum_FIa_tau_cube_le
  obtain ⟨Cg, Kg, hCg, hKg, hG⟩ := Submission.ASP.sum_FIgtil_le
  set B2' : ℝ := max B2 0 with hB2'
  have hB2'0 : 0 ≤ B2' := le_max_right _ _
  set lam2 : ℝ := max lam (B2' / 2) with hlam2
  have hlam2ge : lam ≤ lam2 := le_max_left _ _
  have hlam20 : 0 ≤ lam2 := le_trans (by linarith : (0 : ℝ) ≤ B2' / 2) (le_max_right _ _)
  have hcomp : B2' ≤ 2 * lam2 := by
    have h : B2' / 2 ≤ lam2 := le_max_right _ _
    linarith
  set lamT : ℝ := max (Kg + lam) 0 with hlamT
  have hlamT0 : 0 ≤ lamT := le_max_right _ _
  have hlamTge : Kg + lam ≤ lamT := le_max_left _ _
  obtain ⟨X3, C3, hC3, hT⟩ := Submission.ASP.FIr_T_le lamT hlamT0
  obtain ⟨X1, C1, hC1, hEone⟩ := Eone_le_at_07 lam
  have hS2 : ∀ x : ℕ, max ⌈X2⌉₊ 100 ≤ x → ∀ t : ℕ, 2 ≤ t → t ≤ x →
      (∑ n ∈ Finset.Icc 1 t, Submission.ASP.FIa n * ((n.divisors.card : ℝ)) ^ (3 : ℕ))
        ≤ C2 * (Submission.Aseq x : ℝ) * (Real.log x) ^ B2' := by
    intro x hx t ht2 htx
    have hx2 : X2 ≤ (x : ℝ) :=
      le_trans (Nat.le_ceil X2) (by exact_mod_cast (le_trans (le_max_left _ _) hx))
    have hx100 : 100 ≤ x := le_trans (le_max_right _ _) hx
    have hlog1 : (1 : ℝ) ≤ Real.log x := by
      have h3 : (3 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (by omega : 3 ≤ x)
      exact le_trans Submission.ASP.one_le_log_three (Real.log_le_log (by norm_num) h3)
    have h := hcube x hx2 t ht2 htx
    refine le_trans h ?_
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hC2.le (Nat.cast_nonneg _))
    exact Real.rpow_le_rpow_of_exponent_le hlog1 (le_max_left _ _)
  obtain ⟨Xe, Ce, hCe, hEtwo⟩ := Etwo_le_at_07 B2' C2 lam2 hC2 hB2'0 hcomp (max ⌈X2⌉₊ 100) hS2
  set M : ℝ := 8 * lam2 + 100 with hMdef
  have hM0 : 0 ≤ M := by rw [hMdef]; linarith
  obtain ⟨XL, hLth⟩ := exists_Llog_thresholds M hM0
  refine ⟨max (max (max X1 X3) Xe) (max XL 100) + 1, C1 + Ce + Cg * C3, by positivity, ?_⟩
  intro x hx m hmD hmx
  have hxX1 : X1 ≤ x := by omega
  have hxX3 : X3 ≤ x := by omega
  have hxXe : Xe ≤ x := by omega
  have hxXL : XL ≤ x := by omega
  have hx100 : 100 ≤ x := by omega
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (by omega : 1 ≤ x)
  have hx0 : (0 : ℝ) < (x : ℝ) := by linarith
  have hx3 : (3 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (by omega : 3 ≤ x)
  have hlog1 : (1 : ℝ) ≤ Real.log x :=
    le_trans Submission.ASP.one_le_log_three (Real.log_le_log (by norm_num) hx3)
  have hlog0 : (0 : ℝ) < Real.log x := lt_of_lt_of_le zero_lt_one hlog1
  obtain ⟨hL1, hD72, hLsqD7, hEoneHyp, hlogL, hR3⟩ := hLth x hxXL
  have hm2 : 2 ≤ m := le_trans hD72 hmD
  have hm1 : 1 ≤ m := le_trans (by norm_num) hm2
  have hL2m : (Llog M x + 1) ^ 2 ≤ m := le_trans (by omega) hmD
  have hLm_sqrt : Llog M x < m.sqrt := by
    have h : Llog M x + 1 ≤ m.sqrt := Nat.le_sqrt.mpr (by simpa [pow_two] using hL2m)
    omega
  have hLm : Llog M x ≤ m := le_trans (le_of_lt hLm_sqrt) (Nat.sqrt_le_self m)
  have hRcutm : Submission.Rcut x ≤ m :=
    le_trans (Rcut_le_ceil_rpow_710 (by omega : 2 ≤ x)) hmD
  have he1 : Submission.ASP.Eone Submission.ASP.FIr m ⌈(x : ℝ) ^ ((7 : ℝ) / 10)⌉₊ (Llog M x)
      ≤ C1 * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lam) :=
    hEone x hxX1 m (Llog M x) hm2 hmx hL1 hEoneHyp
  have he2 : Submission.ASP.Etwo Submission.ASP.FIa Submission.ASP.FIg m
      ⌈(x : ℝ) ^ ((7 : ℝ) / 10)⌉₊ (Llog M x)
      ≤ Ce * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lam2) := by
    exact hEtwo x hxXe m (Llog M x) hm2 hmx hmD hL1 hLm_sqrt hR3 hlogL
  have htT := hT x hxX3 m hRcutm hmx
  have hbound := Submission.ASP.Rtilde_sum_le_signed_of_inputs Submission.ASP.FIa
      Submission.ASP.FIg Submission.ASP.FIr Submission.ASP.FIgtil m
      ⌈(x : ℝ) ^ ((7 : ℝ) / 10)⌉₊ (Llog M x) hLm
      (T := C3 * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lamT))
      (X1 := C1 * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lam))
      (E2 := Ce * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lam2))
      (fun n => Submission.ASP.FIa_nonneg n) (fun n => Submission.ASP.FIg_nonneg n)
      (Submission.ASP.FI_approx (m : ℝ)) htT he1 he2
  have hAn : (0 : ℝ) ≤ (Submission.Aseq x : ℝ) := by
    have h0 : (0 : ℝ) ≤ Submission.ASP.Acount Submission.ASP.FIa (x : ℝ) :=
      Finset.sum_nonneg (fun n _ => Submission.ASP.FIa_nonneg n)
    rw [Submission.ASP.FI_Acount_eq] at h0
    linarith
  have hGsum : (∑ d ∈ (Finset.Icc 1 ⌈(x : ℝ) ^ ((7 : ℝ) / 10)⌉₊).filter Squarefree,
      |Submission.ASP.FIgtil d|) ≤ Cg * (Real.log x) ^ Kg := by
    have h := hG ⌈(x : ℝ) ^ ((7 : ℝ) / 10)⌉₊ hD72
    have h' : (∑ d ∈ (Finset.Icc 1 ⌈(x : ℝ) ^ ((7 : ℝ) / 10)⌉₊).filter Squarefree,
          Submission.ASP.FIgtil d)
        = (∑ d ∈ (Finset.Icc 1 ⌈(x : ℝ) ^ ((7 : ℝ) / 10)⌉₊).filter Squarefree,
          |Submission.ASP.FIgtil d|) :=
      Finset.sum_congr rfl (fun d _ => (abs_of_nonneg (Submission.ASP.FIgtil_nonneg d)).symm)
    rw [← h']
    refine le_trans h ?_
    have hD7x : ⌈(x : ℝ) ^ ((7 : ℝ) / 10)⌉₊ ≤ x := ceil_rpow_710_le_self (by omega : 1 ≤ x)
    have hlogdx : Real.log ((⌈(x : ℝ) ^ ((7 : ℝ) / 10)⌉₊ : ℕ) : ℝ) ≤ Real.log x :=
      Real.log_le_log (by positivity) (by exact_mod_cast hD7x)
    have hlogd0 : (0 : ℝ) ≤ Real.log ((⌈(x : ℝ) ^ ((7 : ℝ) / 10)⌉₊ : ℕ) : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (one_le_ceil_rpow_710 (by omega : 1 ≤ x)))
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hlogd0 hlogdx hKg) hCg.le
  have h2 : Ce * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lam2)
      ≤ Ce * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lam) := by
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hCe.le hAn)
    exact Real.rpow_le_rpow_of_exponent_le hlog1 (by linarith)
  have h3 : (∑ d ∈ (Finset.Icc 1 ⌈(x : ℝ) ^ ((7 : ℝ) / 10)⌉₊).filter Squarefree,
        |Submission.ASP.FIgtil d|) * (C3 * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lamT))
      ≤ Cg * C3 * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lam) := by
    have hAC3 : (0 : ℝ) ≤ C3 * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lamT) :=
      mul_nonneg (mul_nonneg hC3.le hAn) (Real.rpow_nonneg hlog0.le _)
    refine le_trans (mul_le_mul_of_nonneg_right hGsum hAC3) ?_
    have hexp : Kg - lamT ≤ -lam := by linarith
    have hLcomb : (Real.log x) ^ Kg * (Real.log x) ^ (-lamT) = (Real.log x) ^ (Kg - lamT) := by
      rw [← Real.rpow_add hlog0]
      ring_nf
    calc (Cg * (Real.log x) ^ Kg) * (C3 * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lamT))
        = Cg * C3 * (Submission.Aseq x : ℝ)
            * ((Real.log x) ^ Kg * (Real.log x) ^ (-lamT)) := by ring
      _ = Cg * C3 * (Submission.Aseq x : ℝ) * (Real.log x) ^ (Kg - lamT) := by rw [hLcomb]
      _ ≤ Cg * C3 * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lam) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hlog1 hexp)
            (mul_nonneg (mul_nonneg hCg.le hC3.le) hAn)
  refine le_trans hbound ?_
  have hX : C1 * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lam)
      + Ce * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lam2)
      + (∑ d ∈ (Finset.Icc 1 ⌈(x : ℝ) ^ ((7 : ℝ) / 10)⌉₊).filter Squarefree,
          |Submission.ASP.FIgtil d|) * (C3 * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lamT))
      ≤ C1 * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lam)
      + Ce * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lam)
      + Cg * C3 * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lam) :=
    add_le_add (add_le_add le_rfl h2) h3
  refine le_trans hX ?_
  have hEq : C1 * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lam)
      + Ce * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lam)
      + Cg * C3 * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lam)
      = (C1 + Ce + Cg * C3) * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lam) := by ring
  rw [hEq]

/-- **`(R′)` for the honest remainder `r̃_full = r̃ + A·gtail` of `ã` at `D₇(x) = ⌈x^{7/10}⌉`.** -/
theorem rtildeFull_D7_le (lam : ℝ) : ∃ X₀ : ℕ, ∃ C : ℝ, 0 < C ∧
    ∀ x : ℕ, X₀ ≤ x → ∀ m : ℕ, ⌈(x : ℝ) ^ ((7 : ℝ) / 10)⌉₊ ≤ m → m ≤ x →
    (∑ d ∈ (Finset.Icc 1 ⌈(x : ℝ) ^ ((7 : ℝ) / 10)⌉₊).filter Squarefree,
        |Submission.ASP.rtildeFull Submission.ASP.FIr Submission.ASP.FIg Submission.ASP.FIgtil
          Submission.ASP.FIa d m|)
      ≤ C * (Submission.Aseq x : ℝ) * (Real.log (x : ℝ)) ^ (-lam) := by
  obtain ⟨Xr, CR, hCR, hR⟩ := rtilde_D7_le lam
  obtain ⟨Ctg, Atg, hCtg, hAtg, hgt⟩ := Submission.ASP.FI_gtail_sum_le
  obtain ⟨CA, hCA, hAup⟩ := Submission.X2Y4R.Aseq_le_const_mul_rpow
  obtain ⟨cA, hcA, XA, hAlow⟩ := Submission.X2Y4R.exists_const_mul_rpow_le_Aseq
  set lam' : ℝ := max lam 1 with hlam'
  have hlam'0 : 0 < lam' := lt_of_lt_of_le zero_lt_one (by rw [hlam']; exact le_max_right _ _)
  have hKpos : (0 : ℝ) < CA * Ctg * 2 * 2 ^ (Atg + 4) := by positivity
  obtain ⟨Y1, -, hY1⟩ := Submission.poly_tail_le (CA * Ctg * 2 * 2 ^ (Atg + 4))
    ((7 : ℝ) / 10) (Atg + 4) (cA / 2) lam' hKpos (by norm_num) (by positivity) hlam'0
  refine ⟨max (max Xr XA) (max Y1 100) + 1, CR + 1, by positivity, ?_⟩
  intro x hx m hmD hmx
  have hxXr : Xr ≤ x := by omega
  have hxXA : XA ≤ x := by omega
  have hxY1 : Y1 ≤ x := by omega
  have hx100 : 100 ≤ x := by omega
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (by omega : 1 ≤ x)
  have hx0 : (0 : ℝ) < (x : ℝ) := by linarith
  have hx3 : (3 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (by omega : 3 ≤ x)
  have hlog1 : (1 : ℝ) ≤ Real.log x :=
    le_trans Submission.ASP.one_le_log_three (Real.log_le_log (by norm_num) hx3)
  have hlog0 : (0 : ℝ) < Real.log x := lt_of_lt_of_le zero_lt_one hlog1
  set D7 : ℕ := ⌈(x : ℝ) ^ ((7 : ℝ) / 10)⌉₊ with hD7
  have hD7_2 : 2 ≤ D7 := by
    have h5 : (2 : ℝ) ≤ (x : ℝ) ^ ((7 : ℝ) / 10) := by
      have h64 : (2 : ℝ) ≤ (64 : ℝ) ^ ((7 : ℝ) / 10) :=
        Submission.ASP.two_le_rpow_seven_tenths (by norm_num)
      have hmono : (64 : ℝ) ^ ((7 : ℝ) / 10) ≤ (x : ℝ) ^ ((7 : ℝ) / 10) :=
        Real.rpow_le_rpow (by norm_num) (by exact_mod_cast (by omega : 64 ≤ x)) (by norm_num)
      linarith
    have h6 : (2 : ℝ) ≤ (D7 : ℝ) := le_trans h5 (Nat.le_ceil _)
    exact_mod_cast h6
  have hmD' : ⌈(x : ℝ) ^ ((7 : ℝ) / 10)⌉₊ ≤ m := by simpa [hD7] using hmD
  have hm2 : 2 ≤ m := le_trans hD7_2 hmD'
  have hm1 : 1 ≤ m := le_trans (by norm_num) hm2
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hrtilde := hR x hxXr m hmD' hmx
  have hAn : (0 : ℝ) ≤ (Submission.Aseq x : ℝ) := by
    have h0 : (0 : ℝ) ≤ Submission.ASP.Acount Submission.ASP.FIa (x : ℝ) :=
      Finset.sum_nonneg (fun n _ => Submission.ASP.FIa_nonneg n)
    rw [Submission.ASP.FI_Acount_eq] at h0
    linarith
  -- the density tail
  have hgtail : (∑ d ∈ (Finset.Icc 1 D7).filter Squarefree,
      |Submission.ASP.gtail Submission.ASP.FIg Submission.ASP.FIgtil d m|)
      ≤ Ctg * (D7 : ℝ) * (Real.log ((D7 : ℝ) + 2)) ^ Atg
          * (Real.log ((m : ℝ) + 2)) ^ 4 / (m : ℝ) := hgt D7 m hm1
  -- the log comparisons
  have hlogD : Real.log ((D7 : ℝ) + 2) ≤ 2 * Real.log x := by
    have hD7x : D7 ≤ x := by rw [hD7]; exact ceil_rpow_710_le_self (by omega : 1 ≤ x)
    have h1 : (D7 : ℝ) + 2 ≤ 2 * (x : ℝ) := by
      have h2 : (D7 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hD7x
      linarith
    have h2 : Real.log ((D7 : ℝ) + 2) ≤ Real.log (2 * (x : ℝ)) :=
      Real.log_le_log (by
        have h0 : (0 : ℝ) ≤ (D7 : ℝ) := Nat.cast_nonneg _
        linarith) h1
    rw [Real.log_mul (by norm_num) (ne_of_gt hx0)] at h2
    linarith [Real.log_two_lt_d9]
  have hlogm : Real.log ((m : ℝ) + 2) ≤ 2 * Real.log x := by
    have hmxR : (m : ℝ) ≤ (x : ℝ) := by exact_mod_cast hmx
    have h1 : (m : ℝ) + 2 ≤ 2 * (x : ℝ) := by linarith
    have h2 : Real.log ((m : ℝ) + 2) ≤ Real.log (2 * (x : ℝ)) :=
      Real.log_le_log (by linarith) h1
    rw [Real.log_mul (by norm_num) (ne_of_gt hx0)] at h2
    linarith [Real.log_two_lt_d9]
  have hb1 : (Real.log ((D7 : ℝ) + 2)) ^ Atg * (Real.log ((m : ℝ) + 2)) ^ 4
      ≤ 2 ^ (Atg + 4) * (Real.log x) ^ (Atg + 4) := by
    have hDn : (0 : ℝ) ≤ Real.log ((D7 : ℝ) + 2) := by
      refine Real.log_nonneg ?_
      have h0 : (0 : ℝ) ≤ (D7 : ℝ) := Nat.cast_nonneg _
      linarith
    have hmn : (0 : ℝ) ≤ Real.log ((m : ℝ) + 2) := Real.log_nonneg (by linarith)
    have h2x : (0 : ℝ) < 2 * Real.log x := by linarith
    have h2 : (Real.log ((D7 : ℝ) + 2)) ^ Atg ≤ (2 * Real.log x) ^ Atg :=
      Real.rpow_le_rpow hDn hlogD hAtg
    have h3 : (Real.log ((m : ℝ) + 2)) ^ (((4 : ℕ) : ℝ))
        ≤ (2 * Real.log x) ^ (((4 : ℕ) : ℝ)) := by
      rw [Real.rpow_natCast, Real.rpow_natCast]
      exact pow_le_pow_left₀ hmn hlogm 4
    rw [show (Real.log ((m : ℝ) + 2)) ^ 4
        = (Real.log ((m : ℝ) + 2)) ^ (((4 : ℕ) : ℝ)) from (Real.rpow_natCast _ 4).symm]
    calc (Real.log ((D7 : ℝ) + 2)) ^ Atg * (Real.log ((m : ℝ) + 2)) ^ (((4 : ℕ) : ℝ))
        ≤ (2 * Real.log x) ^ Atg * (2 * Real.log x) ^ (((4 : ℕ) : ℝ)) :=
          mul_le_mul h2 h3 (Real.rpow_nonneg hmn _) (Real.rpow_nonneg h2x.le _)
      _ = (2 * Real.log x) ^ (Atg + 4) := by
          rw [← Real.rpow_add h2x]
          norm_num
      _ = 2 ^ (Atg + 4) * (Real.log x) ^ (Atg + 4) := Real.mul_rpow (by norm_num) hlog0.le
  have hAcm : |Submission.ASP.Acount Submission.ASP.FIa (m : ℝ)| ≤ CA * (m : ℝ) ^ ((3 : ℝ) / 4) := by
    have h0 : (0 : ℝ) ≤ Submission.ASP.Acount Submission.ASP.FIa (m : ℝ) :=
      Finset.sum_nonneg (fun n _ => Submission.ASP.FIa_nonneg n)
    rw [abs_of_nonneg h0]
    refine le_trans ?_ (hAup m hm1)
    rw [Submission.ASP.FI_Acount_eq]
    linarith
  have hm34 : (m : ℝ) ^ ((3 : ℝ) / 4) / (m : ℝ) ≤ 1 := by
    have hm1R : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
    have h1 : (m : ℝ) ^ ((3 : ℝ) / 4) ≤ (m : ℝ) := by
      have h2 := Real.rpow_le_rpow_of_exponent_le hm1R (show ((3 : ℝ) / 4) ≤ (1 : ℝ) by norm_num)
      rwa [Real.rpow_one] at h2
    exact (div_le_one hm0).mpr h1
  have hkey : CA * (m : ℝ) ^ ((3 : ℝ) / 4)
        * (Ctg * (D7 : ℝ) * (Real.log ((D7 : ℝ) + 2)) ^ Atg
            * (Real.log ((m : ℝ) + 2)) ^ 4 / (m : ℝ))
      = CA * Ctg * ((Real.log ((D7 : ℝ) + 2)) ^ Atg * (Real.log ((m : ℝ) + 2)) ^ 4)
          * ((D7 : ℝ) * ((m : ℝ) ^ ((3 : ℝ) / 4) / (m : ℝ))) := by
    field_simp
  have hD7r : (D7 : ℝ) * ((m : ℝ) ^ ((3 : ℝ) / 4) / (m : ℝ)) ≤ 2 * (x : ℝ) ^ ((7 : ℝ) / 10) := by
    calc (D7 : ℝ) * ((m : ℝ) ^ ((3 : ℝ) / 4) / (m : ℝ))
        ≤ (D7 : ℝ) * 1 := mul_le_mul_of_nonneg_left hm34 (Nat.cast_nonneg _)
      _ = (D7 : ℝ) := mul_one _
      _ ≤ 2 * (x : ℝ) ^ ((7 : ℝ) / 10) := by
          have h := Nat.ceil_lt_add_one (Real.rpow_nonneg hx0.le ((7 : ℝ) / 10))
          have h2 : (1 : ℝ) ≤ (x : ℝ) ^ ((7 : ℝ) / 10) := Real.one_le_rpow hx1 (by norm_num)
          have h3 : (D7 : ℝ) < (x : ℝ) ^ ((7 : ℝ) / 10) + 1 := by rw [hD7]; exact h
          linarith
  have hgterm : |Submission.ASP.Acount Submission.ASP.FIa (m : ℝ)|
        * (Ctg * (D7 : ℝ) * (Real.log ((D7 : ℝ) + 2)) ^ Atg
            * (Real.log ((m : ℝ) + 2)) ^ 4 / (m : ℝ))
      ≤ (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lam) := by
    have hT0 : (0 : ℝ) ≤ Ctg * (D7 : ℝ) * (Real.log ((D7 : ℝ) + 2)) ^ Atg
        * (Real.log ((m : ℝ) + 2)) ^ 4 / (m : ℝ) := by
      have h1 : (0 : ℝ) ≤ (Real.log ((D7 : ℝ) + 2)) ^ Atg :=
        Real.rpow_nonneg (by
          refine Real.log_nonneg ?_
          have h0 : (0 : ℝ) ≤ (D7 : ℝ) := Nat.cast_nonneg _
          linarith) Atg
      have h2 : (0 : ℝ) ≤ (Real.log ((m : ℝ) + 2)) ^ 4 :=
        pow_nonneg (Real.log_nonneg (by linarith)) 4
      have h3 : (0 : ℝ) ≤ (D7 : ℝ) := Nat.cast_nonneg _
      exact div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCtg.le h3) h1) h2) hm0.le
    refine le_trans (mul_le_mul_of_nonneg_right hAcm hT0) ?_
    rw [hkey]
    have hstep1 : CA * Ctg * ((Real.log ((D7 : ℝ) + 2)) ^ Atg * (Real.log ((m : ℝ) + 2)) ^ 4)
          * ((D7 : ℝ) * ((m : ℝ) ^ ((3 : ℝ) / 4) / (m : ℝ)))
        ≤ CA * Ctg * (2 ^ (Atg + 4) * (Real.log x) ^ (Atg + 4))
          * (2 * (x : ℝ) ^ ((7 : ℝ) / 10)) := by
      have hca : (0 : ℝ) ≤ CA * Ctg := mul_nonneg hCA.le hCtg.le
      have h1 : CA * Ctg * ((Real.log ((D7 : ℝ) + 2)) ^ Atg * (Real.log ((m : ℝ) + 2)) ^ 4)
          ≤ CA * Ctg * (2 ^ (Atg + 4) * (Real.log x) ^ (Atg + 4)) :=
        mul_le_mul_of_nonneg_left hb1 hca
      exact mul_le_mul h1 hD7r (by positivity) (by positivity)
    refine le_trans hstep1 ?_
    have hstep2 : CA * Ctg * (2 ^ (Atg + 4) * (Real.log x) ^ (Atg + 4))
          * (2 * (x : ℝ) ^ ((7 : ℝ) / 10))
        = CA * Ctg * 2 * 2 ^ (Atg + 4) * ((x : ℝ) ^ ((7 : ℝ) / 10) * (Real.log x) ^ (Atg + 4)) := by
      ring
    rw [hstep2]
    have hstep3 : CA * Ctg * 2 * 2 ^ (Atg + 4)
          * ((x : ℝ) ^ ((7 : ℝ) / 10) * (Real.log x) ^ (Atg + 4))
        = CA * Ctg * 2 * 2 ^ (Atg + 4) * (x : ℝ) ^ ((7 : ℝ) / 10)
          * (Real.log x) ^ (Atg + 4) := by ring
    rw [hstep3]
    refine le_trans (hY1 x hxY1) ?_
    have h1 : cA * (x : ℝ) ^ ((3 : ℝ) / 4) ≤ (Submission.Aseq x : ℝ) := hAlow x hxXA
    have h2 : (Real.log x) ^ (-lam') ≤ (Real.log x) ^ (-lam) :=
      Real.rpow_le_rpow_of_exponent_le hlog1 (by linarith [le_max_left lam (1 : ℝ)])
    have hx34 : (0 : ℝ) ≤ (x : ℝ) ^ ((3 : ℝ) / 4) := Real.rpow_nonneg hx0.le _
    calc (cA / 2) * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-lam')
        ≤ (cA * (x : ℝ) ^ ((3 : ℝ) / 4)) * (Real.log x) ^ (-lam) := by
          refine mul_le_mul ?_ h2 (Real.rpow_nonneg hlog0.le _) (mul_nonneg hcA.le hx34)
          nlinarith [mul_nonneg hcA.le hx34]
      _ ≤ (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lam) :=
          mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hlog0.le _)
  have hfull := Submission.ASP.RtildeFull_sum_le Submission.ASP.FIr Submission.ASP.FIg
      Submission.ASP.FIgtil Submission.ASP.FIa m D7
      (R := CR * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lam))
      (T := Ctg * (D7 : ℝ) * (Real.log ((D7 : ℝ) + 2)) ^ Atg
            * (Real.log ((m : ℝ) + 2)) ^ 4 / (m : ℝ)) hrtilde hgtail
  refine le_trans hfull ?_
  calc CR * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lam)
        + |Submission.ASP.Acount Submission.ASP.FIa (m : ℝ)|
          * (Ctg * (D7 : ℝ) * (Real.log ((D7 : ℝ) + 2)) ^ Atg
              * (Real.log ((m : ℝ) + 2)) ^ 4 / (m : ℝ))
      ≤ CR * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lam)
        + (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lam) := add_le_add le_rfl hgterm
    _ = (CR + 1) * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lam) := by ring

end

end Work.FIChain
