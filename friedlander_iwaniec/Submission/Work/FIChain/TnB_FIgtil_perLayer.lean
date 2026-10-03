/-
# `Work.FIChain.TnB_FIgtil_perLayer` — the per-layer bound for the FI sieve density

The odd layers `TnB 19 ν_Δ (2k+1) Δ (yFI Δ)` of the `B = 19` Rosser–Iwaniec recursion for the
Friedlander–Iwaniec density `ν_Δ = nuFI Δ = g̃ · hSieveC g̃ (1/log Δ)` are dominated, *uniformly in
`Δ ≥ 3`*, by `φ(2k+1)·VfB ν_Δ (yFI Δ)` with

    `φ(2k+1) = K·(2ρ^{-k})²·(log K + 2 log(2ρ^{-k}))^{2k+1}/(2k+1)! ,  ρ = 9/10`,

whose odd-indexed sums converge.  The route (all inputs proved in the sibling modules, see
`PerLayerDefs.lean` for the vocabulary):

* `chainMassTnB` (combinatorial core): every chain counted by `TnB B ν (2k+1) D y` has all its
  primes above `levC B D k = max ⌈D^{levB B k}⌉₊ 2`, whence
  `TnB ≤ VfB ν (levC B D k)·(windowMass ν (levC B D k) y)^{2k+1}/(2k+1)!`;
* `nuFI_LinNormKup` (the `Ω₂` window norm of `ν_Δ` at level `Δ`) together with the two
  consequences `VfB_ratio_le_LinNormKup` and `sum_nu_le_LinNormKup` converts the window mass and
  the windowed `VfB` into `K·U²·(log K + 2 log U)^{2k+1}/(2k+1)!` with
  `U = log (yFI Δ)/log (levC 19 Δ k)`;
* `U ≤ 2ρ^{-k}` and `U ≥ 1` upgrade this to `phiTerm K k`, and `phiSeries_bound` sums it.

The assembly is `perLayer_step` plus the final theorem.
-/
import Mathlib
import Submission.Work.FIChain.Defs
import Submission.Work.FIChain.LamPlusBLayerDefs
import Submission.Work.FIChain.OddLayersMajorantDefs
import Submission.Work.FIChain.VfBFacts
import Submission.Work.FIChain.sieveDens_le_one_sub
import Submission.Work.FIChain.sharpNorm_two_FIgtil
import Submission.Work.FIChain.PerLayerDefs
import Submission.Work.FIChain.PerLayerAux
import Submission.Work.FIChain.chainMassTnB
import Submission.Work.FIChain.FIgtil_prime_le_third
import Submission.Work.FIChain.VfB_ratio_le_LinNormKup
import Submission.Work.FIChain.sum_nu_le_LinNormKup

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIChain

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## The layer range as a natural number -/

/-- `yFI Δ = ⌈Δ^{1/20}⌉₊ + 1`, viewed as a natural number. -/
def yN (Δ : ℕ) : ℕ := ⌈(Δ : ℝ) ^ ((1 : ℝ) / 20)⌉₊ + 1

lemma yFI_eq_yN (Δ : ℕ) : yFI Δ = (yN Δ : ℝ) := by
  rw [yFI, yN]; push_cast; ring

lemma ceil_yFI (Δ : ℕ) : ⌈yFI Δ⌉₊ = yN Δ := by
  rw [yFI_eq_yN, Nat.ceil_natCast]

lemma one_lt_rpow_twenty (Δ : ℕ) (hΔ : 3 ≤ Δ) : (1 : ℝ) < (Δ : ℝ) ^ ((1 : ℝ) / 20) := by
  have hΔ1 : (1 : ℝ) < (Δ : ℝ) := by exact_mod_cast (by omega : 1 < Δ)
  have h : (Δ : ℝ) ^ (0 : ℝ) < (Δ : ℝ) ^ ((1 : ℝ) / 20) :=
    Real.rpow_lt_rpow_of_exponent_lt hΔ1 (by norm_num)
  rwa [Real.rpow_zero] at h

lemma yN_ge_two (Δ : ℕ) (hΔ : 3 ≤ Δ) : 2 ≤ yN Δ := by
  have h := one_lt_rpow_twenty Δ hΔ
  have hpos : 0 < (Δ : ℝ) ^ ((1 : ℝ) / 20) := by linarith
  have h1 : 1 ≤ ⌈(Δ : ℝ) ^ ((1 : ℝ) / 20)⌉₊ := Nat.ceil_pos.mpr hpos
  simp only [yN]; omega

lemma yN_cast_le (Δ : ℕ) : ((yN Δ : ℕ) : ℝ) ≤ (Δ : ℝ) ^ ((1 : ℝ) / 20) + 2 := by
  have h := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ (Δ : ℝ) ^ ((1 : ℝ) / 20) by positivity)
  simp only [yN]; push_cast
  linarith

lemma yN_pos (Δ : ℕ) : 0 < yN Δ := by simp only [yN]; omega

/-- `yN Δ ≤ Δ` for `Δ ≥ 3`. -/
lemma yN_le_Delta (Δ : ℕ) (hΔ : 3 ≤ Δ) : yN Δ ≤ Δ := by
  have hΔR : (3 : ℝ) ≤ (Δ : ℝ) := by exact_mod_cast hΔ
  have hsub : ((Δ - 1 : ℕ) : ℝ) = (Δ : ℝ) - 1 := by
    push_cast [Nat.cast_sub (by omega : 1 ≤ Δ)]; ring
  have hsq : (Δ : ℝ) ≤ ((Δ : ℝ) - 1) ^ 2 := by nlinarith
  have h1 : (1 : ℝ) ≤ (Δ : ℝ) - 1 := by linarith
  have hp : ((Δ : ℝ) - 1) ^ 2 ≤ ((Δ : ℝ) - 1) ^ 20 := by
    calc ((Δ : ℝ) - 1) ^ 2 = ((Δ : ℝ) - 1) ^ 2 * 1 := by ring
      _ ≤ ((Δ : ℝ) - 1) ^ 2 * ((Δ : ℝ) - 1) ^ 18 := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact one_le_pow₀ h1
      _ = ((Δ : ℝ) - 1) ^ 20 := by ring
  have hkey : (Δ : ℝ) ^ ((1 : ℝ) / 20) ≤ ((Δ - 1 : ℕ) : ℝ) := by
    rw [hsub]
    have h0 : (0 : ℝ) ≤ (Δ : ℝ) - 1 := by linarith
    calc (Δ : ℝ) ^ ((1 : ℝ) / 20) ≤ (((Δ : ℝ) - 1) ^ 20) ^ ((1 : ℝ) / 20) :=
          Real.rpow_le_rpow (by positivity) (le_trans hsq hp) (by norm_num)
      _ = (Δ : ℝ) - 1 := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul h0]
          norm_num
  have h1' : ((⌈(Δ : ℝ) ^ ((1 : ℝ) / 20)⌉₊ : ℕ) : ℝ) ≤ ((Δ - 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.ceil_le.mpr hkey
  have h2 : ((yN Δ : ℕ) : ℝ) ≤ ((Δ - 1 : ℕ) : ℝ) + 1 := by
    simp only [yN]; push_cast; linarith
  have h3 : ((Δ - 1 : ℕ) : ℝ) + 1 = (Δ : ℝ) := by rw [hsub]; ring
  have h4 : ((yN Δ : ℕ) : ℝ) ≤ (Δ : ℝ) := by linarith [h2, h3]
  exact_mod_cast h4

/-! ## Positivity of the density -/

lemma hSieveC_nonneg' (g : ℕ → ℝ) (ε : ℝ) (hg : ∀ n, 0 ≤ g n) (n : ℕ) :
    0 ≤ hSieveC g ε n := by
  rw [hSieveC]
  refine Finset.prod_nonneg fun p hp => ?_
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (Nat.mem_primeFactors.mp hp).1.pos
  have h1 : 0 ≤ (p : ℝ) ^ (-ε) := Real.rpow_nonneg hp0.le _
  have h2 : 0 ≤ (p : ℝ) ^ (-ε) * g p := mul_nonneg h1 (hg p)
  exact div_nonneg (by linarith) (by linarith)

lemma nuFI_nonneg (Δ : ℕ) (n : ℕ) : 0 ≤ nuFI Δ n := by
  rw [nuFI]
  exact mul_nonneg (Submission.ASP.FIgtil_nonneg n)
    (hSieveC_nonneg' _ _ (fun m => Submission.ASP.FIgtil_nonneg m) n)

lemma nuFI_prime_nonneg (Δ : ℕ) (p : ℕ) (_hp : p.Prime) : 0 ≤ nuFI Δ p := nuFI_nonneg Δ p

/-- The one-prime factor is at most `1/2` as soon as the density is at most `1/3`. -/
lemma one_prime_factor_le_half (g t : ℝ) (hg0 : 0 ≤ g) (hg : g ≤ 1 / 3) (ht0 : 0 < t)
    (ht1 : t ≤ 1) : g * ((1 + t) / (1 + t * g)) ≤ 1 / 2 := by
  have hden : 0 < 1 + t * g := by nlinarith
  have h4 : (0 : ℝ) ≤ (1 - g) * (1 - t) := mul_nonneg (by linarith) (by linarith)
  have h2 : g * (1 + t) / (1 + t * g) ≤ 2 * g / (1 + g) := by
    rw [div_le_div_iff₀ hden (by linarith)]
    nlinarith [h4]
  have h3 : 2 * g / (1 + g) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < 1 + g)]
    linarith
  rw [← mul_div_assoc]
  linarith

/-- The density `ν_Δ` is at most `1/2` at every prime, given `g̃ ≤ 1/3`. -/
lemma nuFI_le_half_of (hFI : ∀ p : ℕ, p.Prime → Submission.ASP.FIgtil p ≤ 1 / 3)
    (Δ : ℕ) (hΔ : 3 ≤ Δ) (p : ℕ) (hp : p.Prime) : nuFI Δ p ≤ 1 / 2 := by
  rw [nuFI, hSieveC_prime _ _ hp]
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.one_le
  have hlog : 0 < Real.log (Δ : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < Δ))
  have hinv : 0 < 1 / Real.log (Δ : ℝ) := one_div_pos.mpr hlog
  have ht0 : 0 < (p : ℝ) ^ (-(1 / Real.log (Δ : ℝ))) := Real.rpow_pos_of_pos hp0 _
  have ht1 : (p : ℝ) ^ (-(1 / Real.log (Δ : ℝ))) ≤ 1 := by
    calc (p : ℝ) ^ (-(1 / Real.log (Δ : ℝ))) ≤ (p : ℝ) ^ (0 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
      _ = 1 := Real.rpow_zero _
  exact one_prime_factor_le_half _ _ (Submission.ASP.FIgtil_nonneg p) (hFI p hp) ht0 ht1

/-! ## The window ratio `U` and its two bounds -/

/-- `U = log (yFI Δ) / log (levC 19 Δ k)`: the `Ω₂` cost of the window
`[levC 19 Δ k, yFI Δ)` relative to the full range. -/
def UPer (Δ : ℕ) (k : ℕ) : ℝ :=
  Real.log (yFI Δ) / Real.log ((levC 19 (Δ : ℝ) k : ℕ) : ℝ)

lemma levB_nineteen_le (k : ℕ) : levB 19 k ≤ 1 / 20 := by
  rw [levB]
  have hr : rhoB 19 = (9 : ℝ) / 10 := by norm_num [rhoB]
  rw [hr]
  have h : ((9 : ℝ) / 10) ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have h20 : ((19 : ℝ) + 1) = 20 := by norm_num
  rw [h20]
  exact div_le_div_of_nonneg_right h (by norm_num)

lemma levB_eq (k : ℕ) : levB 19 k = (1 / 20) * ((9 : ℝ) / 10) ^ k := by
  rw [levB]
  have hr : rhoB 19 = (9 : ℝ) / 10 := by norm_num [rhoB]
  rw [hr]
  have h20 : ((19 : ℝ) + 1) = 20 := by norm_num
  rw [h20]; ring

lemma rpow_levB_le (Δ : ℕ) (hΔ : 1 ≤ Δ) (k : ℕ) :
    (Δ : ℝ) ^ levB 19 k ≤ (Δ : ℝ) ^ ((1 : ℝ) / 20) :=
  Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hΔ) (levB_nineteen_le k)

lemma levC_le_yN (Δ : ℕ) (hΔ : 3 ≤ Δ) (k : ℕ) : levC 19 (Δ : ℝ) k ≤ yN Δ := by
  have hx : (Δ : ℝ) ^ levB 19 k ≤ ((yN Δ : ℕ) : ℝ) := by
    calc (Δ : ℝ) ^ levB 19 k ≤ (Δ : ℝ) ^ ((1 : ℝ) / 20) := rpow_levB_le Δ (by omega) k
      _ ≤ ((⌈(Δ : ℝ) ^ ((1 : ℝ) / 20)⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
      _ ≤ ((yN Δ : ℕ) : ℝ) := by
          simp only [yN]; push_cast; linarith
  refine max_le ?_ ?_
  · exact Nat.ceil_le.mpr hx
  · exact yN_ge_two Δ hΔ

lemma levC_ge_two (Δ : ℕ) (k : ℕ) : 2 ≤ levC 19 (Δ : ℝ) k := le_max_right _ _

lemma levC_pos (Δ : ℕ) (k : ℕ) : (0 : ℝ) < ((levC 19 (Δ : ℝ) k : ℕ) : ℝ) := by
  have h := levC_ge_two Δ k
  exact_mod_cast (by omega : 0 < levC 19 (Δ : ℝ) k)

/-- `U ≥ 1`. -/
lemma UPer_ge_one (Δ : ℕ) (hΔ : 3 ≤ Δ) (k : ℕ) : 1 ≤ UPer Δ k := by
  unfold UPer
  rw [yFI_eq_yN]
  have hcy := levC_le_yN Δ hΔ k
  have hcl : (1 : ℝ) < ((levC 19 (Δ : ℝ) k : ℕ) : ℝ) :=
    lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) (by exact_mod_cast levC_ge_two Δ k)
  have hlogc : 0 < Real.log ((levC 19 (Δ : ℝ) k : ℕ) : ℝ) := Real.log_pos hcl
  have hmono : Real.log ((levC 19 (Δ : ℝ) k : ℕ) : ℝ) ≤ Real.log ((yN Δ : ℕ) : ℝ) :=
    Real.log_le_log (lt_of_lt_of_le (by norm_num : (0:ℝ) < 2) (by exact_mod_cast levC_ge_two Δ k))
      (by exact_mod_cast hcy)
  rw [one_le_div hlogc]
  exact hmono

lemma ten_ninths_pow_inv (k : ℕ) :
    ((10 : ℝ) / 9) ^ k * ((9 : ℝ) / 10) ^ k = 1 := by
  rw [← mul_pow]; norm_num

lemma one_le_two_mul_pow (k : ℕ) : (1 : ℝ) ≤ 2 * ((10 : ℝ) / 9) ^ k := by
  have h : (1 : ℝ) ≤ ((10 : ℝ) / 9) ^ k := one_le_pow₀ (by norm_num)
  linarith

/-- `U ≤ 2ρ^{-k}`, i.e. `U ≤ 2·(10/9)^k`. -/
lemma UPer_le (Δ : ℕ) (hΔ : 3 ≤ Δ) (k : ℕ) : UPer Δ k ≤ 2 * (10 / 9 : ℝ) ^ k := by
  unfold UPer
  rw [yFI_eq_yN]
  set A : ℝ := (Δ : ℝ) ^ ((1 : ℝ) / 20) with hAdef
  have hΔ0 : (0 : ℝ) < (Δ : ℝ) := by exact_mod_cast (by omega : 0 < Δ)
  have hA0 : (0 : ℝ) < A := by rw [hAdef]; positivity
  have hA1 : 1 < A := by rw [hAdef]; exact one_lt_rpow_twenty Δ hΔ
  have hlogA : Real.log A = (1 / 20) * Real.log (Δ : ℝ) := by
    rw [hAdef]; exact Real.log_rpow hΔ0 _
  have hlogcA : ((9 : ℝ) / 10) ^ k * Real.log A ≤ Real.log ((levC 19 (Δ : ℝ) k : ℕ) : ℝ) := by
    have h1 : Real.log ((Δ : ℝ) ^ levB 19 k) = ((9 : ℝ) / 10) ^ k * Real.log A := by
      rw [levB_eq, Real.log_rpow hΔ0, hlogA]; ring
    rw [← h1]
    refine Real.log_le_log (Real.rpow_pos_of_pos hΔ0 _) ?_
    calc (Δ : ℝ) ^ levB 19 k ≤ ((⌈(Δ : ℝ) ^ levB 19 k⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
      _ ≤ ((levC 19 (Δ : ℝ) k : ℕ) : ℝ) := by
          simp only [levC, Nat.cast_max]; exact le_max_left _ _
  have hlogc2 : Real.log 2 ≤ Real.log ((levC 19 (Δ : ℝ) k : ℕ) : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast levC_ge_two Δ k)
  have hlogcpos : 0 < Real.log ((levC 19 (Δ : ℝ) k : ℕ) : ℝ) :=
    lt_of_lt_of_le (Real.log_pos (by norm_num)) hlogc2
  have hylog : Real.log ((yN Δ : ℕ) : ℝ) ≤ Real.log (A + 2) := by
    refine Real.log_le_log (by exact_mod_cast yN_pos Δ) ?_
    have h := yN_cast_le Δ
    exact h
  by_cases hA2 : (2 : ℝ) ≤ A
  · have hylog2 : Real.log ((yN Δ : ℕ) : ℝ) ≤ 2 * Real.log A := by
      have h2 : A + 2 ≤ A ^ 2 := by nlinarith
      calc Real.log ((yN Δ : ℕ) : ℝ) ≤ Real.log (A + 2) := hylog
        _ ≤ Real.log (A ^ 2) := Real.log_le_log (by linarith) h2
        _ = 2 * Real.log A := by rw [Real.log_pow]; norm_num
    rw [div_le_iff₀ hlogcpos]
    have hmul := mul_le_mul_of_nonneg_left hlogcA
      (by positivity : (0 : ℝ) ≤ 2 * ((10 : ℝ) / 9) ^ k)
    have heq : 2 * ((10 : ℝ) / 9) ^ k * (((9 : ℝ) / 10) ^ k * Real.log A) = 2 * Real.log A := by
      calc 2 * ((10 : ℝ) / 9) ^ k * (((9 : ℝ) / 10) ^ k * Real.log A)
          = 2 * (((10 : ℝ) / 9) ^ k * ((9 : ℝ) / 10) ^ k) * Real.log A := by ring
        _ = 2 * 1 * Real.log A := by rw [ten_ninths_pow_inv k]
        _ = 2 * Real.log A := by ring
    linarith [hmul, heq.ge, hylog2]
  · have hylog2 : Real.log ((yN Δ : ℕ) : ℝ) ≤ 2 * Real.log 2 := by
      have h2 : A + 2 < 4 := by linarith
      calc Real.log ((yN Δ : ℕ) : ℝ) ≤ Real.log (A + 2) := hylog
        _ ≤ Real.log 4 := le_of_lt (Real.log_lt_log (by linarith) h2)
        _ = 2 * Real.log 2 := by
            rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    rw [div_le_iff₀ hlogcpos]
    have hlog2pos : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have h1 : 2 * Real.log 2 ≤ 2 * ((10 : ℝ) / 9) ^ k * Real.log 2 := by
      have h' : (2 : ℝ) ≤ 2 * ((10 : ℝ) / 9) ^ k := by
        have h2 := one_le_pow₀ (show (1:ℝ) ≤ (10:ℝ)/9 by norm_num) (n := k)
        linarith
      exact mul_le_mul_of_nonneg_right h' hlog2pos
    have h2 : 2 * ((10 : ℝ) / 9) ^ k * Real.log 2
        ≤ 2 * ((10 : ℝ) / 9) ^ k * Real.log ((levC 19 (Δ : ℝ) k : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left hlogc2 (by positivity)
    exact le_trans hylog2 (le_trans h1 h2)

/-! ## The per-layer step -/

lemma fact_pos (k : ℕ) : (0 : ℝ) < ((2 * k + 1).factorial : ℝ) := by positivity

/-- **The per-layer step.**  Combining the chain-mass bound, the windowed `VfB` ratio and the
window measure bound with `U = UPer Δ k ≤ 2ρ^{-k}`. -/
lemma perLayer_step (Δ : ℕ) (hΔ : 3 ≤ Δ) (k : ℕ)
    (hν0 : ∀ p : ℕ, p.Prime → 0 ≤ nuFI Δ p)
    (hν1 : ∀ p : ℕ, p.Prime → nuFI Δ p ≤ 1 / 2)
    (hVr : VfB (nuFI Δ) (levC 19 (Δ : ℝ) k : ℝ)
             ≤ VfB (nuFI Δ) (yFI Δ) * (KFI * UPer Δ k ^ 2))
    (hWm : windowMass (nuFI Δ) (levC 19 (Δ : ℝ) k) (yFI Δ)
             ≤ Real.log KFI + 2 * Real.log (UPer Δ k))
    (hcm : TnB 19 (nuFI Δ) (2 * k + 1) (Δ : ℝ) (yFI Δ)
             ≤ VfB (nuFI Δ) (levC 19 (Δ : ℝ) k : ℝ)
                 * (windowMass (nuFI Δ) (levC 19 (Δ : ℝ) k) (yFI Δ)) ^ (2 * k + 1)
                 / ((2 * k + 1).factorial : ℝ)) :
    TnB 19 (nuFI Δ) (2 * k + 1) (Δ : ℝ) (yFI Δ)
      ≤ VfB (nuFI Δ) (yFI Δ) * phiTerm KFI k := by
  have hU1 : 1 ≤ UPer Δ k := UPer_ge_one Δ hΔ k
  have hU2 : UPer Δ k ≤ 2 * (10 / 9 : ℝ) ^ k := UPer_le Δ hΔ k
  have hKFI0 : 0 ≤ KFI := le_of_lt KFI_pos
  have hKFI1 : 1 ≤ KFI := KFI_one_le
  have hlogK : 0 ≤ Real.log KFI := Real.log_nonneg hKFI1
  have hlogU : 0 ≤ Real.log (UPer Δ k) := Real.log_nonneg hU1
  have hUpos : 0 < UPer Δ k := lt_of_lt_of_le (by norm_num) hU1
  have hMnn : 0 ≤ windowMass (nuFI Δ) (levC 19 (Δ : ℝ) k) (yFI Δ) := by
    rw [windowMass]
    refine Finset.sum_nonneg fun p hp => ?_
    rw [Finset.mem_filter] at hp
    exact hν0 p (Nat.mem_primesBelow.mp hp.1).2
  have hQ1 : 0 ≤ Real.log KFI + 2 * Real.log (UPer Δ k) := by linarith
  have hQ2 : 0 ≤ Real.log KFI + 2 * Real.log (2 * (10 / 9 : ℝ) ^ k) := by
    have h : 0 ≤ Real.log (2 * (10 / 9 : ℝ) ^ k) :=
      Real.log_nonneg (one_le_two_mul_pow k)
    linarith
  have hVy0 : 0 ≤ VfB (nuFI Δ) (yFI Δ) := le_of_lt (VfB_pos hν1 _)
  have hpowM : (windowMass (nuFI Δ) (levC 19 (Δ : ℝ) k) (yFI Δ)) ^ (2 * k + 1)
      ≤ (Real.log KFI + 2 * Real.log (UPer Δ k)) ^ (2 * k + 1) :=
    pow_le_pow_left₀ hMnn hWm _
  have hmul1 : VfB (nuFI Δ) (levC 19 (Δ : ℝ) k : ℝ)
        * (windowMass (nuFI Δ) (levC 19 (Δ : ℝ) k) (yFI Δ)) ^ (2 * k + 1)
      ≤ (VfB (nuFI Δ) (yFI Δ) * (KFI * UPer Δ k ^ 2))
        * (Real.log KFI + 2 * Real.log (UPer Δ k)) ^ (2 * k + 1) :=
    mul_le_mul hVr hpowM (pow_nonneg hMnn _) (by positivity)
  have hstep1 := div_le_div_of_nonneg_right hmul1 (fact_pos k).le
  have hpowQ : (Real.log KFI + 2 * Real.log (UPer Δ k)) ^ (2 * k + 1)
      ≤ (Real.log KFI + 2 * Real.log (2 * (10 / 9 : ℝ) ^ k)) ^ (2 * k + 1) := by
    refine pow_le_pow_left₀ hQ1 ?_ _
    have h3 : Real.log (UPer Δ k) ≤ Real.log (2 * (10 / 9 : ℝ) ^ k) :=
      Real.log_le_log hUpos hU2
    linarith
  have hsqU : UPer Δ k ^ 2 ≤ (2 * (10 / 9 : ℝ) ^ k) ^ 2 :=
    pow_le_pow_left₀ (le_of_lt hUpos) hU2 2
  have hKsq : KFI * UPer Δ k ^ 2 ≤ KFI * (2 * (10 / 9 : ℝ) ^ k) ^ 2 :=
    mul_le_mul_of_nonneg_left hsqU hKFI0
  have hmul2 : (VfB (nuFI Δ) (yFI Δ) * (KFI * UPer Δ k ^ 2))
        * (Real.log KFI + 2 * Real.log (UPer Δ k)) ^ (2 * k + 1)
      ≤ VfB (nuFI Δ) (yFI Δ) * (KFI * (2 * (10 / 9 : ℝ) ^ k) ^ 2)
        * (Real.log KFI + 2 * Real.log (2 * (10 / 9 : ℝ) ^ k)) ^ (2 * k + 1) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hKsq hVy0) hpowQ (pow_nonneg hQ1 _) (by positivity)
  have hstep2 : (VfB (nuFI Δ) (yFI Δ) * (KFI * UPer Δ k ^ 2))
        * (Real.log KFI + 2 * Real.log (UPer Δ k)) ^ (2 * k + 1)
        / ((2 * k + 1).factorial : ℝ)
      ≤ VfB (nuFI Δ) (yFI Δ) * phiTerm KFI k := by
    have h0 := div_le_div_of_nonneg_right hmul2 (fact_pos k).le
    have heq : VfB (nuFI Δ) (yFI Δ) * (KFI * (2 * (10 / 9 : ℝ) ^ k) ^ 2)
          * (Real.log KFI + 2 * Real.log (2 * (10 / 9 : ℝ) ^ k)) ^ (2 * k + 1)
          / ((2 * k + 1).factorial : ℝ)
        = VfB (nuFI Δ) (yFI Δ) * phiTerm KFI k := by
      rw [phiTerm]; ring
    rw [heq] at h0
    exact h0
  exact le_trans hcm (le_trans hstep1 hstep2)

/-! ## Summation over the odd indices -/

lemma phiTerm_nonneg (K : ℝ) (hK : 1 ≤ K) (k : ℕ) : 0 ≤ phiTerm K k := by
  have h1 : 0 ≤ Real.log K := Real.log_nonneg hK
  have h2 : 0 ≤ Real.log (2 * (10 / 9 : ℝ) ^ k) :=
    Real.log_nonneg (one_le_two_mul_pow k)
  have h3 : 0 ≤ Real.log K + 2 * Real.log (2 * (10 / 9 : ℝ) ^ k) := by linarith
  have hnum : 0 ≤ K * (2 * (10 / 9 : ℝ) ^ k) ^ 2
      * (Real.log K + 2 * Real.log (2 * (10 / 9 : ℝ) ^ k)) ^ (2 * k + 1) :=
    mul_nonneg (mul_nonneg (le_trans zero_le_one hK) (sq_nonneg _)) (pow_nonneg h3 _)
  rw [phiTerm]
  exact div_nonneg hnum (Nat.cast_nonneg _)

lemma phiFI_nonneg (K : ℝ) (hK : 1 ≤ K) (n : ℕ) : 0 ≤ phiFI K n := by
  rw [phiFI]
  split_ifs with hn
  · exact phiTerm_nonneg K hK _
  · exact le_refl 0

lemma sum_odd_phiFI (K : ℝ) (N : ℕ) :
    (∑ n ∈ (Finset.range N).filter Odd, phiFI K n)
      = ∑ k ∈ Finset.range (N / 2), phiTerm K k := by
  have himg : (Finset.range N).filter Odd = (Finset.range (N / 2)).image (fun k => 2 * k + 1) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hn, hodd⟩
      obtain ⟨k, rfl⟩ := hodd
      exact ⟨k, by omega, by ring⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨by omega, k, by ring⟩
  rw [himg, Finset.sum_image]
  · refine Finset.sum_congr rfl fun k hk => ?_
    rw [phiFI]
    have hodd : Odd (2 * k + 1) := ⟨k, by ring⟩
    rw [if_pos hodd]
    congr 1
    omega
  · intro x _ y _ hxy
    simp only at hxy
    omega

/-! ## The main theorem -/

theorem TnB_FIgtil_perLayer :
    ∃ φ : ℕ → ℝ, (∀ n : ℕ, 0 ≤ φ n) ∧
      (∃ K : ℝ, 0 < K ∧ ∀ N : ℕ, ∑ n ∈ (Finset.range N).filter Odd, φ n ≤ K) ∧
      ∀ Δ : ℕ, 3 ≤ Δ → ∀ n : ℕ, Odd n →
        Work.FIChain.TnB 19
            (fun d : ℕ => Submission.ASP.FIgtil d
              * Work.FIChain.hSieveC Submission.ASP.FIgtil (1 / Real.log (Δ : ℝ)) d)
            n (Δ : ℝ)
            ((⌈(Δ : ℝ) ^ ((1 : ℝ) / 20)⌉₊ : ℝ) + 1)
          ≤ φ n * Work.FIChain.VfB
            (fun d : ℕ => Submission.ASP.FIgtil d
              * Work.FIChain.hSieveC Submission.ASP.FIgtil (1 / Real.log (Δ : ℝ)) d)
            ((⌈(Δ : ℝ) ^ ((1 : ℝ) / 20)⌉₊ : ℝ) + 1) := by
  obtain ⟨Φ, hΦpos, hΦ⟩ := phiSeries_bound_aux KFI KFI_one_le
  refine ⟨phiFI KFI, fun n => phiFI_nonneg KFI KFI_one_le n, ⟨Φ, hΦpos, ?_⟩, ?_⟩
  · intro N
    rw [sum_odd_phiFI]
    exact hΦ (N / 2)
  · intro Δ hΔ n hn
    obtain ⟨k, rfl⟩ := hn
    have hFI : ∀ p : ℕ, p.Prime → Submission.ASP.FIgtil p ≤ 1 / 3 := fun p hp =>
      FIgtil_prime_le_third p hp
    have hlin : LinNormKup (nuFI Δ) KFI 2 (Δ : ℝ) := nuFI_LinNormKup_aux Δ hΔ
    have hν0 : ∀ p : ℕ, p.Prime → 0 ≤ nuFI Δ p := fun p _ => nuFI_nonneg Δ p
    have hν1 : ∀ p : ℕ, p.Prime → nuFI Δ p ≤ 1 / 2 := fun p hp => nuFI_le_half_of hFI Δ hΔ p hp
    have hD0 : (0 : ℝ) ≤ (Δ : ℝ) := by positivity
    have hy2 : (2 : ℝ) ≤ yFI Δ := by
      rw [yFI_eq_yN]; exact_mod_cast yN_ge_two Δ hΔ
    have hcm : TnB 19 (nuFI Δ) (2 * k + 1) (Δ : ℝ) (yFI Δ)
        ≤ VfB (nuFI Δ) (levC 19 (Δ : ℝ) k : ℝ)
            * (windowMass (nuFI Δ) (levC 19 (Δ : ℝ) k) (yFI Δ)) ^ (2 * k + 1)
            / ((2 * k + 1).factorial : ℝ) :=
      chainMassTnB 19 (by norm_num) hν0 hν1 k (Δ : ℝ) (yFI Δ) hD0 hy2
    have hcy : levC 19 (Δ : ℝ) k ≤ yN Δ := levC_le_yN Δ hΔ k
    have hc2 : 2 ≤ levC 19 (Δ : ℝ) k := levC_ge_two Δ k
    have hyND : (yN Δ : ℝ) ≤ (Δ : ℝ) := by exact_mod_cast yN_le_Delta Δ hΔ
    have hyD : yFI Δ ≤ (Δ : ℝ) := by rw [yFI_eq_yN]; exact hyND
    have hVr : VfB (nuFI Δ) (levC 19 (Δ : ℝ) k : ℝ)
        ≤ VfB (nuFI Δ) (yFI Δ) * (KFI * UPer Δ k ^ 2) := by
      have h := VfB_ratio_le_LinNormKup (ν := nuFI Δ) (C := KFI) (κ := 2) (D := (Δ : ℝ))
        hlin (fun p hp => hν1 p hp) hc2 hcy hyND
      rw [← yFI_eq_yN] at h
      have h2 : (Real.log (yFI Δ) / Real.log ((levC 19 (Δ : ℝ) k : ℕ) : ℝ)) ^ (2 : ℝ)
          = UPer Δ k ^ 2 := by
        rw [Real.rpow_two, pow_two]
        unfold UPer
        ring
      rw [h2] at h
      exact h
    have hWm : windowMass (nuFI Δ) (levC 19 (Δ : ℝ) k) (yFI Δ)
        ≤ Real.log KFI + 2 * Real.log (UPer Δ k) := by
      have h := sum_nu_le_LinNormKup (ν := nuFI Δ) (C := KFI) (κ := 2) (D := (Δ : ℝ))
        hlin hν0 (fun p hp => hν1 p hp) (show (2:ℝ) ≤ ((levC 19 (Δ : ℝ) k : ℕ) : ℝ) by
          exact_mod_cast hc2)
        (show ((levC 19 (Δ : ℝ) k : ℕ) : ℝ) ≤ yFI Δ by rw [yFI_eq_yN]; exact_mod_cast hcy)
        hyD KFI_pos
      have hL : windowMass (nuFI Δ) (levC 19 (Δ : ℝ) k) (yFI Δ)
          = ∑ p ∈ (Nat.primesBelow ⌈yFI Δ⌉₊).filter
              (fun p : ℕ => ((levC 19 (Δ : ℝ) k : ℕ) : ℝ) ≤ (p : ℝ)), nuFI Δ p := by
        rw [windowMass]
        refine Finset.sum_congr ?_ (fun p _ => rfl)
        ext p
        simp only [Finset.mem_filter, Nat.cast_le]
      rw [hL]
      exact h
    have hkey := perLayer_step Δ hΔ k hν0 hν1 hVr hWm hcm
    have hphi : phiFI KFI (2 * k + 1) = phiTerm KFI k := by
      rw [phiFI]
      have hodd : Odd (2 * k + 1) := ⟨k, by ring⟩
      rw [if_pos hodd]
      congr 1
      omega
    change TnB 19 (nuFI Δ) (2 * k + 1) (Δ : ℝ) (yFI Δ)
        ≤ phiFI KFI (2 * k + 1) * VfB (nuFI Δ) (yFI Δ)
    rw [hphi]
    exact mul_comm (VfB (nuFI Δ) (yFI Δ)) (phiTerm KFI k) ▸ hkey

end

end Work.FIChain
