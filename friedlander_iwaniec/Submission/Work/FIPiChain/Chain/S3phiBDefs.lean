/-
# `Submission.Work.FIChain.S3phiBstarDefs` — vocabulary for the `§4–§7` window identity at `HasBc.val`

This module collects

* the **abbreviations** of the `§4–§7` statement `Work.FIChain.S3phi_Bstar_v2` (the window
  condition, the two windows, the rate `loglog x/log x`, the integrand `Φ`), so that the four
  per-summand estimates of that statement can be stated compactly; and

* a **verified diagnosis** of the quantifier structure of `Work.FIChain.SieveInput`: its only
  occurrence of `C_sieve` is the sieve inequality
  `∑_{ν ≤ Δ, ♠} λ_ν(g ν hSieve g ε ν) ≤ C_sieve · ∏_{p < Δ}(1 - g p hSieve g ε p)`, whose
  right-hand side is a *positive* multiple of `C_sieve`.  Hence `SieveInput` bounds `C_sieve` only
  **from below**: for the weight `λ = δ₁` (`Work.FIChain.lamδ`, `λ 1 = 1`, `λ ν = 0` otherwise) the
  admissible constants are exactly `C_sieve ≥ 1/∏_{p<Δ}(1 - g p hSieve g ε p)`
  (`SieveInput_lamδ_iff`), and they are **unbounded above** (`exists_SieveInput_lamδ_large`).
  See the discussion in `Submission/Work/FIChain/S3phi_Bstar_v2.lean`.
-/
import Mathlib
import Submission.Work.FIPiChain.HasB
import Submission.Work.FIChain.Defs
import Submission.Work.FIChain.scale_factsC
import Submission.Work.FIChain.window_marginsC
import Submission.Work.FITop.BformAtilEqXsum
import Submission.Work.FITop.AtilTauPowFourLe
import Submission.Work.FITop.Defs
import Submission.ASP.S7c
import Submission.ASP.S8b
import Submission.ASP.S20
import Submission.ASP.S21
import Submission.ASP.S22
import Submission.ASP.S23
import Submission.ASP.S24
import Submission.ASP.S25
import Submission.Work.FITop.SingleDvdTauSqLe
import Submission.Work.FITop.WindowRangeMarginsChain
import Submission.Work.FITop.BprimeWindowDelta1
import Submission.Work.FITop.RangeCheckChain
import Submission.ASP.S30
import Submission.Work.FITop.WolkeSquarefreeTau
import Submission.Work.FITop.AdTauAggregate
import Submission.Work.FITop.SumIteDivDvd
import Submission.Work.FIChain.rhoWindowC_param
import Submission.Work.FITop.RhoWindowCProp41

set_option autoImplicit false
set_option maxHeartbeats 1600000

open Work.FIChain

namespace Work.FIPiChain

variable [HasBc]

open Finset

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. The vocabulary of the `§4–§7` statement at `HasBc.val` -/

/-- The range condition `x^{1/4+1/64} + 2 < Yc x HasBc.val / Deltac x` of the corrected family
(`window_marginsC` at `η = 1/64`, `B = HasBc.val`). -/
def s3phiCond (x : ℕ) : Prop :=
  (x : ℝ) ^ ((1 : ℝ) / 4 + 1 / 64) + 2 < Yc x HasBc.val / (Deltac x : ℝ)

/-- The `y`-window `[Yc x HasBc.val, e·Yc x HasBc.val]` of the companion's identity (3.4). -/
def s3phiYwin (x : ℕ) : Set ℝ := Set.Icc (Yc x HasBc.val) (Real.exp 1 * Yc x HasBc.val)

/-- The `z`-window `[zc x HasBc.val, e·zc x HasBc.val]`. -/
def s3phiZwin (x : ℕ) : Set ℝ := Set.Icc (zc x HasBc.val) (Real.exp 1 * zc x HasBc.val)

/-- The rate `loglog x / log x` of the `§4–§7` statement. -/
def s3phiRate (x : ℕ) : ℝ := Real.log (Real.log (x : ℝ)) / Real.log (x : ℝ)

/-- The `§4–§7` part of the companion's identity (3.4):
`Φ(z) = ∫_{Yc}^{e·Yc} (T − T₂ + S₂ + S₁)(y,z) dy/y`. -/
def s3phiPhi (x : ℕ) (lam : ℕ → ℝ) (z : ℝ) : ℝ :=
  ∫ y in Yc x HasBc.val..(Real.exp 1 * Yc x HasBc.val),
    (Submission.ASP.Tsum atilc lam (x : ℝ) y - Submission.ASP.Tsum2 atilc lam (x : ℝ) y z
      + Submission.ASP.S2 atilc lam x y z (sc x HasBc.val * y)
      + Submission.ASP.S1 atilc lam x (sc x HasBc.val * y) (sc x HasBc.val * z)) / y

/-- The `T`-summand test function of `s3phiPhi`, with the normalisation `H·Ã(x)` removed. -/
def s3phiT (x : ℕ) (lam : ℕ → ℝ) (y : ℝ) : ℝ :=
  Submission.ASP.Tsum atilc lam (x : ℝ) y

/-- The `T₂`-summand test function of `s3phiPhi`. -/
def s3phiT2 (x : ℕ) (lam : ℕ → ℝ) (y z : ℝ) : ℝ :=
  Submission.ASP.Tsum2 atilc lam (x : ℝ) y z

/-- The `S₂`-summand test function of `s3phiPhi`. -/
def s3phiS2 (x : ℕ) (lam : ℕ → ℝ) (y z : ℝ) : ℝ :=
  Submission.ASP.S2 atilc lam x y z (sc x HasBc.val * y)

/-- The `S₁`-summand test function of `s3phiPhi`. -/
def s3phiS1 (x : ℕ) (lam : ℕ → ℝ) (y z : ℝ) : ℝ :=
  Submission.ASP.S1 atilc lam x (sc x HasBc.val * y) (sc x HasBc.val * z)

/-! ## 2. `SieveInput` bounds `C_sieve` only from below -/

/-- `ρ(1) = 1` and `ρ(n) = 0` for `n = 0` for the weight `λ = δ₁`. -/
lemma rhoOf_lamδ (n : ℕ) : Submission.ASP.rhoOf lamδ n = if n = 0 then 0 else 1 := by
  unfold Submission.ASP.rhoOf lamδ
  rw [Finset.sum_ite_eq']
  by_cases h : n = 0
  · simp [h]
  · simp [Nat.mem_divisors, h]

/-- `hSieveC` at `ν = 1`. -/
lemma hSieveC_one (g : ℕ → ℝ) (ε : ℝ) : hSieveC g ε 1 = 1 := by
  simp [hSieveC]

/-- `hSieveC` at a prime. -/
lemma hSieveC_prime (g : ℕ → ℝ) (ε : ℝ) {p : ℕ} (hp : p.Prime) :
    hSieveC g ε p = (1 + (p : ℝ) ^ (-ε)) / (1 + (p : ℝ) ^ (-ε) * g p) := by
  simp [hSieveC, hp.primeFactors]

/-- The local factor of the sieve inequality, in closed form at a prime. -/
lemma one_sub_gtil_mul_hSieveC (g : ℕ → ℝ) (ε : ℝ) {p : ℕ} (hp : p.Prime)
    (hden : 1 + (p : ℝ) ^ (-ε) * g p ≠ 0) :
    1 - g p * hSieveC g ε p = (1 - g p) / (1 + (p : ℝ) ^ (-ε) * g p) := by
  rw [hSieveC_prime g ε hp, ← mul_div_assoc, sub_div' hden]
  congr 1
  ring

lemma lamδ_one : lamδ 1 = 1 := by simp [lamδ]

lemma lamδ_eq_zero {ν : ℕ} (h : ν ≠ 1) : lamδ ν = 0 := by simp [lamδ, h]

/-- **Characterisation of the admissible `C_sieve` for the trivial weight `λ = δ₁`.**

`λ = δ₁` satisfies the eight conjuncts of `SieveInput` *for free* (it is the trivial non-negative
sieve with `ρ ≡ 1`, hence `ρ ≥ 0` and both `lcm`/`gcd` positivity conjuncts reduce to `g d ≥ 0`
and `1 ≥ 0`), and the sieve inequality is the inequality `1 ≤ C · ∏_{p<Δ}(1 − g p hSieve p)`,
whose right side is a *positive* multiple of `C`.  Hence the admissible constants are exactly
`0 < C ∧ 1 ≤ C·∏(…)`, i.e. an **upper-unbounded** set. -/
lemma SieveInput_lamδ_iff {Δ : ℕ} (hΔ : 1 ≤ Δ) (C : ℝ) :
    SieveInput Submission.ASP.FIgtil Δ lamδ C ↔
      0 < C ∧ (1 : ℝ) ≤ C * ∏ p ∈ Nat.primesBelow Δ,
        (1 - Submission.ASP.FIgtil p
          * hSieveC Submission.ASP.FIgtil (1 / Real.log Δ) p) := by
  constructor
  · intro h
    obtain ⟨-, -, -, -, -, -, -, hC, hsieve⟩ := h
    refine ⟨hC, ?_⟩
    refine le_trans ?_ hsieve
    rw [Finset.sum_eq_single 1]
    · rw [lamδ_one, Submission.ASP.FIgtil_one, hSieveC_one, mul_one, one_mul]
    · intro ν hν hne
      rw [lamδ_eq_zero hne, zero_mul]
    · intro hmem
      exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_refl 1, hΔ⟩, squarefree_one⟩) hmem
  · rintro ⟨hC, hsieve⟩
    refine ⟨lamδ_one, ?_, ?_, ?_, ?_, ?_, ?_, hC, ?_⟩
    · intro ν hν
      exact lamδ_eq_zero (fun h => by omega)
    · intro ν hν
      exact lamδ_eq_zero (fun h => by rw [h] at hν; exact hν squarefree_one)
    · intro ν
      by_cases h : ν = 1
      · rw [h, lamδ_one]; norm_num
      · rw [lamδ_eq_zero h]; norm_num
    · intro n
      rw [rhoOf_lamδ]
      split <;> norm_num
    · intro d
      rw [Finset.sum_eq_single 1]
      · rw [lamδ_one, one_mul, Nat.lcm_one_left]
        exact Submission.ASP.FIgtil_nonneg d
      · intro ν hν hne
        rw [lamδ_eq_zero hne, zero_mul]
      · intro hmem
        exact absurd (Finset.mem_Icc.mpr ⟨le_refl 1, hΔ⟩) hmem
    · intro d
      rw [Finset.sum_eq_single 1]
      · rw [lamδ_one, one_mul, Nat.gcd_one_left, Nat.div_one, Submission.ASP.FIgtil_one]
        norm_num
      · intro ν hν hne
        rw [lamδ_eq_zero hne, zero_mul]
      · intro hmem
        exact absurd (Finset.mem_Icc.mpr ⟨le_refl 1, hΔ⟩) hmem
    · refine le_trans ?_ hsieve
      rw [Finset.sum_eq_single 1]
      · rw [lamδ_one, Submission.ASP.FIgtil_one, hSieveC_one, mul_one, one_mul]
      · intro ν hν hne
        rw [lamδ_eq_zero hne, zero_mul]
      · intro hmem
        exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_refl 1, hΔ⟩, squarefree_one⟩) hmem

/-- The sieve product of `SieveInput` is **strictly positive** (each local factor is
`(1 - g p)/(1 + p^{-ε} g p) > 0` because `g p < 1` for primes). -/
lemma sieveProd_pos {Δ : ℕ} :
    0 < ∏ p ∈ Nat.primesBelow Δ,
        (1 - Submission.ASP.FIgtil p
          * hSieveC Submission.ASP.FIgtil (1 / Real.log Δ) p) := by
  refine Finset.prod_pos (fun p hp => ?_)
  obtain ⟨-, hpp⟩ := Nat.mem_primesBelow.mp hp
  have hu : (0 : ℝ) ≤ (p : ℝ) ^ (-(1 / Real.log Δ)) := Real.rpow_nonneg (Nat.cast_nonneg p) _
  have hden : 0 < 1 + (p : ℝ) ^ (-(1 / Real.log Δ)) * Submission.ASP.FIgtil p :=
    add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hu (Submission.ASP.FIgtil_nonneg p))
  rw [one_sub_gtil_mul_hSieveC Submission.ASP.FIgtil (1 / Real.log Δ) hpp (ne_of_gt hden)]
  exact div_pos (sub_pos.mpr (Submission.ASP.FIgtil_lt_one hpp)) hden

/-- **For the weight `λ = δ₁` the constant `C_sieve` is unbounded above.**  For every level
`Δ ≥ 1` and every real `M` there is a pair `(λ, C_sieve)` with `λ = δ₁`, `M ≤ C_sieve` and
`SieveInput FIgtil Δ λ C_sieve`.

Consequently a statement that quantifies over `(λ, C_sieve)` subject to `SieveInput` alone — such
as `Work.FIChain.S3phi_Bstar_v2` — must hold *simultaneously for every bound* on `C_sieve`, while
every estimate of `§6` available in this workspace (`Submission.ASP.S1_bound_of_sieve`,
`Work.FIChain.LocalS6c.S1_bound_of_sieve`, `M6_le`) is *proportional to* `C_sieve`. -/
theorem exists_SieveInput_lamδ_large {Δ : ℕ} (hΔ : 1 ≤ Δ) (M : ℝ) :
    ∃ C : ℝ, M ≤ C ∧ SieveInput Submission.ASP.FIgtil Δ lamδ C := by
  set P : ℝ := ∏ p ∈ Nat.primesBelow Δ,
      (1 - Submission.ASP.FIgtil p
        * hSieveC Submission.ASP.FIgtil (1 / Real.log Δ) p) with hPdef
  have hPpos : 0 < P := sieveProd_pos
  refine ⟨max (max M 1) (1 / P), le_trans (le_max_left _ _) (le_max_left _ _), ?_⟩
  rw [SieveInput_lamδ_iff hΔ]
  have hCpos : 0 < max (max M 1) (1 / P) :=
    lt_of_lt_of_le zero_lt_one (le_trans (le_max_right M 1) (le_max_left _ _))
  refine ⟨hCpos, ?_⟩
  have hle : 1 / P ≤ max (max M 1) (1 / P) := le_max_right _ _
  calc (1 : ℝ) = (1 / P) * P := by field_simp
    _ ≤ max (max M 1) (1 / P) * P := mul_le_mul_of_nonneg_right hle hPpos.le

end

end Work.FIPiChain
