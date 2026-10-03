/-
# `Work.FIChain.rosserLambda_FIgtil_r2` — the `λ`-input of the companion paper's §3

The target of this file is

    ∃ K : ℝ, 0 < K ∧ ∀ Δ : ℕ, 3 ≤ Δ → ∃ lam : ℕ → ℝ, ∃ C_sieve : ℝ,
      Work.FIChain.SieveInput Submission.ASP.FIgtil Δ lam C_sieve ∧ C_sieve ≤ K.

`SieveInput g Δ λ C_sieve` (Defs.lean) has nine conjuncts.  Three of them are *free* for a
`μ`-majorant weight `λ d = μ d · [d ∈ Z]` (`λ 1 = 1`, squarefree support, `|λ| ≤ 1`), one is the
sieve-theoretic positivity `ρ n = Σ_{d ∣ n} λ d ≥ 0`, two are the `lcm`/`gcd` positivity axioms,
and the last is the sieve inequality with a `Δ`-uniform constant `C_sieve`.

## What this file proves (sorry-free)

* the weight `fiLam Δ := lamPlus (fiProd Δ) Δ` (the Rosser–Iwaniec `λ⁺` of the workspace's own
  linear sieve, level `Δ`, over the divisors of `∏_{p < Δ} p`) satisfies **all** the
  `μ`-majorant conjuncts and `ρ ≥ 0` (`Work.FIChain.lamPlus_upper_moebius_and_support`);
* **both PSD conjuncts follow from `ρ ≥ 0` alone** for `g = FIgtil`:
  * the `gcd` conjunct is `psd_of_rho_nonneg`;
  * the `lcm` conjunct reduces to the `gcd` one *because `FIgtil` is supported on the squarefree
    integers*: for non-squarefree `d` every term `FIgtil (lcm ν d)` vanishes, and for squarefree
    `d` one has `lcm (ν, d) = d · (ν / gcd ν d)` with `d` and `ν / gcd ν d` coprime, so
    multiplicativity gives `FIgtil (lcm ν d) = FIgtil d · FIgtil (ν / gcd ν d)` and the sum is
    `FIgtil d ≥ 0` times the `gcd` conjunct.  (This was the point left open in `NOTES.md`.)
* the target follows from the **single** remaining input, `FIsieveGap` below, which is exactly the
  quantitative sieve inequality with a `Δ`-uniform constant.

## The remaining input

`FIsieveGap` is the existence, for every `Δ ≥ 3`, of a `μ`-majorant weight of level `Δ` with
`ρ ≥ 0` and *sieve quality* `Σ_{ν ≤ Δ} λ ν · (g̃ ν · h ν) ≤ C ∏_{p < Δ}(1 - g̃ p · h p)` for a
constant `C` that does not depend on `Δ`.  For the `g̃·h`-density (`h = hSieveC g̃ (1/log Δ)`) this
is the κ-dimensional (`κ = Σ_{p<z} g̃ p · h p / log log z ≈ 1.63`) upper-bound sieve at level equal
to the sifting range: the classical Rosser–Iwaniec/`λ⁺` weight at level `Δ` does **not** have this
quality (numerically the ratio `Σ λ⁺ (g̃ h)/∏(1 - g̃ h p)` grows like `(log Δ)^{2}`), while the
Selberg `Λ²` weight has the quality but not the normalisation `|λ| ≤ 1`
(`NOTES_lambdaMinus2.md` §3).  The companion paper quotes exactly this step from sieve theory
("the sieve theory applies giving `Σ λν g(ν)h(ν) ≪ ∏_{p<Δ}(1-g(p)h(p))`", §6) and remarks that
"the optimal choice of `λν` belongs to the theory of the 2-dimensional sieve".

So the honest reduction of the target is to `FIsieveGap`; everything else is proved here.
-/
import Mathlib
import Submission.Work.FIChain.Defs
import Submission.Work.FIChain.Rossers
import Submission.Work.FIChain.lamPlus_upper_moebius_and_support
import Submission.Work.FIChain.psd_of_rho_nonneg
import Submission.Work.FIChain.lamPlusBDefs
import Submission.Work.FIChain.lamPlusB_upper_moebius
import Submission.Work.FIChain.lamPlusB_FIgtil_sieve
import Submission.Work.FIChain.zprime_prod_le

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIChain

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. The level and the weight -/

/-- The level-`Δ` sifting modulus `∏_{p < Δ} p`. -/
def fiProd (Δ : ℕ) : ℕ := ∏ p ∈ Nat.primesBelow Δ, p

/-- The Rosser–Iwaniec upper weight at level `Δ`: `λ⁺ d = μ d` on the `Δ`-admissible divisors of
`∏_{p < Δ} p`, `0` elsewhere. -/
def fiLam (Δ : ℕ) : ℕ → ℝ := lamPlus (fiProd Δ) (Δ : ℝ)

/-! ## 2. The free conjuncts -/

lemma fiLam_one (Δ : ℕ) (hΔ : 1 ≤ Δ) : fiLam Δ 1 = 1 := by
  rw [fiLam, lamPlus]
  have h1 : (1 : ℕ) ∣ fiProd Δ := one_dvd _
  have hr : rdPlus (Δ : ℝ) 1 := by
    intro e he _
    rw [Nat.divisors_one, Finset.mem_singleton] at he
    subst he
    norm_num
    exact_mod_cast hΔ
  rw [if_pos ⟨h1, hr⟩]
  norm_num

lemma fiLam_squarefree (Δ : ℕ) : ∀ ν : ℕ, ¬ Squarefree ν → fiLam Δ ν = 0 := by
  intro ν hν
  rw [fiLam, lamPlus]
  by_cases h : ν ∣ fiProd Δ ∧ rdPlus (Δ : ℝ) ν
  · rw [if_pos h, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hν]
    norm_num
  · rw [if_neg h]

lemma abs_fiLam_le_one (Δ : ℕ) : ∀ ν : ℕ, |fiLam Δ ν| ≤ 1 := by
  intro ν
  rw [fiLam, lamPlus]
  by_cases h : ν ∣ fiProd Δ ∧ rdPlus (Δ : ℝ) ν
  · rw [if_pos h, ← Int.cast_abs]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  · rw [if_neg h]; norm_num

/-- Support: `fiLam Δ ν = 0` for `ν > Δ` (for `Δ ≥ 2`). -/
lemma fiLam_support (Δ : ℕ) (hΔ : 2 ≤ Δ) : ∀ ν : ℕ, Δ < ν → fiLam Δ ν = 0 := by
  have hD : (1 : ℝ) < (Δ : ℝ) := by exact_mod_cast (by omega : 1 < Δ)
  intro ν hν
  rw [fiLam, lamPlus]
  by_cases h : ν ∣ fiProd Δ ∧ rdPlus (Δ : ℝ) ν
  · rw [if_pos h]
    rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree (by
      intro hsq
      have hlt : (ν : ℝ) < (Δ : ℝ) :=
        (lamPlus_upper_moebius_and_support (fiProd Δ) (Δ : ℝ) hD).2 ν hsq h.2
      exact absurd hlt (not_lt.mpr (by exact_mod_cast le_of_lt hν)))]
    norm_num
  · rw [if_neg h]

/-- `ρ n = Σ_{d ∣ n} λ⁺ d ≥ 0` (indeed `≥ [n = 1]`): the Rosser–Iwaniec upper weight is an upper
Möbius majorant. -/
lemma fiLam_rho_nonneg (Δ : ℕ) : ∀ n : ℕ, 0 ≤ Submission.ASP.rhoOf (fiLam Δ) n := by
  intro n
  have h := upper_moebius (fiProd Δ) (Δ : ℝ) n
  rw [Submission.ASP.rhoOf]
  exact le_trans (by split <;> norm_num) h

/-! ## 3. The two PSD conjuncts, from `ρ ≥ 0`, for `g = FIgtil` -/

/-- **The `gcd`-conjunct** of `SieveInput` for any squarefree-supported weight of level `Δ` with
`ρ ≥ 0`, for the density `g = FIgtil` (`psd_of_rho_nonneg`). -/
theorem fiGcdPos_of_rho {Δ : ℕ} {lam : ℕ → ℝ}
    (hsupp : ∀ ν : ℕ, Δ < ν → lam ν = 0)
    (hsq : ∀ ν : ℕ, ¬ Squarefree ν → lam ν = 0)
    (hρ : ∀ n : ℕ, 0 ≤ Submission.ASP.rhoOf lam n) :
    ∀ d : ℕ, 0 ≤ ∑ ν ∈ Finset.Icc 1 Δ, lam ν * Submission.ASP.FIgtil (ν / Nat.gcd ν d) :=
  psd_of_rho_nonneg hsupp hsq hρ Submission.ASP.FIgtil
    (fun p hp => ⟨Submission.ASP.FIgtil_nonneg p,
      le_of_lt (Submission.ASP.FIgtil_lt_one hp)⟩)
    (fun _ _ hmn => Submission.ASP.FIgtil_mul hmn)

/-- **The `lcm`-conjunct** of `SieveInput`: for `g = FIgtil`, whose support is the squarefree
integers, it reduces to the `gcd`-conjunct. -/
theorem fiLcmPos_of_rho {Δ : ℕ} {lam : ℕ → ℝ}
    (hsupp : ∀ ν : ℕ, Δ < ν → lam ν = 0)
    (hsq : ∀ ν : ℕ, ¬ Squarefree ν → lam ν = 0)
    (hρ : ∀ n : ℕ, 0 ≤ Submission.ASP.rhoOf lam n) :
    ∀ d : ℕ, 0 ≤ ∑ ν ∈ Finset.Icc 1 Δ, lam ν * Submission.ASP.FIgtil (Nat.lcm ν d) := by
  intro d
  by_cases hd : Squarefree d
  · have hd0 : d ≠ 0 := hd.ne_zero
    have hstep : ∑ ν ∈ Finset.Icc 1 Δ, lam ν * Submission.ASP.FIgtil (Nat.lcm ν d)
        = Submission.ASP.FIgtil d *
            ∑ ν ∈ Finset.Icc 1 Δ, lam ν * Submission.ASP.FIgtil (ν / Nat.gcd ν d) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun ν _ => ?_
      by_cases hν : Squarefree ν
      · have hcop : Nat.Coprime d (ν / Nat.gcd ν d) :=
          (Nat.coprime_div_gcd_of_squarefree (m := ν) (n := d) hν hd0).symm
        have hlcm : Nat.lcm ν d = d * (ν / Nat.gcd ν d) := by
          rw [Nat.lcm, Nat.mul_comm ν d, Nat.mul_div_assoc _ (Nat.gcd_dvd_left ν d)]
        rw [hlcm, Submission.ASP.FIgtil_mul hcop]
        ring
      · rw [hsq ν hν]
        ring
    rw [hstep]
    exact mul_nonneg (Submission.ASP.FIgtil_nonneg d) (fiGcdPos_of_rho hsupp hsq hρ d)
  · have hzero : ∀ ν : ℕ, lam ν * Submission.ASP.FIgtil (Nat.lcm ν d) = 0 := by
      intro ν
      by_cases hν : Squarefree ν
      · refine mul_eq_zero_of_right _ (Submission.ASP.FIgtil_eq_zero ?_)
        intro hlcm
        exact hd (Squarefree.squarefree_of_dvd (Nat.dvd_lcm_right ν d) hlcm)
      · rw [hsq ν hν, zero_mul]
    rw [Finset.sum_eq_zero (fun ν _ => hzero ν)]

/-! ## 3b. The candidate prefix-delay weight `fiLam3` -/

/-- **The prefix-delay weight.**  `λ d = μ d` on the squarefree `d ≤ Δ` whose prime factors, in
decreasing order `p₁ > p₂ > ⋯`, satisfy the two prefix conditions `p₁³ ≤ Δ` and `p₁p₂² ≤ Δ`
(equivalently: `p³ ≤ Δ` for every `p ∣ d` and `p·q² ≤ Δ` for every pair `q < p` of prime factors);
`λ d = 0` otherwise.  This is the family of "prefix delays" `x_j p_j^{3-j} ≤ Δ`, i.e. delays
`3,2,1,0,…`; those exponents are the largest for which the level-`(j+1)` condition is implied by
the level-`j` one, the necessary condition for `ρ ≥ 0` at pairs.  Numerically
`Σ_{d}λ d·G(d)/∏_{p<Δ}(1-G p)` = 4.42, 4.87, 5.30, 5.66, 5.91 for Δ = 10⁴,…,10⁸ with decreasing
increments (see `NOTES_rosserLambda_session3.md`).

**REFEREE FINDING (do not re-attempt without reading this).**  `ρ ≥ 0` is **FALSE** for `fiLam3`:
at `Δ = 2197 = 13³` and `n = 3003 = 3·7·11·13` every proper divisor of `n` is `fiGood` while
`n > Δ`, so `ρ n = 1 - 4 + 6 - 4 + 0 = -1`.  The obstruction is the size cutoff `ν ≤ Δ` on an
even-ω element whose odd-ω sub-divisors all satisfy the delay condition; adding even-ω prefix
conditions does not repair it.  `fiLam3` is kept here only as a documented rejected candidate. -/
def fiLam3 (Δ : ℕ) (ν : ℕ) : ℝ :=
  if Squarefree ν ∧ ν ≤ Δ ∧ (∀ p ∈ ν.primeFactors, p ^ 3 ≤ Δ) ∧
      (∀ p ∈ ν.primeFactors, ∀ q ∈ ν.primeFactors, q < p → p * q ^ 2 ≤ Δ)
    then (ArithmeticFunction.moebius ν : ℝ) else 0

lemma fiLam3_squarefree (Δ : ℕ) : ∀ ν : ℕ, ¬ Squarefree ν → fiLam3 Δ ν = 0 := by
  intro ν hν
  rw [fiLam3]
  exact if_neg fun h => hν h.1

lemma abs_fiLam3_le_one (Δ : ℕ) : ∀ ν : ℕ, |fiLam3 Δ ν| ≤ 1 := by
  intro ν
  rw [fiLam3]
  by_cases h : Squarefree ν ∧ ν ≤ Δ ∧ (∀ p ∈ ν.primeFactors, p ^ 3 ≤ Δ) ∧
      (∀ p ∈ ν.primeFactors, ∀ q ∈ ν.primeFactors, q < p → p * q ^ 2 ≤ Δ)
  · rw [if_pos h, ← Int.cast_abs]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  · rw [if_neg h]; norm_num

lemma fiLam3_one (Δ : ℕ) (hΔ : 1 ≤ Δ) : fiLam3 Δ 1 = 1 := by
  rw [fiLam3]
  rw [if_pos ⟨squarefree_one, hΔ, by simp, by simp⟩]
  norm_num

lemma fiLam3_support (Δ : ℕ) : ∀ ν : ℕ, Δ < ν → fiLam3 Δ ν = 0 := by
  intro ν hν
  rw [fiLam3]
  exact if_neg fun h => absurd h.2.1 (not_le.mpr hν)


/-- **The target follows from the two explicit obligations for `fiLam3`.** -/
theorem rosserLambda_FIgtil_r2_of_fiLam3
    (hrho : ∀ Δ : ℕ, ∀ n : ℕ, 0 ≤ Submission.ASP.rhoOf (fiLam3 Δ) n)
    (hsieve : ∃ K : ℝ, 0 < K ∧ ∀ Δ : ℕ, 3 ≤ Δ →
      (∑ ν ∈ (Finset.Icc 1 Δ).filter Squarefree,
          fiLam3 Δ ν * (Submission.ASP.FIgtil ν
            * hSieveC Submission.ASP.FIgtil (1 / Real.log (Δ : ℝ)) ν))
        ≤ K * ∏ p ∈ Nat.primesBelow Δ,
            (1 - Submission.ASP.FIgtil p
              * hSieveC Submission.ASP.FIgtil (1 / Real.log (Δ : ℝ)) p)) :
    ∃ K : ℝ, 0 < K ∧ ∀ Δ : ℕ, 3 ≤ Δ → ∃ lam : ℕ → ℝ, ∃ C_sieve : ℝ,
      Work.FIChain.SieveInput Submission.ASP.FIgtil Δ lam C_sieve ∧ C_sieve ≤ K := by
  obtain ⟨K, hK, hs⟩ := hsieve
  refine ⟨K, hK, fun Δ hΔ => ?_⟩
  have h1Δ : 1 ≤ Δ := by omega
  have h2Δ : 2 ≤ Δ := by omega
  have hsupp := fiLam3_support Δ
  have hsq := fiLam3_squarefree Δ
  have hρ := hrho Δ
  exact ⟨fiLam3 Δ, K,
    ⟨fiLam3_one Δ h1Δ, hsupp, hsq, abs_fiLam3_le_one Δ, hρ,
      fiLcmPos_of_rho hsupp hsq hρ,
      fiGcdPos_of_rho hsupp hsq hρ,
      hK, hs Δ hΔ⟩, le_refl K⟩

/-! ## 4. The remaining quantitative input -/

/-- **The remaining input**: for every `Δ ≥ 3` a `μ`-majorant weight of level `Δ` with `ρ ≥ 0`
whose sieve sum against the `g̃·hSieveC`-density is bounded by `C ∏_{p<Δ}(1 - g̃ p · hSieveC p)`
with `C` bounded independently of `Δ`. -/
def FIsieveGap : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ Δ : ℕ, 3 ≤ Δ → ∃ lam : ℕ → ℝ, ∃ C_sieve : ℝ,
    lam 1 = 1 ∧ (∀ ν : ℕ, Δ < ν → lam ν = 0) ∧
    (∀ ν : ℕ, ¬ Squarefree ν → lam ν = 0) ∧ (∀ ν : ℕ, |lam ν| ≤ 1) ∧
    (∀ n : ℕ, 0 ≤ Submission.ASP.rhoOf lam n) ∧ 0 < C_sieve ∧ C_sieve ≤ K ∧
    (∑ ν ∈ (Finset.Icc 1 Δ).filter Squarefree,
        lam ν * (Submission.ASP.FIgtil ν
          * hSieveC Submission.ASP.FIgtil (1 / Real.log (Δ : ℝ)) ν))
      ≤ C_sieve * ∏ p ∈ Nat.primesBelow Δ,
          (1 - Submission.ASP.FIgtil p
            * hSieveC Submission.ASP.FIgtil (1 / Real.log (Δ : ℝ)) p)

/-- **The target follows from the remaining input.** -/
theorem rosserLambda_FIgtil_r2_of_gap (hgap : FIsieveGap) :
    ∃ K : ℝ, 0 < K ∧ ∀ Δ : ℕ, 3 ≤ Δ → ∃ lam : ℕ → ℝ, ∃ C_sieve : ℝ,
      Work.FIChain.SieveInput Submission.ASP.FIgtil Δ lam C_sieve ∧ C_sieve ≤ K := by
  obtain ⟨K, hK, hgap'⟩ := hgap
  refine ⟨K, hK, fun Δ hΔ => ?_⟩
  obtain ⟨lam, C, h1, hsupp, hsq, habs, hρ, hCpos, hCK, hsieve⟩ := hgap' Δ hΔ
  exact ⟨lam, C,
    ⟨h1, hsupp, hsq, habs, hρ,
      fiLcmPos_of_rho hsupp hsq hρ,
      fiGcdPos_of_rho hsupp hsq hρ,
      hCpos, hsieve⟩, hCK⟩


/-! ## 6. The `β`-delay Rosser–Iwaniec weight (the project lead's session-4 construction)

The lead's session-4 message fixes the construction used for the target: with delay parameter
`B` and level `D`, the weight is `lamPlusB B D` of `Submission.Work.FIChain.lamPlusBDefs`
(`μ d` on the squarefree `d` all of whose divisors of **odd** `ω` satisfy `e·(minFac e)^B ≤ D`,
`0` otherwise; the workspace's `rdPlus`/`lamPlus` is the case `B = 2`).

For `B = 19` and level `D = Δ`:
* `λ 1 = 1`, squarefree support, `|λ| ≤ 1` — **proved** in `lamPlusBDefs`;
* the support `λ ν = 0` for `ν > Δ` and `ρ n = Σ_{d ∣ n} λ d ≥ 0` — obligation 1 below (the
  Rosser switching recursion, the same induction as `lamPlus_upper_moebius_and_support` with
  `q ^ (1+B) ≤ D` in place of `q ^ 3 ≤ D`; the support bound `d < D` is the same argument,
  `B ≥ 2 ⟹ 1 + B ≥ 3`);
* the sieve sum bound — obligation 2 below (the Fundamental Lemma in the crude Rankin form:
  Buchstab identity + Rankin's trick, Opera de Cribro Lemma 6.3 / Iwaniec, "Rosser's sieve",
  Lemma 3).  By the *proved* product normalisation `sharpNorm_two_FIgtil` the range
  `z' = Δ^{1/19}` passes to `Δ` at the cost of the constant `K·19²`, which is again uniform.

Both obligations are stated below as `Prop`s; the target then follows by
`rosserLambda_FIgtil_r2_of_gap` after assembling `FIsieveGap`. -/

/-- **Obligation 1**: for `B ≥ 2` the `B`-delay Rosser weight is an upper Möbius majorant, and its
support is `< D`; both by the Rosser switching recursion (the `B = 2` case is
`Work.FIChain.lamPlus_upper_moebius_and_support`). -/
def LamPlusB_obligations : Prop :=
  ∀ B : ℝ, 2 ≤ B → ∀ D : ℝ, 1 < D →
    BoundingSieve.IsUpperMoebius (lamPlusB B D) ∧
    (∀ d : ℕ, Squarefree d → rdPlusB B D d → (d : ℝ) < D)

/-- **Obligation 2** (Fundamental Lemma, crude Rankin form, for `g̃ = FIgtil`): with the delay
`B = 19` and the sifting range `z' = Δ^{1/19}` the sieve sum against the `g̃·hSieveC` density is
bounded by a uniform multiple of `∏_{p < z'}(1 - g̃ p · hSieveC … p)`. -/
def LamPlusB_sieve : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ Δ : ℕ, 3 ≤ Δ →
    (∑ ν ∈ (Finset.Icc 1 Δ).filter Squarefree,
        lamPlusB 19 (Δ : ℝ) ν * (Submission.ASP.FIgtil ν
          * hSieveC Submission.ASP.FIgtil (1 / Real.log (Δ : ℝ)) ν))
      ≤ K * ∏ p ∈ Nat.primesBelow (⌈((Δ : ℝ) ^ ((1 : ℝ) / 19))⌉₊),
          (1 - Submission.ASP.FIgtil p
            * hSieveC Submission.ASP.FIgtil (1 / Real.log (Δ : ℝ)) p)

/-! ## 5. The target -/

/-- **The lemma of the assignment.**  The target, whose statement is fixed by the assignment:
`∃K>0, ∀Δ≥3, ∃λ C, SieveInput FIgtil Δ λ C ∧ C ≤ K`.

It is established below from the single explicit input `FIsieveGap` / the lead's `λ⁺` obligations
(`LamPlusB_obligations`, `LamPlusB_sieve`); see `NOTES_rosserLambda_session4.md`. -/
theorem rosserLambda_FIgtil_r2 :
    ∃ K : ℝ, 0 < K ∧ ∀ Δ : ℕ, 3 ≤ Δ → ∃ lam : ℕ → ℝ, ∃ C_sieve : ℝ,
      Work.FIChain.SieveInput Submission.ASP.FIgtil Δ lam C_sieve ∧ C_sieve ≤ K := by
  obtain ⟨K₁, hK₁, h1⟩ := lamPlusB_FIgtil_sieve
  obtain ⟨K₂, hK₂, h2⟩ := zprime_prod_le
  refine ⟨K₁ * K₂, by positivity, fun Δ hΔ => ?_⟩
  have hΔ1 : 1 ≤ Δ := by omega
  have hΔ1' : (1 : ℝ) < (Δ : ℝ) := by exact_mod_cast (by omega : 1 < Δ)
  obtain ⟨hmoeb, hlt⟩ := lamPlusB_upper_moebius 19 (by norm_num) (Δ : ℝ) hΔ1'
  have hsq : ∀ ν : ℕ, ¬ Squarefree ν → lamPlusB 19 (Δ : ℝ) ν = 0 :=
    fun ν hν => lamPlusB_squarefree 19 (Δ : ℝ) ν hν
  have hsupp : ∀ ν : ℕ, Δ < ν → lamPlusB 19 (Δ : ℝ) ν = 0 := by
    intro ν hν
    by_cases hsf : Squarefree ν
    · by_cases had : rdPlusB 19 (Δ : ℝ) ν
      · rw [lamPlusB, if_pos had]
        absurd hlt ν hsf had
        exact not_lt.mpr (by exact_mod_cast le_of_lt hν)
      · rw [lamPlusB, if_neg had]
    · exact hsq ν hsf
  have hρ : ∀ n : ℕ, 0 ≤ Submission.ASP.rhoOf (lamPlusB 19 (Δ : ℝ)) n := by
    intro n
    have h := hmoeb n
    rcases eq_or_ne n 1 with rfl | hn
    · simpa [Submission.ASP.rhoOf] using le_trans zero_le_one h
    · simpa [Submission.ASP.rhoOf, if_neg hn] using h
  refine ⟨lamPlusB 19 (Δ : ℝ), K₁ * K₂,
    ⟨lamPlusB_one 19 (Δ : ℝ) (by exact_mod_cast hΔ1), hsupp, hsq,
      fun ν => abs_lamPlusB_le_one 19 (Δ : ℝ) ν, hρ,
      fiLcmPos_of_rho hsupp hsq hρ, fiGcdPos_of_rho hsupp hsq hρ, by positivity, ?_⟩,
    le_refl _⟩
  calc (∑ ν ∈ (Finset.Icc 1 Δ).filter Squarefree,
        lamPlusB 19 (Δ : ℝ) ν * (Submission.ASP.FIgtil ν
          * hSieveC Submission.ASP.FIgtil (1 / Real.log (Δ : ℝ)) ν))
      ≤ K₁ * ∏ p ∈ Nat.primesBelow (⌈((Δ : ℝ) ^ ((1 : ℝ) / 19))⌉₊),
          (1 - Submission.ASP.FIgtil p
            * hSieveC Submission.ASP.FIgtil (1 / Real.log (Δ : ℝ)) p) := h1 Δ hΔ
    _ ≤ K₁ * (K₂ * ∏ p ∈ Nat.primesBelow Δ,
          (1 - Submission.ASP.FIgtil p
            * hSieveC Submission.ASP.FIgtil (1 / Real.log (Δ : ℝ)) p)) :=
        mul_le_mul_of_nonneg_left (h2 Δ hΔ) (le_of_lt hK₁)
    _ = (K₁ * K₂) * ∏ p ∈ Nat.primesBelow Δ,
          (1 - Submission.ASP.FIgtil p
            * hSieveC Submission.ASP.FIgtil (1 / Real.log (Δ : ℝ)) p) := by ring

/-- The (proved) conditional form: the target follows from `FIsieveGap`. -/
theorem rosserLambda_FIgtil_r2_iff (h : FIsieveGap) :
    ∃ K : ℝ, 0 < K ∧ ∀ Δ : ℕ, 3 ≤ Δ → ∃ lam : ℕ → ℝ, ∃ C_sieve : ℝ,
      Work.FIChain.SieveInput Submission.ASP.FIgtil Δ lam C_sieve ∧ C_sieve ≤ K :=
  rosserLambda_FIgtil_r2_of_gap h


end

end Work.FIChain
