import Mathlib
import Submission.Work.FIPiChain.HasB
import Submission.Work.FIChain.Defs
import Submission.Work.FIChain.S3zdev
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
import Submission.Work.FIChain.scale_factsC
import Submission.Work.FIChain.rhoWindowC_param
import Submission.Work.FITop.RhoWindowCProp41
import Submission.Work.FIChain.AcountAtilC_ge_const_mul_rpow
import Submission.Work.FIChain.AcountAtilC_le_const_mul_rpow

set_option autoImplicit false
set_option maxHeartbeats 1600000

open Work.FIChain

namespace Work.FIPiChain

variable [HasBc]

open Finset
open scoped BigOperators

noncomputable section

/-! The completion-deviation sum `Work.FIChain.S3delSum` at the pinned scale
`HasBc.val = 2^31 + 2` is `≪ Ã(x)/log x`, which is what the deviation step
`Work.FIChain.S3avgFix_le_of_zavg` has to absorb.

`S3delSum ã λ x (zc x HasBc.val) = ∑_{zc < n ≤ e·zc} |ã(n)·ρ_λ(n)·Λ(n)|` runs over
`≈ zc x HasBc.val ≍ x^{5/16}` integers only, and `|ρ_λ(n)| ≤ τ(n)` for `|λ| ≤ 1`, while
`|ã(n)| ≤ an(n) ≤ 4·n^{1/4}` (`FIa` is the counting function of `x² + y⁴ = n`), so the sum is
`≪ zc^{5/4}·log²zc ≍ x^{25/64}·log²x`, whereas `Ã(x) ≥ c·x^{3/4}/log x`-type lower bounds hold
(`AcountAtilC_ge_const_mul_rpow`).  The assertion is therefore an elementary estimate in `x` once
the two scale bounds `zc ≍ x^{5/16}` (`window_marginsC`, `scale_factsC`) are in place.  A cruder
route also works: `τ(n) ≤ n` and `Λ(n) ≤ log n`, whence
`∑_{n ≤ e·zc} ã(n)τ(n)log n ≤ (e·zc)log(e·zc)·Ã(e·zc)` with `Ã(e·zc) ≤ C(e·zc)^{3/4}`.

The hypothesis `∀ ν, |lam ν| ≤ 1` is exactly the `SieveInput` conjunct needed.

The proof follows the crude route: every term is bounded by
`ã(n)·(n+1)·log n ≤ ã(n)·2e·zc·log(e·zc)`, the window `(zc, e·zc]` has at most `⌊e·zc⌋₊ ≤ e·zc`
terms, all of them inside `[1, ⌊e·zc⌋₊]`, and `Ã(⌊e·zc⌋₊) ≤ Cu·(e·zc)^{3/4}`.  With
`zc ≤ 2x^{5/16}` (`YcB_le_two_mul_rpow` below, a re-run of `scale_factsC`'s `Yc_upper`) this gives
`S3delSum ≪ zc^{7/4}·log x ≪ x^{35/64}·log x`, and `log²x ≪ x^{13/64}` absorbs the remaining
logarithm against the lower bound `Ã(x) ≫ x^{3/4}`. -/

/-! ## 0. Elementary inputs about the pinned scales -/

/-- `1/4 - 2·η = 3/16` at the fixed `η = 1/32`. -/
private lemma etac_quarter_B : (1 : ℝ) / 4 - 2 * etac = 3 / 16 := by norm_num [etac]

/-- **Upper bound for the corrected outer scale.**  For `x ≥ 2` and *any* real `B`,
`Yc x B = √x/(sc x B·(log x)^{B+2}) ≤ 2·x^{5/16}`: the dyadic `sc x B = 2^{Jc x B}` dominates
`x^{3/16}/(2(log x)^{B+2})`, and the common factor `(log x)^{B+2}` cancels. -/
private lemma YcB_le_two_mul_rpow (x : ℕ) (hx : 2 ≤ x) (B : ℝ) :
    Yc x B ≤ 2 * (x : ℝ) ^ ((5 : ℝ) / 16) := by
  have hx1 : (1 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 1 < x)
  have hxpos : (0 : ℝ) < (x : ℝ) := by linarith
  have hLpos : 0 < Real.log (x : ℝ) := Real.log_pos hx1
  have hLp : 0 < (Real.log (x : ℝ)) ^ (B + 2) := Real.rpow_pos_of_pos hLpos _
  have hu : 0 < (x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac) / (2 * (Real.log (x : ℝ)) ^ (B + 2)) :=
    div_pos (Real.rpow_pos_of_pos hxpos _) (by positivity)
  have hle_sc : (x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac) / (2 * (Real.log (x : ℝ)) ^ (B + 2))
      ≤ sc x B := by
    have hceil : Real.log ((x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac)
        / (2 * (Real.log (x : ℝ)) ^ (B + 2))) / Real.log 2 ≤ (Jc x B : ℝ) := Nat.le_ceil _
    calc (x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac) / (2 * (Real.log (x : ℝ)) ^ (B + 2))
        = (2 : ℝ) ^ (Real.log ((x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac)
            / (2 * (Real.log (x : ℝ)) ^ (B + 2))) / Real.log 2) :=
          (Work.FITop.FI_two_rpow_log_div_log _ hu).symm
      _ ≤ (2 : ℝ) ^ (Jc x B : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hceil
      _ = sc x B := by rw [sc, Real.rpow_natCast]
  have h1 : (x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac) / 2 ≤ sc x B * (Real.log (x : ℝ)) ^ (B + 2) := by
    have h2 : (x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac) / (2 * (Real.log (x : ℝ)) ^ (B + 2))
        * (Real.log (x : ℝ)) ^ (B + 2) ≤ sc x B * (Real.log (x : ℝ)) ^ (B + 2) :=
      mul_le_mul_of_nonneg_right hle_sc hLp.le
    have h3 : (x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac) / (2 * (Real.log (x : ℝ)) ^ (B + 2))
        * (Real.log (x : ℝ)) ^ (B + 2) = (x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac) / 2 := by
      field_simp
    rwa [h3] at h2
  have hYc : Yc x B ≤ Real.sqrt (x : ℝ) / ((x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac) / 2) := by
    rw [Yc]
    exact div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (by positivity) h1
  have hval : Real.sqrt (x : ℝ) / ((x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac) / 2)
      = 2 * (x : ℝ) ^ ((5 : ℝ) / 16) := by
    have hx3 : (x : ℝ) ^ ((3 : ℝ) / 16) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hxpos _)
    have hA : Real.sqrt (x : ℝ) / ((x : ℝ) ^ ((3 : ℝ) / 16) / 2)
        = 2 * ((x : ℝ) ^ ((1 : ℝ) / 2) / (x : ℝ) ^ ((3 : ℝ) / 16)) := by
      rw [Real.sqrt_eq_rpow]
      field_simp
    rw [etac_quarter_B, hA, ← Real.rpow_sub hxpos]
    congr 1
    norm_num
  rw [hval] at hYc
  exact hYc

/-- `ρ_λ(n) = ∑_{ν ∣ n} λ_ν` is bounded by `τ(n)` when `|λ_ν| ≤ 1`. -/
private lemma abs_rhoOf_le_divisors_card (lam : ℕ → ℝ) (hlam : ∀ ν : ℕ, |lam ν| ≤ 1) (n : ℕ) :
    |Submission.ASP.rhoOf lam n| ≤ (n.divisors.card : ℝ) := by
  rw [Submission.ASP.rhoOf]
  calc |∑ ν ∈ n.divisors, lam ν| ≤ ∑ ν ∈ n.divisors, |lam ν| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ν ∈ n.divisors, (1 : ℝ) := Finset.sum_le_sum (fun ν _ => hlam ν)
    _ = (n.divisors.card : ℝ) := by simp

/-- `ã` is nonnegative. -/
private lemma atilc_nonneg (n : ℕ) : 0 ≤ atilc n := by
  rw [atilc, Work.FITop.atilFIa, Submission.ASP.atil, Submission.ASP.FIa]
  positivity

/-- For `x ≥ 100` and `0 ≤ Z ≤ 2x^{5/16}`, `log(e·Z) ≤ 2·log x`. -/
private lemma log_exp_mul_le_two_mul_log (x : ℕ) (hx : 100 ≤ x) (Z : ℝ) (hZ : 0 ≤ Z)
    (hZle : Z ≤ 2 * (x : ℝ) ^ ((5 : ℝ) / 16)) :
    Real.log (Real.exp 1 * Z) ≤ 2 * Real.log (x : ℝ) := by
  have hx100 : (100 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have hxpos : (0 : ℝ) < (x : ℝ) := by linarith
  -- `log 10 ≥ 2`, hence `log x ≥ 4`
  have hlog10 : (2 : ℝ) ≤ Real.log 10 := by
    have he2 : Real.exp 1 ^ 2 ≤ (10 : ℝ) := by
      nlinarith [Real.exp_pos 1, Real.exp_one_lt_three]
    have h := Real.log_le_log (by positivity : (0 : ℝ) < Real.exp 1 ^ 2) he2
    rw [Real.log_pow, Real.log_exp] at h
    push_cast at h
    linarith
  have hlogx : (4 : ℝ) ≤ Real.log (x : ℝ) := by
    have h100 : Real.log (100 : ℝ) = 2 * Real.log 10 := by
      have h : (100 : ℝ) = 10 ^ 2 := by norm_num
      rw [h, Real.log_pow]
      norm_num
    have h2 : Real.log (100 : ℝ) ≤ Real.log (x : ℝ) := Real.log_le_log (by norm_num) hx100
    rw [h100] at h2
    linarith
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 2) (le_of_lt Real.exp_one_gt_two)
    rwa [Real.log_exp] at h
  by_cases hZ0 : Z = 0
  · rw [hZ0, mul_zero, Real.log_zero]
    linarith
  · have hZpos : 0 < Z := lt_of_le_of_ne hZ (Ne.symm hZ0)
    have hEpos : 0 < Real.exp 1 * Z := mul_pos (Real.exp_pos 1) hZpos
    have hle1 : Real.exp 1 * Z ≤ Real.exp 1 * (2 * (x : ℝ) ^ ((5 : ℝ) / 16)) :=
      mul_le_mul_of_nonneg_left hZle (Real.exp_pos 1).le
    have hlog : Real.log (Real.exp 1 * Z)
        ≤ Real.log (Real.exp 1 * (2 * (x : ℝ) ^ ((5 : ℝ) / 16))) :=
      Real.log_le_log hEpos hle1
    have hsplit : Real.log (Real.exp 1 * (2 * (x : ℝ) ^ ((5 : ℝ) / 16)))
        = 1 + Real.log 2 + (5 / 16) * Real.log (x : ℝ) := by
      rw [Real.log_mul (ne_of_gt (Real.exp_pos 1)) (by positivity),
        Real.log_exp, Real.log_mul (by norm_num) (ne_of_gt (Real.rpow_pos_of_pos hxpos _)),
        Real.log_rpow hxpos]
      ring
    rw [hsplit] at hlog
    linarith

/-- `(log x)^2 ≤ 2·x^{13/64}` for all large `x` (the classical `log ≪ x^ε`). -/
private lemma eventually_logSq_le_two_mul_rpow :
    ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x → (Real.log (x : ℝ)) ^ 2 ≤ 2 * (x : ℝ) ^ ((13 : ℝ) / 64) := by
  obtain ⟨a, ha⟩ := Filter.eventually_atTop.1
    (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (by norm_num : (0 : ℝ) < (13 : ℝ) / 64)).eventuallyLE
  refine ⟨max ⌈a⌉₊ 100, fun x hx => ?_⟩
  have hx100 : (100 : ℝ) ≤ (x : ℝ) := by
    exact_mod_cast (le_trans (le_max_right _ _) hx : 100 ≤ x)
  have hxpos : (0 : ℝ) < (x : ℝ) := by linarith
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by linarith
  have hlog0 : 0 ≤ Real.log (x : ℝ) := Real.log_nonneg hx1
  have hax : a ≤ (x : ℝ) := by
    have h1 : a ≤ ((⌈a⌉₊ : ℕ) : ℝ) := Nat.le_ceil a
    have h2 : ((⌈a⌉₊ : ℕ) : ℝ) ≤ (x : ℝ) := by
      have h3 : ⌈a⌉₊ ≤ x := le_trans (le_max_left _ _) hx
      exact_mod_cast h3
    linarith
  have h := ha (x : ℝ) hax
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hlog0 2),
    Real.norm_of_nonneg (Real.rpow_nonneg hxpos.le _)] at h
  rw [Real.rpow_two] at h
  calc (Real.log (x : ℝ)) ^ 2 ≤ (x : ℝ) ^ ((13 : ℝ) / 64) := h
    _ ≤ 2 * (x : ℝ) ^ ((13 : ℝ) / 64) := by
        have h0 : 0 ≤ (x : ℝ) ^ ((13 : ℝ) / 64) := Real.rpow_nonneg hxpos.le _
        linarith

/-! ## 1. The crude term-by-term bound -/

/-- Every term of `S3delSum` is bounded by `a n·2e·Z·log(e·Z)` on the window, and the index set
is contained in `[1, ⌊e·Z⌋₊]`; hence the whole sum is at most
`2·e·Z·log(e·Z)·Acount a ⌊e·Z⌋₊`. -/
private lemma S3delSum_le_mul_Acount (a : ℕ → ℝ) (ha : ∀ n : ℕ, 0 ≤ a n) (lam : ℕ → ℝ)
    (hlam : ∀ ν : ℕ, |lam ν| ≤ 1) (N : ℕ) (Z : ℝ) (hZ : 1 ≤ Real.exp 1 * Z) :
    S3delSum a lam N Z ≤ 2 * (Real.exp 1 * Z) * Real.log (Real.exp 1 * Z)
      * Submission.ASP.Acount a (⌊Real.exp 1 * Z⌋₊) := by
  rw [S3delSum]
  set E : ℝ := Real.exp 1 * Z with hE
  have hE1 : 1 ≤ E := hZ
  have hEpos : 0 < E := lt_of_lt_of_le zero_lt_one hE1
  have hlogE0 : 0 ≤ Real.log E := Real.log_nonneg hE1
  have hterm : ∀ n ∈ (Finset.Icc 1 N).filter
      (fun n => Z < ((n : ℕ) : ℝ) ∧ ((n : ℕ) : ℝ) ≤ E),
      |a n * Submission.ASP.rhoOf lam n * (ArithmeticFunction.vonMangoldt n : ℝ)|
        ≤ a n * (2 * E * Real.log E) := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨hn1, _⟩, _, hnE⟩ := hn
    have hn1' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
    have hlogmono : Real.log (n : ℝ) ≤ Real.log E := Real.log_le_log hnpos hnE
    have hcard : (n.divisors.card : ℝ) ≤ 2 * E := by
      have hc : n.divisors.card ≤ n + 1 := by
        calc n.divisors.card ≤ (Finset.range (n + 1)).card := Finset.card_le_card ?_
          _ = n + 1 := Finset.card_range (n + 1)
        intro m hm
        rw [Nat.mem_divisors] at hm
        rw [Finset.mem_range]
        exact Nat.lt_succ_of_le (Nat.le_of_dvd (by omega) hm.1)
      calc (n.divisors.card : ℝ) ≤ ((n : ℕ) : ℝ) + 1 := by exact_mod_cast hc
        _ ≤ 2 * (n : ℝ) := by linarith
        _ ≤ 2 * E := by linarith
    have hΛ0 : (0 : ℝ) ≤ (ArithmeticFunction.vonMangoldt n : ℝ) :=
      ArithmeticFunction.vonMangoldt_nonneg
    have hΛlog : (ArithmeticFunction.vonMangoldt n : ℝ) ≤ Real.log (n : ℝ) :=
      ArithmeticFunction.vonMangoldt_le_log
    have hr : |Submission.ASP.rhoOf lam n| ≤ 2 * E :=
      le_trans (abs_rhoOf_le_divisors_card lam hlam n) hcard
    have hstep : |Submission.ASP.rhoOf lam n| * (ArithmeticFunction.vonMangoldt n : ℝ)
        ≤ (2 * E) * Real.log E := by
      have h2 : |Submission.ASP.rhoOf lam n| * (ArithmeticFunction.vonMangoldt n : ℝ)
          ≤ (2 * E) * (ArithmeticFunction.vonMangoldt n : ℝ) :=
        mul_le_mul hr le_rfl hΛ0 (by linarith [hEpos])
      have h3 : (2 * E) * (ArithmeticFunction.vonMangoldt n : ℝ) ≤ (2 * E) * Real.log E :=
        mul_le_mul_of_nonneg_left (le_trans hΛlog hlogmono) (by linarith [hEpos])
      linarith
    have h4 : |a n * Submission.ASP.rhoOf lam n * (ArithmeticFunction.vonMangoldt n : ℝ)|
        = a n * (|Submission.ASP.rhoOf lam n| * (ArithmeticFunction.vonMangoldt n : ℝ)) := by
      rw [abs_mul, abs_mul, abs_of_nonneg (ha n), abs_of_nonneg hΛ0]
      ring
    rw [h4]
    calc a n * (|Submission.ASP.rhoOf lam n| * (ArithmeticFunction.vonMangoldt n : ℝ))
        ≤ a n * ((2 * E) * Real.log E) := mul_le_mul_of_nonneg_left hstep (ha n)
      _ = a n * (2 * E * Real.log E) := by ring
  calc ∑ n ∈ (Finset.Icc 1 N).filter (fun n => Z < ((n : ℕ) : ℝ) ∧ ((n : ℕ) : ℝ) ≤ E),
        |a n * Submission.ASP.rhoOf lam n * (ArithmeticFunction.vonMangoldt n : ℝ)|
      ≤ ∑ n ∈ (Finset.Icc 1 N).filter (fun n => Z < ((n : ℕ) : ℝ) ∧ ((n : ℕ) : ℝ) ≤ E),
          a n * (2 * E * Real.log E) := Finset.sum_le_sum hterm
    _ = (2 * E * Real.log E) * ∑ n ∈ (Finset.Icc 1 N).filter
          (fun n => Z < ((n : ℕ) : ℝ) ∧ ((n : ℕ) : ℝ) ≤ E), a n := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun n _ => by ring)
    _ ≤ (2 * E * Real.log E) * Submission.ASP.Acount a (⌊E⌋₊) := by
        refine mul_le_mul_of_nonneg_left ?_
          (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hEpos.le) hlogE0)
        have hsub : (Finset.Icc 1 N).filter (fun n => Z < ((n : ℕ) : ℝ) ∧ ((n : ℕ) : ℝ) ≤ E)
            ⊆ Finset.Icc 1 ⌊E⌋₊ := by
          intro n hn
          rw [Finset.mem_filter, Finset.mem_Icc] at hn
          rw [Finset.mem_Icc]
          exact ⟨hn.1.1, Nat.le_floor hn.2.2⟩
        have h := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => ha i)
        simpa [Submission.ASP.Acount, Nat.floor_natCast] using h

/-! ## 2. The pure real-arithmetic core -/

/-- The final numeric comparison: with `Z ≤ 2x^{5/16}` (`x ≥ 100`, `1 ≤ Z`) and
`(log x)^2 ≤ 2x^{13/64}`, the crude sum bound `2·eZ·log(eZ)·Cu·(eZ)^{3/4}` is at most
`K·c·x^{3/4}/log x` for `K = 2·(16·Cu·e²)/c`. -/
private lemma core_arith (Cu c : ℝ) (hCu : 0 < Cu) (hc : 0 < c) (x : ℕ) (hx : 100 ≤ x)
    (Z : ℝ) (hZ0 : 0 ≤ Z) (hZ1 : 1 ≤ Z)
    (hZle : Z ≤ 2 * (x : ℝ) ^ ((5 : ℝ) / 16))
    (hlogsq : (Real.log (x : ℝ)) ^ 2 ≤ 2 * (x : ℝ) ^ ((13 : ℝ) / 64)) :
    2 * (Real.exp 1 * Z) * Real.log (Real.exp 1 * Z) * (Cu * (Real.exp 1 * Z) ^ ((3 : ℝ) / 4))
      ≤ (2 * (16 * Cu * (Real.exp 1) ^ 2) / c) * (c * (x : ℝ) ^ ((3 : ℝ) / 4))
          * (Real.log (x : ℝ)) ^ (-(1 : ℤ)) := by
  have hx100 : (100 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have hxpos : (0 : ℝ) < (x : ℝ) := by linarith
  set E : ℝ := Real.exp 1 * Z with hE
  set L : ℝ := Real.log (x : ℝ) with hL
  have hLpos : 0 < L := by rw [hL]; exact Real.log_pos (by linarith)
  have hL0 : 0 ≤ L := hLpos.le
  have hlogsqL : L ^ 2 ≤ 2 * (x : ℝ) ^ ((13 : ℝ) / 64) := hlogsq
  have hE1 : 1 ≤ E := by
    rw [hE]
    have he1 : (1 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_two]
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ Real.exp 1 * Z := mul_le_mul he1 hZ1 zero_le_one (le_of_lt (Real.exp_pos 1))
  have hEpos : 0 < E := lt_of_lt_of_le zero_lt_one hE1
  have hlogE0 : 0 ≤ Real.log E := Real.log_nonneg hE1
  have hlogE : Real.log E ≤ 2 * L := by
    rw [hE, hL]
    exact log_exp_mul_le_two_mul_log x hx Z hZ0 hZle
  -- `E·E^{3/4} = E^{7/4}`
  have hE74 : E * E ^ ((3 : ℝ) / 4) = E ^ ((7 : ℝ) / 4) := by
    nth_rewrite 1 [← Real.rpow_one E]
    rw [← Real.rpow_add hEpos]
    congr 1
    norm_num
  -- `E^{7/4} ≤ (2e)^{7/4}·x^{35/64}`
  have hEpow : E ^ ((7 : ℝ) / 4) ≤ (2 * Real.exp 1) ^ ((7 : ℝ) / 4) * (x : ℝ) ^ ((35 : ℝ) / 64) := by
    have hEle : E ≤ 2 * Real.exp 1 * (x : ℝ) ^ ((5 : ℝ) / 16) := by
      rw [hE]
      calc Real.exp 1 * Z ≤ Real.exp 1 * (2 * (x : ℝ) ^ ((5 : ℝ) / 16)) :=
            mul_le_mul_of_nonneg_left hZle (Real.exp_pos 1).le
        _ = 2 * Real.exp 1 * (x : ℝ) ^ ((5 : ℝ) / 16) := by ring
    calc E ^ ((7 : ℝ) / 4) ≤ (2 * Real.exp 1 * (x : ℝ) ^ ((5 : ℝ) / 16)) ^ ((7 : ℝ) / 4) :=
          Real.rpow_le_rpow hEpos.le hEle (by norm_num)
      _ = (2 * Real.exp 1) ^ ((7 : ℝ) / 4) * ((x : ℝ) ^ ((5 : ℝ) / 16)) ^ ((7 : ℝ) / 4) := by
          rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hxpos.le _)]
      _ = (2 * Real.exp 1) ^ ((7 : ℝ) / 4) * (x : ℝ) ^ ((35 : ℝ) / 64) := by
          rw [← Real.rpow_mul hxpos.le]
          congr 1
          norm_num
  -- `(2e)^{7/4} ≤ 4e²`
  have hC1 : (2 * Real.exp 1) ^ ((7 : ℝ) / 4) ≤ 4 * (Real.exp 1) ^ 2 := by
    have h2 : (2 : ℝ) ^ ((7 : ℝ) / 4) ≤ 4 := by
      have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
        (by norm_num : ((7 : ℝ) / 4) ≤ 2)
      have h4 : (2 : ℝ) ^ ((2 : ℝ)) = 4 := by rw [Real.rpow_two]; norm_num
      linarith [h, h4]
    have he : (Real.exp 1) ^ ((7 : ℝ) / 4) ≤ (Real.exp 1) ^ 2 := by
      have he1 : (1 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_two]
      have h := Real.rpow_le_rpow_of_exponent_le he1 (by norm_num : ((7 : ℝ) / 4) ≤ 2)
      rwa [Real.rpow_two] at h
    calc (2 * Real.exp 1) ^ ((7 : ℝ) / 4)
        = (2 : ℝ) ^ ((7 : ℝ) / 4) * (Real.exp 1) ^ ((7 : ℝ) / 4) :=
          Real.mul_rpow (by norm_num) (Real.exp_pos 1).le
      _ ≤ 4 * (Real.exp 1) ^ 2 := mul_le_mul h2 he (by positivity) (by norm_num)
  -- `x^{35/64}·x^{13/64} = x^{3/4}`
  have hXprod : (x : ℝ) ^ ((35 : ℝ) / 64) * (x : ℝ) ^ ((13 : ℝ) / 64)
      = (x : ℝ) ^ ((3 : ℝ) / 4) := by
    rw [← Real.rpow_add hxpos]
    norm_num
  have hXr0 : (0 : ℝ) ≤ (x : ℝ) ^ ((35 : ℝ) / 64) := Real.rpow_nonneg hxpos.le _
  -- `x^{35/64}·L² ≤ 2x^{3/4}`
  have hXrL2 : (x : ℝ) ^ ((35 : ℝ) / 64) * L ^ 2 ≤ 2 * (x : ℝ) ^ ((3 : ℝ) / 4) := by
    have h := mul_le_mul_of_nonneg_left hlogsqL hXr0
    have h' : (x : ℝ) ^ ((35 : ℝ) / 64) * (2 * (x : ℝ) ^ ((13 : ℝ) / 64))
        = 2 * (x : ℝ) ^ ((3 : ℝ) / 4) := by
      rw [show (x : ℝ) ^ ((35 : ℝ) / 64) * (2 * (x : ℝ) ^ ((13 : ℝ) / 64))
          = 2 * ((x : ℝ) ^ ((35 : ℝ) / 64) * (x : ℝ) ^ ((13 : ℝ) / 64)) from by ring, hXprod]
    linarith [h, h']
  have hApos : 0 < 16 * Cu * (Real.exp 1) ^ 2 := by positivity
  have hbound1 : 2 * E * Real.log E * (Cu * E ^ ((3 : ℝ) / 4))
      ≤ 16 * Cu * (Real.exp 1) ^ 2 * (x : ℝ) ^ ((35 : ℝ) / 64) * L := by
    have hp : E ^ ((7 : ℝ) / 4) * Real.log E
        ≤ ((2 * Real.exp 1) ^ ((7 : ℝ) / 4) * (x : ℝ) ^ ((35 : ℝ) / 64)) * (2 * L) :=
      mul_le_mul hEpow hlogE hlogE0 (by positivity)
    have hB : 2 * Cu * (E ^ ((7 : ℝ) / 4) * Real.log E)
        ≤ 2 * Cu * (((2 * Real.exp 1) ^ ((7 : ℝ) / 4) * (x : ℝ) ^ ((35 : ℝ) / 64)) * (2 * L)) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    have hD1 : (2 * Real.exp 1) ^ ((7 : ℝ) / 4) * (x : ℝ) ^ ((35 : ℝ) / 64)
        ≤ (4 * (Real.exp 1) ^ 2) * (x : ℝ) ^ ((35 : ℝ) / 64) :=
      mul_le_mul_of_nonneg_right hC1 hXr0
    have hD2 : 4 * Cu * ((2 * Real.exp 1) ^ ((7 : ℝ) / 4) * (x : ℝ) ^ ((35 : ℝ) / 64))
        ≤ 4 * Cu * ((4 * (Real.exp 1) ^ 2) * (x : ℝ) ^ ((35 : ℝ) / 64)) :=
      mul_le_mul_of_nonneg_left hD1 (by positivity)
    have hD : 4 * Cu * (2 * Real.exp 1) ^ ((7 : ℝ) / 4) * (x : ℝ) ^ ((35 : ℝ) / 64) * L
        ≤ 4 * Cu * (4 * (Real.exp 1) ^ 2) * (x : ℝ) ^ ((35 : ℝ) / 64) * L := by
      calc 4 * Cu * (2 * Real.exp 1) ^ ((7 : ℝ) / 4) * (x : ℝ) ^ ((35 : ℝ) / 64) * L
          = (4 * Cu * ((2 * Real.exp 1) ^ ((7 : ℝ) / 4) * (x : ℝ) ^ ((35 : ℝ) / 64))) * L := by
            ring
        _ ≤ (4 * Cu * ((4 * (Real.exp 1) ^ 2) * (x : ℝ) ^ ((35 : ℝ) / 64))) * L :=
            mul_le_mul_of_nonneg_right hD2 hL0
        _ = 4 * Cu * (4 * (Real.exp 1) ^ 2) * (x : ℝ) ^ ((35 : ℝ) / 64) * L := by ring
    calc 2 * E * Real.log E * (Cu * E ^ ((3 : ℝ) / 4))
        = 2 * Cu * (E * E ^ ((3 : ℝ) / 4)) * Real.log E := by ring
      _ = 2 * Cu * E ^ ((7 : ℝ) / 4) * Real.log E := by rw [hE74]
      _ = 2 * Cu * (E ^ ((7 : ℝ) / 4) * Real.log E) := by ring
      _ ≤ 2 * Cu
            * (((2 * Real.exp 1) ^ ((7 : ℝ) / 4) * (x : ℝ) ^ ((35 : ℝ) / 64)) * (2 * L)) := hB
      _ = 4 * Cu * (2 * Real.exp 1) ^ ((7 : ℝ) / 4) * (x : ℝ) ^ ((35 : ℝ) / 64) * L := by ring
      _ ≤ 4 * Cu * (4 * (Real.exp 1) ^ 2) * (x : ℝ) ^ ((35 : ℝ) / 64) * L := hD
      _ = 16 * Cu * (Real.exp 1) ^ 2 * (x : ℝ) ^ ((35 : ℝ) / 64) * L := by ring
  have hbound2 : 16 * Cu * (Real.exp 1) ^ 2 * (x : ℝ) ^ ((35 : ℝ) / 64) * L
      ≤ (2 * (16 * Cu * (Real.exp 1) ^ 2) / c) * (c * (x : ℝ) ^ ((3 : ℝ) / 4))
          * L ^ (-(1 : ℤ)) := by
    have hR : (2 * (16 * Cu * (Real.exp 1) ^ 2) / c) * (c * (x : ℝ) ^ ((3 : ℝ) / 4))
        * L ^ (-(1 : ℤ)) = 2 * (16 * Cu * (Real.exp 1) ^ 2) * (x : ℝ) ^ ((3 : ℝ) / 4) / L := by
      rw [zpow_neg_one]
      field_simp
    rw [hR, le_div_iff₀ hLpos]
    calc 16 * Cu * (Real.exp 1) ^ 2 * (x : ℝ) ^ ((35 : ℝ) / 64) * L * L
        = 16 * Cu * (Real.exp 1) ^ 2 * ((x : ℝ) ^ ((35 : ℝ) / 64) * L ^ 2) := by ring
      _ ≤ 16 * Cu * (Real.exp 1) ^ 2 * (2 * (x : ℝ) ^ ((3 : ℝ) / 4)) :=
          mul_le_mul_of_nonneg_left hXrL2 hApos.le
      _ = 2 * (16 * Cu * (Real.exp 1) ^ 2) * (x : ℝ) ^ ((3 : ℝ) / 4) := by ring
  linarith [hbound1, hbound2]

/-! ## 3. The theorem -/

theorem S3delSum_Bstar :
    ∃ K : ℝ, ∃ x₀ : ℕ, 0 < K ∧ ∀ x : ℕ, x₀ ≤ x → ∀ lam : ℕ → ℝ,
      (∀ ν : ℕ, |lam ν| ≤ 1) →
      Work.FIChain.S3delSum Work.FIChain.atilc lam x (Work.FIChain.zc x HasBc.val)
        ≤ K * Work.FIChain.AcountAtilC x * (Real.log (x : ℝ)) ^ (-(1 : ℤ)) := by
  obtain ⟨c, hc, Xc, hAc⟩ := AcountAtilC_ge_const_mul_rpow
  obtain ⟨Cu, hCu, hAu⟩ := AcountAtilC_le_const_mul_rpow
  obtain ⟨Xlog, hlog⟩ := eventually_logSq_le_two_mul_rpow
  have hBpos : (0 : ℝ) < HasBc.val := by have := HasBc.ge_two; linarith
  obtain ⟨Xsc, hsc⟩ := Filter.eventually_atTop.1 (scale_factsC HasBc.val hBpos)
  refine ⟨2 * (16 * Cu * (Real.exp 1) ^ 2) / c,
    max (max Xc Xlog) (max 100 (max Xsc 1)), by positivity, ?_⟩
  intro x hx lam hlam
  have hxXc : Xc ≤ x := le_trans (le_trans (le_max_left Xc Xlog) (le_max_left _ _)) hx
  have hxXlog : Xlog ≤ x := le_trans (le_trans (le_max_right Xc Xlog) (le_max_left _ _)) hx
  have hx100 : 100 ≤ x := le_trans (le_trans (le_max_left 100 (max Xsc 1)) (le_max_right _ _)) hx
  have hxXsc : Xsc ≤ x :=
    le_trans (le_trans (le_trans (le_max_left Xsc 1) (le_max_right 100 (max Xsc 1)))
      (le_max_right _ _)) hx
  have hx2 : 2 ≤ x := by omega
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (by omega : 1 ≤ x)
  have hx1lt : (1 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 1 < x)
  -- the scale `zc x HasBc.val`
  have hZge : (256 : ℝ) ≤ zc x HasBc.val := by
    have h := (hsc x hxXsc).1
    have h' : (256 : ℝ) ≤ (((⌊Yc x HasBc.val⌋₊ : ℕ) : ℝ)) := by exact_mod_cast h
    simpa [zc, Zc] using h'
  have hZ1 : 1 ≤ zc x HasBc.val := by linarith
  have hZ0 : 0 ≤ zc x HasBc.val := by linarith
  have hYcnonneg : (0 : ℝ) ≤ Yc x HasBc.val := by
    rw [Yc]
    refine div_nonneg (Real.sqrt_nonneg _) (mul_nonneg ?_ (Real.rpow_nonneg (Real.log_nonneg hx1) _))
    rw [sc]
    positivity
  have hZle : zc x HasBc.val ≤ 2 * (x : ℝ) ^ ((5 : ℝ) / 16) := by
    have hfl := Nat.floor_le hYcnonneg
    calc zc x HasBc.val = (((⌊Yc x HasBc.val⌋₊ : ℕ) : ℝ)) := by simp [zc, Zc]
      _ ≤ Yc x HasBc.val := hfl
      _ ≤ 2 * (x : ℝ) ^ ((5 : ℝ) / 16) := YcB_le_two_mul_rpow x hx2 HasBc.val
  -- the crude counting bound
  have hE1 : 1 ≤ Real.exp 1 * zc x HasBc.val := by
    have he1 : (1 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_two]
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ Real.exp 1 * zc x HasBc.val := mul_le_mul he1 hZ1 zero_le_one (le_of_lt (Real.exp_pos 1))
  have hEpos : 0 < Real.exp 1 * zc x HasBc.val := lt_of_lt_of_le zero_lt_one hE1
  have hS : S3delSum atilc lam x (zc x HasBc.val)
      ≤ 2 * (Real.exp 1 * zc x HasBc.val) * Real.log (Real.exp 1 * zc x HasBc.val)
          * AcountAtilC ⌊Real.exp 1 * zc x HasBc.val⌋₊ := by
    simpa [AcountAtilC, Work.FITop.AcountAtil] using
      S3delSum_le_mul_Acount atilc atilc_nonneg lam hlam x (zc x HasBc.val) hE1
  -- the upper bound `Ã ≤ Cu·(eZ)^{3/4}` at the window top
  have hfl1 : 1 ≤ ⌊Real.exp 1 * zc x HasBc.val⌋₊ := by
    apply Nat.le_floor
    simpa using hE1
  have hAcE : AcountAtilC ⌊Real.exp 1 * zc x HasBc.val⌋₊
      ≤ Cu * (Real.exp 1 * zc x HasBc.val) ^ ((3 : ℝ) / 4) := by
    have h1 := hAu ⌊Real.exp 1 * zc x HasBc.val⌋₊ hfl1
    have h2 : (((⌊Real.exp 1 * zc x HasBc.val⌋₊ : ℕ) : ℝ)) ≤ Real.exp 1 * zc x HasBc.val :=
      Nat.floor_le hEpos.le
    have h3 : (((⌊Real.exp 1 * zc x HasBc.val⌋₊ : ℕ) : ℝ)) ^ ((3 : ℝ) / 4)
        ≤ (Real.exp 1 * zc x HasBc.val) ^ ((3 : ℝ) / 4) :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) h2 (by norm_num)
    exact le_trans h1 (mul_le_mul_of_nonneg_left h3 hCu.le)
  -- the lower bound `Ã(x) ≥ c·x^{3/4}` and the logarithm bound
  have hAcx : c * (x : ℝ) ^ ((3 : ℝ) / 4) ≤ AcountAtilC x := hAc x hxXc
  have hlogsq : (Real.log (x : ℝ)) ^ 2 ≤ 2 * (x : ℝ) ^ ((13 : ℝ) / 64) := hlog x hxXlog
  have hcore := core_arith Cu c hCu hc x hx100 (zc x HasBc.val) hZ0 hZ1 hZle hlogsq
  calc S3delSum atilc lam x (zc x HasBc.val)
      ≤ 2 * (Real.exp 1 * zc x HasBc.val) * Real.log (Real.exp 1 * zc x HasBc.val)
          * AcountAtilC ⌊Real.exp 1 * zc x HasBc.val⌋₊ := hS
    _ ≤ 2 * (Real.exp 1 * zc x HasBc.val) * Real.log (Real.exp 1 * zc x HasBc.val)
          * (Cu * (Real.exp 1 * zc x HasBc.val) ^ ((3 : ℝ) / 4)) :=
        mul_le_mul_of_nonneg_left hAcE
          (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hEpos.le)
            (Real.log_nonneg hE1))
    _ ≤ (2 * (16 * Cu * (Real.exp 1) ^ 2) / c) * (c * (x : ℝ) ^ ((3 : ℝ) / 4))
          * (Real.log (x : ℝ)) ^ (-(1 : ℤ)) := hcore
    _ ≤ (2 * (16 * Cu * (Real.exp 1) ^ 2) / c) * AcountAtilC x
          * (Real.log (x : ℝ)) ^ (-(1 : ℤ)) := by
        have hKpos : 0 < 2 * (16 * Cu * (Real.exp 1) ^ 2) / c := by positivity
        have hLnp : 0 ≤ (Real.log (x : ℝ)) ^ (-(1 : ℤ)) := by
          rw [zpow_neg_one]
          exact (inv_pos.mpr (Real.log_pos hx1lt)).le
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hAcx hKpos.le) hLnp

end

end Work.FIPiChain
