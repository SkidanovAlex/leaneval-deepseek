/-
# `Submission.Work.FIChain.rhoWindowC_param` — the `ρ`-window at the corrected `B`-dependent scale

`Work.FITop.RhoWindowCPow` proves the companion's `(B′)`-type `ρ`-window (one `μ`, on the product
`mn`) with error `K·Ã(x)(log x)^{-4}` **at the fixed companion scale** `(Ctrunc x, z1 x, s1 x·z1 x)`
of `Work.FITop.Defs`.  The chain of `Submission/Work/FIChain/` needs the same window at the
corrected, `B`-dependent family

* `s = sc x B = 2^{Jc} ≈ x^{1/4-2η}/(2(log x)^{B+2})`,
* `z = zc x B = ⌊√x/(s·(log x)^{B+2})⌋ ≈ 2x^{1/4+2η}`,

i.e. with window `(zc, sc·zc]` and truncation level `⌊√(zc)⌋`.

The proof is *structurally* the proof of `RhoWindowCPow`: for each window position `t` one applies
`Prop41Statement` at `N = ⌊t⌋` to the integer window `(⌊t⌋, 2⌊t⌋]` (the real window differs from it
by the single integer `2⌊t⌋+1`, handled by `rwcp_extra_le`), Hölder with exponents `3/2, 3`
(`HolderTwoThird`) combines the `τ³`-weighted factor (`rwcp_tau3_bound` + `AseqTauEightBound`) with
the unweighted one, and `rwcp_combine` produces the `(log x)^{-4}`.

The only inputs of that proof are the *range conditions* on `(s,t)`:
`1 ≤ s`, `s ≤ ⌊t⌋^{1-η}` (the `(2.12)` truncation condition `C ≤ N^{1-η}` of `Prop41Statement`),
`x^{1/4+η} < ⌊t⌋ < √x(log x)^{-B₀}` (the range `(4.6)`) and `2t+1 ≤ √x` (so that the extra integer
`2⌊t⌋+1` still has `(2⌊t⌋+1)² ≤ x`).  We therefore prove the *parametric* lemma
`RhoWindowC_param_aux` once, and then instantiate it at the corrected family: the range conditions
are supplied by `Submission.Work.FIChain.window_marginsC` and
`Submission.Work.FIChain.scale_factsC` (the sibling modules of this directory), and the constant
`B` of the family is chosen `> B₀ - 2` so that the window top `sc·zc = √x(log x)^{-(B+2)}` sits
below the top `√x(log x)^{-B₀}` of the range `(4.6)`.
-/
import Mathlib
import Submission.Work.FIChain.Defs
import Submission.Work.FIChain.window_marginsC
import Submission.Work.FIChain.scale_factsC
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
import Submission.Work.FITop.RhoWindowCProp41
import Submission.Work.FITop.RangeCheckChain

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIChain

open Finset Filter
open Work.FITop
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. The reusable part of `RhoWindowCPow`

Below, verbatim, are the private helpers of `Submission/Work/FITop/RhoWindowCPow.lean` (the
bilinear inner sums `Bin`/`BinWin`, the window decomposition, the `τ³`-bound and the single-integer
remainder) together with the public `rwcp_*` facts of
`Submission/Work/FITop/RhoWindowCProp41.lean` (accessible by `open Work.FITop`). -/


/-! ## 2. `XrhoC` and the bilinear inner sums -/

/-- The inner `n`-sum of `BformAtil`. -/
private def Bin (x N : ℕ) (C : ℝ) (m : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 (2 * N),
    (if N < n ∧ m * n ≤ x ∧ Nat.Coprime n m
      then (ArithmeticFunction.moebius n : ℝ) * Work.FIPlan.gammaTrunc C n * atilFIa (m * n)
      else 0)

/-- The `γ`-summand of `BinWin`. -/
private def gw (m : ℕ) (C : ℝ) (n : ℕ) : ℝ :=
  Work.FIPlan.gammaTrunc C n * (ArithmeticFunction.moebius n : ℝ) * atilFIa (m * n)

/-- The same inner sum in the "window + filter" form matching `XrhoC`. -/
private def BinWin (x : ℕ) (t u : ℝ) (C : ℝ) (m : ℕ) : ℝ :=
  ∑ n ∈ (Finset.Icc 1 x).filter (fun n => m * n ≤ x),
    (if t < (n : ℝ) ∧ (n : ℝ) ≤ u then gw m C n else 0)

private lemma BinWin_eq_sum_gw (x : ℕ) (t u C : ℝ) (m : ℕ) :
    BinWin x t u C m = ∑ n ∈ (Finset.Icc 1 x).filter (fun n => m * n ≤ x),
      (if t < (n : ℝ) ∧ (n : ℝ) ≤ u then gw m C n else 0) := rfl

private lemma BformAtil_eq_sum_abs_Bin (x N : ℕ) (C : ℝ) :
    BformAtil x N C = ∑ m ∈ Finset.Icc 1 x, |Bin x N C m| := rfl

private lemma gw_def (m : ℕ) (C : ℝ) (n : ℕ) :
    gw m C n = Work.FIPlan.gammaTrunc C n * (ArithmeticFunction.moebius n : ℝ)
      * atilFIa (m * n) := rfl

private lemma XrhoC_eq_mu_mul_BinWin (x m : ℕ) (s t u : ℝ) :
    XrhoC atilFIa x m s t u
      = (ArithmeticFunction.moebius m : ℝ) * BinWin x t u s m := by
  rw [XrhoC, BinWin, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  by_cases h : t < (n : ℝ) ∧ (n : ℝ) ≤ u
  · rw [if_pos h, if_pos h]
    have hthis := rwcp_mu_mul_mu_mul_atil m n
    simp only [gw]
    calc Work.FIPlan.gammaTrunc s n * (ArithmeticFunction.moebius (m * n) : ℝ)
            * atilFIa (m * n)
        = Work.FIPlan.gammaTrunc s n
            * ((ArithmeticFunction.moebius (m * n) : ℝ) * atilFIa (m * n)) := by ring
      _ = Work.FIPlan.gammaTrunc s n
            * ((ArithmeticFunction.moebius m : ℝ) * (ArithmeticFunction.moebius n : ℝ)
              * atilFIa (m * n)) := by rw [← hthis]
      _ = (ArithmeticFunction.moebius m : ℝ)
            * (Work.FIPlan.gammaTrunc s n * (ArithmeticFunction.moebius n : ℝ)
              * atilFIa (m * n)) := by ring
  · rw [if_neg h, if_neg h, mul_zero]

private lemma BinWin_abs_eq_Bin_abs (x N : ℕ) (C : ℝ) {m : ℕ} (hm : 1 ≤ m) :
    |BinWin x (N : ℝ) ((2 * N : ℕ) : ℝ) C m| = |Bin x N C m| := by
  have hsets : (Finset.Icc 1 (2 * N)).filter (fun n => N < n ∧ m * n ≤ x)
      = ((Finset.Icc 1 x).filter (fun n => m * n ≤ x)).filter
          (fun (n : ℕ) => (N : ℝ) < (n : ℝ) ∧ (n : ℝ) ≤ ((2 * N : ℕ) : ℝ)) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hn1, hn2⟩, hNn, hmn⟩
      have hnx : n ≤ x := by
        have h : n ≤ m * n := Nat.le_mul_of_pos_left n (by omega : 0 < m)
        omega
      exact ⟨⟨⟨hn1, hnx⟩, hmn⟩, by exact_mod_cast hNn, by exact_mod_cast hn2⟩
    · rintro ⟨⟨⟨hn1, _hnx⟩, hmn⟩, hNn, hn2⟩
      exact ⟨⟨hn1, by exact_mod_cast hn2⟩, by exact_mod_cast hNn, hmn⟩
  have hBin : Bin x N C m
      = ∑ n ∈ (Finset.Icc 1 (2 * N)).filter (fun n => N < n ∧ m * n ≤ x), gw m C n := by
    have h1 : Bin x N C m
        = ∑ n ∈ (Finset.Icc 1 (2 * N)).filter (fun n => N < n ∧ m * n ≤ x),
            (if N < n ∧ m * n ≤ x ∧ Nat.Coprime n m
              then (ArithmeticFunction.moebius n : ℝ) * Work.FIPlan.gammaTrunc C n
                * atilFIa (m * n) else 0) := by
      rw [Bin]
      exact (Finset.sum_subset
        (Finset.filter_subset (fun n => N < n ∧ m * n ≤ x) (Finset.Icc 1 (2 * N)))
        (fun n hn hnot => by
          rw [if_neg]
          rintro ⟨h1, h2, -⟩
          exact hnot (Finset.mem_filter.mpr ⟨hn, h1, h2⟩))).symm
    rw [h1]
    refine Finset.sum_congr rfl (fun n hn => ?_)
    rw [Finset.mem_filter] at hn
    obtain ⟨-, hNn, hmn⟩ := hn
    by_cases hc : Nat.Coprime n m
    · rw [if_pos ⟨hNn, hmn, hc⟩]; simp only [gw]; ring
    · have h0 : atilFIa (m * n) = 0 :=
        rwcp_not_coprime_atil_eq_zero (m := m) (n := n) (fun h => hc (Nat.coprime_comm.mp h))
      rw [if_neg (fun h => hc h.2.2)]
      simp only [gw]
      rw [h0]; ring
  have hBW : BinWin x (N : ℝ) ((2 * N : ℕ) : ℝ) C m
      = ∑ n ∈ (Finset.Icc 1 (2 * N)).filter (fun n => N < n ∧ m * n ≤ x), gw m C n := by
    rw [BinWin]
    rw [← Finset.sum_filter]
    rw [← hsets]
  rw [hBin, hBW]


/-! ## 3. The window decomposition -/

/-- A single-integer window `(b, b+1]` selects at most the term `n = b+1`. -/
private lemma rwcp_BinWin_single (x b : ℕ) (s : ℝ) (m : ℕ) :
    BinWin x (b : ℝ) (((b + 1 : ℕ)) : ℝ) s m
      = (if b + 1 ∈ (Finset.Icc 1 x).filter (fun n => m * n ≤ x)
          then gw m s (b + 1) else 0) := by
  rw [BinWin_eq_sum_gw]
  have hite : ∀ n : ℕ, (if (b : ℝ) < (n : ℝ) ∧ (n : ℝ) ≤ (((b + 1 : ℕ)) : ℝ)
        then gw m s n else 0) = (if n = b + 1 then gw m s n else 0) := by
    intro n
    by_cases h : n = b + 1
    · subst h
      rw [if_pos ⟨by push_cast; linarith, le_rfl⟩, if_pos rfl]
    · rw [if_neg h, if_neg]
      rintro ⟨h1, h2⟩
      have h1' : b < n := by exact_mod_cast h1
      have h2' : n ≤ b + 1 := by exact_mod_cast h2
      omega
  rw [Finset.sum_congr rfl (fun n _ => hite n)]
  rw [Finset.sum_ite_eq']

/-! ## 4. The `τ³`-weighted bound -/

private lemma rwcp_tau3_bound (x : ℕ) (s t u : ℝ) :
    (∑ m ∈ Finset.Icc 1 x, ((m.divisors.card : ℝ))^3 * |XrhoC atilFIa x m s t u|)
      ≤ ∑ l ∈ Finset.Icc 1 x, ((l.divisors.card : ℝ))^8 * atilFIa l := by
  have h1 : ∀ m : ℕ, |XrhoC atilFIa x m s t u|
      ≤ ∑ n ∈ (Finset.Icc 1 x).filter (fun n => m * n ≤ x),
          ((n.divisors.card : ℝ)) * atilFIa (m * n) := by
    intro m
    rw [XrhoC]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine Finset.sum_le_sum (fun n _ => ?_)
    by_cases h : t < (n : ℝ) ∧ (n : ℝ) ≤ u
    · rw [if_pos h]
      have hγ := rwcp_abs_gammaTrunc_le s n
      have hμ := rwcp_abs_moebius_cast_le_one (m * n)
      have hã0 : 0 ≤ atilFIa (m * n) := rwcp_atilFIa_nonneg _
      have hγ0 : 0 ≤ (n.divisors.card : ℝ) := Nat.cast_nonneg _
      rw [abs_mul, abs_mul, abs_of_nonneg hã0]
      calc |Work.FIPlan.gammaTrunc s n| * |(ArithmeticFunction.moebius (m * n) : ℝ)|
            * atilFIa (m * n)
          ≤ (n.divisors.card : ℝ) * 1 * atilFIa (m * n) :=
            mul_le_mul (mul_le_mul hγ hμ (abs_nonneg _) hγ0) le_rfl hã0 (by positivity)
        _ = (n.divisors.card : ℝ) * atilFIa (m * n) := by ring
    · rw [if_neg h, abs_zero]
      exact mul_nonneg (Nat.cast_nonneg _) (rwcp_atilFIa_nonneg _)
  have h2 : (∑ m ∈ Finset.Icc 1 x, ((m.divisors.card : ℝ))^3 * |XrhoC atilFIa x m s t u|)
      ≤ ∑ m ∈ Finset.Icc 1 x, ∑ n ∈ (Finset.Icc 1 x).filter (fun n => m * n ≤ x),
          ((m.divisors.card : ℝ))^3 * (((n.divisors.card : ℝ)) * atilFIa (m * n)) := by
    refine Finset.sum_le_sum (fun m _ => ?_)
    have hm := mul_le_mul_of_nonneg_left (h1 m) (by positivity : (0 : ℝ) ≤ ((m.divisors.card : ℝ))^3)
    rwa [Finset.mul_sum] at hm
  have h3 : (∑ m ∈ Finset.Icc 1 x, ∑ n ∈ (Finset.Icc 1 x).filter (fun n => m * n ≤ x),
          ((m.divisors.card : ℝ))^3 * (((n.divisors.card : ℝ)) * atilFIa (m * n)))
      ≤ ∑ m ∈ Finset.Icc 1 x, ∑ n ∈ (Finset.Icc 1 x).filter (fun n => m * n ≤ x),
          ((m * n).divisors.card : ℝ)^4 * atilFIa (m * n) := by
    refine Finset.sum_le_sum (fun m hm => Finset.sum_le_sum (fun n hn => ?_))
    rw [Finset.mem_Icc] at hm
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨hm1, _⟩ := hm
    obtain ⟨⟨hn1, _⟩, _⟩ := hn
    have hmn0 : m * n ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
    have hτm : ((m.divisors.card : ℝ)) ≤ ((m * n).divisors.card : ℝ) :=
      by exact_mod_cast Submission.ASP.card_divisors_le_of_dvd (dvd_mul_right m n) hmn0
    have hτn : ((n.divisors.card : ℝ)) ≤ ((m * n).divisors.card : ℝ) :=
      by exact_mod_cast Submission.ASP.card_divisors_le_of_dvd (dvd_mul_left n m) hmn0
    have hã0 : 0 ≤ atilFIa (m * n) := rwcp_atilFIa_nonneg _
    have hτmn0 : 0 ≤ ((m * n).divisors.card : ℝ) := Nat.cast_nonneg _
    have hτm0 : 0 ≤ ((m.divisors.card : ℝ)) := Nat.cast_nonneg _
    calc ((m.divisors.card : ℝ))^3 * (((n.divisors.card : ℝ)) * atilFIa (m * n))
        ≤ (((m * n).divisors.card : ℝ))^3 * (((m * n).divisors.card : ℝ) * atilFIa (m * n)) :=
          mul_le_mul (pow_le_pow_left₀ hτm0 hτm 3)
            (mul_le_mul_of_nonneg_right hτn hã0)
            (mul_nonneg (Nat.cast_nonneg _) hã0) (by positivity)
      _ = (((m * n).divisors.card : ℝ))^4 * atilFIa (m * n) := by ring
  have h4 : (∑ m ∈ Finset.Icc 1 x, ∑ n ∈ (Finset.Icc 1 x).filter (fun n => m * n ≤ x),
          ((m * n).divisors.card : ℝ)^4 * atilFIa (m * n))
      ≤ ∑ l ∈ Finset.Icc 1 x, ((l.divisors.card : ℝ))
          * (((l.divisors.card : ℝ))^4 * atilFIa l) :=
    TauMulReindex (g := fun l => ((l.divisors.card : ℝ))^4 * atilFIa l)
      (fun l => mul_nonneg (by positivity) (rwcp_atilFIa_nonneg l)) x
  have h5 : (∑ l ∈ Finset.Icc 1 x, ((l.divisors.card : ℝ))
        * (((l.divisors.card : ℝ))^4 * atilFIa l))
      ≤ ∑ l ∈ Finset.Icc 1 x, ((l.divisors.card : ℝ))^8 * atilFIa l := by
    refine Finset.sum_le_sum (fun l hl => ?_)
    rw [Finset.mem_Icc] at hl
    obtain ⟨hl1, _⟩ := hl
    have hτ1 : (1 : ℝ) ≤ (l.divisors.card : ℝ) := by
      have : 1 ≤ l.divisors.card :=
        Finset.card_pos.mpr ⟨1, Nat.mem_divisors.mpr ⟨one_dvd l, by omega⟩⟩
      exact_mod_cast this
    have hã0 : 0 ≤ atilFIa l := rwcp_atilFIa_nonneg l
    have hpow : ((l.divisors.card : ℝ)) * (((l.divisors.card : ℝ))^4)
        ≤ ((l.divisors.card : ℝ))^8 := by
      calc ((l.divisors.card : ℝ)) * (((l.divisors.card : ℝ))^4)
          = ((l.divisors.card : ℝ))^5 := by ring
        _ ≤ ((l.divisors.card : ℝ))^8 := pow_le_pow_right₀ hτ1 (by norm_num)
    calc ((l.divisors.card : ℝ)) * (((l.divisors.card : ℝ))^4 * atilFIa l)
        = (((l.divisors.card : ℝ)) * ((l.divisors.card : ℝ))^4) * atilFIa l := by ring
      _ ≤ ((l.divisors.card : ℝ))^8 * atilFIa l := mul_le_mul_of_nonneg_right hpow hã0
  exact le_trans h2 (le_trans h3 (le_trans h4 h5))

/-! ## 5. The single-integer window is negligible -/

/-- The extra single-integer window `(n₀-1, n₀]` contributes at most `τ(n₀)·A_{n₀}(x)`. -/
private lemma rwcp_extra_le (x n₀ : ℕ) (hn₀ : 1 ≤ n₀) (s : ℝ) :
    (∑ m ∈ Finset.Icc 1 x, |BinWin x (((n₀ - 1 : ℕ)) : ℝ) ((n₀ : ℕ) : ℝ) s m|)
      ≤ (n₀.divisors.card : ℝ) * ∑ n ∈ (Finset.Icc 1 x).filter (fun n => n₀ ∣ n), atilFIa n := by
  have h1 : ∀ m : ℕ, |BinWin x (((n₀ - 1 : ℕ)) : ℝ) ((n₀ : ℕ) : ℝ) s m|
      ≤ (if m * n₀ ≤ x then (n₀.divisors.card : ℝ) * atilFIa (m * n₀) else 0) := by
    intro m
    have hBs : BinWin x (((n₀ - 1 : ℕ)) : ℝ) ((n₀ : ℕ) : ℝ) s m
        = (if n₀ ∈ (Finset.Icc 1 x).filter (fun n => m * n ≤ x) then gw m s n₀ else 0) := by
      have h := rwcp_BinWin_single x (n₀ - 1) s m
      rw [show ((n₀ - 1 : ℕ) + 1 : ℕ) = n₀ from by omega] at h
      exact h
    rw [hBs]
    by_cases hF : n₀ ∈ (Finset.Icc 1 x).filter (fun n => m * n ≤ x)
    · rw [if_pos hF]
      have hmn : m * n₀ ≤ x := (Finset.mem_filter.mp hF).2
      have hγ := rwcp_abs_gammaTrunc_le s n₀
      have hμ := rwcp_abs_moebius_cast_le_one n₀
      have hã0 : 0 ≤ atilFIa (m * n₀) := rwcp_atilFIa_nonneg _
      have hγ0 : 0 ≤ (n₀.divisors.card : ℝ) := Nat.cast_nonneg _
      rw [gw, abs_mul, abs_mul, abs_of_nonneg hã0]
      have hle : |Work.FIPlan.gammaTrunc s n₀| * |(ArithmeticFunction.moebius n₀ : ℝ)|
            * atilFIa (m * n₀) ≤ (n₀.divisors.card : ℝ) * atilFIa (m * n₀) := by
        calc |Work.FIPlan.gammaTrunc s n₀| * |(ArithmeticFunction.moebius n₀ : ℝ)|
                * atilFIa (m * n₀)
            ≤ (n₀.divisors.card : ℝ) * 1 * atilFIa (m * n₀) :=
              mul_le_mul (mul_le_mul hγ hμ (abs_nonneg _) hγ0) le_rfl hã0 (by positivity)
          _ = (n₀.divisors.card : ℝ) * atilFIa (m * n₀) := by ring
      rw [if_pos hmn]; exact hle
    · rw [if_neg hF, abs_zero]
      by_cases hmn : m * n₀ ≤ x
      · rw [if_pos hmn]
        exact mul_nonneg (Nat.cast_nonneg _) (rwcp_atilFIa_nonneg _)
      · rw [if_neg hmn]
  refine le_trans (Finset.sum_le_sum (fun m _ => h1 m)) ?_
  have h3 : (∑ m ∈ Finset.Icc 1 x,
        (if m * n₀ ≤ x then (n₀.divisors.card : ℝ) * atilFIa (m * n₀) else 0))
      = (n₀.divisors.card : ℝ)
        * ∑ m ∈ Finset.Icc 1 x, (if m * n₀ ≤ x then atilFIa (m * n₀) else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    by_cases h : m * n₀ ≤ x <;> simp [h]
  have h4 : (∑ m ∈ Finset.Icc 1 x, (if m * n₀ ≤ x then atilFIa (m * n₀) else 0))
      ≤ ∑ n ∈ (Finset.Icc 1 x).filter (fun n => n₀ ∣ n), atilFIa n := by
    have h := SumIteDivDvd n₀ x hn₀ (fun _ : ℕ => (1 : ℝ)) (fun n => atilFIa n)
    simp only [one_mul] at h
    have heq : (∑ m ∈ Finset.Icc 1 x, (if m * n₀ ≤ x then atilFIa (m * n₀) else 0))
        = ∑ m ∈ Finset.Icc 1 x, (if n₀ * m ≤ x then atilFIa (n₀ * m) else 0) := by
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [mul_comm m n₀]
    rw [heq]; exact h
  rw [h3]
  exact mul_le_mul_of_nonneg_left h4 (Nat.cast_nonneg _)

/-! ## 6. The combination of the two Hölder factors -/

private lemma rwcp_combine {L C Kw Au : ℝ} (hL : 1 ≤ L) (hC : 0 ≤ C) (hKw : 0 ≤ Kw)
    (hAu : 0 ≤ Au) :
    (C * Au * L ^ (262144 : ℕ)) ^ ((2 : ℝ) / 3)
        * (Kw * Au * L ^ (-((2 : ℝ) ^ (26 : ℕ)))) ^ ((1 : ℝ) / 3)
      ≤ (C ^ ((2 : ℝ) / 3) * Kw ^ ((1 : ℝ) / 3) * Au) * L ^ (-(4 : ℤ)) := by
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hCA : 0 ≤ C * Au := mul_nonneg hC hAu
  have hKA : 0 ≤ Kw * Au := mul_nonneg hKw hAu
  have hL18 : L ^ (262144 : ℕ) = L ^ ((262144 : ℕ) : ℝ) := (Real.rpow_natCast L 262144).symm
  have hA18 : 0 ≤ L ^ ((262144 : ℕ) : ℝ) := Real.rpow_nonneg hLpos.le _
  have hA26 : 0 ≤ L ^ (-((2 : ℝ) ^ (26 : ℕ))) := Real.rpow_nonneg hLpos.le _
  have step1 : (C * Au * L ^ (262144 : ℕ)) ^ ((2 : ℝ) / 3)
      = (C ^ ((2 : ℝ) / 3) * Au ^ ((2 : ℝ) / 3))
          * L ^ ((((262144 : ℕ)) : ℝ) * ((2 : ℝ) / 3)) := by
    rw [hL18, Real.mul_rpow hCA hA18, Real.mul_rpow hC hAu, ← Real.rpow_mul hLpos.le]
  have step2 : (Kw * Au * L ^ (-((2 : ℝ) ^ (26 : ℕ)))) ^ ((1 : ℝ) / 3)
      = (Kw ^ ((1 : ℝ) / 3) * Au ^ ((1 : ℝ) / 3))
          * L ^ ((-((2 : ℝ) ^ (26 : ℕ))) * ((1 : ℝ) / 3)) := by
    rw [Real.mul_rpow hKA hA26, Real.mul_rpow hKw hAu, ← Real.rpow_mul hLpos.le]
  have hAueq : Au ^ ((2 : ℝ) / 3) * Au ^ ((1 : ℝ) / 3) = Au := by
    rw [← Real.rpow_add' hAu (by norm_num : (2 : ℝ) / 3 + (1 : ℝ) / 3 ≠ 0)]
    rw [show (2 : ℝ) / 3 + (1 : ℝ) / 3 = 1 by norm_num, Real.rpow_one]
  have hLeq : L ^ ((((262144 : ℕ)) : ℝ) * ((2 : ℝ) / 3))
        * L ^ ((-((2 : ℝ) ^ (26 : ℕ))) * ((1 : ℝ) / 3))
      = L ^ ((-66584576 : ℝ) / 3) := by
    rw [← Real.rpow_add' (le_of_lt hLpos)
      (by norm_num : (((262144 : ℕ)) : ℝ) * ((2 : ℝ) / 3)
        + (-((2 : ℝ) ^ (26 : ℕ))) * ((1 : ℝ) / 3) ≠ 0)]
    rw [show (((262144 : ℕ)) : ℝ) * ((2 : ℝ) / 3)
        + (-((2 : ℝ) ^ (26 : ℕ))) * ((1 : ℝ) / 3) = (-66584576 : ℝ) / 3 by norm_num]
  have key : (C * Au * L ^ (262144 : ℕ)) ^ ((2 : ℝ) / 3)
        * (Kw * Au * L ^ (-((2 : ℝ) ^ (26 : ℕ)))) ^ ((1 : ℝ) / 3)
      = (C ^ ((2 : ℝ) / 3) * Kw ^ ((1 : ℝ) / 3) * Au) * L ^ ((-66584576 : ℝ) / 3) := by
    rw [step1, step2]
    calc ((C ^ ((2 : ℝ) / 3) * Au ^ ((2 : ℝ) / 3))
            * L ^ ((((262144 : ℕ)) : ℝ) * ((2 : ℝ) / 3)))
            * ((Kw ^ ((1 : ℝ) / 3) * Au ^ ((1 : ℝ) / 3))
                * L ^ ((-((2 : ℝ) ^ (26 : ℕ))) * ((1 : ℝ) / 3)))
        = (C ^ ((2 : ℝ) / 3) * (Au ^ ((2 : ℝ) / 3) * Au ^ ((1 : ℝ) / 3)) * Kw ^ ((1 : ℝ) / 3))
            * (L ^ ((((262144 : ℕ)) : ℝ) * ((2 : ℝ) / 3))
                * L ^ ((-((2 : ℝ) ^ (26 : ℕ))) * ((1 : ℝ) / 3))) := by ring
      _ = (C ^ ((2 : ℝ) / 3) * Au * Kw ^ ((1 : ℝ) / 3)) * L ^ ((-66584576 : ℝ) / 3) := by
            rw [hAueq, hLeq]
      _ = (C ^ ((2 : ℝ) / 3) * Kw ^ ((1 : ℝ) / 3) * Au) * L ^ ((-66584576 : ℝ) / 3) := by ring
  have hArpow : (0 : ℝ) ≤ C ^ ((2 : ℝ) / 3) * Kw ^ ((1 : ℝ) / 3) * Au :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg hC _) (Real.rpow_nonneg hKw _)) hAu
  rw [key, ← Real.rpow_intCast L (-4)]
  refine mul_le_mul_of_nonneg_left ?_ hArpow
  exact Real.rpow_le_rpow_of_exponent_le hL (by norm_num)

/-! ## 2. The parametric window lemma -/

/-! ## 3. The window at the corrected `B`-dependent scale -/

end

end Work.FIChain
