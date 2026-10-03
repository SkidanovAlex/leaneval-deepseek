import Mathlib
import Submission.Work.FIArea4.A4c.Defs
import Submission.Work.FIArea4.A6Crude

namespace Work.FIArea4.A4c

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## Elementary facts about `junkCut` -/

/-- `junkCut X m z₁ z₂ d = 1{m < d ∧ d ≤ X ∧ |Δ(z₁,z₂)| ≤ 4dm}` vanishes for `X < d`. -/
lemma junkCut_eq_zero_of_lt {X m d : ℕ} (z1 z2 : GaussianInt) (h : X < d) :
    junkCut X m z1 z2 d = 0 := by
  have hc : ¬ (m < d ∧ d ≤ X ∧ Work.FIPlan.absDelta z1 z2 ≤ 4 * d * m) := by
    rintro ⟨-, hdX, -⟩
    omega
  unfold junkCut
  rw [if_neg hc]

/-- `junkCut` is an indicator function, hence bounded by `1` in absolute value. -/
lemma abs_junkCut_le_one (X m : ℕ) (z1 z2 : GaussianInt) (d : ℕ) :
    |junkCut X m z1 z2 d| ≤ 1 := by
  unfold junkCut
  by_cases h : m < d ∧ d ≤ X ∧ Work.FIPlan.absDelta z1 z2 ≤ 4 * d * m
  · rw [if_pos h]; norm_num
  · rw [if_neg h]; norm_num

/-- If `d ≤ X`, `m ≤ X` and `|Δ(z₁,z₂)| > 4X²`, then `junkCut X m z₁ z₂ d = 0`: the support
condition `|Δ| ≤ 4dm` together with `d,m ≤ X` forces `|Δ| ≤ 4X²`. -/
lemma junkCut_eq_zero_of_not_absDelta {X m d : ℕ} (z1 z2 : GaussianInt) (hdX : d ≤ X)
    (hmX : m ≤ X) (hΔ : ¬ Work.FIPlan.absDelta z1 z2 ≤ 4 * X * X) :
    junkCut X m z1 z2 d = 0 := by
  have hc : ¬ (m < d ∧ d ≤ X ∧ Work.FIPlan.absDelta z1 z2 ≤ 4 * d * m) := by
    rintro ⟨-, -, hdm⟩
    refine hΔ (le_trans hdm ?_)
    calc 4 * d * m = 4 * (d * m) := by ring
      _ ≤ 4 * (X * X) := Nat.mul_le_mul_left 4 (Nat.mul_le_mul hdX hmX)
      _ = 4 * X * X := by ring
  unfold junkCut
  rw [if_neg hc]

/-- **The trivial bound for the inner `d`-sum of the junk cut.**  `junkCut X m z₁ z₂ d` is
supported on `m < d ≤ X ∧ |Δ(z₁,z₂)| ≤ 4dm`, so for `z₁,z₂` in the inner box `boxN Pa` the summand
is bounded by `|logFac6 z₁z₂| ≤ 40(log(4N)+1)`, and at most `X` values of `d` can contribute
(`d ∈ Sset z₁ z₂ ⊆ Icc 1 (|Δ|/4+1)` with `d ≤ X`).  If `d ≤ X` and `m ≤ X` then
`|Δ(z₁,z₂)| ≤ 4dm ≤ 4X²`, so when `|Δ| > 4X²` the sum vanishes identically.

Route: with `A := (Sset z₁ z₂).filter (fun d => d ≤ X)`, all terms outside `A` are literally
`0` (`junkCut` has the clause `d ≤ X`), each term of `A` has `|(φ(d)/d)·junkCut·(z₂/z₁|d)·logFac6|
≤ 1·1·1·|logFac6| ≤ 40(log(4N)+1)` (`Nat.totient_le`, `a6_ratioSym_abs_le`,
`a6_logFac6_abs_le`, the last via `a6_mem_boxN_gnorm_le`), and `A ⊆ Icc 1 X` so `A.card ≤ X`;
if `¬ (|Δ| ≤ 4X²)` then `junkCut` vanishes at every `d ∈ Sset` because `4dm ≤ 4X·m ≤ 4X²`. -/
theorem junkDsum_abs_le (Pa : Work.FITop.Params) (X m : ℕ) (hX : 1 ≤ X) (hm : m ≤ X)
    {z1 z2 : GaussianInt} (hz1 : z1 ∈ Work.FITop.boxN Pa) (hz2 : z2 ∈ Work.FITop.boxN Pa) :
    |∑ d ∈ Work.FITop4.Sset z1 z2,
        ((Nat.totient d : ℝ) / (d : ℝ)) * Work.FIArea4.A4c.junkCut X m z1 z2 d
          * (Work.FITop4.ratioSym z1 z2 d : ℝ) * Work.FITop4.logFac6 z1 z2|
      ≤ (if Work.FIPlan.absDelta z1 z2 ≤ 4 * X * X then
          (X : ℝ) * (40 * (Real.log (4 * Pa.N) + 1)) else 0) := by
  have hN1 : (1 : ℝ) ≤ Pa.N := by exact_mod_cast Pa.hN1
  have hCnn : 0 ≤ 40 * (Real.log (4 * Pa.N) + 1) := by
    have h4N : (0 : ℝ) ≤ Real.log (4 * Pa.N) := Real.log_nonneg (by linarith)
    linarith
  have hlog : |Work.FITop4.logFac6 z1 z2| ≤ 40 * (Real.log (4 * Pa.N) + 1) :=
    a6_logFac6_abs_le Pa.N hN1 z1 z2 (a6_mem_boxN_gnorm_le Pa hz1)
      (a6_mem_boxN_gnorm_le Pa hz2)
  by_cases hΔ : Work.FIPlan.absDelta z1 z2 ≤ 4 * X * X
  · rw [if_pos hΔ]
    set A : Finset ℕ := (Work.FITop4.Sset z1 z2).filter (fun d => d ≤ X) with hA
    have hA_mem : ∀ d : ℕ, d ∈ A ↔ d ∈ Work.FITop4.Sset z1 z2 ∧ d ≤ X := by
      intro d
      rw [hA]
      exact Finset.mem_filter
    have hA_sub : A ⊆ Work.FITop4.Sset z1 z2 := fun d hd => ((hA_mem d).mp hd).1
    have hsum_eq :
        (∑ d ∈ Work.FITop4.Sset z1 z2,
            ((Nat.totient d : ℝ) / (d : ℝ)) * junkCut X m z1 z2 d
              * (Work.FITop4.ratioSym z1 z2 d : ℝ) * Work.FITop4.logFac6 z1 z2)
          = ∑ d ∈ A,
            ((Nat.totient d : ℝ) / (d : ℝ)) * junkCut X m z1 z2 d
              * (Work.FITop4.ratioSym z1 z2 d : ℝ) * Work.FITop4.logFac6 z1 z2 := by
      refine (Finset.sum_subset hA_sub ?_).symm
      intro d hdS hdA
      have hdX : ¬ d ≤ X := by
        intro hle
        exact hdA ((hA_mem d).mpr ⟨hdS, hle⟩)
      rw [junkCut_eq_zero_of_lt (X := X) (m := m) (d := d) z1 z2
        (Nat.lt_of_not_le hdX)]
      ring
    have hterm : ∀ d ∈ A,
        |((Nat.totient d : ℝ) / (d : ℝ)) * junkCut X m z1 z2 d
          * (Work.FITop4.ratioSym z1 z2 d : ℝ) * Work.FITop4.logFac6 z1 z2|
        ≤ 40 * (Real.log (4 * Pa.N) + 1) := by
      intro d hd
      obtain ⟨hdS, _hdX⟩ := (hA_mem d).mp hd
      have hd1 : 1 ≤ d := (Finset.mem_Icc.mp (Finset.mem_filter.mp hdS).1).1
      have hcard1 : |(Nat.totient d : ℝ) / (d : ℝ)| ≤ 1 := by
        have hdpos : (0 : ℝ) < (d : ℝ) := by
          exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hd1)
        rw [abs_div, abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (Nat.cast_nonneg _),
          div_le_one hdpos]
        exact_mod_cast Nat.totient_le d
      have hrs : |(Work.FITop4.ratioSym z1 z2 d : ℝ)| ≤ 1 := a6_ratioSym_abs_le z1 z2 d
      have h1 : |(Nat.totient d : ℝ) / (d : ℝ)| * |junkCut X m z1 z2 d| ≤ 1 := by
        simpa using mul_le_mul hcard1 (abs_junkCut_le_one X m z1 z2 d) (abs_nonneg _)
          (by norm_num : (0 : ℝ) ≤ 1)
      rw [abs_mul, abs_mul, abs_mul]
      calc |(Nat.totient d : ℝ) / (d : ℝ)| * |junkCut X m z1 z2 d|
              * |(Work.FITop4.ratioSym z1 z2 d : ℝ)| * |Work.FITop4.logFac6 z1 z2|
          ≤ 1 * |Work.FITop4.logFac6 z1 z2| := by
            refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
            calc |(Nat.totient d : ℝ) / (d : ℝ)| * |junkCut X m z1 z2 d|
                  * |(Work.FITop4.ratioSym z1 z2 d : ℝ)|
                ≤ 1 * 1 := mul_le_mul h1 hrs (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
              _ = 1 := by ring
        _ ≤ 1 * (40 * (Real.log (4 * Pa.N) + 1)) :=
            mul_le_mul_of_nonneg_left hlog (by norm_num)
        _ = 40 * (Real.log (4 * Pa.N) + 1) := by ring
    have hAcard : A.card ≤ X := by
      have hsub : A ⊆ Finset.Icc 1 X := by
        intro d hd
        obtain ⟨hdS, hdX⟩ := (hA_mem d).mp hd
        have hd1 : 1 ≤ d := (Finset.mem_Icc.mp (Finset.mem_filter.mp hdS).1).1
        exact Finset.mem_Icc.mpr ⟨hd1, hdX⟩
      calc A.card ≤ (Finset.Icc 1 X).card := Finset.card_le_card hsub
        _ = X := by rw [Nat.card_Icc]; omega
    have hAcardR : (A.card : ℝ) ≤ (X : ℝ) := by exact_mod_cast hAcard
    rw [hsum_eq]
    calc |∑ d ∈ A, ((Nat.totient d : ℝ) / (d : ℝ)) * junkCut X m z1 z2 d
          * (Work.FITop4.ratioSym z1 z2 d : ℝ) * Work.FITop4.logFac6 z1 z2|
        ≤ ∑ d ∈ A, |((Nat.totient d : ℝ) / (d : ℝ)) * junkCut X m z1 z2 d
          * (Work.FITop4.ratioSym z1 z2 d : ℝ) * Work.FITop4.logFac6 z1 z2| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _d ∈ A, (40 * (Real.log (4 * Pa.N) + 1)) := Finset.sum_le_sum hterm
      _ = (A.card : ℝ) * (40 * (Real.log (4 * Pa.N) + 1)) := by
          simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (X : ℝ) * (40 * (Real.log (4 * Pa.N) + 1)) :=
          mul_le_mul_of_nonneg_right hAcardR hCnn
  · rw [if_neg hΔ]
    have hzero : (∑ d ∈ Work.FITop4.Sset z1 z2,
        ((Nat.totient d : ℝ) / (d : ℝ)) * junkCut X m z1 z2 d
          * (Work.FITop4.ratioSym z1 z2 d : ℝ) * Work.FITop4.logFac6 z1 z2) = 0 := by
      refine Finset.sum_eq_zero (fun d _hdS => ?_)
      by_cases hdX : d ≤ X
      · rw [junkCut_eq_zero_of_not_absDelta (X := X) (m := m) (d := d) z1 z2 hdX hm hΔ]
        ring
      · rw [junkCut_eq_zero_of_lt (X := X) (m := m) (d := d) z1 z2 (Nat.lt_of_not_le hdX)]
        ring
    rw [hzero, abs_zero]

end

end Work.FIArea4.A4c
