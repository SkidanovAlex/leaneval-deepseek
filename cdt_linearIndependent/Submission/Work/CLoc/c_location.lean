import Mathlib
import Submission.CDTPlan.Interfaces
import Submission.CDT.LocationSing
import Submission.Work.CLoc.defs
import Submission.Work.CLoc.gap_delta
import Submission.Work.CLoc.small_small_le
import Submission.Work.CLoc.large_large_ge

/-! Guidance from the project lead (the requester):

# Area CLoc — location of the singularities, non-strict gap (`Submission.CDTPlan.CLocation`)

a = 2m+1, b = 2n+1, x_{±±} = (a ± √(a²−1))(b ± √(b²−1)), y = x²/(x−1).
Under m,n ≥ 1, m ≠ n, 10⁶|m−n| ≤ n (so n ≥ 10⁶, m ≥ 10⁶ − 1):
|y_{--}| ≈ 4e-27 (≤ 1e-20 needed), |y_{++}| ≈ 1.6e13, |y_{+-}|, |y_{-+}| ≥ 999998.25 (≥ 900000
needed) — computed at the extreme cases m = n ± 1, n = 10⁶ and m = n ± 2, n = 2·10⁶.
The prior run proved the STRICT-gap positive version with an ε: `Submission/CDT/LocationSing.lean`
(`location_core`, `location_singularities`, `ymap_*` lemmas). Adapt it: the non-strict gap only
changes ε from 10⁻⁶ to 10⁻⁶ exactly with ≤, and the targets here have a lot of slack.
Useful: η := x_{+-} satisfies |η − 1| ≈ |a−b|/b ≤ ~1e-6·(1+O(1/n)) and y = η²/(η−1).

## The proof

Write `P := max m n`, `Q := min m n`, `d := P - Q ≥ 1`, `ε := 10⁻⁶` and `A := sqP P`,
`C := sqP Q`.  The non-strict gap hypothesis is exactly `d ≤ Q ε (1+2ε)` (`ε` instead of a strict
`< ε` for the case `m > n`; for `m < n`, where the gap hypothesis reads `d·10⁶ ≤ Q + d`, it gives
the slightly weaker `d ≤ Q/(10⁶-1) ≤ Q ε (1+2ε)`).  It forces `Q ≥ 999998`.

* `x_{--} = sqM P · sqM Q = 1/(AC)`: `|y| = 1/(AC(AC-1)) ≤ 10⁻²⁰` since `AC ≥ 16·10¹²`
  (`Submission.Work.CLoc.small_small_le`);
* `x_{++} = A·C ≥ 16·10¹²`: `|y| = (AC)²/(AC-1) ≥ AC > 900000`
  (`Submission.Work.CLoc.large_large_ge`);
* the two mixed points are `η := A/C` and `1/η`, with `y(η) = η²/(η-1)` and `|y(1/η)| = 1/(η(η-1))`;
  the relative gap `δ := (A-C)/C = η - 1` satisfies `δ ≤ 1.0005·10⁻⁶`
  (`Submission.Work.CLoc.gap_delta`), so `y(η) ≥ 1/δ ≥ 999500` and
  `|y(1/η)| ≥ 1/((1+δ)δ) ≥ 999499` (`Submission.Work.CLoc.mixed_ge`).
-/

namespace Work.CLoc

open Submission.CDTPlan
open Submission.CDT.LocationSing

/-- The mixed singularities `η = sqP P/sqP Q` and `1/η`: their `y`-values are at least `900000`,
because the relative gap `η - 1 = (sqP P - sqP Q)/sqP Q` is at most `1.0005·10⁻⁶`.  (`y(η) = η²/δ`
and `|y(1/η)| = 1/(η δ)`, and `η ≤ 1 + δ`.) -/
lemma cLoc_mixed_ge (P Q : ℕ) (hQ : 1 ≤ Q) (hPQ : Q < P)
    (hdelta : (sqP (P:ℝ) - sqP (Q:ℝ)) / sqP (Q:ℝ) ≤ 1.0005/10^6) :
    900000 ≤ |ymap (sqP (P:ℝ) * sqM (Q:ℝ))| ∧
      900000 ≤ |ymap (sqM (P:ℝ) * sqP (Q:ℝ))| := by
  have hP0 : (0:ℝ) ≤ (P:ℝ) := by positivity
  have hQ0 : (0:ℝ) ≤ (Q:ℝ) := by positivity
  have hApos : 0 < sqP (P:ℝ) := sqP_pos _ hP0
  have hCpos : 0 < sqP (Q:ℝ) := sqP_pos _ hQ0
  have hCA : sqP (Q:ℝ) < sqP (P:ℝ) := sqP_lt_sqP hQ0 (by exact_mod_cast hPQ)
  have hδeq : sqP (P:ℝ)/sqP (Q:ℝ) - 1 = (sqP (P:ℝ) - sqP (Q:ℝ))/sqP (Q:ℝ) := by
    field_simp
  have hη1 : 1 < sqP (P:ℝ)/sqP (Q:ℝ) := (one_lt_div hCpos).mpr hCA
  have hδle : sqP (P:ℝ)/sqP (Q:ℝ) - 1 ≤ 1.0005/10^6 := by rw [hδeq]; exact hdelta
  have hδpos : 0 < sqP (P:ℝ)/sqP (Q:ℝ) - 1 := by linarith
  constructor
  · have hAC : sqP (P:ℝ) * sqM (Q:ℝ) = sqP (P:ℝ)/sqP (Q:ℝ) := by
      rw [sqM_eq_inv _ hQ0, inv_eq_one_div, mul_one_div]
    rw [hAC]
    have hval : |ymap (sqP (P:ℝ)/sqP (Q:ℝ))| =
        (sqP (P:ℝ)/sqP (Q:ℝ))^2 / (sqP (P:ℝ)/sqP (Q:ℝ) - 1) := by
      unfold ymap
      rw [abs_of_pos (div_pos (pow_pos (by linarith : (0:ℝ) < sqP (P:ℝ)/sqP (Q:ℝ)) 2) hδpos)]
    rw [hval, le_div_iff₀ hδpos]
    have h1 : 900000 * (sqP (P:ℝ)/sqP (Q:ℝ) - 1) ≤ 900000 * (1.0005/10^6) :=
      mul_le_mul_of_nonneg_left hδle (by norm_num)
    have h2 : (900000 : ℝ) * (1.0005/10^6) ≤ 1 := by norm_num
    have h3 : (1:ℝ) ≤ (sqP (P:ℝ)/sqP (Q:ℝ))^2 := by nlinarith [hη1]
    linarith
  · have hCP : sqM (P:ℝ) * sqP (Q:ℝ) = sqP (Q:ℝ)/sqP (P:ℝ) := by
      rw [sqM_eq_inv _ hP0, inv_eq_one_div, one_div_mul_eq_div]
    rw [hCP]
    have hxeq : sqP (Q:ℝ)/sqP (P:ℝ) = (sqP (P:ℝ)/sqP (Q:ℝ))⁻¹ := by rw [inv_div]
    have hval : ymap (sqP (Q:ℝ)/sqP (P:ℝ)) =
        -(1/((sqP (P:ℝ)/sqP (Q:ℝ)) * (sqP (P:ℝ)/sqP (Q:ℝ) - 1))) := by
      rw [hxeq]
      unfold ymap
      field_simp
      rw [one_div, one_div, neg_inv]
      congr 1
      ring
    have hDpos : 0 < (sqP (P:ℝ)/sqP (Q:ℝ)) * (sqP (P:ℝ)/sqP (Q:ℝ) - 1) :=
      mul_pos (by linarith) hδpos
    rw [hval, abs_neg, abs_of_pos (div_pos one_pos hDpos), le_div_iff₀ hDpos]
    have hb1 : sqP (P:ℝ)/sqP (Q:ℝ) ≤ 1 + 1.0005/10^6 := by linarith
    have hprod : (sqP (P:ℝ)/sqP (Q:ℝ)) * (sqP (P:ℝ)/sqP (Q:ℝ) - 1) ≤
        (1 + 1.0005/10^6) * (1.0005/10^6) :=
      mul_le_mul hb1 hδle hδpos.le (by norm_num)
    have hnum : (900000:ℝ) * ((1 + 1.0005/10^6) * (1.0005/10^6)) ≤ 1 := by norm_num
    linarith

/-- The non-strict gap forces `Q` to be large: `Q ≥ 999998` whenever `Q < P` and
`P - Q ≤ Q ε (1+2ε)`, `ε = 10⁻⁶`. -/
lemma cLoc_Q_ge (P Q : ℕ) (hPQ : Q < P)
    (hd : (P:ℝ) - (Q:ℝ) ≤ (Q:ℝ) * (1/10^6) * (1 + 2/10^6)) : (999998:ℝ) ≤ (Q:ℝ) := by
  have h1 : (1:ℝ) ≤ (P:ℝ) - (Q:ℝ) := by
    have h2 : ((Q:ℝ) + 1) ≤ (P:ℝ) := by
      have : Q + 1 ≤ P := hPQ
      exact_mod_cast this
    linarith
  have h2 : (1:ℝ) ≤ (Q:ℝ) * (1/10^6) * (1 + 2/10^6) := le_trans h1 hd
  nlinarith [h2]

/-- The four `y`-values of the singularities for `1 ≤ Q < P` with the non-strict gap
`P - Q ≤ Q ε (1+2ε)`, `ε = 10⁻⁶`. -/
lemma cLoc_core (P Q : ℕ) (hPQ : Q < P)
    (hd : (P:ℝ) - (Q:ℝ) ≤ (Q:ℝ) * (1/10^6) * (1 + 2/10^6)) :
    |ymap (sqP (P:ℝ) * sqP (Q:ℝ))| ≥ 900000 ∧
    |ymap (sqP (P:ℝ) * sqM (Q:ℝ))| ≥ 900000 ∧
    |ymap (sqM (P:ℝ) * sqP (Q:ℝ))| ≥ 900000 ∧
    |ymap (sqM (P:ℝ) * sqM (Q:ℝ))| ≤ 1/10^20 := by
  have hQ8 : (999998:ℝ) ≤ (Q:ℝ) := cLoc_Q_ge P Q hPQ hd
  have hQ : 1 ≤ Q := by
    have h : (1:ℝ) ≤ (Q:ℝ) := by linarith [hQ8]
    exact_mod_cast h
  have hδ := gap_delta P Q hQ hPQ hd
  obtain ⟨hm1, hm2⟩ := cLoc_mixed_ge P Q hQ hPQ hδ
  exact ⟨large_large_ge P Q hQ8 hPQ, hm1, hm2, small_small_le P Q hQ8 hPQ⟩

theorem c_location : CLocation := by
  intro m n _ _ hmn hgap
  have hgapR : (10:ℝ)^6 * |(m:ℝ) - (n:ℝ)| ≤ (n:ℝ) := by
    have h : ((10^6 : ℕ) : ℝ) * ((((m:ℤ) - n).natAbs : ℕ) : ℝ) ≤ (n:ℝ) := by
      exact_mod_cast hgap
    rw [Nat.cast_natAbs, Int.cast_abs, Nat.cast_pow, Nat.cast_ofNat] at h
    push_cast at h
    convert h using 2
  rw [yOf_eq_ymap, xRoot_mm m n, xRoot_pp m n, xRoot_pm m n, xRoot_mp m n]
  rcases Nat.lt_or_gt_of_ne hmn with hlt | hlt
  · -- m < n : P = n, Q = m
    have hd : (n:ℝ) - (m:ℝ) ≤ (m:ℝ) * (1/10^6) * (1 + 2/10^6) := by
      have hm0 : (0:ℝ) ≤ (m:ℝ) := by positivity
      have hle : (m:ℝ) ≤ (n:ℝ) := by exact_mod_cast le_of_lt hlt
      have habs : |(m:ℝ) - (n:ℝ)| = (n:ℝ) - (m:ℝ) := by
        rw [abs_of_nonpos (by linarith : (m:ℝ) - (n:ℝ) ≤ 0), neg_sub]
      have hg : (10:ℝ)^6 * ((n:ℝ) - (m:ℝ)) ≤ (n:ℝ) := by rwa [habs] at hgapR
      have h1 : ((10:ℝ)^6 - 1) * ((n:ℝ) - (m:ℝ)) ≤ (m:ℝ) := by
        have hn' : (n:ℝ) = (m:ℝ) + ((n:ℝ) - (m:ℝ)) := by ring
        nlinarith [hg, hn']
      have h2 : (n:ℝ) - (m:ℝ) ≤ (m:ℝ) / ((10:ℝ)^6 - 1) := by
        rw [le_div_iff₀ (by norm_num : (0:ℝ) < (10:ℝ)^6 - 1)]
        linarith [h1]
      have h3 : (1:ℝ) / ((10:ℝ)^6 - 1) ≤ (1/10^6) * (1 + 2/10^6) := by
        rw [div_le_iff₀ (by norm_num : (0:ℝ) < (10:ℝ)^6 - 1)]
        norm_num
      calc (n:ℝ) - (m:ℝ) ≤ (m:ℝ) / ((10:ℝ)^6 - 1) := h2
        _ = (m:ℝ) * ((1:ℝ) / ((10:ℝ)^6 - 1)) := by rw [mul_one_div]
        _ ≤ (m:ℝ) * ((1/10^6) * (1 + 2/10^6)) := mul_le_mul_of_nonneg_left h3 hm0
        _ = (m:ℝ) * (1/10^6) * (1 + 2/10^6) := by ring
    obtain ⟨hpp, hpm, hmp, hmm⟩ := cLoc_core n m hlt hd
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [mul_comm (sqM (m:ℝ)) (sqM (n:ℝ))]; exact hmm
    · rw [mul_comm (sqP (m:ℝ)) (sqP (n:ℝ))]; exact hpp
    · rw [mul_comm (sqP (m:ℝ)) (sqM (n:ℝ))]; exact hmp
    · rw [mul_comm (sqM (m:ℝ)) (sqP (n:ℝ))]; exact hpm
  · -- n < m : P = m, Q = n
    have hd : (m:ℝ) - (n:ℝ) ≤ (n:ℝ) * (1/10^6) * (1 + 2/10^6) := by
      have hn0 : (0:ℝ) ≤ (n:ℝ) := by positivity
      have hle : (n:ℝ) ≤ (m:ℝ) := by exact_mod_cast le_of_lt hlt
      have habs : |(m:ℝ) - (n:ℝ)| = (m:ℝ) - (n:ℝ) := by
        rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ (m:ℝ) - (n:ℝ))]
      have hg : (10:ℝ)^6 * ((m:ℝ) - (n:ℝ)) ≤ (n:ℝ) := by rwa [habs] at hgapR
      have h1 : (m:ℝ) - (n:ℝ) ≤ (n:ℝ) / (10:ℝ)^6 := by
        rw [le_div_iff₀ (by norm_num : (0:ℝ) < (10:ℝ)^6)]
        linarith [hg]
      calc (m:ℝ) - (n:ℝ) ≤ (n:ℝ) / (10:ℝ)^6 := h1
        _ = (n:ℝ) * ((1:ℝ)/(10:ℝ)^6) := by rw [div_eq_mul_inv, div_eq_mul_inv, one_mul]
        _ ≤ (n:ℝ) * ((1/10^6) * (1 + 2/10^6)) := by
            apply mul_le_mul_of_nonneg_left _ hn0
            norm_num
        _ = (n:ℝ) * (1/10^6) * (1 + 2/10^6) := by ring
    obtain ⟨hpp, hpm, hmp, hmm⟩ := cLoc_core m n hlt hd
    exact ⟨hmm, hpp, hpm, hmp⟩

end Work.CLoc
