import Mathlib
import Submission.Work.C17.seventeen_defs
import Submission.Work.C17d.DyChainDefs
import Submission.Work.C17d.DyChain_ana
import Submission.Work.C17d.DyChain_rat
import Submission.Work.C17d.Cls_eq_pairStep

namespace Work.C17

open Polynomial Work.C17d
open scoped BigOperators
open Submission.CDTPlan

noncomputable section

/-! ## The final polynomial data

The class chain `cls a b k` (`k ≤ 3`) is computed by the cleared chain `(Dc k, Ac k, Bc k)` of
`Work.C17d`, with `Dc k = (P₂·W)^{2^k-1}` — so `Dc 3 = (P₂·W)^7` is a common multiple of all
`Dc k`, `k ≤ 3`.  Multiplying everything by a further `W²` puts the common denominator `D` into
the shape `W²·Dc 3`, which vanishes at `0` and `2`; the multipliers below are the explicit
quotients `m_k = D/D_k` (`W = X²-2X`). -/

/-- `wX` evaluated at `z` is `z² - 2z`. -/
lemma wX_eval₂ (z : ℂ) : wX.eval₂ (algebraMap ℚ ℂ) z = z ^ 2 - 2 * z := by simp [wX]

/-- The multiplier taking the level-`k` clearing to the common denominator `W²·Dc 3`. -/
def mfin (a b : ℚ) : Fin 4 → Polynomial ℚ
  | 0 => wX ^ 2 * Dc a b 3
  | 1 => (P2x a b) ^ 6 * wX ^ 8
  | 2 => (P2x a b) ^ 4 * wX ^ 6
  | 3 => wX ^ 2

/-- `m_k · D_k = W² · Dc 3`. -/
lemma mfin_mul_Dc (a b : ℚ) (k : Fin 4) :
    mfin a b k * Dc a b (k : ℕ) = wX ^ 2 * Dc a b 3 := by
  fin_cases k <;> simp [mfin, Work.C17d.Dc_succ] <;> ring

/-- `m_k` vanishes at `0`. -/
lemma mfin_eval₂_zero (a b : ℚ) (k : Fin 4) :
    (mfin a b k).eval₂ (algebraMap ℚ ℂ) 0 = 0 := by
  fin_cases k <;>
    simp only [mfin, Polynomial.eval₂_mul, Polynomial.eval₂_pow, wX_eval₂] <;> norm_num

/-- `m_k` vanishes at `2`. -/
lemma mfin_eval₂_two (a b : ℚ) (k : Fin 4) :
    (mfin a b k).eval₂ (algebraMap ℚ ℂ) 2 = 0 := by
  fin_cases k <;>
    simp only [mfin, Polynomial.eval₂_mul, Polynomial.eval₂_pow, wX_eval₂] <;> norm_num

/-- The pointwise identity for the final polynomial data, on the whole disc. -/
lemma DyIter_mfin_eq (a b : ℚ) (y1 : ℂ → ℂ) {δ : ℝ} (hδ : 0 < δ)
    (hy1d : DifferentiableOn ℂ y1 (Metric.ball ((xs a b : ℂ)) δ))
    (hode : ∀ z ∈ Metric.ball ((xs a b : ℂ)) δ,
      (P2x a b).eval₂ (algebraMap ℚ ℂ) z * deriv (deriv y1) z
        + (P1x a b).eval₂ (algebraMap ℚ ℂ) z * deriv y1 z
        + (P0x a b).eval₂ (algebraMap ℚ ℂ) z * y1 z = 0) (k : Fin 4) :
    ∀ z ∈ Metric.ball ((xs a b : ℂ)) δ,
      ((wX ^ 2 * Dc a b 3).eval₂ (algebraMap ℚ ℂ) z) * DyIter (k : ℕ) y1 z
        = ((mfin a b k * Ac a b (k : ℕ)).eval₂ (algebraMap ℚ ℂ) z) * y1 z
          + ((mfin a b k * Bc a b (k : ℕ)).eval₂ (algebraMap ℚ ℂ) z) * deriv y1 z := by
  intro z hz
  by_cases h02 : z ∈ ({0, 2} : Set ℂ)
  · have hz' : z = 0 ∨ z = 2 := by simpa using h02
    rcases hz' with h | h
    · subst h
      simp only [Polynomial.eval₂_mul, Polynomial.eval₂_pow, mfin_eval₂_zero, wX_eval₂]
      norm_num
    · subst h
      simp only [Polynomial.eval₂_mul, Polynomial.eval₂_pow, mfin_eval₂_two, wX_eval₂]
      norm_num
  · have hana := Work.C17d.DyChain_ana a b y1 hδ hy1d hode (k : ℕ) z
      ⟨hz, h02⟩
    have hmul : (mfin a b k).eval₂ (algebraMap ℚ ℂ) z * (Dc a b (k : ℕ)).eval₂ (algebraMap ℚ ℂ) z
        = (wX ^ 2 * Dc a b 3).eval₂ (algebraMap ℚ ℂ) z := by
      have h := congrArg (fun p : Polynomial ℚ => p.eval₂ (algebraMap ℚ ℂ) z) (mfin_mul_Dc a b k)
      simpa only [Polynomial.eval₂_mul] using h
    have hLHS : (wX ^ 2 * Dc a b 3).eval₂ (algebraMap ℚ ℂ) z * DyIter (k : ℕ) y1 z
        = (mfin a b k).eval₂ (algebraMap ℚ ℂ) z
          * ((Dc a b (k : ℕ)).eval₂ (algebraMap ℚ ℂ) z * DyIter (k : ℕ) y1 z) := by
      rw [← hmul]; ring
    have hRHS : (mfin a b k).eval₂ (algebraMap ℚ ℂ) z
          * ((Ac a b (k : ℕ)).eval₂ (algebraMap ℚ ℂ) z * y1 z
            + (Bc a b (k : ℕ)).eval₂ (algebraMap ℚ ℂ) z * deriv y1 z)
        = ((mfin a b k * Ac a b (k : ℕ)).eval₂ (algebraMap ℚ ℂ) z) * y1 z
          + ((mfin a b k * Bc a b (k : ℕ)).eval₂ (algebraMap ℚ ℂ) z) * deriv y1 z := by
      rw [Polynomial.eval₂_mul, Polynomial.eval₂_mul]; ring
    rw [hLHS, hana, hRHS]

theorem DyIter_eq_cls (a b : ℚ) (y1 : ℂ → ℂ) {δ : ℝ} (hδ : 0 < δ)
    (hy1d : DifferentiableOn ℂ y1 (Metric.ball ((xs a b : ℂ)) δ))
    (hode : ∀ z ∈ Metric.ball ((xs a b : ℂ)) δ,
      (P2x a b).eval₂ (algebraMap ℚ ℂ) z * deriv (deriv y1) z
        + (P1x a b).eval₂ (algebraMap ℚ ℂ) z * deriv y1 z
        + (P0x a b).eval₂ (algebraMap ℚ ℂ) z * y1 z = 0) :
    ∃ D : Polynomial ℚ, D ≠ 0 ∧
      ∀ k : Fin 4, ∃ A B : Polynomial ℚ,
        (algebraMap (Polynomial ℚ) (RatFunc ℚ) A
            = algebraMap (Polynomial ℚ) (RatFunc ℚ) D * (cls a b k).1 ∧
          algebraMap (Polynomial ℚ) (RatFunc ℚ) B
            = algebraMap (Polynomial ℚ) (RatFunc ℚ) D * (cls a b k).2) ∧
        ∀ z ∈ Metric.ball ((xs a b : ℂ)) δ,
          (D.eval₂ (algebraMap ℚ ℂ) z) * DyIter (k : ℕ) y1 z
            = (A.eval₂ (algebraMap ℚ ℂ) z) * y1 z
              + (B.eval₂ (algebraMap ℚ ℂ) z) * deriv y1 z := by
  refine ⟨wX ^ 2 * Dc a b 3,
    mul_ne_zero (pow_ne_zero 2 Work.C17d.wX_ne_zero) (Work.C17d.Dc_ne_zero a b 3), ?_⟩
  intro k
  refine ⟨mfin a b k * Ac a b (k : ℕ), mfin a b k * Bc a b (k : ℕ), ?_, ?_⟩
  · constructor
    · have hrat := (Work.C17d.DyChain_rat a b (k : ℕ)).1
      have hcls := Work.C17d.Cls_eq_pairStep a b k
      calc algebraMap (Polynomial ℚ) (RatFunc ℚ) (mfin a b k * Ac a b (k : ℕ))
          = algebraMap (Polynomial ℚ) (RatFunc ℚ) (mfin a b k)
            * algebraMap (Polynomial ℚ) (RatFunc ℚ) (Ac a b (k : ℕ)) := map_mul _ _ _
        _ = algebraMap (Polynomial ℚ) (RatFunc ℚ) (mfin a b k)
            * (algebraMap (Polynomial ℚ) (RatFunc ℚ) (Dc a b (k : ℕ))
                * ((Work.C17d.pairStep a b)^[(k : ℕ)] (1, 0)).1) := by rw [hrat]
        _ = (algebraMap (Polynomial ℚ) (RatFunc ℚ) (mfin a b k)
              * algebraMap (Polynomial ℚ) (RatFunc ℚ) (Dc a b (k : ℕ)))
            * ((Work.C17d.pairStep a b)^[(k : ℕ)] (1, 0)).1 := by rw [mul_assoc]
        _ = algebraMap (Polynomial ℚ) (RatFunc ℚ) (wX ^ 2 * Dc a b 3)
            * ((Work.C17d.pairStep a b)^[(k : ℕ)] (1, 0)).1 := by
          rw [← map_mul, mfin_mul_Dc]
        _ = algebraMap (Polynomial ℚ) (RatFunc ℚ) (wX ^ 2 * Dc a b 3) * (cls a b k).1 := by
          rw [hcls]
    · have hrat := (Work.C17d.DyChain_rat a b (k : ℕ)).2
      have hcls := Work.C17d.Cls_eq_pairStep a b k
      calc algebraMap (Polynomial ℚ) (RatFunc ℚ) (mfin a b k * Bc a b (k : ℕ))
          = algebraMap (Polynomial ℚ) (RatFunc ℚ) (mfin a b k)
            * algebraMap (Polynomial ℚ) (RatFunc ℚ) (Bc a b (k : ℕ)) := map_mul _ _ _
        _ = algebraMap (Polynomial ℚ) (RatFunc ℚ) (mfin a b k)
            * (algebraMap (Polynomial ℚ) (RatFunc ℚ) (Dc a b (k : ℕ))
                * ((Work.C17d.pairStep a b)^[(k : ℕ)] (1, 0)).2) := by rw [hrat]
        _ = (algebraMap (Polynomial ℚ) (RatFunc ℚ) (mfin a b k)
              * algebraMap (Polynomial ℚ) (RatFunc ℚ) (Dc a b (k : ℕ)))
            * ((Work.C17d.pairStep a b)^[(k : ℕ)] (1, 0)).2 := by rw [mul_assoc]
        _ = algebraMap (Polynomial ℚ) (RatFunc ℚ) (wX ^ 2 * Dc a b 3)
            * ((Work.C17d.pairStep a b)^[(k : ℕ)] (1, 0)).2 := by
          rw [← map_mul, mfin_mul_Dc]
        _ = algebraMap (Polynomial ℚ) (RatFunc ℚ) (wX ^ 2 * Dc a b 3) * (cls a b k).2 := by
          rw [hcls]
  · exact DyIter_mfin_eq a b y1 hδ hy1d hode k

end

end Work.C17
