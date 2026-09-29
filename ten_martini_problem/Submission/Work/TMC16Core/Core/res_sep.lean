import Mathlib
import Submission.Work.TMC16Core.Core.blk_sep_base
import Submission.Work.TMC16Core.Core.irrat_blk_shift

namespace Work.TMC16Core.Core

/-- `fracDist` is even. -/
private lemma res_sep_fracDist_neg (x : ℝ) :
    Work.TMC16Core.fracDist (-x) = Work.TMC16Core.fracDist x := by
  rw [fracDist_eq_nn, fracDist_eq_nn]
  exact nn_neg' x

/-- Reduction of a signed multiple to the corresponding natural multiple. -/
private lemma res_sep_fracDist_int (α : ℝ) (m : ℤ) :
    Work.TMC16Core.fracDist ((m : ℝ) * α)
      = Work.TMC16Core.fracDist (((m.natAbs : ℕ) : ℝ) * α) := by
  rcases Int.natAbs_eq m with h | h
  · have h1 : (m : ℝ) = ((m.natAbs : ℕ) : ℝ) := by
      have h3 := congrArg (fun z : ℤ => (z : ℝ)) h
      simpa only [Int.cast_natCast] using h3
    rw [h1]
  · have h1 : (m : ℝ) = -(((m.natAbs : ℕ) : ℝ)) := by
      have h3 := congrArg (fun z : ℤ => (z : ℝ)) h
      simpa only [Int.cast_neg, Int.cast_natCast] using h3
    rw [h1, neg_mul, res_sep_fracDist_neg]

theorem res_sep {α : ℝ} {q : ℕ → ℕ} {Δ : ℕ → ℝ} {n ℓ : ℕ}
    (hqpos : ∀ m, 0 < q m) (hmono : StrictMono q)
    (hΔpos : ∀ m, 0 < Δ m)
    (hΔeq : ∀ m, Δ m = Work.TMC16Core.fracDist ((q m : ℝ) * α))
    (hΔup : ∀ m, Δ m < 1 / ((q (m + 1) : ℝ)))
    (hΔlo : ∀ m, 1 / (((q (m + 1) : ℝ)) + (q m : ℝ)) < Δ m)
    (hbest : ∀ m k : ℕ, q m ≤ k → k < q (m + 1) → Δ m ≤ Work.TMC16Core.fracDist ((k : ℝ) * α))
    (hℓ : 1 ≤ ℓ) (hn : 1 ≤ n)
    (hℓb : 10 * (ℓ : ℤ) * (q n : ℤ) ≤ (q (n + 1) : ℤ))
    {m : ℤ} (hm1 : 1 ≤ |m|) (hm2 : |m| ≤ 2 * ((ℓ : ℤ) + 1) * (q n : ℤ)) :
    1 / (2 * (q (n + 1) : ℝ)) ≤ Work.TMC16Core.fracDist ((m : ℝ) * α) := by
  -- The base-scale separation of the first block.
  have hbase : ∀ d : ℕ, 1 ≤ d → d < q 0 →
      1 / (2 * (q 0 : ℝ)) ≤ Work.TMC16Core.fracDist ((d : ℝ) * α) :=
    blk_sep_base hqpos hmono hΔpos hΔeq hΔup hΔlo hbest
  -- The natural size of `m`.
  have hdt : ((m.natAbs : ℕ) : ℤ) = |m| := Int.natCast_natAbs m
  have hd1 : 1 ≤ m.natAbs := Int.ofNat_le.mp (by rw [hdt]; exact hm1)
  -- `|m| < q (n+1)` because `2 (ℓ+1) q n < 10 ℓ q n ≤ q (n+1)`.
  have hdn : m.natAbs < q (n + 1) := by
    have hℓ1 : (1 : ℤ) ≤ (ℓ : ℤ) := by exact_mod_cast hℓ
    have hqn1 : (1 : ℤ) ≤ (q n : ℤ) := by exact_mod_cast hqpos n
    have hstep : 2 * ((ℓ : ℤ) + 1) * (q n : ℤ) < 10 * (ℓ : ℤ) * (q n : ℤ) := by
      have key : (0 : ℤ) < (q n : ℤ) * (8 * (ℓ : ℤ) - 2) := by
        apply mul_pos
        · linarith
        · linarith
      nlinarith [key]
    have hlt : ((m.natAbs : ℕ) : ℤ) < (q (n + 1) : ℤ) := by
      rw [hdt]
      calc |m| ≤ 2 * ((ℓ : ℤ) + 1) * (q n : ℤ) := hm2
        _ < 10 * (ℓ : ℤ) * (q n : ℤ) := hstep
        _ ≤ (q (n + 1) : ℤ) := hℓb
    exact Int.ofNat_lt.mp hlt
  have hscale := sep_scale hqpos hmono hΔpos hΔeq hΔlo hbest hbase hd1 hdn
  rw [← res_sep_fracDist_int α m] at hscale
  exact hscale

end Work.TMC16Core.Core
