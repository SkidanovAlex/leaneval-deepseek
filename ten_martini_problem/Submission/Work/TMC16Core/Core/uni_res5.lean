import Mathlib
import Submission.Work.TMC16Core.Core.windows
import Submission.Work.TMC16Core.Core.irrat_blk_shift
import Submission.Work.TMC16Core.Core.coll_res
import Submission.Work.TMC16Core.Core.uni_res5_aux
import Submission.Work.TMC16Core.Core.res_card
import Submission.Work.TMC16Core.Core.res_bij
import Submission.Work.TMC16Core.Core.res_sep
import Submission.Work.TMC16Core.Core.res_arith

namespace Work.TMC16Core.Core

open Work.TMC16Core

noncomputable section

set_option maxHeartbeats 1600000

/-- **Strictness of `10 ℓ q n < q (n+1)`.**  The shifted block estimate `irrat_blk_shift` wants
the strict form, while the target hypotheses give only `10 ℓ q n ≤ q (n+1)`.  If equality held,
then `q (n+1) α = 10 ℓ (q n α)` and the fractional part of the latter is `10 ℓ Δ n` (there is no
wrap-around, because `10 ℓ Δ n < 1/q n ≤ 1/2`), i.e. `Δ (n+1) = 10 ℓ Δ n`.  Combining
`10 ℓ / (q (n+1) + q n) < Δ (n+1) < 1/q (n+2)` with `q (n+1) = 10 ℓ q n` then gives
`q (n+2) < (1 + 1/(10ℓ)) q n ≤ 11 q n/10 < 10 ℓ q n = q (n+1)`, contradicting strict
monotonicity of `q`. -/
theorem res_strict_hℓb {α : ℝ} {q : ℕ → ℕ} {Δ : ℕ → ℝ} {n ℓ : ℕ}
    (hqpos : ∀ m, 0 < q m) (hmono : StrictMono q)
    (hΔpos : ∀ m, 0 < Δ m)
    (hΔeq : ∀ m, Δ m = fracDist ((q m : ℝ) * α))
    (hΔup : ∀ m, Δ m < 1 / ((q (m + 1) : ℝ)))
    (hΔlo : ∀ m, 1 / (((q (m + 1) : ℝ)) + (q m : ℝ)) < Δ m)
    (hbest : ∀ m k : ℕ, q m ≤ k → k < q (m + 1) → Δ m ≤ fracDist ((k : ℝ) * α))
    (hn : 1 ≤ n) (hℓ : 1 ≤ ℓ)
    (hℓb : 10 * (ℓ : ℤ) * (q n : ℤ) ≤ (q (n + 1) : ℤ)) :
    10 * (ℓ : ℝ) * (q n : ℝ) < (q (n + 1) : ℝ) := by
  have hge : 10 * (ℓ : ℝ) * (q n : ℝ) ≤ (q (n + 1) : ℝ) := by exact_mod_cast hℓb
  by_contra hcon
  push_neg at hcon
  have heq : (q (n + 1) : ℝ) = 10 * (ℓ : ℝ) * (q n : ℝ) := le_antisymm hcon hge
  have hqn2 : 2 ≤ q n := by
    have h0 : 0 < q 0 := hqpos 0
    have hlt : q 0 < q 1 := hmono (by norm_num)
    have hle : q 1 ≤ q n := hmono.monotone hn
    omega
  have hℓR : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ
  have hqnR : (0 : ℝ) < (q n : ℝ) := by have := hqpos n; exact_mod_cast this
  set δ : ℝ := (q n : ℝ) * α - ((round ((q n : ℝ) * α)) : ℝ) with hδ
  have hδabs : |δ| = Δ n := by
    rw [hΔeq n, hδ]
    simp only [Work.TMC16Core.fracDist]
  have hΔn_lt : Δ n < 1 / (10 * (ℓ : ℝ) * (q n : ℝ)) := by
    have h := hΔup n
    rwa [heq] at h
  have h10 : 10 * (ℓ : ℝ) * Δ n < 1 / (q n : ℝ) := by
    have h1 : 10 * (ℓ : ℝ) * Δ n < 10 * (ℓ : ℝ) * (1 / (10 * (ℓ : ℝ) * (q n : ℝ))) :=
      mul_lt_mul_of_pos_left hΔn_lt (by positivity)
    have h2 : 10 * (ℓ : ℝ) * (1 / (10 * (ℓ : ℝ) * (q n : ℝ))) = 1 / (q n : ℝ) := by
      field_simp
    linarith [h1, h2]
  have h10half : |10 * (ℓ : ℝ) * δ| < 1 / 2 := by
    rw [show 10 * (ℓ : ℝ) * δ = (10 * (ℓ : ℝ)) * δ by ring, abs_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 10 * (ℓ : ℝ)), hδabs]
    have hle : 1 / (q n : ℝ) ≤ 1 / 2 := by
      apply one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2)
      exact_mod_cast hqn2
    linarith
  have hfrac : Δ (n + 1) = 10 * (ℓ : ℝ) * Δ n := by
    rw [hΔeq (n + 1)]
    have hcast : (q (n + 1) : ℝ) * α = 10 * (ℓ : ℝ) * ((q n : ℝ) * α) := by
      rw [heq]; ring
    rw [hcast]
    have hsplit : 10 * (ℓ : ℝ) * ((q n : ℝ) * α)
        = 10 * (ℓ : ℝ) * δ + (((10 : ℤ) * (ℓ : ℤ) * round ((q n : ℝ) * α) : ℤ) : ℝ) := by
      rw [hδ]; push_cast; ring
    rw [hsplit, fracDist, round_add_intCast]
    have hround0 : round (10 * (ℓ : ℝ) * δ) = 0 := by
      rw [round_eq_iff, Set.mem_Ico]
      exact ⟨by linarith [neg_abs_le (10 * (ℓ : ℝ) * δ)],
        by linarith [(abs_lt.mp h10half).2]⟩
    rw [hround0]
    rw [show 10 * (ℓ : ℝ) * δ + (((10 : ℤ) * (ℓ : ℤ) * round ((q n : ℝ) * α) : ℤ) : ℝ)
        - (((0 : ℤ) + 10 * (ℓ : ℤ) * round ((q n : ℝ) * α) : ℤ) : ℝ) = 10 * (ℓ : ℝ) * δ by
      push_cast; ring]
    rw [show 10 * (ℓ : ℝ) * δ = (10 * (ℓ : ℝ)) * δ by ring, abs_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 10 * (ℓ : ℝ)), hδabs]
  have h2 := hΔup (n + 1)
  rw [hfrac] at h2
  have h1 : 10 * (ℓ : ℝ) * (1 / (((q (n + 1) : ℝ)) + (q n : ℝ))) < 10 * (ℓ : ℝ) * Δ n :=
    mul_lt_mul_of_pos_left (hΔlo n) (by positivity)
  have hone : 10 * (ℓ : ℝ) / (((q (n + 1) : ℝ)) + (q n : ℝ)) < 1 / (q (n + 2) : ℝ) := by
    rw [show 10 * (ℓ : ℝ) * (1 / (((q (n + 1) : ℝ)) + (q n : ℝ)))
        = 10 * (ℓ : ℝ) / (((q (n + 1) : ℝ)) + (q n : ℝ)) by ring] at h1
    linarith
  have hd1 : (0 : ℝ) < ((q (n + 1) : ℝ)) + (q n : ℝ) := by
    have h := hqpos (n + 1); have h' := hqpos n
    have : (0 : ℝ) < (q (n + 1) : ℝ) := by exact_mod_cast h
    have : (0 : ℝ) < (q n : ℝ) := by exact_mod_cast h'
    linarith
  have hd2 : (0 : ℝ) < (q (n + 2) : ℝ) := by
    have h := hqpos (n + 2); exact_mod_cast h
  rw [div_lt_div_iff₀ hd1 hd2] at hone
  rw [heq] at hone
  -- hone : 10 ℓ * q(n+2) < 1 * ((10 ℓ q n) + q n)
  have hmono2 : (q (n + 1) : ℝ) < (q (n + 2) : ℝ) := by
    have h := hmono (Nat.lt_succ_self (n + 1))
    exact_mod_cast h
  have hℓ1 : (1 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hℓ
  have hbig : 10 * (ℓ : ℝ) * (q n : ℝ) < (q (n + 2) : ℝ) := by
    rw [← heq]; exact hmono2
  have hlt2 : (q (n + 2) : ℝ) ≤ (11 / 10) * (q n : ℝ) := by
    have hpos10 : (0 : ℝ) < 10 * (ℓ : ℝ) := by linarith
    have h9 : (q (n + 2) : ℝ) ≤ ((q n : ℝ) * (10 * (ℓ : ℝ) + 1)) / (10 * (ℓ : ℝ)) := by
      rw [le_div_iff₀ hpos10]; linarith [hone]
    have h10' : ((q n : ℝ) * (10 * (ℓ : ℝ) + 1)) / (10 * (ℓ : ℝ)) ≤ (11 / 10) * (q n : ℝ) := by
      rw [div_le_iff₀ hpos10]
      have hh : (q n : ℝ) * 1 ≤ (q n : ℝ) * (ℓ : ℝ) :=
        mul_le_mul_of_nonneg_left hℓ1 (le_of_lt hqnR)
      nlinarith [hh, hpos10]
    linarith
  have h10ge : (10 : ℝ) ≤ 10 * (ℓ : ℝ) := by linarith
  have hprod : 10 * (q n : ℝ) ≤ 10 * (ℓ : ℝ) * (q n : ℝ) := by
    have hh := mul_le_mul_of_nonneg_right h10ge (le_of_lt hqnR)
    linarith [hh]
  nlinarith [hlt2, hbig, hprod, hqnR]

/-- The shift is bounded by `ℓ - 1` (in absolute value). -/
lemma resLsh_abs {h ℓ : ℕ} (hℓ : 1 ≤ ℓ) (k : ℤ) : |resLsh h ℓ k| ≤ (ℓ : ℤ) - 1 := by
  have h1 : (0 : ℤ) ≤ (ℓ : ℤ) - 1 := by omega
  by_cases hk : k < (h : ℤ)
  · rw [resLsh, if_pos hk, abs_zero]; exact h1
  · rw [resLsh, if_neg hk, abs_of_nonneg h1]

/-- **The shifted block estimate in the form used for the resonant windows.**  For a block
`Icc p (p + q n - 1)` of `q n` consecutive indices, whose images `resSite k` carry the shift
`resLsh h ℓ k ∈ {0, ℓ-1}`, the sum of `log |sin (π (ξ + resSite k · α))|` with the minimal term
removed is `-(q n - 1) log 2` up to `8 log (q n)`.

This is `irrat_blk_shift` with the strict inequality `10 ℓ q n < q (n+1)` supplied by
`res_strict_hℓb`, and with its error term `log (q n) + 32 (Δ n + ℓ Δ n) q n log (q n)` bounded by
`8 log (q n)` (using `ℓ Δ n < 1/(10 q n)` and `Δ n < 1/(10 q n)`). -/
theorem res_blk {α : ℝ} {q : ℕ → ℕ} {Δ : ℕ → ℝ} {n h ℓ : ℕ} {p : ℤ} {ξ : ℝ} {k₀ : ℤ}
    (hqpos : ∀ m, 0 < q m) (hmono : StrictMono q)
    (hΔpos : ∀ m, 0 < Δ m)
    (hΔeq : ∀ m, Δ m = fracDist ((q m : ℝ) * α))
    (hΔup : ∀ m, Δ m < 1 / ((q (m + 1) : ℝ)))
    (hΔlo : ∀ m, 1 / (((q (m + 1) : ℝ)) + (q m : ℝ)) < Δ m)
    (hbest : ∀ m k : ℕ, q m ≤ k → k < q (m + 1) → Δ m ≤ fracDist ((k : ℝ) * α))
    (hn : 1 ≤ n) (hℓ : 1 ≤ ℓ)
    (hℓb : 10 * (ℓ : ℤ) * (q n : ℤ) ≤ (q (n + 1) : ℤ))
    (hk₀ : k₀ ∈ Finset.Icc p (p + (q n : ℤ) - 1))
    (hmin : ∀ k ∈ Finset.Icc p (p + (q n : ℤ) - 1),
      |Real.sin (Real.pi * (ξ + ((resSite (q n) h ℓ k : ℤ) : ℝ) * α))| ≥
        |Real.sin (Real.pi * (ξ + ((resSite (q n) h ℓ k₀ : ℤ) : ℝ) * α))|) :
    |∑ k ∈ (Finset.Icc p (p + (q n : ℤ) - 1)).erase k₀,
        Real.log |Real.sin (Real.pi * (ξ + ((resSite (q n) h ℓ k : ℤ) : ℝ) * α))|
      + ((q n : ℝ) - 1) * Real.log 2| ≤ 8 * Real.log (q n : ℝ) := by
  have hstrict := res_strict_hℓb hqpos hmono hΔpos hΔeq hΔup hΔlo hbest hn hℓ hℓb
  have hLsh : ∀ k : ℤ, |resLsh h ℓ k| ≤ (ℓ : ℤ) - 1 := fun k => resLsh_abs hℓ k
  have h := irrat_blk_shift (n := n) (r := n) hqpos hmono hΔpos hΔeq hΔup hΔlo hbest
      le_rfl hℓ hstrict (Lsh := resLsh h ℓ) hLsh hk₀ (by
        intro k hk
        simpa [resSite] using hmin k hk)
  simp only [resSite] at h ⊢
  have hqposn : (0 : ℝ) < (q n : ℝ) := by have := hqpos n; exact_mod_cast this
  have hlogq : (0 : ℝ) ≤ Real.log (q n : ℝ) := Real.log_nonneg (by exact_mod_cast hqpos n)
  have h10q : 10 * (q n : ℝ) ≤ (q (n + 1) : ℝ) := by
    have h1 : (1 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hℓ
    have h2 : 10 * (1 : ℝ) * (q n : ℝ) ≤ 10 * (ℓ : ℝ) * (q n : ℝ) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      linarith
    have h3 : 10 * (ℓ : ℝ) * (q n : ℝ) ≤ (q (n + 1) : ℝ) := by exact_mod_cast hℓb
    linarith [h2, h3]
  have hq1 : (0 : ℝ) < (q (n + 1) : ℝ) := by have := hqpos (n + 1); exact_mod_cast this
  have hA1 : Δ n * (q n : ℝ) < 1 / 10 := by
    have h1 : Δ n * (q n : ℝ) < (1 / (q (n + 1) : ℝ)) * (q n : ℝ) :=
      mul_lt_mul_of_pos_right (hΔup n) hqposn
    have h2 : (1 / (q (n + 1) : ℝ)) * (q n : ℝ) = (q n : ℝ) / (q (n + 1) : ℝ) := by ring
    rw [h2] at h1
    have h3 : (q n : ℝ) / (q (n + 1) : ℝ) ≤ 1 / 10 := by
      rw [div_le_iff₀ hq1]; nlinarith [h10q]
    linarith
  have hA2 : (ℓ : ℝ) * Δ n * (q n : ℝ) < 1 / 10 := by
    have h1 : Δ n * (q n : ℝ) < (1 / (q (n + 1) : ℝ)) * (q n : ℝ) :=
      mul_lt_mul_of_pos_right (hΔup n) hqposn
    have h2 : (1 / (q (n + 1) : ℝ)) * (q n : ℝ) = (q n : ℝ) / (q (n + 1) : ℝ) := by ring
    rw [h2] at h1
    have h3 : (q n : ℝ) / (q (n + 1) : ℝ) < 1 / (10 * (ℓ : ℝ)) := by
      rw [div_lt_div_iff₀ hq1 (by positivity : (0 : ℝ) < 10 * (ℓ : ℝ))]
      nlinarith [hstrict]
    have h4 : Δ n * (q n : ℝ) < 1 / (10 * (ℓ : ℝ)) := lt_trans h1 h3
    have h5 : (ℓ : ℝ) * (Δ n * (q n : ℝ)) < (ℓ : ℝ) * (1 / (10 * (ℓ : ℝ))) :=
      mul_lt_mul_of_pos_left h4 (by exact_mod_cast hℓ : (0 : ℝ) < (ℓ : ℝ))
    have h6 : (ℓ : ℝ) * (1 / (10 * (ℓ : ℝ))) = 1 / 10 := by field_simp
    nlinarith [h5, h6.le, h6.ge]
  have hA : (Δ n + (ℓ : ℝ) * Δ n) * (q n : ℝ) < 1 / 5 := by nlinarith [hA1, hA2]
  have h32 : 32 * ((Δ n + (ℓ : ℝ) * Δ n) * (q n : ℝ)) ≤ 7 := by linarith
  have h1 : 32 * ((Δ n + (ℓ : ℝ) * Δ n) * (q n : ℝ) * Real.log (q n : ℝ))
      ≤ 7 * Real.log (q n : ℝ) := by
    rw [show 32 * ((Δ n + (ℓ : ℝ) * Δ n) * (q n : ℝ) * Real.log (q n : ℝ))
        = (32 * ((Δ n + (ℓ : ℝ) * Δ n) * (q n : ℝ))) * Real.log (q n : ℝ) by ring]
    exact mul_le_mul_of_nonneg_right h32 hlogq
  linarith [h, h1]

/-- `log |sin x| ≤ 0` (with Lean's convention `log 0 = 0`). -/
lemma log_abs_sin_nonpos (x : ℝ) : Real.log |Real.sin x| ≤ 0 := by
  rcases eq_or_ne (Real.sin x) 0 with h | h
  · rw [h, abs_zero, Real.log_zero]
  · have h1 : 0 < |Real.sin x| := abs_pos.mpr h
    have h2 : |Real.sin x| ≤ 1 := by
      rw [abs_le]
      exact ⟨Real.neg_one_le_sin x, Real.sin_le_one x⟩
    exact Real.log_nonpos (le_of_lt h1) h2

/-- a block of `q n` consecutive integers has `q n` elements. -/
lemma card_block (p : ℤ) (qn : ℕ) : (Finset.Icc p (p + (qn : ℤ) - 1)).card = qn := by
  rw [Int.card_Icc]
  have h : p + (qn : ℤ) - 1 + 1 - p = (qn : ℤ) := by ring
  rw [h, Int.toNat_natCast]

/-- Upper bound for a sum over a whole block, from the block estimate with its minimum removed
(the removed minimum is non-positive). -/
lemma blk_sum_le {f : ℤ → ℝ} {B : Finset ℤ} {k₀ : ℤ} {A E : ℝ}
    (hk₀ : k₀ ∈ B) (h0 : f k₀ ≤ 0)
    (hblk : ∑ k ∈ B.erase k₀, f k ≤ A + E) :
    ∑ k ∈ B, f k ≤ A + E := by
  have h := Finset.sum_erase_add B f hk₀
  linarith

/-- Upper bound for the sum over a block with one index `k_j` removed, when the removed minimum
is dominated by `f k_j`. -/
lemma blk_sum_le_erase {f : ℤ → ℝ} {B : Finset ℤ} {k₀ k_j : ℤ} {A E : ℝ}
    (hk₀ : k₀ ∈ B) (hkj : k_j ∈ B) (hmin : f k₀ ≤ f k_j)
    (hblk : ∑ k ∈ B.erase k₀, f k ≤ A + E) :
    ∑ k ∈ B.erase k_j, f k ≤ A + E := by
  rcases eq_or_ne k_j k₀ with h | h
  · subst h; exact hblk
  · have h1 := Finset.sum_erase_add B f hk₀
    have h2 := Finset.sum_erase_add B f hkj
    have h3 : ∑ k ∈ B.erase k_j, f k = ∑ k ∈ B.erase k₀, f k + f k₀ - f k_j := by linarith
    rw [h3]; linarith

/-- Lower bound for a sum over a whole block, restoring the removed minimum at a lower bound
`B0` for its value. -/
lemma blk_sum_ge {f : ℤ → ℝ} {B : Finset ℤ} {k₀ : ℤ} {A E B0 : ℝ}
    (hk₀ : k₀ ∈ B) (hb : B0 ≤ f k₀)
    (hblk : A - E ≤ ∑ k ∈ B.erase k₀, f k) :
    A - E + B0 ≤ ∑ k ∈ B, f k := by
  have h := Finset.sum_erase_add B f hk₀
  linarith

/-- Lower bound for the sum over a block with one index `k_j` removed, restoring the removed
minimum. -/
lemma blk_sum_ge_erase {f : ℤ → ℝ} {B : Finset ℤ} {k₀ k_j : ℤ} {A E B0 : ℝ}
    (hk₀ : k₀ ∈ B) (hkj : k_j ∈ B) (h0 : f k_j ≤ 0) (hb : B0 ≤ f k₀)
    (hblk : A - E ≤ ∑ k ∈ B.erase k₀, f k) :
    A - E + B0 ≤ ∑ k ∈ B.erase k_j, f k := by
  rcases eq_or_ne k_j k₀ with h | h
  · subst h
    have h1 := Finset.sum_erase_add B f hk₀
    linarith
  · have h1 := Finset.sum_erase_add B f hk₀
    have h2 := Finset.sum_erase_add B f hkj
    have h3 : ∑ k ∈ B.erase k_j, f k = ∑ k ∈ B.erase k₀, f k + f k₀ - f k_j := by linarith
    rw [h3]; linarith

/-- `(card (Icc p (p + q n - 1)) : ℝ) = q n`. -/
lemma card_block_R (p : ℤ) (qn : ℕ) :
    ((Finset.Icc p (p + (qn : ℤ) - 1)).card : ℝ) = (qn : ℝ) := by
  rw [card_block]

/-- Upper bound for the block sum over a whole `q n`-block. -/
lemma res_blk_le {α : ℝ} {q : ℕ → ℕ} {Δ : ℕ → ℝ} {n h ℓ : ℕ} {ξ : ℝ} {B : Finset ℤ} {p : ℤ}
    (hB : B = Finset.Icc p (p + (q n : ℤ) - 1))
    (hqpos : ∀ m, 0 < q m) (hmono : StrictMono q) (hΔpos : ∀ m, 0 < Δ m)
    (hΔeq : ∀ m, Δ m = fracDist ((q m : ℝ) * α))
    (hΔup : ∀ m, Δ m < 1 / ((q (m + 1) : ℝ)))
    (hΔlo : ∀ m, 1 / (((q (m + 1) : ℝ)) + (q m : ℝ)) < Δ m)
    (hbest : ∀ m k : ℕ, q m ≤ k → k < q (m + 1) → Δ m ≤ fracDist ((k : ℝ) * α))
    (hn : 1 ≤ n) (hℓ : 1 ≤ ℓ)
    (hℓb : 10 * (ℓ : ℤ) * (q n : ℤ) ≤ (q (n + 1) : ℤ)) :
    ∑ k ∈ B, Real.log |Real.sin (Real.pi * (ξ + ((resSite (q n) h ℓ k : ℤ) : ℝ) * α))|
      ≤ -((q n : ℝ) - 1) * Real.log 2 + 8 * Real.log (q n : ℝ) := by
  subst hB
  have hne : (Finset.Icc p (p + (q n : ℤ) - 1)).Nonempty :=
    ⟨p, by rw [Finset.mem_Icc]; have := hqpos n; omega⟩
  obtain ⟨k₀, hk₀, hk₀min⟩ := Finset.exists_min_image (Finset.Icc p (p + (q n : ℤ) - 1))
      (fun k => |Real.sin (Real.pi * (ξ + ((resSite (q n) h ℓ k : ℤ) : ℝ) * α))|) hne
  have hblk := res_blk hqpos hmono hΔpos hΔeq hΔup hΔlo hbest hn hℓ hℓb hk₀
      (fun k hk => hk₀min k hk)
  refine blk_sum_le (f := fun k => Real.log |Real.sin (Real.pi * (ξ + ((resSite (q n) h ℓ k : ℤ) : ℝ) * α))|)
    hk₀ (log_abs_sin_nonpos _) ?_
  have h := (abs_le.mp hblk).2
  linarith

/-- Upper bound for the block sum with one index `k_j` removed (the block contains `k_j`). -/
lemma res_blk_le_erase {α : ℝ} {q : ℕ → ℕ} {Δ : ℕ → ℝ} {n h ℓ : ℕ} {ξ : ℝ}
    {B : Finset ℤ} {p : ℤ} {k_j : ℤ}
    (hB : B = Finset.Icc p (p + (q n : ℤ) - 1))
    (hqpos : ∀ m, 0 < q m) (hmono : StrictMono q) (hΔpos : ∀ m, 0 < Δ m)
    (hΔeq : ∀ m, Δ m = fracDist ((q m : ℝ) * α))
    (hΔup : ∀ m, Δ m < 1 / ((q (m + 1) : ℝ)))
    (hΔlo : ∀ m, 1 / (((q (m + 1) : ℝ)) + (q m : ℝ)) < Δ m)
    (hbest : ∀ m k : ℕ, q m ≤ k → k < q (m + 1) → Δ m ≤ fracDist ((k : ℝ) * α))
    (hn : 1 ≤ n) (hℓ : 1 ≤ ℓ)
    (hℓb : 10 * (ℓ : ℤ) * (q n : ℤ) ≤ (q (n + 1) : ℤ))
    (hk_j : k_j ∈ B)
    (hpos : ∀ k ∈ B, k ≠ k_j →
      Real.sin (Real.pi * (ξ + ((resSite (q n) h ℓ k : ℤ) : ℝ) * α)) ≠ 0) :
    ∑ k ∈ B.erase k_j,
        Real.log |Real.sin (Real.pi * (ξ + ((resSite (q n) h ℓ k : ℤ) : ℝ) * α))|
      ≤ -((q n : ℝ) - 1) * Real.log 2 + 8 * Real.log (q n : ℝ) := by
  subst hB
  have hne : (Finset.Icc p (p + (q n : ℤ) - 1)).Nonempty :=
    ⟨p, by rw [Finset.mem_Icc]; have := hqpos n; omega⟩
  obtain ⟨k₀, hk₀, hk₀min⟩ := Finset.exists_min_image (Finset.Icc p (p + (q n : ℤ) - 1))
      (fun k => |Real.sin (Real.pi * (ξ + ((resSite (q n) h ℓ k : ℤ) : ℝ) * α))|) hne
  have hblk := res_blk hqpos hmono hΔpos hΔeq hΔup hΔlo hbest hn hℓ hℓb hk₀
      (fun k hk => hk₀min k hk)
  have hfkj : Real.log |Real.sin (Real.pi * (ξ + ((resSite (q n) h ℓ k₀ : ℤ) : ℝ) * α))|
      ≤ Real.log |Real.sin (Real.pi * (ξ + ((resSite (q n) h ℓ k_j : ℤ) : ℝ) * α))| := by
    rcases eq_or_ne k₀ k_j with hne | hne
    · rw [hne]
    · rcases eq_or_ne (Real.log |Real.sin (Real.pi * (ξ + ((resSite (q n) h ℓ k_j : ℤ) : ℝ) * α))|) 0 with h0 | h0
      · rw [h0]
        exact log_abs_sin_nonpos _
      · have hspos : 0 < |Real.sin (Real.pi * (ξ + ((resSite (q n) h ℓ k₀ : ℤ) : ℝ) * α))| := by
          rw [abs_pos]
          exact hpos k₀ hk₀ hne
        exact Real.log_le_log hspos (hk₀min k_j hk_j)
  refine blk_sum_le_erase (f := fun k => Real.log |Real.sin (Real.pi * (ξ + ((resSite (q n) h ℓ k : ℤ) : ℝ) * α))|)
    hk₀ hk_j hfkj ?_
  have h := (abs_le.mp hblk).2
  linarith

/-- Lower bound for the block sum over the whole `q n`-block, given a lower bound `B0` for every
term (in particular for the removed minimum). -/
lemma res_blk_ge {α : ℝ} {q : ℕ → ℕ} {Δ : ℕ → ℝ} {n h ℓ : ℕ} {ξ : ℝ}
    {B : Finset ℤ} {p : ℤ} {B0 : ℝ}
    (hB : B = Finset.Icc p (p + (q n : ℤ) - 1))
    (hqpos : ∀ m, 0 < q m) (hmono : StrictMono q) (hΔpos : ∀ m, 0 < Δ m)
    (hΔeq : ∀ m, Δ m = fracDist ((q m : ℝ) * α))
    (hΔup : ∀ m, Δ m < 1 / ((q (m + 1) : ℝ)))
    (hΔlo : ∀ m, 1 / (((q (m + 1) : ℝ)) + (q m : ℝ)) < Δ m)
    (hbest : ∀ m k : ℕ, q m ≤ k → k < q (m + 1) → Δ m ≤ fracDist ((k : ℝ) * α))
    (hn : 1 ≤ n) (hℓ : 1 ≤ ℓ)
    (hℓb : 10 * (ℓ : ℤ) * (q n : ℤ) ≤ (q (n + 1) : ℤ))
    (hlb : ∀ k ∈ B,
      B0 ≤ Real.log |Real.sin (Real.pi * (ξ + ((resSite (q n) h ℓ k : ℤ) : ℝ) * α))|) :
    -((q n : ℝ) - 1) * Real.log 2 - 8 * Real.log (q n : ℝ) + B0
      ≤ ∑ k ∈ B,
          Real.log |Real.sin (Real.pi * (ξ + ((resSite (q n) h ℓ k : ℤ) : ℝ) * α))| := by
  subst hB
  have hne : (Finset.Icc p (p + (q n : ℤ) - 1)).Nonempty :=
    ⟨p, by rw [Finset.mem_Icc]; have := hqpos n; omega⟩
  obtain ⟨k₀, hk₀, hk₀min⟩ := Finset.exists_min_image (Finset.Icc p (p + (q n : ℤ) - 1))
      (fun k => |Real.sin (Real.pi * (ξ + ((resSite (q n) h ℓ k : ℤ) : ℝ) * α))|) hne
  have hblk := res_blk hqpos hmono hΔpos hΔeq hΔup hΔlo hbest hn hℓ hℓb hk₀
      (fun k hk => hk₀min k hk)
  refine blk_sum_ge (f := fun k => Real.log |Real.sin (Real.pi * (ξ + ((resSite (q n) h ℓ k : ℤ) : ℝ) * α))|)
    hk₀ (hlb k₀ hk₀) ?_
  have h := (abs_le.mp hblk).1
  linarith

/-- Lower bound for the block sum with one index `k_j` removed, in the case that the `sin`-factor
at `k_j` vanishes (so that the removed minimum can be chosen at `k_j`, at no cost). -/
lemma res_blk_ge_erase_kj {α : ℝ} {q : ℕ → ℕ} {Δ : ℕ → ℝ} {n h ℓ : ℕ} {ξ : ℝ}
    {B : Finset ℤ} {p : ℤ} {k_j : ℤ}
    (hB : B = Finset.Icc p (p + (q n : ℤ) - 1))
    (hqpos : ∀ m, 0 < q m) (hmono : StrictMono q) (hΔpos : ∀ m, 0 < Δ m)
    (hΔeq : ∀ m, Δ m = fracDist ((q m : ℝ) * α))
    (hΔup : ∀ m, Δ m < 1 / ((q (m + 1) : ℝ)))
    (hΔlo : ∀ m, 1 / (((q (m + 1) : ℝ)) + (q m : ℝ)) < Δ m)
    (hbest : ∀ m k : ℕ, q m ≤ k → k < q (m + 1) → Δ m ≤ fracDist ((k : ℝ) * α))
    (hn : 1 ≤ n) (hℓ : 1 ≤ ℓ)
    (hℓb : 10 * (ℓ : ℤ) * (q n : ℤ) ≤ (q (n + 1) : ℤ))
    (hk_j : k_j ∈ B)
    (hsin0 : Real.sin (Real.pi * (ξ + ((resSite (q n) h ℓ k_j : ℤ) : ℝ) * α)) = 0) :
    -((q n : ℝ) - 1) * Real.log 2 - 8 * Real.log (q n : ℝ)
      ≤ ∑ k ∈ B.erase k_j,
          Real.log |Real.sin (Real.pi * (ξ + ((resSite (q n) h ℓ k : ℤ) : ℝ) * α))| := by
  subst hB
  have hblk := res_blk hqpos hmono hΔpos hΔeq hΔup hΔlo hbest hn hℓ hℓb hk_j (by
    intro k hk
    rw [hsin0, abs_zero]
    exact abs_nonneg _)
  have h := (abs_le.mp hblk).1
  linarith

/-- `W = J1resG h ∪ J2resG q n h ℓ` is the image of the block `resK q n h` under `resSite`. -/
lemma resW_image {qn h ℓ : ℕ} (hℓ : 1 ≤ ℓ) (hh : 3 * qn / 5 ≤ h) (hh' : h ≤ 5 * qn / 8) :
    resW qn h ℓ = (resK qn h).image (resSite qn h ℓ) :=
  (res_bij (qn := qn) (h := h) (ℓ := ℓ) hℓ hh hh').1

lemma resW_preimage {qn h ℓ : ℕ} (hℓ : 1 ≤ ℓ) (hh : 3 * qn / 5 ≤ h) (hh' : h ≤ 5 * qn / 8)
    {j : ℤ} (hj : j ∈ resW qn h ℓ) :
    ∃ k_j ∈ resK qn h, resSite qn h ℓ k_j = j :=
  Finset.mem_image.mp (by rw [← resW_image hℓ hh hh']; exact hj)

lemma resW_erase_image {qn h ℓ : ℕ} (hℓ : 1 ≤ ℓ) (hh : 3 * qn / 5 ≤ h) (hh' : h ≤ 5 * qn / 8)
    {j k_j : ℤ} (hk_j : k_j ∈ resK qn h) (hkj : resSite qn h ℓ k_j = j) :
    (resW qn h ℓ).erase j = ((resK qn h).erase k_j).image (resSite qn h ℓ) := by
  have hW := resW_image hℓ hh hh'
  have hinj := (res_bij (qn := qn) (h := h) (ℓ := ℓ) hℓ hh hh').2.1
  rw [hW]
  ext x
  constructor
  · intro hx
    rw [Finset.mem_erase] at hx
    obtain ⟨hne, hximg⟩ := hx
    obtain ⟨k, hk, hkx⟩ := Finset.mem_image.mp hximg
    refine Finset.mem_image.mpr ⟨k, ?_, hkx⟩
    rw [Finset.mem_erase]
    exact ⟨fun hkk => hne (by rw [← hkx, hkk, hkj]), hk⟩
  · intro hx
    obtain ⟨k, hk, hkx⟩ := Finset.mem_image.mp hx
    rw [Finset.mem_erase] at hk
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_image.mpr ⟨k, hk.2, hkx⟩⟩
    intro hcontra
    exact hk.1 (hinj hk.2 hk_j (by rw [hkx, hcontra, hkj]))

/-- Every site of the window is bounded in absolute value by `(ℓ+1) q n`. -/
lemma resSite_abs_le {qn h ℓ : ℕ} (hℓ : 1 ≤ ℓ) (hh : 3 * qn / 5 ≤ h) (hh' : h ≤ 5 * qn / 8)
    {k : ℤ} (hk : k ∈ resK qn h) : |resSite qn h ℓ k| ≤ ((ℓ : ℤ) + 1) * (qn : ℤ) := by
  have hqn : h ≤ qn := by
    have h8 : h * 8 ≤ 5 * qn := (Nat.le_div_iff_mul_le (by norm_num : 0 < 8)).mp hh'
    have h9 : h * 8 ≤ qn * 8 := by nlinarith [h8]
    exact Nat.le_of_mul_le_mul_right h9 (by norm_num)
  have hb := res_bij (qn := qn) (h := h) (ℓ := ℓ) hℓ hh hh' |>.2.2.2.2 k hk
  have h1 : -(((ℓ : ℤ) + 1) * (qn : ℤ)) ≤ resSite qn h ℓ k := by
    have : (0 : ℤ) ≤ (ℓ : ℤ) := by omega
    nlinarith [hb.1, hb.2, this]
  have h2 : resSite qn h ℓ k ≤ ((ℓ : ℤ) + 1) * (qn : ℤ) := by
    nlinarith [hb.1, hb.2]
  exact abs_le.mpr ⟨h1, h2⟩

/-- `2 fracDist w ≤ |sin (π w)|`. -/
lemma two_mul_fracDist_le_abs_sin' (w : ℝ) :
    2 * fracDist w ≤ |Real.sin (Real.pi * w)| := by
  have h := Basic.two_div_pi_mul_le_S w
  have e : 2 / Real.pi * (Real.pi * Basic.nn w) = 2 * Basic.nn w := by field_simp
  rw [e] at h
  have hnn : Basic.nn w = fracDist w := rfl
  have hS : Basic.S w = |Real.sin (Real.pi * w)| := rfl
  rwa [hnn, hS] at h

/-- Lower bound for the `sin`-factor of a difference `m α` with `m ≠ 0` in the window's
range. -/
lemma res_min_term_ge {α : ℝ} {q : ℕ → ℕ} {Δ : ℕ → ℝ} {n ℓ : ℕ} {β : ℝ} {m : ℤ}
    (hqpos : ∀ m, 0 < q m) (hmono : StrictMono q) (hΔpos : ∀ m, 0 < Δ m)
    (hΔeq : ∀ m, Δ m = fracDist ((q m : ℝ) * α))
    (hΔup : ∀ m, Δ m < 1 / ((q (m + 1) : ℝ)))
    (hΔlo : ∀ m, 1 / (((q (m + 1) : ℝ)) + (q m : ℝ)) < Δ m)
    (hbest : ∀ m k : ℕ, q m ≤ k → k < q (m + 1) → Δ m ≤ fracDist ((k : ℝ) * α))
    (hn : 1 ≤ n) (hℓ : 1 ≤ ℓ)
    (hℓb : 10 * (ℓ : ℤ) * (q n : ℤ) ≤ (q (n + 1) : ℤ))
    (hβ : (q (n + 1) : ℝ) ≤ Real.exp (β * (q n : ℝ)))
    (hm1 : m ≠ 0) (hm2 : |m| ≤ 2 * ((ℓ : ℤ) + 1) * (q n : ℤ)) :
    -β * (q n : ℝ) ≤ Real.log |Real.sin (Real.pi * ((m : ℝ) * α))| := by
  have hm1' : 1 ≤ |m| := Int.one_le_abs hm1
  have hsep := res_sep (α := α) (q := q) (Δ := Δ) hqpos hmono hΔpos hΔeq hΔup hΔlo hbest
    hℓ hn hℓb hm1' hm2
  have hsin := two_mul_fracDist_le_abs_sin' ((m : ℝ) * α)
  have hq1 : (0 : ℝ) < (q (n + 1) : ℝ) := by have := hqpos (n + 1); exact_mod_cast this
  have h1 : 1 / (q (n + 1) : ℝ) ≤ |Real.sin (Real.pi * ((m : ℝ) * α))| := by
    have h2 : 2 * (1 / (2 * (q (n + 1) : ℝ))) = 1 / (q (n + 1) : ℝ) := by field_simp
    nlinarith [hsep, hsin, h2.le, h2.ge]
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < 1 / (q (n + 1) : ℝ)) h1
  have h2 : Real.log (1 / (q (n + 1) : ℝ)) = -Real.log (q (n + 1) : ℝ) := by
    rw [one_div, Real.log_inv]
  have h3 : Real.log (q (n + 1) : ℝ) ≤ β * (q n : ℝ) :=
    (Real.log_le_iff_le_exp hq1).mpr hβ
  linarith [hlog, h2.le, h2.ge, h3]

/-- Lower bound for the `θ`-factor at a pair of window indices. -/
lemma res_theta_term_ge {α θ c : ℝ} {qn ℓ : ℕ} {i j : ℤ}
    (hc : 0 < c)
    (hθ : ∀ k : ℤ, |k| ≤ 4 * ((ℓ : ℤ) + 2) * (qn : ℤ) →
      c ≤ fracDist (2 * θ + (k : ℝ) * α))
    (hrange : |i + j| ≤ 4 * ((ℓ : ℤ) + 2) * (qn : ℤ)) :
    Real.log (2 * c) ≤ Real.log |Real.sin (Real.pi * (2 * θ + ((i + j : ℤ) : ℝ) * α))| := by
  have h1 : 2 * c ≤ |Real.sin (Real.pi * (2 * θ + ((i + j : ℤ) : ℝ) * α))| :=
    le_trans (mul_le_mul_of_nonneg_left (hθ (i + j) hrange) (by norm_num))
      (two_mul_fracDist_le_abs_sin' _)
  exact Real.log_le_log (by positivity) h1

/-- **Upper bound for a window sum.**  For any phase `ξ`, the sum of `log |sin (π (ξ + i α))|`
over the resonant window with one node `j` removed is at most `-(2 q n - 2) log 2 + 16 log (q n)`.

The two blocks `resB1`, `resB2` are estimated by `res_blk_le` / `res_blk_le_erase`; the hypothesis
`hpos` (all terms of the sum are non-zero) is what allows the removed minimum to be compared with
the term at the node `j`. -/
lemma res_sum_up {α : ℝ} {q : ℕ → ℕ} {Δ : ℕ → ℝ} {n h ℓ : ℕ} {j : ℤ} {ξ : ℝ}
    (hqpos : ∀ m, 0 < q m) (hmono : StrictMono q) (hΔpos : ∀ m, 0 < Δ m)
    (hΔeq : ∀ m, Δ m = fracDist ((q m : ℝ) * α))
    (hΔup : ∀ m, Δ m < 1 / ((q (m + 1) : ℝ)))
    (hΔlo : ∀ m, 1 / (((q (m + 1) : ℝ)) + (q m : ℝ)) < Δ m)
    (hbest : ∀ m k : ℕ, q m ≤ k → k < q (m + 1) → Δ m ≤ fracDist ((k : ℝ) * α))
    (hn : 1 ≤ n) (hℓ : 1 ≤ ℓ) (hh : 3 * q n / 5 ≤ h) (hh' : h ≤ 5 * q n / 8)
    (hℓb : 10 * (ℓ : ℤ) * (q n : ℤ) ≤ (q (n + 1) : ℤ))
    (hj : j ∈ resW (q n) h ℓ)
    (hpos : ∀ k ∈ resK (q n) h, resSite (q n) h ℓ k ≠ j →
      Real.sin (Real.pi * (ξ + ((resSite (q n) h ℓ k : ℤ) : ℝ) * α)) ≠ 0) :
    ∑ i ∈ (resW (q n) h ℓ).erase j, Real.log |Real.sin (Real.pi * (ξ + (i : ℝ) * α))|
      ≤ -((2 : ℝ) * (q n : ℝ) - 2) * Real.log 2 + 16 * Real.log (q n : ℝ) := by
  obtain ⟨hc1, hc2, hcW, hK, hdisj, hcB1, hcB2⟩ := res_card (qn := q n) (h := h) (ℓ := ℓ) hℓ hh hh'
  have hinj : Set.InjOn (resSite (q n) h ℓ) ((resK (q n) h : Finset ℤ) : Set ℤ) :=
    (res_bij (qn := q n) (h := h) (ℓ := ℓ) hℓ hh hh').2.1
  obtain ⟨k_j, hk_j, hk_j_eq⟩ := resW_preimage hℓ hh hh' hj
  have hErase := resW_erase_image (qn := q n) (h := h) (ℓ := ℓ) hℓ hh hh' hk_j hk_j_eq
  rw [hErase, Finset.sum_image
    (f := fun i : ℤ => Real.log |Real.sin (Real.pi * (ξ + (i : ℝ) * α))|)
    (fun a ha b hb hab => hinj (Finset.mem_of_mem_erase ha) (Finset.mem_of_mem_erase hb) hab)]
  have hmemK : ∀ {x : ℤ}, x ∈ resB1 (q n) h ∨ x ∈ resB2 (q n) h → x ∈ resK (q n) h :=
    fun hx => by rw [hK]; exact hx.elim (Finset.mem_union_left _) (Finset.mem_union_right _)
  have hfin : ∀ (k : ℤ), k ∈ resK (q n) h → k ≠ k_j →
      Real.sin (Real.pi * (ξ + ((resSite (q n) h ℓ k : ℤ) : ℝ) * α)) ≠ 0 :=
    fun k hk hne => hpos k hk (fun hcon => hne (hinj hk hk_j (by rw [hcon, hk_j_eq])))
  rcases Finset.mem_union.mp (by rw [← hK]; exact hk_j) with hk1 | hk2
  · have hun : (resK (q n) h).erase k_j = (resB1 (q n) h).erase k_j ∪ resB2 (q n) h := by
      rw [hK]
      ext x
      simp only [Finset.mem_erase, Finset.mem_union]
      constructor
      · rintro ⟨hne, hx1 | hx2⟩
        · exact Or.inl ⟨hne, hx1⟩
        · exact Or.inr hx2
      · rintro (⟨hne, hx1⟩ | hx2)
        · exact ⟨hne, Or.inl hx1⟩
        · exact ⟨fun hcontra => Finset.disjoint_left.mp hdisj hk1 (by rw [← hcontra]; exact hx2),
            Or.inr hx2⟩
    have hdj : Disjoint ((resB1 (q n) h).erase k_j) (resB2 (q n) h) :=
      Finset.disjoint_left.mpr (fun x hx1 hx2 =>
        Finset.disjoint_left.mp hdisj (Finset.mem_of_mem_erase hx1) hx2)
    rw [hun, Finset.sum_union hdj]
    have hA : ∑ k ∈ (resB1 (q n) h).erase k_j,
        Real.log |Real.sin (Real.pi * (ξ + ((resSite (q n) h ℓ k : ℤ) : ℝ) * α))|
        ≤ -((q n : ℝ) - 1) * Real.log 2 + 8 * Real.log (q n : ℝ) :=
      res_blk_le_erase (ξ := ξ) (B := resB1 (q n) h) (p := -(h : ℤ))
        (by rw [resB1]; congr 1; ring) hqpos hmono hΔpos hΔeq hΔup hΔlo hbest hn hℓ hℓb hk1
        (fun k hk hne => hfin k (hmemK (Or.inl hk)) hne)
    have hB : ∑ k ∈ resB2 (q n) h,
        Real.log |Real.sin (Real.pi * (ξ + ((resSite (q n) h ℓ k : ℤ) : ℝ) * α))|
        ≤ -((q n : ℝ) - 1) * Real.log 2 + 8 * Real.log (q n : ℝ) :=
      res_blk_le (ξ := ξ) (B := resB2 (q n) h) (p := (q n : ℤ) - (h : ℤ))
        (by rw [resB2]; congr 1; ring) hqpos hmono hΔpos hΔeq hΔup hΔlo hbest hn hℓ hℓb
    linarith
  · have hun : (resK (q n) h).erase k_j = resB1 (q n) h ∪ (resB2 (q n) h).erase k_j := by
      rw [hK]
      ext x
      simp only [Finset.mem_erase, Finset.mem_union]
      constructor
      · rintro ⟨hne, hx1 | hx2⟩
        · exact Or.inl hx1
        · exact Or.inr ⟨hne, hx2⟩
      · rintro (hx1 | ⟨hne, hx2⟩)
        · exact ⟨fun hcontra => Finset.disjoint_left.mp hdisj hx1 (by rw [hcontra]; exact hk2),
            Or.inl hx1⟩
        · exact ⟨hne, Or.inr hx2⟩
    have hdj : Disjoint (resB1 (q n) h) ((resB2 (q n) h).erase k_j) :=
      Finset.disjoint_left.mpr (fun x hx1 hx2 =>
        Finset.disjoint_left.mp hdisj hx1 (Finset.mem_of_mem_erase hx2))
    rw [hun, Finset.sum_union hdj]
    have hA : ∑ k ∈ resB1 (q n) h,
        Real.log |Real.sin (Real.pi * (ξ + ((resSite (q n) h ℓ k : ℤ) : ℝ) * α))|
        ≤ -((q n : ℝ) - 1) * Real.log 2 + 8 * Real.log (q n : ℝ) :=
      res_blk_le (ξ := ξ) (B := resB1 (q n) h) (p := -(h : ℤ))
        (by rw [resB1]; congr 1; ring) hqpos hmono hΔpos hΔeq hΔup hΔlo hbest hn hℓ hℓb
    have hB : ∑ k ∈ (resB2 (q n) h).erase k_j,
        Real.log |Real.sin (Real.pi * (ξ + ((resSite (q n) h ℓ k : ℤ) : ℝ) * α))|
        ≤ -((q n : ℝ) - 1) * Real.log 2 + 8 * Real.log (q n : ℝ) :=
      res_blk_le_erase (ξ := ξ) (B := resB2 (q n) h) (p := (q n : ℤ) - (h : ℤ))
        (by rw [resB2]; congr 1; ring) hqpos hmono hΔpos hΔeq hΔup hΔlo hbest hn hℓ hℓb hk2
        (fun k hk hne => hfin k (hmemK (Or.inr hk)) hne)
    linarith

/-- **Lower bound for the difference sum of the window.**  The sum of
`log |sin (π (-j α + i α))|` over the resonant window with the node `j` removed is at least
`-(2 q n - 2) log 2 - 16 log (q n) - β q n`.

The block containing `k_j` has its minimum at `k_j` itself (where the sine vanishes), so the block
estimate applies with no loss; the other block's minimum is bounded with `res_min_term_ge`. -/
lemma res_sum_low_diff {α : ℝ} {q : ℕ → ℕ} {Δ : ℕ → ℝ} {n h ℓ : ℕ} {j : ℤ} {β : ℝ}
    (hqpos : ∀ m, 0 < q m) (hmono : StrictMono q) (hΔpos : ∀ m, 0 < Δ m)
    (hΔeq : ∀ m, Δ m = fracDist ((q m : ℝ) * α))
    (hΔup : ∀ m, Δ m < 1 / ((q (m + 1) : ℝ)))
    (hΔlo : ∀ m, 1 / (((q (m + 1) : ℝ)) + (q m : ℝ)) < Δ m)
    (hbest : ∀ m k : ℕ, q m ≤ k → k < q (m + 1) → Δ m ≤ fracDist ((k : ℝ) * α))
    (hn : 1 ≤ n) (hℓ : 1 ≤ ℓ) (hh : 3 * q n / 5 ≤ h) (hh' : h ≤ 5 * q n / 8)
    (hℓb : 10 * (ℓ : ℤ) * (q n : ℤ) ≤ (q (n + 1) : ℤ))
    (hβ : (q (n + 1) : ℝ) ≤ Real.exp (β * (q n : ℝ)))
    (hj : j ∈ resW (q n) h ℓ) :
    -((2 : ℝ) * (q n : ℝ) - 2) * Real.log 2 - 16 * Real.log (q n : ℝ) - β * (q n : ℝ)
      ≤ ∑ i ∈ (resW (q n) h ℓ).erase j,
          Real.log |Real.sin (Real.pi * (-(j : ℝ) * α + (i : ℝ) * α))| := by
  obtain ⟨hc1, hc2, hcW, hK, hdisj, hcB1, hcB2⟩ := res_card (qn := q n) (h := h) (ℓ := ℓ) hℓ hh hh'
  have hinj : Set.InjOn (resSite (q n) h ℓ) ((resK (q n) h : Finset ℤ) : Set ℤ) :=
    (res_bij (qn := q n) (h := h) (ℓ := ℓ) hℓ hh hh').2.1
  obtain ⟨k_j, hk_j, hk_j_eq⟩ := resW_preimage hℓ hh hh' hj
  have hErase := resW_erase_image (qn := q n) (h := h) (ℓ := ℓ) hℓ hh hh' hk_j hk_j_eq
  rw [hErase, Finset.sum_image
    (f := fun i : ℤ => Real.log |Real.sin (Real.pi * (-(j : ℝ) * α + (i : ℝ) * α))|)
    (fun a ha b hb hab => hinj (Finset.mem_of_mem_erase ha) (Finset.mem_of_mem_erase hb) hab)]
  have hmemK : ∀ {x : ℤ}, x ∈ resB1 (q n) h ∨ x ∈ resB2 (q n) h → x ∈ resK (q n) h :=
    fun hx => by rw [hK]; exact hx.elim (Finset.mem_union_left _) (Finset.mem_union_right _)
  have hsin0 : Real.sin (Real.pi * (-(j : ℝ) * α + ((resSite (q n) h ℓ k_j : ℤ) : ℝ) * α)) = 0 := by
    rw [show (-(j : ℝ) * α) + ((resSite (q n) h ℓ k_j : ℤ) : ℝ) * α = 0 by
      rw [hk_j_eq]; ring]
    simp
  have habsj : |resSite (q n) h ℓ k_j| ≤ ((ℓ : ℤ) + 1) * (q n : ℤ) :=
    resSite_abs_le (qn := q n) (h := h) (ℓ := ℓ) hℓ hh hh' hk_j
  have hm_bound : ∀ k : ℤ, k ∈ resK (q n) h →
      |resSite (q n) h ℓ k - j| ≤ 2 * ((ℓ : ℤ) + 1) * (q n : ℤ) := by
    intro k hkK
    have h1 := resSite_abs_le (qn := q n) (h := h) (ℓ := ℓ) hℓ hh hh' hkK
    have h2 : |resSite (q n) h ℓ k - j| ≤ |resSite (q n) h ℓ k| + |j| := by
      rw [sub_eq_add_neg]
      calc |resSite (q n) h ℓ k + -j| ≤ |resSite (q n) h ℓ k| + |(-j : ℤ)| := abs_add_le _ _
        _ = |resSite (q n) h ℓ k| + |j| := by rw [abs_neg]
    have h3 : |j| ≤ ((ℓ : ℤ) + 1) * (q n : ℤ) := by rw [← hk_j_eq]; exact habsj
    calc |resSite (q n) h ℓ k - j| ≤ ((ℓ : ℤ) + 1) * (q n : ℤ) + ((ℓ : ℤ) + 1) * (q n : ℤ) := by
          linarith
      _ = 2 * ((ℓ : ℤ) + 1) * (q n : ℤ) := by ring
  have hmin_lb : ∀ k : ℤ, k ∈ resK (q n) h → k ≠ k_j →
      -β * (q n : ℝ) ≤
        Real.log |Real.sin (Real.pi * (-(j : ℝ) * α + ((resSite (q n) h ℓ k : ℤ) : ℝ) * α))| := by
    intro k hkK hkne
    have hmne : resSite (q n) h ℓ k - j ≠ 0 := by
      intro hcon
      have h1 : resSite (q n) h ℓ k = j := sub_eq_zero.mp hcon
      exact hkne (hinj hkK hk_j (by rw [h1, hk_j_eq]))
    have harg : (-(j : ℝ) * α) + ((resSite (q n) h ℓ k : ℤ) : ℝ) * α
        = (((resSite (q n) h ℓ k - j : ℤ)) : ℝ) * α := by push_cast; ring
    rw [harg]
    exact res_min_term_ge (α := α) (q := q) (Δ := Δ) (β := β) (m := resSite (q n) h ℓ k - j)
      hqpos hmono hΔpos hΔeq hΔup hΔlo hbest hn hℓ hℓb hβ hmne (hm_bound k hkK)
  rcases Finset.mem_union.mp (by rw [← hK]; exact hk_j) with hk1 | hk2
  · have hne2 : ∀ k : ℤ, k ∈ resB2 (q n) h → k ≠ k_j := by
      intro k hk hcon
      rw [hcon] at hk
      exact Finset.disjoint_left.mp hdisj hk1 hk
    have hun : (resK (q n) h).erase k_j = (resB1 (q n) h).erase k_j ∪ resB2 (q n) h := by
      rw [hK]
      ext x
      simp only [Finset.mem_erase, Finset.mem_union]
      constructor
      · rintro ⟨hne, hx1 | hx2⟩
        · exact Or.inl ⟨hne, hx1⟩
        · exact Or.inr hx2
      · rintro (⟨hne, hx1⟩ | hx2)
        · exact ⟨hne, Or.inl hx1⟩
        · exact ⟨fun hcontra => Finset.disjoint_left.mp hdisj hk1 (by rw [← hcontra]; exact hx2),
            Or.inr hx2⟩
    have hdj : Disjoint ((resB1 (q n) h).erase k_j) (resB2 (q n) h) :=
      Finset.disjoint_left.mpr (fun x hx1 hx2 =>
        Finset.disjoint_left.mp hdisj (Finset.mem_of_mem_erase hx1) hx2)
    rw [hun, Finset.sum_union hdj]
    have hA : -((q n : ℝ) - 1) * Real.log 2 - 8 * Real.log (q n : ℝ)
        ≤ ∑ k ∈ (resB1 (q n) h).erase k_j,
          Real.log |Real.sin (Real.pi * (-(j : ℝ) * α + ((resSite (q n) h ℓ k : ℤ) : ℝ) * α))| :=
      res_blk_ge_erase_kj (ξ := -(j : ℝ) * α) (B := resB1 (q n) h) (p := -(h : ℤ))
        (by rw [resB1]; congr 1; ring) hqpos hmono hΔpos hΔeq hΔup hΔlo hbest hn hℓ hℓb hk1 hsin0
    have hB : -((q n : ℝ) - 1) * Real.log 2 - 8 * Real.log (q n : ℝ) + (-β * (q n : ℝ))
        ≤ ∑ k ∈ resB2 (q n) h,
          Real.log |Real.sin (Real.pi * (-(j : ℝ) * α + ((resSite (q n) h ℓ k : ℤ) : ℝ) * α))| :=
      res_blk_ge (ξ := -(j : ℝ) * α) (B := resB2 (q n) h) (p := (q n : ℤ) - (h : ℤ))
        (B0 := -β * (q n : ℝ))
        (by rw [resB2]; congr 1; ring) hqpos hmono hΔpos hΔeq hΔup hΔlo hbest hn hℓ hℓb
        (fun k hk => hmin_lb k (hmemK (Or.inr hk)) (hne2 k hk))
    linarith
  · have hne1 : ∀ k : ℤ, k ∈ resB1 (q n) h → k ≠ k_j := by
      intro k hk hcon
      rw [hcon] at hk
      exact Finset.disjoint_left.mp hdisj hk hk2
    have hun : (resK (q n) h).erase k_j = resB1 (q n) h ∪ (resB2 (q n) h).erase k_j := by
      rw [hK]
      ext x
      simp only [Finset.mem_erase, Finset.mem_union]
      constructor
      · rintro ⟨hne, hx1 | hx2⟩
        · exact Or.inl hx1
        · exact Or.inr ⟨hne, hx2⟩
      · rintro (hx1 | ⟨hne, hx2⟩)
        · exact ⟨fun hcontra => Finset.disjoint_left.mp hdisj hx1 (by rw [hcontra]; exact hk2),
            Or.inl hx1⟩
        · exact ⟨hne, Or.inr hx2⟩
    have hdj : Disjoint (resB1 (q n) h) ((resB2 (q n) h).erase k_j) :=
      Finset.disjoint_left.mpr (fun x hx1 hx2 =>
        Finset.disjoint_left.mp hdisj hx1 (Finset.mem_of_mem_erase hx2))
    rw [hun, Finset.sum_union hdj]
    have hA : -((q n : ℝ) - 1) * Real.log 2 - 8 * Real.log (q n : ℝ) + (-β * (q n : ℝ))
        ≤ ∑ k ∈ resB1 (q n) h,
          Real.log |Real.sin (Real.pi * (-(j : ℝ) * α + ((resSite (q n) h ℓ k : ℤ) : ℝ) * α))| :=
      res_blk_ge (ξ := -(j : ℝ) * α) (B := resB1 (q n) h) (p := -(h : ℤ)) (B0 := -β * (q n : ℝ))
        (by rw [resB1]; congr 1; ring) hqpos hmono hΔpos hΔeq hΔup hΔlo hbest hn hℓ hℓb
        (fun k hk => hmin_lb k (hmemK (Or.inl hk)) (hne1 k hk))
    have hB : -((q n : ℝ) - 1) * Real.log 2 - 8 * Real.log (q n : ℝ)
        ≤ ∑ k ∈ (resB2 (q n) h).erase k_j,
          Real.log |Real.sin (Real.pi * (-(j : ℝ) * α + ((resSite (q n) h ℓ k : ℤ) : ℝ) * α))| :=
      res_blk_ge_erase_kj (ξ := -(j : ℝ) * α) (B := resB2 (q n) h) (p := (q n : ℤ) - (h : ℤ))
        (by rw [resB2]; congr 1; ring) hqpos hmono hΔpos hΔeq hΔup hΔlo hbest hn hℓ hℓb hk2 hsin0
    linarith

/-- Dropping a non-positive term from a block sum can only increase it. -/
lemma sum_erase_ge_of_nonpos {f : ℤ → ℝ} {B : Finset ℤ} {k_j : ℤ}
    (hkj : k_j ∈ B) (h0 : f k_j ≤ 0) :
    ∑ k ∈ B, f k ≤ ∑ k ∈ B.erase k_j, f k := by
  have h := Finset.sum_erase_add B f hkj
  linarith

/-- **Lower bound for the `θ`-sum of the window.**  The sum of `log |sin (π (2 θ + (i+j) α))|`
over the resonant window with the node `j` removed is at least
`-(2 q n - 2) log 2 - 16 log (q n) + 2 log (2 c)`.

Both blocks are estimated by `res_blk_ge` with `B0 = log (2c)`, which is available for every term
by the hypothesis `hθ`. -/
lemma res_sum_low_theta {α : ℝ} {q : ℕ → ℕ} {Δ : ℕ → ℝ} {n h ℓ : ℕ} {j : ℤ} {θ c : ℝ}
    (hqpos : ∀ m, 0 < q m) (hmono : StrictMono q) (hΔpos : ∀ m, 0 < Δ m)
    (hΔeq : ∀ m, Δ m = fracDist ((q m : ℝ) * α))
    (hΔup : ∀ m, Δ m < 1 / ((q (m + 1) : ℝ)))
    (hΔlo : ∀ m, 1 / (((q (m + 1) : ℝ)) + (q m : ℝ)) < Δ m)
    (hbest : ∀ m k : ℕ, q m ≤ k → k < q (m + 1) → Δ m ≤ fracDist ((k : ℝ) * α))
    (hn : 1 ≤ n) (hℓ : 1 ≤ ℓ) (hh : 3 * q n / 5 ≤ h) (hh' : h ≤ 5 * q n / 8)
    (hℓb : 10 * (ℓ : ℤ) * (q n : ℤ) ≤ (q (n + 1) : ℤ))
    (hc : 0 < c)
    (hθ : ∀ k : ℤ, |k| ≤ 4 * ((ℓ : ℤ) + 2) * (q n : ℤ) → c ≤ fracDist (2 * θ + (k : ℝ) * α))
    (hj : j ∈ resW (q n) h ℓ) :
    -((2 : ℝ) * (q n : ℝ) - 2) * Real.log 2 - 16 * Real.log (q n : ℝ) + 2 * Real.log (2 * c)
      ≤ ∑ i ∈ (resW (q n) h ℓ).erase j,
          Real.log |Real.sin (Real.pi * (2 * θ + (j : ℝ) * α + (i : ℝ) * α))| := by
  obtain ⟨hc1, hc2, hcW, hK, hdisj, hcB1, hcB2⟩ := res_card (qn := q n) (h := h) (ℓ := ℓ) hℓ hh hh'
  have hinj : Set.InjOn (resSite (q n) h ℓ) ((resK (q n) h : Finset ℤ) : Set ℤ) :=
    (res_bij (qn := q n) (h := h) (ℓ := ℓ) hℓ hh hh').2.1
  obtain ⟨k_j, hk_j, hk_j_eq⟩ := resW_preimage hℓ hh hh' hj
  have hErase := resW_erase_image (qn := q n) (h := h) (ℓ := ℓ) hℓ hh hh' hk_j hk_j_eq
  rw [hErase, Finset.sum_image
    (f := fun i : ℤ => Real.log |Real.sin (Real.pi * (2 * θ + (j : ℝ) * α + (i : ℝ) * α))|)
    (fun a ha b hb hab => hinj (Finset.mem_of_mem_erase ha) (Finset.mem_of_mem_erase hb) hab)]
  have hmemK : ∀ {x : ℤ}, x ∈ resB1 (q n) h ∨ x ∈ resB2 (q n) h → x ∈ resK (q n) h :=
    fun hx => by rw [hK]; exact hx.elim (Finset.mem_union_left _) (Finset.mem_union_right _)
  have habsj : |resSite (q n) h ℓ k_j| ≤ ((ℓ : ℤ) + 1) * (q n : ℤ) :=
    resSite_abs_le (qn := q n) (h := h) (ℓ := ℓ) hℓ hh hh' hk_j
  have hmin_lb : ∀ k : ℤ, k ∈ resK (q n) h → Real.log (2 * c) ≤
      Real.log |Real.sin (Real.pi * (2 * θ + (j : ℝ) * α + ((resSite (q n) h ℓ k : ℤ) : ℝ) * α))| := by
    intro k hkK
    have h1 := resSite_abs_le (qn := q n) (h := h) (ℓ := ℓ) hℓ hh hh' hkK
    have h2 : |j| ≤ ((ℓ : ℤ) + 1) * (q n : ℤ) := by rw [← hk_j_eq]; exact habsj
    have h3 : |resSite (q n) h ℓ k + j| ≤ |resSite (q n) h ℓ k| + |j| := abs_add_le _ _
    have hℓR : (1 : ℤ) ≤ (ℓ : ℤ) := by exact_mod_cast hℓ
    have hq0 : (0 : ℤ) ≤ (q n : ℤ) := by positivity
    have h5 : (2 : ℤ) * ((ℓ : ℤ) + 1) * (q n : ℤ) ≤ 4 * ((ℓ : ℤ) + 2) * (q n : ℤ) := by
      nlinarith [hq0, hℓR]
    have hrange : |resSite (q n) h ℓ k + j| ≤ 4 * ((ℓ : ℤ) + 2) * (q n : ℤ) := by
      have h4 : ((ℓ : ℤ) + 1) * (q n : ℤ) + ((ℓ : ℤ) + 1) * (q n : ℤ)
          = 2 * ((ℓ : ℤ) + 1) * (q n : ℤ) := by ring
      linarith
    have harg : (2 * θ + (j : ℝ) * α) + ((resSite (q n) h ℓ k : ℤ) : ℝ) * α
        = 2 * θ + (((resSite (q n) h ℓ k + j : ℤ)) : ℝ) * α := by push_cast; ring
    rw [harg]
    exact res_theta_term_ge (α := α) (θ := θ) (c := c) (qn := q n) (ℓ := ℓ)
      (i := resSite (q n) h ℓ k) (j := j) hc hθ hrange
  rcases Finset.mem_union.mp (by rw [← hK]; exact hk_j) with hk1 | hk2
  · have hun : (resK (q n) h).erase k_j = (resB1 (q n) h).erase k_j ∪ resB2 (q n) h := by
      rw [hK]
      ext x
      simp only [Finset.mem_erase, Finset.mem_union]
      constructor
      · rintro ⟨hne, hx1 | hx2⟩
        · exact Or.inl ⟨hne, hx1⟩
        · exact Or.inr hx2
      · rintro (⟨hne, hx1⟩ | hx2)
        · exact ⟨hne, Or.inl hx1⟩
        · exact ⟨fun hcontra => Finset.disjoint_left.mp hdisj hk1 (by rw [← hcontra]; exact hx2),
            Or.inr hx2⟩
    have hdj : Disjoint ((resB1 (q n) h).erase k_j) (resB2 (q n) h) :=
      Finset.disjoint_left.mpr (fun x hx1 hx2 =>
        Finset.disjoint_left.mp hdisj (Finset.mem_of_mem_erase hx1) hx2)
    rw [hun, Finset.sum_union hdj]
    have hA0 : -((q n : ℝ) - 1) * Real.log 2 - 8 * Real.log (q n : ℝ) + Real.log (2 * c)
        ≤ ∑ k ∈ resB1 (q n) h,
          Real.log |Real.sin (Real.pi * (2 * θ + (j : ℝ) * α + ((resSite (q n) h ℓ k : ℤ) : ℝ) * α))| :=
      res_blk_ge (ξ := 2 * θ + (j : ℝ) * α) (B := resB1 (q n) h) (p := -(h : ℤ)) (B0 := Real.log (2 * c))
        (by rw [resB1]; congr 1; ring) hqpos hmono hΔpos hΔeq hΔup hΔlo hbest hn hℓ hℓb
        (fun k hk => hmin_lb k (hmemK (Or.inl hk)))
    have hA := le_trans hA0 (sum_erase_ge_of_nonpos hk1 (log_abs_sin_nonpos _))
    have hB : -((q n : ℝ) - 1) * Real.log 2 - 8 * Real.log (q n : ℝ) + Real.log (2 * c)
        ≤ ∑ k ∈ resB2 (q n) h,
          Real.log |Real.sin (Real.pi * (2 * θ + (j : ℝ) * α + ((resSite (q n) h ℓ k : ℤ) : ℝ) * α))| :=
      res_blk_ge (ξ := 2 * θ + (j : ℝ) * α) (B := resB2 (q n) h) (p := (q n : ℤ) - (h : ℤ))
        (B0 := Real.log (2 * c))
        (by rw [resB2]; congr 1; ring) hqpos hmono hΔpos hΔeq hΔup hΔlo hbest hn hℓ hℓb
        (fun k hk => hmin_lb k (hmemK (Or.inr hk)))
    linarith
  · have hun : (resK (q n) h).erase k_j = resB1 (q n) h ∪ (resB2 (q n) h).erase k_j := by
      rw [hK]
      ext x
      simp only [Finset.mem_erase, Finset.mem_union]
      constructor
      · rintro ⟨hne, hx1 | hx2⟩
        · exact Or.inl hx1
        · exact Or.inr ⟨hne, hx2⟩
      · rintro (hx1 | ⟨hne, hx2⟩)
        · exact ⟨fun hcontra => Finset.disjoint_left.mp hdisj hx1 (by rw [hcontra]; exact hk2),
            Or.inl hx1⟩
        · exact ⟨hne, Or.inr hx2⟩
    have hdj : Disjoint (resB1 (q n) h) ((resB2 (q n) h).erase k_j) :=
      Finset.disjoint_left.mpr (fun x hx1 hx2 =>
        Finset.disjoint_left.mp hdisj hx1 (Finset.mem_of_mem_erase hx2))
    rw [hun, Finset.sum_union hdj]
    have hA : -((q n : ℝ) - 1) * Real.log 2 - 8 * Real.log (q n : ℝ) + Real.log (2 * c)
        ≤ ∑ k ∈ resB1 (q n) h,
          Real.log |Real.sin (Real.pi * (2 * θ + (j : ℝ) * α + ((resSite (q n) h ℓ k : ℤ) : ℝ) * α))| :=
      res_blk_ge (ξ := 2 * θ + (j : ℝ) * α) (B := resB1 (q n) h) (p := -(h : ℤ)) (B0 := Real.log (2 * c))
        (by rw [resB1]; congr 1; ring) hqpos hmono hΔpos hΔeq hΔup hΔlo hbest hn hℓ hℓb
        (fun k hk => hmin_lb k (hmemK (Or.inl hk)))
    have hB0 : -((q n : ℝ) - 1) * Real.log 2 - 8 * Real.log (q n : ℝ) + Real.log (2 * c)
        ≤ ∑ k ∈ resB2 (q n) h,
          Real.log |Real.sin (Real.pi * (2 * θ + (j : ℝ) * α + ((resSite (q n) h ℓ k : ℤ) : ℝ) * α))| :=
      res_blk_ge (ξ := 2 * θ + (j : ℝ) * α) (B := resB2 (q n) h) (p := (q n : ℤ) - (h : ℤ))
        (B0 := Real.log (2 * c))
        (by rw [resB2]; congr 1; ring) hqpos hmono hΔpos hΔeq hΔup hΔlo hbest hn hℓ hℓb
        (fun k hk => hmin_lb k (hmemK (Or.inr hk)))
    have hB := le_trans hB0 (sum_erase_ge_of_nonpos hk2 (log_abs_sin_nonpos _))
    linarith

/-- Every element of the window is bounded in absolute value by `(ℓ+1) q n`. -/
lemma resW_abs_le {qn h ℓ : ℕ} (hℓ : 1 ≤ ℓ) (hh : 3 * qn / 5 ≤ h) (hh' : h ≤ 5 * qn / 8)
    {i : ℤ} (hi : i ∈ resW qn h ℓ) : |i| ≤ ((ℓ : ℤ) + 1) * (qn : ℤ) := by
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp (by rw [← resW_image hℓ hh hh']; exact hi)
  exact resSite_abs_le (qn := qn) (h := h) (ℓ := ℓ) hℓ hh hh' hk

/-- **Distinctness of the cosines of the window phases.** -/
lemma res_cos_ne {α : ℝ} {q : ℕ → ℕ} {Δ : ℕ → ℝ} {n h ℓ : ℕ} {θ c : ℝ}
    (hqpos : ∀ m, 0 < q m) (hmono : StrictMono q) (hΔpos : ∀ m, 0 < Δ m)
    (hΔeq : ∀ m, Δ m = fracDist ((q m : ℝ) * α))
    (hΔup : ∀ m, Δ m < 1 / ((q (m + 1) : ℝ)))
    (hΔlo : ∀ m, 1 / (((q (m + 1) : ℝ)) + (q m : ℝ)) < Δ m)
    (hbest : ∀ m k : ℕ, q m ≤ k → k < q (m + 1) → Δ m ≤ fracDist ((k : ℝ) * α))
    (hn : 1 ≤ n) (hℓ : 1 ≤ ℓ) (hh : 3 * q n / 5 ≤ h) (hh' : h ≤ 5 * q n / 8)
    (hℓb : 10 * (ℓ : ℤ) * (q n : ℤ) ≤ (q (n + 1) : ℤ))
    (hc : 0 < c)
    (hθ : ∀ k : ℤ, |k| ≤ 4 * ((ℓ : ℤ) + 2) * (q n : ℤ) → c ≤ fracDist (2 * θ + (k : ℝ) * α))
    {i j : ℤ} (hi : i ∈ resW (q n) h ℓ) (hj : j ∈ resW (q n) h ℓ) (hij : i ≠ j) :
    Real.cos (2 * Real.pi * (θ + (i : ℝ) * α)) ≠ Real.cos (2 * Real.pi * (θ + (j : ℝ) * α)) := by
  intro hcon
  rw [Real.cos_eq_cos_iff] at hcon
  have h2pi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hbnd : ∀ x : ℤ, x ∈ resW (q n) h ℓ → |x| ≤ ((ℓ : ℤ) + 1) * (q n : ℤ) :=
    fun x hx => resW_abs_le (qn := q n) (h := h) (ℓ := ℓ) hℓ hh hh' hx
  have hle_R : (1 : ℤ) ≤ (ℓ : ℤ) := by exact_mod_cast hℓ
  have hq0 : (0 : ℤ) ≤ (q n : ℤ) := by positivity
  obtain ⟨k, hk | hk⟩ := hcon
  · have h2 : (2 * Real.pi) * ((((j - i : ℤ)) : ℝ) * α) = (2 * Real.pi) * (k : ℝ) := by
      have h3 : 2 * Real.pi * (θ + (j : ℝ) * α) - 2 * Real.pi * (θ + (i : ℝ) * α) = (k : ℝ) * (2 * Real.pi) := by
        rw [hk]; ring
      have h4 : 2 * Real.pi * (θ + (j : ℝ) * α) - 2 * Real.pi * (θ + (i : ℝ) * α)
          = (2 * Real.pi) * ((((j - i : ℤ)) : ℝ) * α) := by push_cast; ring
      rw [h4] at h3
      linarith [h3]
    have hz : (((j - i : ℤ)) : ℝ) * α = (k : ℝ) := mul_left_cancel₀ h2pi h2
    have hm : j - i ≠ 0 := by intro h0; exact hij (by omega)
    have hrange : |j - i| ≤ 2 * ((ℓ : ℤ) + 1) * (q n : ℤ) := by
      have h1 := hbnd j hj
      have h2' := hbnd i hi
      have h3 : |j - i| ≤ |j| + |i| := by
        rw [sub_eq_add_neg]
        calc |j + -i| ≤ |j| + |(-i : ℤ)| := abs_add_le _ _
          _ = |j| + |i| := by rw [abs_neg]
      calc |j - i| ≤ ((ℓ : ℤ) + 1) * (q n : ℤ) + ((ℓ : ℤ) + 1) * (q n : ℤ) := by linarith
        _ = 2 * ((ℓ : ℤ) + 1) * (q n : ℤ) := by ring
    have hsep := res_sep (α := α) (q := q) (Δ := Δ) hqpos hmono hΔpos hΔeq hΔup hΔlo hbest
      hℓ hn hℓb (Int.one_le_abs hm) hrange
    rw [hz, fracDist_intCast] at hsep
    have hq1 : (0 : ℝ) < (q (n + 1) : ℝ) := by have := hqpos (n + 1); exact_mod_cast this
    have hpos : (0 : ℝ) < 1 / (2 * (q (n + 1) : ℝ)) := by positivity
    linarith
  · have h2 : (2 * Real.pi) * (2 * θ + (((i + j : ℤ)) : ℝ) * α) = (2 * Real.pi) * (k : ℝ) := by
      have h3 : 2 * Real.pi * (θ + (j : ℝ) * α) + 2 * Real.pi * (θ + (i : ℝ) * α) = (k : ℝ) * (2 * Real.pi) := by
        rw [hk]; ring
      have h4 : 2 * Real.pi * (θ + (j : ℝ) * α) + 2 * Real.pi * (θ + (i : ℝ) * α)
          = (2 * Real.pi) * (2 * θ + (((i + j : ℤ)) : ℝ) * α) := by push_cast; ring
      rw [h4] at h3
      linarith [h3]
    have hz : 2 * θ + (((i + j : ℤ)) : ℝ) * α = (k : ℝ) := mul_left_cancel₀ h2pi h2
    have h1 := hbnd i hi
    have h2' := hbnd j hj
    have h3 : |i + j| ≤ |i| + |j| := abs_add_le _ _
    have hrange : |i + j| ≤ 4 * ((ℓ : ℤ) + 2) * (q n : ℤ) := by
      have h5 : (2 : ℤ) * ((ℓ : ℤ) + 1) * (q n : ℤ) ≤ 4 * ((ℓ : ℤ) + 2) * (q n : ℤ) := by
        nlinarith [hq0, hle_R]
      have h4 : ((ℓ : ℤ) + 1) * (q n : ℤ) + ((ℓ : ℤ) + 1) * (q n : ℤ)
          = 2 * ((ℓ : ℤ) + 1) * (q n : ℤ) := by ring
      linarith
    have hc' := hθ (i + j) hrange
    rw [hz, fracDist_intCast] at hc'
    linarith

/-- **The Lagrange product bound in Finset form.**  For every node `j` of the resonant window and
every `x ∈ [-1,1]`, the Lagrange product is `< exp ((2 q n - 1) ε)` with
`ε = β/2 + β/(4 q n - 2) + 2 log(1/c)/q n + 200 log(q n)/q n + 200/q n`.

The four sums arising from `|cos A - cos B| = 2 |sin ((A+B)/2)| |sin ((A-B)/2)|` are estimated by
`res_sum_up` (twice, numerator), `res_sum_low_theta` and `res_sum_low_diff`. -/
lemma res_bound {α β : ℝ} {q : ℕ → ℕ} {Δ : ℕ → ℝ} {n h ℓ : ℕ} {θ c : ℝ}
    (hqpos : ∀ m, 0 < q m) (hmono : StrictMono q) (hΔpos : ∀ m, 0 < Δ m)
    (hΔeq : ∀ m, Δ m = fracDist ((q m : ℝ) * α))
    (hΔup : ∀ m, Δ m < 1 / ((q (m + 1) : ℝ)))
    (hΔlo : ∀ m, 1 / (((q (m + 1) : ℝ)) + (q m : ℝ)) < Δ m)
    (hbest : ∀ m k : ℕ, q m ≤ k → k < q (m + 1) → Δ m ≤ fracDist ((k : ℝ) * α))
    (hn : 1 ≤ n) (hℓ : 1 ≤ ℓ) (hh : 3 * q n / 5 ≤ h) (hh' : h ≤ 5 * q n / 8)
    (hℓb : 10 * (ℓ : ℤ) * (q n : ℤ) ≤ (q (n + 1) : ℤ))
    (hβ : (q (n + 1) : ℝ) ≤ Real.exp (β * (q n : ℝ)))
    (hc : 0 < c) (hc1 : c ≤ 1)
    (hθ : ∀ k : ℤ, |k| ≤ 4 * ((ℓ : ℤ) + 2) * (q n : ℤ) → c ≤ fracDist (2 * θ + (k : ℝ) * α))
    {j : ℤ} (hj : j ∈ resW (q n) h ℓ) {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    |∏ i ∈ (resW (q n) h ℓ).erase j,
        (x - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))) /
          (Real.cos (2 * Real.pi * (θ + (j : ℝ) * α)) - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α)))|
      < Real.exp ((2 * (q n : ℝ) - 1) *
          (β / 2 + β / (4 * (q n : ℝ) - 2) + 2 * Real.log (1 / c) / (q n : ℝ)
            + 200 * Real.log (q n : ℝ) / (q n : ℝ) + 200 / (q n : ℝ))) := by
  set W := resW (q n) h ℓ with hW
  have hΛ : (0 : ℝ) < 1 / c := by positivity
  by_cases hzero : ∃ i ∈ W.erase j, x - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α)) = 0
  · obtain ⟨i, hi, hiz⟩ := hzero
    have h1 : (∏ i ∈ W.erase j, (x - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))) /
        (Real.cos (2 * Real.pi * (θ + (j : ℝ) * α)) - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α)))) = 0 :=
      Finset.prod_eq_zero hi (by rw [hiz, zero_div])
    rw [h1, abs_zero]
    exact Real.exp_pos _
  · push_neg at hzero
    set a : ℝ := Real.arccos x / (2 * Real.pi) with ha
    have hxa : Real.cos (2 * Real.pi * a) = x := by
      have h2pi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
      calc Real.cos (2 * Real.pi * a) = Real.cos (Real.arccos x) := by
            congr 1
            rw [ha]
            field_simp
          _ = x := Real.cos_arccos hx.1 hx.2
    -- per-factor factorisations
    have hfacN : ∀ i : ℤ, |x - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))|
        = 2 * |Real.sin (Real.pi * (a + (θ + (i : ℝ) * α)))| *
            |Real.sin (Real.pi * (a - (θ + (i : ℝ) * α)))| := by
      intro i
      rw [← hxa, Real.cos_sub_cos]
      rw [show (2 * Real.pi * a + 2 * Real.pi * (θ + (i : ℝ) * α)) / 2
            = Real.pi * (a + (θ + (i : ℝ) * α)) by ring,
          show (2 * Real.pi * a - 2 * Real.pi * (θ + (i : ℝ) * α)) / 2
            = Real.pi * (a - (θ + (i : ℝ) * α)) by ring]
      rw [abs_mul, abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hfacD : ∀ i : ℤ,
        |Real.cos (2 * Real.pi * (θ + (j : ℝ) * α)) - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))|
        = 2 * |Real.sin (Real.pi * (2 * θ + (((i + j : ℤ)) : ℝ) * α))| *
            |Real.sin (Real.pi * (-(j : ℝ) * α + (i : ℝ) * α))| := by
      intro i
      rw [Real.cos_sub_cos]
      rw [show (2 * Real.pi * (θ + (j : ℝ) * α) + 2 * Real.pi * (θ + (i : ℝ) * α)) / 2
            = Real.pi * (2 * θ + (((i + j : ℤ)) : ℝ) * α) by push_cast; ring,
          show (2 * Real.pi * (θ + (j : ℝ) * α) - 2 * Real.pi * (θ + (i : ℝ) * α)) / 2
            = -(Real.pi * (-(j : ℝ) * α + (i : ℝ) * α)) by push_cast; ring]
      rw [Real.sin_neg, abs_mul, abs_mul, abs_neg, abs_neg,
        abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    -- non-vanishing of the sine factors
    have hsinN : ∀ i ∈ W.erase j, Real.sin (Real.pi * (a + (θ + (i : ℝ) * α))) ≠ 0 ∧
        Real.sin (Real.pi * (a - (θ + (i : ℝ) * α))) ≠ 0 := by
      intro i hi
      have h1 : 2 * |Real.sin (Real.pi * (a + (θ + (i : ℝ) * α)))|
          * |Real.sin (Real.pi * (a - (θ + (i : ℝ) * α)))| ≠ 0 := by
        rw [← hfacN i]
        exact (abs_pos.mpr (hzero i hi)).ne'
      constructor
      · intro h0; exact h1 (by rw [h0]; simp)
      · intro h0; exact h1 (by rw [h0]; simp)
    have hsinD : ∀ i ∈ W.erase j, Real.sin (Real.pi * (2 * θ + (((i + j : ℤ)) : ℝ) * α)) ≠ 0 ∧
        Real.sin (Real.pi * (-(j : ℝ) * α + (i : ℝ) * α)) ≠ 0 := by
      intro i hi
      rw [Finset.mem_erase] at hi
      have h3 : Real.cos (2 * Real.pi * (θ + (j : ℝ) * α))
          ≠ Real.cos (2 * Real.pi * (θ + (i : ℝ) * α)) :=
        res_cos_ne hqpos hmono hΔpos hΔeq hΔup hΔlo hbest hn hℓ hh hh' hℓb hc hθ
          (hW ▸ hj) (hW ▸ hi.2) (fun h => hi.1 h.symm)
      have h1 : 2 * |Real.sin (Real.pi * (2 * θ + (((i + j : ℤ)) : ℝ) * α))|
          * |Real.sin (Real.pi * (-(j : ℝ) * α + (i : ℝ) * α))| ≠ 0 := by
        rw [← hfacD i]
        exact (abs_pos.mpr (sub_ne_zero.mpr h3)).ne'
      constructor
      · intro h0; exact h1 (by rw [h0]; simp)
      · intro h0; exact h1 (by rw [h0]; simp)
    -- log of the product
    have hnum_ne : ∀ i ∈ W.erase j, x - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α)) ≠ 0 := hzero
    have hden_ne : ∀ i ∈ W.erase j,
        Real.cos (2 * Real.pi * (θ + (j : ℝ) * α)) - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α)) ≠ 0 := by
      intro i hi
      rw [Finset.mem_erase] at hi
      exact sub_ne_zero.mpr (res_cos_ne hqpos hmono hΔpos hΔeq hΔup hΔlo hbest hn hℓ hh hh' hℓb hc hθ
        (hW ▸ hj) (hW ▸ hi.2) (fun h => hi.1 h.symm))
    have hlog : Real.log |∏ i ∈ W.erase j,
          (x - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))) /
            (Real.cos (2 * Real.pi * (θ + (j : ℝ) * α)) - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α)))|
        = (∑ i ∈ W.erase j, Real.log |x - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))|)
          - (∑ i ∈ W.erase j,
              Real.log |Real.cos (2 * Real.pi * (θ + (j : ℝ) * α)) - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))|) := by
      rw [Finset.abs_prod]
      have h1 : ∏ i ∈ W.erase j,
            |(x - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))) /
              (Real.cos (2 * Real.pi * (θ + (j : ℝ) * α)) - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α)))|
          = (∏ i ∈ W.erase j, |x - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))|) /
            (∏ i ∈ W.erase j,
              |Real.cos (2 * Real.pi * (θ + (j : ℝ) * α)) - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))|) := by
        rw [Finset.prod_congr rfl (fun i hi => abs_div _ _), Finset.prod_div_distrib]
      have hN : (∏ i ∈ W.erase j, |x - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))|) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr (fun i hi => (abs_pos.mpr (hnum_ne i hi)).ne')
      have hD : (∏ i ∈ W.erase j,
          |Real.cos (2 * Real.pi * (θ + (j : ℝ) * α)) - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))|) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr (fun i hi => (abs_pos.mpr (hden_ne i hi)).ne')
      rw [h1, Real.log_div hN hD,
        Real.log_prod (fun i hi => (abs_pos.mpr (hnum_ne i hi)).ne'),
        Real.log_prod (fun i hi => (abs_pos.mpr (hden_ne i hi)).ne')]
    -- expansion of the two sums
    have htermN : ∀ i ∈ W.erase j, Real.log |x - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))|
        = Real.log 2 + (Real.log |Real.sin (Real.pi * (a + (θ + (i : ℝ) * α)))|
            + Real.log |Real.sin (Real.pi * (a - (θ + (i : ℝ) * α)))|) := by
      intro i hi
      have hs := (hsinN i hi).1
      have ht := (hsinN i hi).2
      have h1 : |x - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))|
          = 2 * (|Real.sin (Real.pi * (a + (θ + (i : ℝ) * α)))|
            * |Real.sin (Real.pi * (a - (θ + (i : ℝ) * α)))|) := by
        rw [hfacN i]; ring
      rw [h1, Real.log_mul (by norm_num) (mul_ne_zero (abs_ne_zero.mpr hs) (abs_ne_zero.mpr ht)),
        Real.log_mul (abs_ne_zero.mpr hs) (abs_ne_zero.mpr ht)]
      try ring
    have htermD : ∀ i ∈ W.erase j,
        Real.log |Real.cos (2 * Real.pi * (θ + (j : ℝ) * α)) - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))|
        = Real.log 2 + (Real.log |Real.sin (Real.pi * (2 * θ + (((i + j : ℤ)) : ℝ) * α))|
            + Real.log |Real.sin (Real.pi * (-(j : ℝ) * α + (i : ℝ) * α))|) := by
      intro i hi
      have hs := (hsinD i hi).1
      have ht := (hsinD i hi).2
      have h1 : |Real.cos (2 * Real.pi * (θ + (j : ℝ) * α)) - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))|
          = 2 * (|Real.sin (Real.pi * (2 * θ + (((i + j : ℤ)) : ℝ) * α))|
            * |Real.sin (Real.pi * (-(j : ℝ) * α + (i : ℝ) * α))|) := by
        rw [hfacD i]; ring
      rw [h1, Real.log_mul (by norm_num) (mul_ne_zero (abs_ne_zero.mpr hs) (abs_ne_zero.mpr ht)),
        Real.log_mul (abs_ne_zero.mpr hs) (abs_ne_zero.mpr ht)]
      try ring
    have hexpN : ∑ i ∈ W.erase j, Real.log |x - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))|
        = (W.erase j).card * Real.log 2 + ∑ i ∈ W.erase j,
            (Real.log |Real.sin (Real.pi * (a + (θ + (i : ℝ) * α)))|
              + Real.log |Real.sin (Real.pi * (a - (θ + (i : ℝ) * α)))|) := by
      rw [Finset.sum_congr rfl htermN, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    have hexpD : ∑ i ∈ W.erase j,
          Real.log |Real.cos (2 * Real.pi * (θ + (j : ℝ) * α)) - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))|
        = (W.erase j).card * Real.log 2 + ∑ i ∈ W.erase j,
            (Real.log |Real.sin (Real.pi * (2 * θ + (((i + j : ℤ)) : ℝ) * α))|
              + Real.log |Real.sin (Real.pi * (-(j : ℝ) * α + (i : ℝ) * α))|) := by
      rw [Finset.sum_congr rfl htermD, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    -- the four sums, in the shape of the four estimates
    have hS1 : ∑ i ∈ W.erase j,
            (Real.log |Real.sin (Real.pi * (a + (θ + (i : ℝ) * α)))|
              + Real.log |Real.sin (Real.pi * (a - (θ + (i : ℝ) * α)))|)
        = (∑ i ∈ W.erase j, Real.log |Real.sin (Real.pi * ((a + θ) + (i : ℝ) * α))|)
          + (∑ i ∈ W.erase j, Real.log |Real.sin (Real.pi * ((θ - a) + (i : ℝ) * α))|) := by
      rw [Finset.sum_add_distrib]
      congr 1
      · exact Finset.sum_congr rfl (fun i _ => by
          rw [show a + (θ + (i : ℝ) * α) = (a + θ) + (i : ℝ) * α by ring])
      · refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [show a - (θ + (i : ℝ) * α) = -((θ - a) + (i : ℝ) * α) by ring]
        rw [show Real.pi * -((θ - a) + (i : ℝ) * α) = -(Real.pi * ((θ - a) + (i : ℝ) * α)) by ring,
          Real.sin_neg, abs_neg]
    have hS2 : ∑ i ∈ W.erase j,
            (Real.log |Real.sin (Real.pi * (2 * θ + (((i + j : ℤ)) : ℝ) * α))|
              + Real.log |Real.sin (Real.pi * (-(j : ℝ) * α + (i : ℝ) * α))|)
        = (∑ i ∈ W.erase j, Real.log |Real.sin (Real.pi * (2 * θ + (j : ℝ) * α + (i : ℝ) * α))|)
          + (∑ i ∈ W.erase j, Real.log |Real.sin (Real.pi * (-(j : ℝ) * α + (i : ℝ) * α))|) := by
      rw [Finset.sum_add_distrib]
      congr 1
      exact Finset.sum_congr rfl (fun i _ => by
        rw [show 2 * θ + (((i + j : ℤ)) : ℝ) * α = 2 * θ + (j : ℝ) * α + (i : ℝ) * α by
          push_cast; ring])
    have hmain : Real.log |∏ i ∈ W.erase j,
          (x - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))) /
            (Real.cos (2 * Real.pi * (θ + (j : ℝ) * α)) - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α)))|
        = (∑ i ∈ W.erase j, Real.log |Real.sin (Real.pi * ((a + θ) + (i : ℝ) * α))|)
          + (∑ i ∈ W.erase j, Real.log |Real.sin (Real.pi * ((θ - a) + (i : ℝ) * α))|)
          - ((∑ i ∈ W.erase j, Real.log |Real.sin (Real.pi * (2 * θ + (j : ℝ) * α + (i : ℝ) * α))|)
            + (∑ i ∈ W.erase j, Real.log |Real.sin (Real.pi * (-(j : ℝ) * α + (i : ℝ) * α))|)) := by
      rw [hlog, hexpN, hS1, hexpD, hS2]
      ring
    -- the four estimates
    have hUp1 : ∑ i ∈ W.erase j, Real.log |Real.sin (Real.pi * ((a + θ) + (i : ℝ) * α))|
        ≤ -((2 : ℝ) * (q n : ℝ) - 2) * Real.log 2 + 16 * Real.log (q n : ℝ) := by
      refine res_sum_up hqpos hmono hΔpos hΔeq hΔup hΔlo hbest hn hℓ hh hh' hℓb
        (ξ := a + θ) (by rw [← hW]; exact hj) ?_
      intro k hk hne
      have hkW : resSite (q n) h ℓ k ∈ W.erase j := by
        rw [Finset.mem_erase]
        exact ⟨hne, by rw [hW]; exact (res_bij (qn := q n) (h := h) (ℓ := ℓ) hℓ hh hh').2.2.2.1 k hk⟩
      have hs := (hsinN (resSite (q n) h ℓ k) hkW).1
      rw [show (a + θ) + ((resSite (q n) h ℓ k : ℤ) : ℝ) * α
          = a + (θ + ((resSite (q n) h ℓ k : ℤ) : ℝ) * α) by ring]
      exact hs
    have hUp2 : ∑ i ∈ W.erase j, Real.log |Real.sin (Real.pi * ((θ - a) + (i : ℝ) * α))|
        ≤ -((2 : ℝ) * (q n : ℝ) - 2) * Real.log 2 + 16 * Real.log (q n : ℝ) := by
      refine res_sum_up hqpos hmono hΔpos hΔeq hΔup hΔlo hbest hn hℓ hh hh' hℓb
        (ξ := θ - a) (by rw [← hW]; exact hj) ?_
      intro k hk hne
      have hkW : resSite (q n) h ℓ k ∈ W.erase j := by
        rw [Finset.mem_erase]
        exact ⟨hne, by rw [hW]; exact (res_bij (qn := q n) (h := h) (ℓ := ℓ) hℓ hh hh').2.2.2.1 k hk⟩
      have hs := (hsinN (resSite (q n) h ℓ k) hkW).2
      intro h0
      apply hs
      have harg : Real.pi * (a - (θ + ((resSite (q n) h ℓ k : ℤ) : ℝ) * α))
          = -(Real.pi * ((θ - a) + ((resSite (q n) h ℓ k : ℤ) : ℝ) * α)) := by ring
      rw [harg, Real.sin_neg, h0, neg_zero]
    have hLo3 : -((2 : ℝ) * (q n : ℝ) - 2) * Real.log 2 - 16 * Real.log (q n : ℝ)
          + 2 * Real.log (2 * c)
        ≤ ∑ i ∈ W.erase j, Real.log |Real.sin (Real.pi * (2 * θ + (j : ℝ) * α + (i : ℝ) * α))| :=
      res_sum_low_theta hqpos hmono hΔpos hΔeq hΔup hΔlo hbest hn hℓ hh hh' hℓb hc hθ
        (by rw [← hW]; exact hj)
    have hLo4 : -((2 : ℝ) * (q n : ℝ) - 2) * Real.log 2 - 16 * Real.log (q n : ℝ)
          - β * (q n : ℝ)
        ≤ ∑ i ∈ W.erase j, Real.log |Real.sin (Real.pi * (-(j : ℝ) * α + (i : ℝ) * α))| :=
      res_sum_low_diff hqpos hmono hΔpos hΔeq hΔup hΔlo hbest hn hℓ hh hh' hℓb hβ
        (by rw [← hW]; exact hj)
    -- assemble
    have hmain : Real.log |∏ i ∈ W.erase j,
          (x - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))) /
            (Real.cos (2 * Real.pi * (θ + (j : ℝ) * α)) - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α)))|
        = (∑ i ∈ W.erase j, Real.log |Real.sin (Real.pi * ((a + θ) + (i : ℝ) * α))|)
          + (∑ i ∈ W.erase j, Real.log |Real.sin (Real.pi * ((θ - a) + (i : ℝ) * α))|)
          - ((∑ i ∈ W.erase j, Real.log |Real.sin (Real.pi * (2 * θ + (j : ℝ) * α + (i : ℝ) * α))|)
            + (∑ i ∈ W.erase j, Real.log |Real.sin (Real.pi * (-(j : ℝ) * α + (i : ℝ) * α))|)) := by
      rw [hlog, hexpN, hS1, hexpD, hS2]
      ring
    have hlogR : Real.log |∏ i ∈ W.erase j,
          (x - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))) /
            (Real.cos (2 * Real.pi * (θ + (j : ℝ) * α)) - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α)))|
        ≤ β * (q n : ℝ) + 64 * Real.log (q n : ℝ) + 2 * Real.log (1 / (2 * c)) := by
      have h1 : Real.log (1 / (2 * c)) = -Real.log (2 * c) := by rw [one_div, Real.log_inv]
      rw [hmain]
      have h2 := Real.log_pos (by norm_num : (1:ℝ) < 2)
      linarith [hUp1, hUp2, hLo3, hLo4]
    -- conclude
    have hq1 : (1 : ℝ) ≤ (q n : ℝ) := by exact_mod_cast hqpos n
    have harith := res_arith (β := β) (q := (q n : ℝ)) (c := c) hq1 hc hc1
    have hε : β / 2 + β / (4 * (q n : ℝ) - 2) + 2 * Real.log (1 / c) / (q n : ℝ)
          + 200 * Real.log (q n : ℝ) / (q n : ℝ) + 200 / (q n : ℝ)
        = β / 2 + β / (4 * (q n : ℝ) - 2) + 2 * Real.log (1 / c) / (q n : ℝ)
          + 200 * Real.log (q n : ℝ) / (q n : ℝ) + 200 / (q n : ℝ) := rfl
    have hpos : 0 < |∏ i ∈ W.erase j,
          (x - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))) /
            (Real.cos (2 * Real.pi * (θ + (j : ℝ) * α)) - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α)))| := by
      rw [Finset.abs_prod]
      refine Finset.prod_pos (fun i hi => ?_)
      rw [abs_div]
      exact div_pos (abs_pos.mpr (hnum_ne i hi)) (abs_pos.mpr (hden_ne i hi))
    have hkey : Real.log |∏ i ∈ W.erase j,
          (x - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))) /
            (Real.cos (2 * Real.pi * (θ + (j : ℝ) * α)) - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α)))|
        ≤ (2 * (q n : ℝ) - 1) *
          (β / 2 + β / (4 * (q n : ℝ) - 2) + 2 * Real.log (1 / c) / (q n : ℝ)
            + 200 * Real.log (q n : ℝ) / (q n : ℝ) + 200 / (q n : ℝ)) - 1 := by
      nlinarith [harith, hlogR]
    calc |∏ i ∈ W.erase j,
          (x - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))) /
            (Real.cos (2 * Real.pi * (θ + (j : ℝ) * α)) - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α)))|
        = Real.exp (Real.log |∏ i ∈ W.erase j,
          (x - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))) /
            (Real.cos (2 * Real.pi * (θ + (j : ℝ) * α)) - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α)))|) :=
          (Real.exp_log hpos).symm
      _ ≤ Real.exp ((2 * (q n : ℝ) - 1) *
          (β / 2 + β / (4 * (q n : ℝ) - 2) + 2 * Real.log (1 / c) / (q n : ℝ)
            + 200 * Real.log (q n : ℝ) / (q n : ℝ) + 200 / (q n : ℝ)) - 1) :=
          Real.exp_le_exp.mpr hkey
      _ < Real.exp ((2 * (q n : ℝ) - 1) *
          (β / 2 + β / (4 * (q n : ℝ) - 2) + 2 * Real.log (1 / c) / (q n : ℝ)
            + 200 * Real.log (q n : ℝ) / (q n : ℝ) + 200 / (q n : ℝ))) := by
          apply Real.exp_lt_exp.mpr
          linarith
theorem uni_res5 {α β : ℝ} {q : ℕ → ℕ} {Δ : ℕ → ℝ} {n h ℓ : ℕ} {θ c : ℝ}
    (hqpos : ∀ m, 0 < q m) (hmono : StrictMono q)
    (hΔpos : ∀ m, 0 < Δ m)
    (hΔeq : ∀ m, Δ m = Work.TMC16Core.fracDist ((q m : ℝ) * α))
    (hΔup : ∀ m, Δ m < 1 / ((q (m + 1) : ℝ)))
    (hΔlo : ∀ m, 1 / (((q (m + 1) : ℝ)) + (q m : ℝ)) < Δ m)
    (hbest : ∀ m k : ℕ, q m ≤ k → k < q (m + 1) → Δ m ≤ Work.TMC16Core.fracDist ((k : ℝ) * α))
    (hβ0 : 0 ≤ β)
    (hn : 2 ≤ n) (hℓ : 1 ≤ ℓ) (hh : 3 * q n / 5 ≤ h) (hh' : h ≤ 5 * q n / 8)
    (hℓb : 10 * (ℓ : ℤ) * (q n : ℤ) ≤ (q (n + 1) : ℤ))
    (hβ : (q (n + 1) : ℝ) ≤ Real.exp (β * (q n : ℝ)))
    (hc : 0 < c)
    (hθ : ∀ k : ℤ, |k| ≤ 4 * ((ℓ : ℤ) + 2) * (q n : ℤ) →
      c ≤ Work.TMC16Core.fracDist (2 * θ + (k : ℝ) * α))
    (hcoll : ∀ j ∈ Work.TMC16Core.Core.J1resG h ∪ Work.TMC16Core.Core.J2resG (q n) h ℓ,
      -β * (q n : ℝ) - 10 ≤
        ∑ i ∈ (Work.TMC16Core.Core.J1resG h ∪ Work.TMC16Core.Core.J2resG (q n) h ℓ).filter
            (fun i => i ≠ j ∧ (q n : ℤ) ∣ (i - j)),
          Real.log |Real.sin (Real.pi * (((i - j : ℤ)) : ℝ) * α)|) :
    Work.TMC16Core.Uniform (β / 2 + β / (4 * (q n : ℝ) - 2)
        + 2 * Real.log (1 / c) / (q n : ℝ)
        + 200 * Real.log (q n : ℝ) / (q n : ℝ) + 200 / (q n : ℝ))
      (fun j : {j : ℤ // j ∈ Work.TMC16Core.Core.J1resG h ∪
          Work.TMC16Core.Core.J2resG (q n) h ℓ} =>
        θ + (j : ℝ) * α) := by
  have hn1 : 1 ≤ n := by omega
  have hc1 : c ≤ 1 := by
    have h0 := hθ 0 (by
      rw [abs_zero]
      have hq0 : (0 : ℤ) ≤ (q n : ℤ) := by positivity
      have hl0 : (0 : ℤ) ≤ (ℓ : ℤ) + 2 := by omega
      nlinarith [hq0, hl0])
    have h1 : Work.TMC16Core.fracDist (2 * θ + ((0 : ℤ) : ℝ) * α) ≤ 1 / 2 := by
      rw [Int.cast_zero, zero_mul, add_zero]
      exact abs_sub_round (2 * θ)
    exact le_trans (le_trans h0 h1) (by norm_num)
  have hcardit : Fintype.card {k : ℤ // k ∈ Work.TMC16Core.Core.J1resG h ∪
      Work.TMC16Core.Core.J2resG (q n) h ℓ} = 2 * q n := by
    show Fintype.card {k : ℤ // k ∈ resW (q n) h ℓ} = 2 * q n
    rw [Fintype.card_coe]
    exact (res_card (qn := q n) (h := h) (ℓ := ℓ) hℓ hh hh').2.2.1
  have hexp : ((Fintype.card {k : ℤ // k ∈ Work.TMC16Core.Core.J1resG h ∪
      Work.TMC16Core.Core.J2resG (q n) h ℓ} : ℝ) - 1) = (2 * (q n : ℝ) - 1) := by
    rw [hcardit]
    push_cast
    ring
  rw [Work.TMC16Core.Uniform]
  refine ⟨?_, ?_⟩
  · intro i j hij hcon
    exact res_cos_ne (q := q) (Δ := Δ) (n := n) (h := h) (ℓ := ℓ) (θ := θ) (c := c)
      hqpos hmono hΔpos hΔeq hΔup hΔlo hbest hn1 hℓ hh hh' hℓb hc hθ
      (show (i : ℤ) ∈ resW (q n) h ℓ from i.property)
      (show (j : ℤ) ∈ resW (q n) h ℓ from j.property)
      (fun hEq => hij (Subtype.ext hEq)) hcon
  · intro j x hx
    have hprod : (∏ i ∈ Finset.univ.erase j,
          (x - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))) /
            (Real.cos (2 * Real.pi * (θ + (j : ℝ) * α)) - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))))
        = ∏ i ∈ (resW (q n) h ℓ).erase (j : ℤ),
          (x - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))) /
            (Real.cos (2 * Real.pi * (θ + (j : ℝ) * α)) - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))) := by
      refine Finset.prod_bij (fun (i : {k : ℤ // k ∈ Work.TMC16Core.Core.J1resG h ∪
          Work.TMC16Core.Core.J2resG (q n) h ℓ}) _ => (i : ℤ)) ?_ ?_ ?_ ?_
      · intro i hi
        rw [Finset.mem_erase] at hi ⊢
        exact ⟨fun hEq => hi.1 (Subtype.ext hEq), i.property⟩
      · intro i _ i' _ hEq
        exact Subtype.ext hEq
      · intro b hb
        rw [Finset.mem_erase] at hb
        refine ⟨⟨b, hb.2⟩, ?_, rfl⟩
        rw [Finset.mem_erase]
        exact ⟨fun hEq => hb.1 (congrArg Subtype.val hEq), Finset.mem_univ _⟩
      · intro i _
        rfl
    rw [hprod, hexp]
    exact res_bound (q := q) (Δ := Δ) (n := n) (h := h) (ℓ := ℓ) (θ := θ) (c := c)
      (β := β) hqpos hmono hΔpos hΔeq hΔup hΔlo hbest hn1 hℓ hh hh' hℓb hβ hc hc1 hθ
      (show (j : ℤ) ∈ resW (q n) h ℓ from j.property) hx

end

end Work.TMC16Core.Core
