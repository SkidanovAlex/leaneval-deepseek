import Mathlib
import Submission.Work.TMC16Core.Core.blk_sep_base
import Submission.Work.TMC16Core.Core.uni_nonres3_havoid
import Submission.Work.TMC16Core.Defs

namespace Work.TMC16Core.NrFinal

open Work.TMC16Core

/-- **Separation at scale `n`, for a natural index `j`.**

With the continued-fraction package `(q, Δ)` (positivity, strict monotonicity, the sandwich
`1/(q(k+1)+q k) < Δ k < 1/q(k+1)` and the best-approximation property on the blocks
`[q k, q(k+1))`), every `1 ≤ j < q n` satisfies `fracDist (j * α) ≥ 1/(2 q n)`.

Two cases: if `j < q 0` this is exactly the base separation `blk_sep_base` (and
`1/(2 q n) ≤ 1/(2 q 0)`); if `j ≥ q 0`, the block `[q m, q(m+1))` containing `j` has `m < n`,
so the best-approximation bound `Δ m ≤ fracDist (j * α)` and the lower sandwich for `Δ m`
give `fracDist (j * α) ≥ Δ m > 1/(q(m+1) + q m) > 1/(2 q n)`. -/
theorem sep_small_nat {α : ℝ} {q : ℕ → ℕ} {Δ : ℕ → ℝ} {n : ℕ}
    (hqpos : ∀ i, 0 < q i) (hmono : StrictMono q) (hΔpos : ∀ i, 0 < Δ i)
    (hΔeq : ∀ i, Δ i = fracDist ((q i : ℝ) * α))
    (hΔup : ∀ i, Δ i < 1 / ((q (i + 1) : ℝ)))
    (hΔlo : ∀ i, 1 / (((q (i + 1) : ℝ)) + (q i : ℝ)) < Δ i)
    (hbest : ∀ i j : ℕ, q i ≤ j → j < q (i + 1) → Δ i ≤ fracDist ((j : ℝ) * α))
    {j : ℕ} (hj1 : 1 ≤ j) (hjn : j < q n) :
    1 / (2 * (q n : ℝ)) ≤ fracDist ((j : ℝ) * α) := by
  rcases lt_or_ge j (q 0) with hsmall | hsmall
  · -- Base scale: `j < q 0`; use the already-established base separation.
    have hb := Work.TMC16Core.Core.blk_sep_base hqpos hmono hΔpos hΔeq hΔup hΔlo hbest j hj1 hsmall
    have hq0n : q 0 ≤ q n := hmono.monotone (Nat.zero_le n)
    have hq0nR : (q 0 : ℝ) ≤ (q n : ℝ) := by exact_mod_cast hq0n
    have hq0pos : (0 : ℝ) < (q 0 : ℝ) := by exact_mod_cast hqpos 0
    have hle : 1 / (2 * (q n : ℝ)) ≤ 1 / (2 * (q 0 : ℝ)) :=
      one_div_le_one_div_of_le (a := 2 * (q 0 : ℝ)) (b := 2 * (q n : ℝ))
        (by linarith) (by linarith)
    linarith
  · -- `q 0 ≤ j`; find the block `[q m, q(m+1))` containing `j`.
    obtain ⟨m, hm1, hm2⟩ := Work.TMC16Core.Core.exists_block hmono hsmall
    have hmn : m < n := by
      by_contra h
      have hnm : n ≤ m := by omega
      have hq : q n ≤ q m := hmono.monotone hnm
      omega
    have hbestm := hbest m j hm1 hm2
    have hlom := hΔlo m
    have hqmp1n : (q (m + 1) : ℝ) ≤ (q n : ℝ) := by
      exact_mod_cast hmono.monotone (by omega : m + 1 ≤ n)
    have hqm_lt : (q m : ℝ) < (q (m + 1) : ℝ) := by
      exact_mod_cast hmono (Nat.lt_succ_self m)
    have hpos : 0 < (q (m + 1) : ℝ) + (q m : ℝ) := by
      have h1 : (0 : ℝ) < (q (m + 1) : ℝ) := by exact_mod_cast hqpos (m + 1)
      have h2 : (0 : ℝ) < (q m : ℝ) := by exact_mod_cast hqpos m
      linarith
    have hlt : (q (m + 1) : ℝ) + (q m : ℝ) < 2 * (q n : ℝ) := by linarith
    have hkey : 1 / (2 * (q n : ℝ)) < 1 / ((q (m + 1) : ℝ) + (q m : ℝ)) :=
      one_div_lt_one_div_of_lt hpos hlt
    linarith

theorem sep_small {α : ℝ} {q : ℕ → ℕ} {Δ : ℕ → ℝ} {n : ℕ}
    (hqpos : ∀ i, 0 < q i) (hmono : StrictMono q) (hΔpos : ∀ i, 0 < Δ i)
    (hΔeq : ∀ i, Δ i = Work.TMC16Core.fracDist ((q i : ℝ) * α))
    (hΔup : ∀ i, Δ i < 1 / ((q (i + 1) : ℝ)))
    (hΔlo : ∀ i, 1 / (((q (i + 1) : ℝ)) + (q i : ℝ)) < Δ i)
    (hbest : ∀ i j : ℕ, q i ≤ j → j < q (i + 1) → Δ i ≤ Work.TMC16Core.fracDist ((j : ℝ) * α))
    {d : ℤ} (hd : d ≠ 0) (hdn : |d| < (q n : ℤ)) :
    1 / (2 * (q n : ℝ)) ≤ Work.TMC16Core.fracDist ((d : ℝ) * α) := by
  set m : ℕ := d.natAbs with hm
  have habs : (m : ℤ) = |d| := by rw [hm]; exact (Int.abs_eq_natAbs d).symm
  have hmpos : 0 < m := by rw [hm]; exact Int.natAbs_pos.mpr hd
  have hm1 : 1 ≤ m := hmpos
  have hm_lt : m < q n := by
    have h2 : (m : ℤ) < (q n : ℤ) := by rw [habs]; exact hdn
    exact_mod_cast h2
  have hm_cast : (m : ℝ) = |(d : ℝ)| := by
    calc (m : ℝ) = ((m : ℤ) : ℝ) := by simp
      _ = ((|d| : ℤ) : ℝ) := by rw [habs]
      _ = |(d : ℝ)| := Int.cast_abs
  have hfd : Work.TMC16Core.fracDist ((d : ℝ) * α) = Work.TMC16Core.fracDist ((m : ℝ) * α) := by
    rw [hm_cast]
    rcases lt_or_ge (d : ℝ) 0 with hneg | hpos
    · rw [abs_of_neg hneg]
      have hring : -(d : ℝ) * α = -((d : ℝ) * α) := by ring
      rw [hring, Work.TMC16Core.Core.fracDist_neg]
    · rw [abs_of_nonneg hpos]
  rw [hfd]
  exact sep_small_nat hqpos hmono hΔpos hΔeq hΔup hΔlo hbest hm1 hm_lt

end Work.TMC16Core.NrFinal
