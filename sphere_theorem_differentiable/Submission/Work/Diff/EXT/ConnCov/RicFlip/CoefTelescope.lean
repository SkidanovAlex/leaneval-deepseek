import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `Work.Diff.EXT.ConnCov.RicFlip.CoefTelescope`

The coefficient telescoping identity used in the expansion of the tower `pD^k`
(`RicFlip/towerExpansionSm.lean`).  Writing `c k = (-1)^(m+1+k) (m+1-k)!` for the coefficient of
the `k`-th term of the left sum, the relations `T 0 = Sh 0`, `T (k+1) = Ins k + Sh (k+1)` and
`Sh (m+1) = 0` give

`Σ_{k ≤ m+1} c k · T k = Σ_{j ≤ m} (-1)^(m+j) (m-j)! · (Ins j - (m-j+1) Sh j)`,

i.e. the "top" term `Sh (m+1)` disappears exactly against the coefficient telescoping
`c (k+1) = (-1)^(m+k) (m-k)!` (`coeff_succ`), the identity `(m-j)! (m-j+1) = (m-j+1)!`
(`fac_shift_sum`) and the telescoping of the sequence `a j = (-1)^(m+j) (m-j+1)! Sh j`.
-/

namespace Work.Diff.EXT.ConnCov.RicFlip

/-- The `k`-th coefficient of the left sum: `c (k+1) = (-1)^(m+k) (m-k)!`. -/
private lemma coeff_succ (m k : ℕ) :
    ((-1 : ℝ) ^ ((m + 1) + (k + 1)) * (((m + 1) - (k + 1)).factorial : ℝ))
      = (-1 : ℝ) ^ (m + k) * ((m - k).factorial : ℝ) := by
  have h1 : m + 1 - (k + 1) = m - k := Nat.add_sub_add_right m 1 k
  have h2 : m + 1 + (k + 1) = (m + k) + 2 := by omega
  rw [h1, h2, pow_add]
  norm_num

/-- Termwise telescoping step: for `k ≤ m` the `k`-th `d`-term and the `(k+1)`-st `a`-term cancel.
At `k = m` this uses `Sh (m+1) = 0`. -/
private lemma shift_term (m k : ℕ) (Sh : ℕ → ℝ) (hk : k ≤ m) (htop : Sh (m + 1) = 0) :
    (-1 : ℝ) ^ (m + k) * ((m - k).factorial : ℝ) * Sh (k + 1)
      + (-1 : ℝ) ^ (m + (k + 1)) * ((((m - (k + 1)) + 1).factorial : ℝ)) * Sh (k + 1) = 0 := by
  rcases eq_or_lt_of_le hk with h | h
  · subst h; simp [htop]
  · have h1 : (m - (k + 1)) + 1 = m - k := by omega
    have h2 : m + (k + 1) = (m + k) + 1 := by omega
    rw [h1, h2, show (-1 : ℝ) ^ ((m + k) + 1) = (-1 : ℝ) ^ (m + k) * (-1) from pow_succ _ _]
    ring

/-- `(m-j)! · (m-j+1) = (m-j+1)!` (the coefficient of `Sh j` in the right sum). -/
private lemma fac_shift_sum (m j : ℕ) (Sh : ℕ → ℝ) :
    (((-1 : ℝ) ^ (m + j) * ((m - j).factorial : ℝ)) * (((m - j + 1 : ℕ) : ℝ))) * Sh j
      = (-1 : ℝ) ^ (m + j) * (((m - j + 1).factorial : ℝ)) * Sh j := by
  rw [Nat.factorial_succ (m - j)]
  push_cast
  ring

theorem CoefTelescope (m : ℕ) (Ins Sh T : ℕ → ℝ)
    (hT0 : T 0 = Sh 0)
    (hT : ∀ k, T (k + 1) = Ins k + Sh (k + 1))
    (hShtop : Sh (m + 1) = 0) :
    (∑ k ∈ Finset.range (m + 2),
        ((-1 : ℝ) ^ ((m + 1) + k) * (((m + 1) - k).factorial : ℝ)) * T k)
      = ∑ j ∈ Finset.range (m + 1),
          ((-1 : ℝ) ^ (m + j) * ((m - j).factorial : ℝ))
            * (Ins j - (((m - j + 1 : ℕ) : ℝ)) * Sh j) := by
  -- Abbreviations for the four partial sums and the two end terms.
  set U : ℝ := ∑ k ∈ Finset.range (m + 1),
        (-1 : ℝ) ^ (m + k) * ((m - k).factorial : ℝ) * (Ins k + Sh (k + 1)) with hU
  set S : ℝ := ∑ k ∈ Finset.range (m + 1),
        (-1 : ℝ) ^ (m + k) * ((m - k).factorial : ℝ) * Ins k with hS
  set Y : ℝ := ∑ k ∈ Finset.range (m + 1),
        (-1 : ℝ) ^ (m + k) * ((m - k).factorial : ℝ) * Sh (k + 1) with hY
  set Z : ℝ := ∑ j ∈ Finset.range (m + 1),
        (((-1 : ℝ) ^ (m + j) * ((m - j).factorial : ℝ))) * (((m - j + 1 : ℕ) : ℝ)) * Sh j with hZ
  set W : ℝ := ∑ j ∈ Finset.range (m + 1),
        (-1 : ℝ) ^ (m + j) * (((m - j + 1).factorial : ℝ)) * Sh j with hW
  set V : ℝ := ∑ k ∈ Finset.range (m + 1),
        (-1 : ℝ) ^ (m + (k + 1)) * ((((m - (k + 1)) + 1).factorial : ℝ)) * Sh (k + 1) with hV
  set P : ℝ := ((-1 : ℝ) ^ (m + 1) * (((m + 1).factorial : ℝ))) * Sh 0 with hP
  set P0 : ℝ := (-1 : ℝ) ^ (m + 0) * (((m - 0 + 1).factorial : ℝ)) * Sh 0 with hP0
  -- Step 1: peel `k = 0` off the left sum and substitute `T`.
  have hL : (∑ k ∈ Finset.range (m + 2),
        ((-1 : ℝ) ^ ((m + 1) + k) * (((m + 1) - k).factorial : ℝ)) * T k) = P + U := by
    rw [hP, hU, Finset.sum_range_succ']
    have hsum : (∑ k ∈ Finset.range (m + 1),
          ((-1 : ℝ) ^ ((m + 1) + (k + 1)) * (((m + 1) - (k + 1)).factorial : ℝ)) * T (k + 1))
        = ∑ k ∈ Finset.range (m + 1),
            (-1 : ℝ) ^ (m + k) * ((m - k).factorial : ℝ) * (Ins k + Sh (k + 1)) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [hT k, coeff_succ]
    have hc0 : ((-1 : ℝ) ^ ((m + 1) + 0) * (((m + 1) - 0).factorial : ℝ)) * T 0
        = ((-1 : ℝ) ^ (m + 1) * (((m + 1).factorial : ℝ))) * Sh 0 := by
      rw [hT0]; simp
    rw [hsum, hc0]
    ring
  -- Step 2: split the `Ins` and `Sh` parts of the left sum.
  have hU2 : U = S + Y := by
    rw [hU, hS, hY, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  -- Step 3: split the right sum.
  have hR2 : (∑ j ∈ Finset.range (m + 1),
          ((-1 : ℝ) ^ (m + j) * ((m - j).factorial : ℝ))
            * (Ins j - (((m - j + 1 : ℕ) : ℝ)) * Sh j)) = S - Z := by
    rw [hS, hZ, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  -- Step 4: `Y = -V` (the shifted sequence), termwise.
  have hYV : Y = -V := by
    rw [hY, hV, eq_neg_iff_add_eq_zero, ← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro k hk
    exact shift_term m k Sh (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)) hShtop
  -- Step 5: `Z = W` (factorial shift).
  have hZW : Z = W := by
    rw [hZ, hW]
    apply Finset.sum_congr rfl
    intro j _
    exact fac_shift_sum m j Sh
  -- Step 6: the telescoping `W - V = P0`.
  have htel : W - V = P0 := by
    rw [hW, hV, hP0, ← Finset.sum_sub_distrib, Finset.sum_range_sub']
    simp [hShtop]
  -- Step 7: the boundary terms cancel.
  have hA0 : P + P0 = 0 := by
    rw [hP, hP0]
    have h1 : m - 0 + 1 = m + 1 := by omega
    rw [h1, show m + 0 = m from rfl,
      show (-1 : ℝ) ^ (m + 1) = (-1 : ℝ) ^ m * (-1) from pow_succ _ _]
    ring
  rw [hL, hU2, hR2, hYV, hZW]
  have h1 : W = P0 + V := by linarith [htel]
  have h2 : P = -P0 := by linarith [hA0]
  rw [h1, h2]
  ring

end Work.Diff.EXT.ConnCov.RicFlip
