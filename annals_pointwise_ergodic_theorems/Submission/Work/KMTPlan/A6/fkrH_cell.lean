import Mathlib
import Submission.Work.KMTPlan.A6.FkrBasic

namespace Work.KMTPlan.A6

/-- **The cell identity for `fkrH`.**  If `β` is monotone with `β 0 ≥ 0`, `β K = 1` and
`s ∈ [β (j-1), β j]` with `1 ≤ j ≤ K`, then `fkrH` has constant slope `w j x` on the `j`-th cell:
the increment from the node `β (j-1)` to the point `s` is `w j x * (s - β (j-1))`.

Indeed, for `k ≠ j` the two quantities `fkrPhi β k s` and `fkrPhi β k (β (j-1))` agree (both
arguments lie on the same side of the block `(β (k-1), β k]`), while for `k = j` the difference
is exactly `s - β (j-1)`. -/
lemma fkrH_cell {X : Type*} [MeasurableSpace X] {K : ℕ} {β : ℕ → ℝ} {w : ℕ → X → ℂ} {x : X}
    (hβ0 : 0 ≤ β 0) (hβmono : Monotone β) (hβK : β K = 1)
    {j : ℕ} (hj1 : 1 ≤ j) (hjK : j ≤ K) {s : ℝ} (hs0 : 0 ≤ s)
    (hsl : β (j - 1) ≤ s) (hsr : s ≤ β j) :
    Work.KMTPlan.A6.fkrH K β w x s - Work.KMTPlan.A6.fkrH K β w x (β (j - 1))
      = w j x * ((s - β (j - 1) : ℝ) : ℂ) := by
  -- `s` and `β (j-1)` both lie in `[0,1]`, so the clamping in `fkrPhi` is inactive.
  have hs1 : s ≤ 1 := le_trans hsr (le_trans (hβmono hjK) (le_of_eq hβK))
  have hj1m : 0 ≤ β (j - 1) := le_trans hβ0 (hβmono (Nat.zero_le _))
  have hbj1_le_1 : β (j - 1) ≤ 1 := le_trans hsl hs1
  -- The cell computation: only the `j`-th summand survives.
  have key : ∀ k ∈ Finset.Icc 1 K,
      fkrPhi β k s - fkrPhi β k (β (j - 1)) = if k = j then s - β (j - 1) else 0 := by
    intro k hk
    simp only [Finset.mem_Icc] at hk
    rw [fkrPhi_le β k hs0 hs1, fkrPhi_le β k hj1m hbj1_le_1]
    by_cases h : k = j
    · subst h
      rw [if_pos rfl]
      simp only [min_eq_left hsr, min_eq_right hsl,
        min_eq_left (hβmono (Nat.sub_le k 1)), min_eq_right (le_refl (β (k - 1)))]
      ring
    · rw [if_neg h]
      rcases lt_or_gt_of_ne h with hlt | hgt
      · -- `k < j`: both `s` and `β (j-1)` are to the right of the `k`-th block.
        have hkm : k ≤ j - 1 := by omega
        simp only [min_eq_right (le_trans (hβmono hkm) hsl),
          min_eq_right (le_trans (hβmono (by omega : k - 1 ≤ j - 1)) hsl),
          min_eq_right (hβmono hkm), min_eq_right (hβmono (by omega : k - 1 ≤ j - 1))]
        ring
      · -- `j < k`: both `s` and `β (j-1)` are to the left of the `k`-th block.
        have hjm : j ≤ k - 1 := by omega
        simp only [min_eq_left (le_trans hsr (hβmono (by omega : j ≤ k))),
          min_eq_left (le_trans hsr (hβmono hjm)),
          min_eq_left (hβmono (by omega : j - 1 ≤ k)),
          min_eq_left (hβmono (by omega : j - 1 ≤ k - 1))]
        ring
  have hsum : ∑ k ∈ Finset.Icc 1 K, (w k x * ((fkrPhi β k s : ℝ) : ℂ)
      - w k x * ((fkrPhi β k (β (j - 1)) : ℝ) : ℂ))
      = ∑ k ∈ Finset.Icc 1 K, (if k = j then w j x * ((s - β (j - 1) : ℝ) : ℂ) else 0) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [← mul_sub, ← Complex.ofReal_sub, key k hk]
    by_cases h : k = j
    · subst h; rw [if_pos rfl, if_pos rfl]
    · rw [if_neg h, if_neg h, Complex.ofReal_zero, mul_zero]
  rw [fkrH, fkrH, ← Finset.sum_sub_distrib, hsum, Finset.sum_ite_eq']
  rw [if_pos (Finset.mem_Icc.mpr ⟨hj1, hjK⟩)]

end Work.KMTPlan.A6
