import Mathlib
import Submission.Work.TMComp.C7Aux.rtlSchedule
import Submission.Work.TMComp.C7Aux.rtl_run_le

/-!
# Counting the visits of a fixed index in the rational-tower schedule

`rtl_card_le` bounds the number of times `t < S` at which the index `rtli A cκ Q k N₀ t` of the
`(scale, index)` recursion `rtlU` (`rtlSchedule`) equals a prescribed value `i < k`.

The mathematics: the index function `rtli` is non-decreasing (`rtli_mono`), so the set of times at
which it takes a prescribed value is a contiguous block of integers.  On such a block the run-length
estimate `rtl_run_le` (proved in `rtl_run_le`) says that a block on which `rtli = i < k` spans fewer
than `4b/cκ` steps.  Hence such a block has at most `Sb` elements, as soon as `4b/cκ < Sb`.
-/

namespace Work.TMComp.C7Aux

theorem rtl_card_le (A cκ b : ℝ) (Q : ℕ → ℕ) (k N₀ : ℕ) (Sb : ℕ)
    (hA : 0 < A) (hcκ : 0 < cκ) (hb : 0 < b)
    (hQ1 : ∀ i ≤ k, 1 ≤ Q i)
    (hgrowth : ∀ i < k, (Q (i+1) : ℝ) ≤ Real.exp (b * (Q i : ℝ)))
    (hA0 : A * (Q 0 : ℝ) ≤ (N₀ : ℝ))
    (hbig : ∀ i ≤ k, Real.log 10 ≤ cκ * (Q i : ℝ) / 4)
    (hbig2 : ∀ i ≤ k, 2 ≤ Real.exp (cκ * (Q i : ℝ) / 2) / (5 * (Q i : ℝ)))
    (hSb : 4 * b / cκ < Sb)
    {i : ℕ} (hik : i < k) (S : ℕ) :
    ((Finset.range S).filter (fun t => Work.TMComp.C7Aux.rtli A cκ Q k N₀ t = i)).card ≤ Sb := by
  let T : Finset ℕ := (Finset.range S).filter (fun t => rtli A cκ Q k N₀ t = i)
  change T.card ≤ Sb
  by_cases hne : T.Nonempty
  · -- the set of times with index `i` is nonempty: it is a block `[min, max]`
    have hmin : T.min' hne ∈ T := Finset.min'_mem T hne
    have hmax : T.max' hne ∈ T := Finset.max'_mem T hne
    have hmn : T.min' hne ≤ T.max' hne := Finset.min'_le T _ hmax
    have hi1 : rtli A cκ Q k N₀ (T.min' hne) = i := (Finset.mem_filter.mp hmin).2
    have hi2 : rtli A cκ Q k N₀ (T.max' hne) = i := (Finset.mem_filter.mp hmax).2
    -- run-length estimate for the block
    have hgap := rtl_run_le A cκ b Q k N₀ hA hcκ hb hQ1 hgrowth hA0 hbig hbig2 hik hi1 hi2 hmn
    have hgapC : ((T.max' hne : ℝ) - (T.min' hne : ℝ)) * cκ < 4 * b := by nlinarith [hgap]
    have hSb' : 4 * b < (Sb : ℝ) * cκ := (div_lt_iff₀ hcκ).mp hSb
    have hreal : ((T.max' hne : ℝ) - (T.min' hne : ℝ)) < (Sb : ℝ) :=
      lt_of_mul_lt_mul_right (lt_trans hgapC hSb') (le_of_lt hcκ)
    -- convert to a strict bound of natural numbers
    have hnat : T.max' hne - T.min' hne < Sb := by
      have hreal' : ((T.max' hne - T.min' hne : ℕ) : ℝ) < (Sb : ℝ) := by
        rw [Nat.cast_sub hmn]
        exact hreal
      exact_mod_cast hreal'
    -- the block is contained in the interval `[min, max]`
    have hsub : T ⊆ Finset.Icc (T.min' hne) (T.max' hne) := by
      intro t ht
      exact Finset.mem_Icc.mpr ⟨Finset.min'_le T t ht, Finset.le_max' T t ht⟩
    have hcard : T.card ≤ (Finset.Icc (T.min' hne) (T.max' hne)).card := Finset.card_le_card hsub
    have hIcc : (Finset.Icc (T.min' hne) (T.max' hne)).card
        = T.max' hne + 1 - T.min' hne := by simp
    omega
  · have h0 : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simp [h0]

end Work.TMComp.C7Aux
