import Mathlib
import Submission.Work.SG.ApplyBDefs
import Submission.Work.SG.applyB_range
import Submission.Work.SG.RepCoh_blk
import Submission.Work.SG.cobstepAux.blk_sub3_dvd

/-!
# `Work.SG.cobstepAux.applyB_cong3`

`Data.applyB B y` is the right fold `(List.zipWith M3.mulV B (blocks y)).foldr V3.add 0`, i.e. the
blockwise linear expression `∑_{g < k} B_g *ᵥ (blocks y)_g`.  If the coordinatewise difference
`y1 - y2 - y3` is divisible by `n` on the first `3 * k` coordinates, then the same difference of
the three `applyB` results is divisible by `n` in each coordinate: `applyB` only reads those
coordinates and is `ℤ`-linear in them.

The proof rewrites each `applyB` as a `Finset`-sum over the block index (`applyB_range_blocks_gen`),
pulls the coordinate out of the sum (`Finset.sum_apply`), distributes the subtraction over the
sum (`Finset.sum_sub_distrib`) and applies the per-block step `blk_sub3_dvd` to each summand
(`Finset.dvd_sum`).
-/

namespace Work.SG.cobstepAux

open Work.SG

/-- A list of length `3 * k` has exactly `k` blocks. -/
theorem blocks_len_of_len (y : List ℤ) {k : ℕ} (h : y.length = 3 * k) :
    (Work.SG.Data.blocks y).length = k := by
  rw [Work.SG.blocks_length, h]
  omega

/-- A finite sum of pointwise divisible triples is divisible. -/
theorem dvd_sum_sub3 {ι : Type*} (s : Finset ι) (n : ℤ) (f1 f2 f3 : ι → ℤ)
    (h : ∀ g ∈ s, n ∣ f1 g - f2 g - f3 g) :
    n ∣ (∑ g ∈ s, f1 g) - (∑ g ∈ s, f2 g) - (∑ g ∈ s, f3 g) := by
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  exact Finset.dvd_sum h

theorem applyB_cong3 (B : List Work.SG.Data.M3) (n : ℤ) {k : ℕ} (hB : B.length = k)
    {y1 y2 y3 : List ℤ} (h1 : y1.length = 3 * k) (h2 : y2.length = 3 * k) (h3 : y3.length = 3 * k)
    (hcong : ∀ q, q < 3 * k → n ∣ y1.getD q 0 - y2.getD q 0 - y3.getD q 0) :
    ∀ c : Fin 3, n ∣ (Work.SG.Data.applyB B y1).toFun c - (Work.SG.Data.applyB B y2).toFun c
      - (Work.SG.Data.applyB B y3).toFun c := by
  have hbl1 := blocks_len_of_len y1 h1
  have hbl2 := blocks_len_of_len y2 h2
  have hbl3 := blocks_len_of_len y3 h3
  have e1 := applyB_range_blocks_gen B y1 (by rw [hbl1, hB])
  have e2 := applyB_range_blocks_gen B y2 (by rw [hbl2, hB])
  have e3 := applyB_range_blocks_gen B y3 (by rw [hbl3, hB])
  intro c
  rw [e1, e2, e3]
  simp only [Finset.sum_apply]
  refine dvd_sum_sub3 _ n _ _ _ fun g hg => ?_
  have hgk : g < k := by
    have h' := Finset.mem_range.mp hg
    rwa [hB] at h'
  exact blk_sub3_dvd (B.getD g Work.SG.Data.M3.zero) n h1 h2 h3 hgk hcong c

end Work.SG.cobstepAux
