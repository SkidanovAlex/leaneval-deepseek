import Mathlib
import Submission.Work.Peluse.Basic

namespace Work.Peluse.Prop36SW

/-- **Window/lag reindexing of `§5` of Peluse's argument.**

The kernel `F : ℤ → ℤ → ℂ` is supported on the "window" relation `u + m ∈ symIcc M`, i.e.
`F m u = 0` as soon as the pair `(m, u)` leaves the band `{(m,u) : |m + u| ≤ M}`.  Then the
sum of `F` over the lag/window rectangle
`m ∈ [-(K-1), K-1]`, `u ∈ symIcc M = [-M, M]` collapses to the diagonal description of that
band: each non-vanishing term is uniquely `(m, u) = (k - y, y)` with `y = u ∈ symIcc M` and
`k = u + m ∈ symIcc M`.  The hypothesis `2M + 1 ≤ K` guarantees `k - y ∈ [-(K-1), K-1]`, so
no term of the right-hand side is lost.

This is the elementary re-indexing used when the §5 window sum is re-expressed as a sum over
pairs of window points `y, k` with lag `k - y`. -/
theorem windowLagWindowReindex {M K : ℕ} (hK : 2 * M + 1 ≤ K) (F : ℤ → ℤ → ℂ)
    (hF : ∀ m u : ℤ, u + m ∉ Work.Peluse.symIcc M → F m u = 0) :
    (∑ m ∈ Finset.Icc (-(K : ℤ) + 1) ((K : ℤ) - 1), ∑ u ∈ Work.Peluse.symIcc M, F m u)
      = ∑ y ∈ Work.Peluse.symIcc M, ∑ k ∈ Work.Peluse.symIcc M, F (k - y) y := by
  -- `2M ≤ K - 1`, i.e. the lag of two window points always lies in the lag interval.
  have hMK : 2 * (M : ℤ) ≤ (K : ℤ) - 1 := by
    have h1 : ((2 * M + 1 : ℕ) : ℤ) ≤ (K : ℤ) := by exact_mod_cast hK
    push_cast at h1
    linarith
  have hmemS : ∀ z : ℤ, z ∈ Work.Peluse.symIcc M ↔ -(M : ℤ) ≤ z ∧ z ≤ (M : ℤ) := by
    intro z; simp [Work.Peluse.symIcc, Finset.mem_Icc]
  have hmemT : ∀ z : ℤ,
      z ∈ Finset.Icc (-(K : ℤ) + 1) ((K : ℤ) - 1) ↔ -(K : ℤ) + 1 ≤ z ∧ z ≤ (K : ℤ) - 1 := by
    intro z; simp [Finset.mem_Icc]
  -- Both sides as sums over the corresponding product of index sets.
  have hL : (∑ m ∈ Finset.Icc (-(K : ℤ) + 1) ((K : ℤ) - 1), ∑ u ∈ Work.Peluse.symIcc M, F m u)
      = ∑ x ∈ Finset.Icc (-(K : ℤ) + 1) ((K : ℤ) - 1) ×ˢ Work.Peluse.symIcc M,
          F x.1 x.2 :=
    (Finset.sum_product' _ _ F).symm
  have hR : (∑ y ∈ Work.Peluse.symIcc M, ∑ k ∈ Work.Peluse.symIcc M, F (k - y) y)
      = ∑ x ∈ Work.Peluse.symIcc M ×ˢ Work.Peluse.symIcc M, F (x.2 - x.1) x.1 :=
    (Finset.sum_product' _ _ (fun y k => F (k - y) y)).symm
  -- On the lag/window rectangle only the pairs with `u + m ∈ symIcc M` can contribute.
  have hstep2 : (∑ x ∈ Finset.Icc (-(K : ℤ) + 1) ((K : ℤ) - 1) ×ˢ Work.Peluse.symIcc M,
          F x.1 x.2)
      = ∑ x ∈ (Finset.Icc (-(K : ℤ) + 1) ((K : ℤ) - 1) ×ˢ Work.Peluse.symIcc M).filter
            (fun x : ℤ × ℤ => x.2 + x.1 ∈ Work.Peluse.symIcc M), F x.1 x.2 := by
    refine (Finset.sum_filter_of_ne ?_).symm
    intro x _ hne
    by_contra h
    exact hne (hF x.1 x.2 h)
  -- Reindex the surviving pairs `(m, u) ↦ (u, u + m) = (y, k)`.
  have hstep3 : (∑ x ∈ (Finset.Icc (-(K : ℤ) + 1) ((K : ℤ) - 1) ×ˢ Work.Peluse.symIcc M).filter
            (fun x : ℤ × ℤ => x.2 + x.1 ∈ Work.Peluse.symIcc M), F x.1 x.2)
      = ∑ q ∈ Work.Peluse.symIcc M ×ˢ Work.Peluse.symIcc M, F (q.2 - q.1) q.1 := by
    refine Finset.sum_nbij (fun x : ℤ × ℤ => (x.2, x.1 + x.2)) ?_ ?_ ?_ ?_
    · -- the map lands in `symIcc M × symIcc M`
      intro x hx
      rw [Finset.mem_filter, Finset.mem_product] at hx
      exact Finset.mem_product.mpr ⟨hx.1.2, by simpa [add_comm] using hx.2⟩
    · -- the map is injective
      intro x _ y _ hxy
      simp only [Prod.mk.injEq] at hxy
      obtain ⟨h1, h2⟩ := hxy
      exact Prod.ext (by linarith) h1
    · -- and surjective (with inverse `(y, k) ↦ (k - y, y)`)
      intro q hq
      rw [Finset.mem_coe, Finset.mem_product] at hq
      obtain ⟨hq1, hq2⟩ := hq
      refine ⟨(q.2 - q.1, q.1), ?_, ?_⟩
      · rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_product]
        refine ⟨⟨?_, hq1⟩, ?_⟩
        · -- `q.2 - q.1` lies in the lag interval since `2M ≤ K - 1`
          rw [hmemT]
          have h1 := (hmemS q.1).mp hq1
          have h2 := (hmemS q.2).mp hq2
          constructor <;> linarith
        · -- `q.1 + (q.2 - q.1) = q.2 ∈ symIcc M`
          simpa using hq2
      · -- the image of the inverse is `q`
        simp
    · -- the summands agree
      intro x _
      simp
  rw [hL, hR, hstep2, hstep3]

end Work.Peluse.Prop36SW
