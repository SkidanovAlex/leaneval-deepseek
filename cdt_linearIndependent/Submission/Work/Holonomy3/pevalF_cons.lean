import Mathlib
import Submission.Work.Holonomy3.mv_lex_defs
import Submission.Work.Holonomy3.pevalF_consPt

/-!
# Truncated slice decomposition of `pevalF` along the first variable

`pevalF_consPt` expresses `pevalF c (consPt w z)` as a sum over the set `suppFst c` of first
coordinates occurring in the support of `c`.  If the first coordinate of every element of
`c.support` is at most `N`, the same value is obtained by summing over the full range
`k = 0, …, N`, because `sliceF c k = 0` (hence the corresponding term vanishes) whenever `k` does
not occur as a first coordinate.
-/

namespace Work.Holonomy3

open scoped BigOperators

/-- If `t` is not the first coordinate of any element of the support of `c`, then the slice
`sliceF c t` is the zero family. -/
theorem sliceF_eq_zero_of_notMem {d : ℕ} (c : (Fin (d + 1) →₀ ℕ) →₀ ℂ) {t : ℕ}
    (ht : t ∉ suppFst c) : sliceF c t = 0 := by
  ext m
  rw [sliceF_apply, Finsupp.coe_zero, Pi.zero_apply]
  by_contra h
  exact ht (mem_suppFst.mpr ⟨consIdx t m, Finsupp.mem_support_iff.mpr h, consIdx_zero t m⟩)

/-- The zero family evaluates to zero. -/
theorem pevalF_zero {d : ℕ} (z : Fin d → ℂ) : pevalF (0 : (Fin d →₀ ℕ) →₀ ℂ) z = 0 := by
  simp [pevalF]

theorem pevalF_cons {d : ℕ} (c : (Fin (d + 1) →₀ ℕ) →₀ ℂ) (N : ℕ)
    (hN : ∀ m ∈ c.support, m 0 ≤ N) (w : ℂ) (z : Fin d → ℂ) :
    Work.Holonomy3.pevalF c (Work.Holonomy3.consPt w z)
      = Finset.sum (Finset.range (N + 1))
          (fun k => Work.Holonomy3.pevalF (Work.Holonomy3.sliceF c k) z * w ^ k) := by
  rw [pevalF_consPt]
  -- Every first coordinate occurring in the support of `c` is at most `N`.
  have hsub : suppFst c ⊆ Finset.range (N + 1) := by
    intro t ht
    rw [Finset.mem_range]
    obtain ⟨m, hm, rfl⟩ := mem_suppFst.mp ht
    exact Nat.lt_succ_of_le (hN m hm)
  -- All the extra terms in the sum over `range (N + 1)` vanish.
  have hzero : ∀ k ∈ Finset.range (N + 1), k ∉ suppFst c →
      w ^ k * pevalF (sliceF c k) z = 0 := by
    intro k _ hk
    rw [sliceF_eq_zero_of_notMem c hk, pevalF_zero, mul_zero]
  rw [Finset.sum_subset hsub hzero]
  exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)

end Work.Holonomy3
