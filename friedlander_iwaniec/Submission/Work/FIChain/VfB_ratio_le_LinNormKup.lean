import Mathlib
import Submission.Work.FIChain.VfBFacts

namespace Work.FIChain

/-- **`VfB` ratio bound under the windowed norm `LinNormKup`**: for `2 ≤ c ≤ z ≤ D`,
`VfB c ≤ VfB z · C (log z / log c)^κ`.  Same proof as `VfB_ratio_le`, with the
`LinNormKup` hypothesis supplying the sieve product estimate on the window `[c,z] ⊆ [2,D]`. -/
theorem VfB_ratio_le_LinNormKup {ν : ℕ → ℝ} {C κ D : ℝ} (h : Work.FIChain.LinNormKup ν C κ D)
    (hν1 : ∀ p : ℕ, p.Prime → ν p ≤ 1 / 2) {c z : ℕ} (hc : 2 ≤ c) (hcz : c ≤ z)
    (hzD : (z : ℝ) ≤ D) :
    Work.FIChain.VfB ν (c : ℝ) ≤ Work.FIChain.VfB ν (z : ℝ) * (C * (Real.log z / Real.log c) ^ κ) := by
  have hsub : Nat.primesBelow c ⊆ Nat.primesBelow z := by
    intro p hp; rw [Nat.mem_primesBelow] at hp ⊢
    exact ⟨lt_of_lt_of_le hp.1 hcz, hp.2⟩
  have hset : Nat.primesBelow z \ Nat.primesBelow c
      = (Nat.primesBelow z).filter (fun p : ℕ => c ≤ p) := by
    ext p; simp only [Finset.mem_sdiff, Finset.mem_filter, Nat.mem_primesBelow]
    constructor
    · rintro ⟨⟨hz, hp⟩, hnc⟩
      exact ⟨⟨hz, hp⟩, by by_contra h; exact hnc ⟨by omega, hp⟩⟩
    · rintro ⟨⟨hz, hp⟩, hc'⟩; exact ⟨⟨hz, hp⟩, by omega⟩
  have hlin := h (c:ℝ) (z:ℝ) (by exact_mod_cast hc) (by exact_mod_cast hcz) hzD
  simp only [Nat.ceil_natCast, Nat.cast_le] at hlin
  rw [Finset.prod_inv_distrib] at hlin
  rw [VfB, VfB, Nat.ceil_natCast, Nat.ceil_natCast]
  have hsd := Finset.prod_sdiff hsub (f := fun p : ℕ => (1 - ν p))
  rw [hset] at hsd
  have hVz : 0 < ∏ p ∈ Nat.primesBelow z, (1 - ν p) := Finset.prod_pos (fun p hp => by
    have := hν1 p (Nat.mem_primesBelow.mp hp).2; linarith)
  have hVc0 : 0 < ∏ p ∈ Nat.primesBelow c, (1 - ν p) := Finset.prod_pos (fun p hp => by
    have := hν1 p (Nat.mem_primesBelow.mp hp).2; linarith)
  have hsd' : ∏ p ∈ (Nat.primesBelow z).filter (fun p : ℕ => c ≤ p), (1 - ν p)
      = (∏ p ∈ Nat.primesBelow z, (1 - ν p)) / (∏ p ∈ Nat.primesBelow c, (1 - ν p)) := by
    rw [eq_div_iff (ne_of_gt hVc0)]
    exact hsd
  rw [hsd', inv_div, div_le_iff₀ hVz, mul_comm] at hlin
  exact hlin

end Work.FIChain
