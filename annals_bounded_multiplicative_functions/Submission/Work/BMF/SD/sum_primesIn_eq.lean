import Mathlib
import Submission.Work.BMF.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.SD

theorem sum_primesIn_eq (P Q : ℝ) (hP : 2 ≤ P) (hPQ : P ≤ Q) (f : ℕ → ℝ) :
    ∑ p ∈ Work.BMF.primesIn P Q, f p
      = (∑ p ∈ (⌊Q⌋₊).primesLE, f p) - ∑ p ∈ (⌈P⌉₊ - 1).primesLE, f p := by
  have hP0 : (0:ℝ) ≤ P := by linarith
  have hceil2 : 2 ≤ ⌈P⌉₊ := by
    have h : ⌈(2:ℝ)⌉₊ ≤ ⌈P⌉₊ := Nat.ceil_mono hP
    simpa using h
  have hfloor : (⌈P⌉₊ - 1 : ℕ) ≤ ⌊Q⌋₊ := by
    refine Nat.le_floor ?_
    have h2 := Nat.ceil_lt_add_one hP0
    have hcs : ((⌈P⌉₊ - 1 : ℕ) : ℝ) = (⌈P⌉₊ : ℝ) - 1 := by
      rw [Nat.cast_sub (show 1 ≤ ⌈P⌉₊ by omega), Nat.cast_one]
    rw [hcs]; linarith
  have hsub : (⌈P⌉₊ - 1).primesLE ⊆ (⌊Q⌋₊).primesLE := by
    intro p hp
    rw [Nat.mem_primesLE] at hp ⊢
    exact ⟨le_trans hp.1 hfloor, hp.2⟩
  have heq : Work.BMF.primesIn P Q = (⌊Q⌋₊).primesLE \ (⌈P⌉₊ - 1).primesLE := by
    ext p
    simp only [Work.BMF.primesIn, Work.BMF.natIcc, Finset.mem_filter, Finset.mem_Icc,
      Finset.mem_sdiff, Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨hl, hr⟩, hp⟩
      exact ⟨⟨hr, hp⟩, fun h => absurd h.1 (by omega)⟩
    · rintro ⟨⟨hr, hp⟩, hnot⟩
      have hlt : ⌈P⌉₊ - 1 < p := by
        by_contra hc
        exact hnot ⟨by omega, hp⟩
      exact ⟨⟨by omega, hr⟩, hp⟩
  rw [heq]
  have hs := Finset.sum_sdiff (f := f) hsub
  linarith

end Work.BMF.SD
