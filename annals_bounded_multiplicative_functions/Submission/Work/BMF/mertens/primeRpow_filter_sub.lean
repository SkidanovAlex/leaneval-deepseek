import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mertens

theorem primeRpow_filter_sub {x y ε : ℝ} (hyx : y ≤ x) :
    (∑ p ∈ ((⌊x⌋₊).primesLE.filter (fun p : ℕ => y < (p : ℝ))), (1 : ℝ) / (p : ℝ) ^ (1 + ε)) =
      (∑ p ∈ (⌊x⌋₊).primesLE, (1 : ℝ) / (p : ℝ) ^ (1 + ε)) -
        (∑ p ∈ (⌊y⌋₊).primesLE, (1 : ℝ) / (p : ℝ) ^ (1 + ε)) := by
  have hsub : (⌊y⌋₊).primesLE ⊆ (⌊x⌋₊).primesLE := by
    intro p hp
    rw [Nat.mem_primesLE] at hp ⊢
    exact ⟨le_trans hp.1 (Nat.floor_mono hyx), hp.2⟩
  have hfilter : (⌊x⌋₊).primesLE \ (⌊y⌋₊).primesLE
      = (⌊x⌋₊).primesLE.filter (fun p : ℕ => y < (p : ℝ)) := by
    ext p
    simp only [Finset.mem_sdiff, Finset.mem_filter, Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨hpx, hpprime⟩, hpny⟩
      exact ⟨⟨hpx, hpprime⟩, (Nat.floor_lt' (Nat.Prime.ne_zero hpprime)).mp
        (Nat.lt_of_not_le (fun h => hpny ⟨h, hpprime⟩))⟩
    · rintro ⟨⟨hpx, hpprime⟩, hyp⟩
      exact ⟨⟨hpx, hpprime⟩, fun ⟨hpy, _⟩ =>
        absurd hpy (not_le.mpr ((Nat.floor_lt' (Nat.Prime.ne_zero hpprime)).mpr hyp))⟩
  rw [← hfilter, eq_sub_iff_add_eq]
  exact Finset.sum_sdiff hsub

end Work.BMF.mertens
