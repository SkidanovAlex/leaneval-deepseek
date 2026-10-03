import Mathlib

namespace Work.Analysis.PertCrux

/-- Cutting an orbit at its first vanishing time.  Let `f₀ 0 = 0` and let `x` be an orbit of `f₀`
(`x (n+1) = f₀ (x n)`) which vanishes somewhere at a time `≥ N`, with `N ≤ m`.  Then there is a cut
`L` with `N ≤ L ≤ m` such that `x j ≠ 0` for all `N ≤ j < L` and, the vanishing locus of `x` being
an upper set (`x j = 0 → f₀ 0 = 0 → x (j+1) = 0 → …`), the sum over `[N, m)` equals the sum over
the initial nonzero segment `[N, L)`. -/
theorem exists_cut {f₀ : ℂ → ℂ} (hf0 : f₀ 0 = 0) {x : ℕ → ℂ}
    (hx : ∀ n : ℕ, x (n + 1) = f₀ (x n)) {N m : ℕ} (hNm : N ≤ m)
    (hex : ∃ j : ℕ, N ≤ j ∧ x j = 0) :
    ∃ L : ℕ, N ≤ L ∧ L ≤ m ∧ (∀ j : ℕ, N ≤ j → j < L → x j ≠ 0) ∧
      ∑ j ∈ Finset.Ico N m, ‖x j‖ = ∑ j ∈ Finset.Ico N L, ‖x j‖ := by
  -- Vanishing is an upper set along the orbit: once `x j = 0`, `x n = 0` for all `n ≥ j`.
  have hge : ∀ j n : ℕ, j ≤ n → x j = 0 → x n = 0 := by
    intro j n hjn hj
    induction n, hjn using Nat.le_induction with
    | base => exact hj
    | succ k _ ih => rw [hx k, ih, hf0]
  -- `Nat.find hex` is the first vanishing time at or after `N`.
  obtain ⟨hNk, hxk⟩ := Nat.find_spec hex
  have hmin : ∀ j : ℕ, N ≤ j → x j = 0 → Nat.find hex ≤ j :=
    fun j hj hxj => Nat.find_min' hex ⟨hj, hxj⟩
  refine ⟨min (Nat.find hex) m, le_min hNk hNm, min_le_right _ _, ?_, ?_⟩
  · -- up to the cut the orbit is nonzero, by minimality of the first vanishing time
    intro j hjN hjL
    have hjk : j < Nat.find hex := lt_of_lt_of_le hjL (min_le_left _ _)
    intro hxj
    have := hmin j hjN hxj
    omega
  · by_cases hmk : m ≤ Nat.find hex
    · -- no vanishing before `m`: the cut is `m` and the two sums are identical
      rw [min_eq_right hmk]
    · -- the cut is the first vanishing time `Nat.find hex ≤ m`; all later terms vanish
      have hkm : Nat.find hex ≤ m := le_of_lt (lt_of_not_ge hmk)
      rw [min_eq_left hkm]
      have hzero : ∀ j ∈ Finset.Ico (Nat.find hex) m, ‖x j‖ = 0 := by
        intro j hj
        rw [Finset.mem_Ico] at hj
        simpa using hge (Nat.find hex) j hj.1 hxk
      rw [← Finset.sum_Ico_consecutive (fun j => ‖x j‖) hNk hkm]
      rw [Finset.sum_eq_zero hzero, add_zero]

end Work.Analysis.PertCrux
