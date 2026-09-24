import Mathlib

namespace Work.GM.Affine

/-- Periodisation identity, finite-support form.

If `f` vanishes outside `[-R, R]` and `m > 0`, then for `x ∈ [0,1]` the full
periodised sum `∑_{k ∈ ℤ} f ((x + k)/m)` is actually a finite sum, supported on
the index window `[-K, K]` — provided `mR + 1 ≤ K`. Concretely it equals the
finite sum over `j ∈ {0, …, 2K}` of `f ((x + (j - K))/m)`. -/
theorem periodization_tsum_finsum {f : ℝ → ℝ} {m R : ℝ} (hm : 0 < m)
    (hf : ∀ y : ℝ, R < |y| → f y = 0) {K : ℕ} (hK : m * R + 1 ≤ (K : ℝ)) :
    ∀ x ∈ Set.Icc (0:ℝ) 1,
      (∑' k : ℤ, f ((x + (k : ℝ)) / m))
        = ∑ j ∈ Finset.range (2 * K + 1), f ((x + ((j : ℤ) - (K : ℤ))) / m) := by
  intro x hx
  rw [Set.mem_Icc] at hx
  obtain ⟨hx0, hx1⟩ := hx
  -- Every index outside the window `[-K, K]` gives value `0`.
  have hsupp : ∀ k : ℤ, k ∉ Finset.Icc (-(K:ℤ)) (K:ℤ) → f ((x + (k:ℝ))/m) = 0 := by
    intro k hk
    apply hf
    -- `k < -K` or `K < k`.
    have hklt : k < -(K:ℤ) ∨ (K:ℤ) < k := by
      simpa only [Finset.mem_Icc, not_and_or, not_le] using hk
    -- In either case `mR < |x + k|`.
    have hbound : m * R < |x + (k:ℝ)| := by
      rcases hklt with hkA | hkB
      · -- `k ≤ -K - 1`, and `x ≤ 1`, so `x + k ≤ -K ≤ 0`.
        have hkR : (k:ℝ) + 1 ≤ -(K:ℝ) := by
          have h1 : k + 1 ≤ -(K:ℤ) := by omega
          exact_mod_cast h1
        have h2 : (K:ℝ) ≤ -(x + (k:ℝ)) := by linarith
        have h3 : -(x + (k:ℝ)) ≤ |x + (k:ℝ)| := neg_le_abs _
        linarith
      · -- `k ≥ K + 1` and `x ≥ 0`, so `x + k ≥ K + 1`.
        have hkR : (K:ℝ) + 1 ≤ (k:ℝ) := by
          have h1 : (K:ℤ) + 1 ≤ k := by omega
          exact_mod_cast h1
        have h2 : (K:ℝ) ≤ x + (k:ℝ) := by linarith
        have h3 : x + (k:ℝ) ≤ |x + (k:ℝ)| := le_abs_self _
        linarith
    have hdiv : R < |(x + (k:ℝ))/m| := by
      rw [abs_div, abs_of_pos hm, lt_div_iff₀ hm]
      rw [show R * m = m * R by ring]
      exact hbound
    exact hdiv
  -- Collapse the `tsum` onto the finite window `[-K, K]`.
  have h1 : (∑' k : ℤ, f ((x + (k:ℝ))/m))
      = ∑ k ∈ Finset.Icc (-(K:ℤ)) (K:ℤ), f ((x + (k:ℝ))/m) :=
    tsum_eq_sum (f := fun k : ℤ => f ((x + (k:ℝ))/m)) (s := Finset.Icc (-(K:ℤ)) (K:ℤ)) hsupp
  rw [h1]
  -- Reindex `j ↦ j - K` from `{0, …, 2K}` onto `[-K, K]`.
  symm
  refine Finset.sum_bij (fun j (_ : j ∈ Finset.range (2*K+1)) => (j:ℤ) - (K:ℤ)) ?_ ?_ ?_ ?_
  · intro j hj
    rw [Finset.mem_range] at hj
    rw [Finset.mem_Icc]
    constructor
    · have : (0:ℤ) ≤ (j:ℤ) := Int.natCast_nonneg j
      linarith
    · have hj' : j ≤ 2*K := by omega
      have h2 : (j:ℤ) ≤ ((2*K:ℕ):ℤ) := by exact_mod_cast hj'
      push_cast at h2
      linarith
  · intro a _ b _ hab
    omega
  · intro b hb
    rw [Finset.mem_Icc] at hb
    obtain ⟨hb1, hb2⟩ := hb
    refine ⟨(b + (K:ℤ)).toNat, ?_, ?_⟩
    · rw [Finset.mem_range]
      have hbk : 0 ≤ b + (K:ℤ) := by linarith
      have hcast : (((b + (K:ℤ)).toNat : ℤ)) = b + (K:ℤ) := Int.toNat_of_nonneg hbk
      have h2 : ((b + (K:ℤ)).toNat : ℤ) ≤ ((2*K:ℕ):ℤ) := by
        rw [hcast]; push_cast; linarith
      have h3 : (b + (K:ℤ)).toNat ≤ 2*K := Int.ofNat_le.mp h2
      omega
    · have hbk : 0 ≤ b + (K:ℤ) := by linarith
      have hcast : (((b + (K:ℤ)).toNat : ℤ)) = b + (K:ℤ) := Int.toNat_of_nonneg hbk
      show ((b + (K:ℤ)).toNat : ℤ) - (K:ℤ) = b
      rw [hcast]; ring
  · intro a _
    simp only [Int.cast_sub]

end Work.GM.Affine
