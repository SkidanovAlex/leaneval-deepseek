import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.Lead.GalTame

/-- If among the summands of a finite sum of complex numbers at most one is non-zero, then the
squared norm of the sum is the sum of the squared norms. -/
lemma normSumSqSubsingleton {ι : Type*} (s : Finset ι) (W : ι → ℂ)
    (h : ∀ k ∈ s, ∀ k' ∈ s, W k ≠ 0 → W k' ≠ 0 → k = k') :
    ‖∑ k ∈ s, W k‖ ^ 2 = ∑ k ∈ s, ‖W k‖ ^ 2 := by
  by_cases h0 : ∃ k ∈ s, W k ≠ 0
  · -- exactly one summand is non-zero: it is `k₀`, and the sum collapses onto it
    obtain ⟨k₀, hk₀, hw₀⟩ := h0
    have hzero : ∀ k ∈ s, k ≠ k₀ → W k = 0 := by
      intro k hk hkne
      by_contra hw
      exact hkne (h k hk k₀ hk₀ hw hw₀)
    rw [Finset.sum_eq_single k₀ (fun k hk hkne => hzero k hk hkne) (fun hc => absurd hk₀ hc),
      Finset.sum_eq_single k₀ (fun k hk hkne => by rw [hzero k hk hkne, norm_zero]; norm_num)
        (fun hc => absurd hk₀ hc)]
  · -- all summands vanish
    push Not at h0
    have hsum : ∑ k ∈ s, W k = 0 := Finset.sum_eq_zero (fun k hk => h0 k hk)
    have hsum2 : ∑ k ∈ s, ‖W k‖ ^ 2 = 0 :=
      Finset.sum_eq_zero (fun k hk => by rw [h0 k hk, norm_zero]; norm_num)
    rw [hsum, hsum2, norm_zero]
    norm_num

end Work.Diff.STE.Lead.GalTame
