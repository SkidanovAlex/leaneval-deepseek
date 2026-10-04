import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.Comp

/-- Route: each `z ↦ iteratedFDeriv ℝ i Φ z` is continuous (`ContDiff.continuous_iteratedFDeriv`),
the closed ball of radius `R` is compact, so `IsCompact.exists_bound_of_continuousOn` gives a bound
`M i` for each `i ≤ s`; take the finite maximum over `i ∈ range (s+1)`. -/
theorem phi_derivBound (Φ : ℂ → ℂ) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (R : ℝ) (s : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z : ℂ, ‖z‖ ≤ R → ∀ i : ℕ, i ≤ s →
      ‖iteratedFDeriv ℝ i Φ z‖ ≤ M := by
  have hcompact : IsCompact {z : ℂ | ‖z‖ ≤ R} := by
    simpa [Metric.closedBall, dist_eq_norm] using isCompact_closedBall (0 : ℂ) R
  have hcont : ∀ i : ℕ, ContinuousOn (fun z : ℂ => iteratedFDeriv ℝ i Φ z) {z : ℂ | ‖z‖ ≤ R} :=
    fun i => (hΦ.continuous_iteratedFDeriv (by simp)).continuousOn
  choose C hC using fun i : ℕ =>
    hcompact.exists_bound_of_continuousOn (hcont i)
  have hne : (Finset.range (s+1)).Nonempty := ⟨0, Finset.mem_range.mpr (Nat.succ_pos s)⟩
  refine ⟨(Finset.range (s+1)).sup' hne (fun i => |C i|), ?_, ?_⟩
  · have h0 : (0 : ℕ) ∈ Finset.range (s+1) := Finset.mem_range.mpr (Nat.succ_pos s)
    have := Finset.le_sup' (fun i : ℕ => |C i|) h0
    exact le_trans (abs_nonneg (C 0)) this
  · intro z hz i hi
    have hmem : i ∈ Finset.range (s+1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hi)
    have h1 : ‖iteratedFDeriv ℝ i Φ z‖ ≤ C i := hC i z hz
    have h2 : C i ≤ |C i| := le_abs_self (C i)
    have h3 : |C i| ≤ (Finset.range (s+1)).sup' hne (fun i => |C i|) :=
      Finset.le_sup' (fun i : ℕ => |C i|) hmem
    linarith

end Work.Diff.STE.Comp
