import Mathlib

namespace Work.RPCore.Chain

theorem rotation_orbit (N : ℕ) (δ α : ℝ) (A U : ℕ → ℝ)
    (hrec : ∀ k, N ≤ k → k ≤ 2*N - 1 →
      A (k+1) = Real.cos δ * A k - Real.sin δ * U (k-1) ∧
      U k = Real.sin δ * A k + Real.cos δ * U (k-1))
    (hA : A N = α) (hU : U (N-1) = 0) :
    (∀ m, m ≤ N → A (N+m) = α * Real.cos ((m:ℝ)*δ)) ∧
    (∀ m, m ≤ N → U (N+m-1) = α * Real.sin ((m:ℝ)*δ)) := by
  have main : ∀ n, n ≤ N →
      A (N+n) = α * Real.cos ((n:ℝ)*δ) ∧
      U (N+n-1) = α * Real.sin ((n:ℝ)*δ) := by
    intro n
    induction n with
    | zero =>
      intro _
      constructor
      · simpa using hA
      · simpa using hU
    | succ n ih =>
      intro hn
      have hn' : n ≤ N := by omega
      obtain ⟨ihA, ihU⟩ := ih hn'
      have hkN1 : N ≤ N + n := by omega
      have hkN2 : N + n ≤ 2*N - 1 := by omega
      obtain ⟨h1, h2⟩ := hrec (N+n) hkN1 hkN2
      have hcast : ((n+1 : ℕ) : ℝ) * δ = (n:ℝ)*δ + δ := by push_cast; ring
      constructor
      · have hidx : N + (n+1) = N + n + 1 := by omega
        rw [hidx, h1, ihA, ihU, hcast, Real.cos_add]
        ring
      · have hidx : N + (n+1) - 1 = N + n := by omega
        rw [hidx, h2, ihA, ihU, hcast, Real.sin_add]
        ring
  exact ⟨fun m hm => (main m hm).1, fun m hm => (main m hm).2⟩

end Work.RPCore.Chain
