import Mathlib
import Submission.Commons.Combinatorics.Ramsey.dkt_dhj_of_increment_mult

namespace Commons.Combinatorics.Ramsey

/-- Converting the "affine/uniform" increment hypothesis (a subspace whose `d0`-dimensional
pullback exceeds the trivial count by an additive `γ · k^(n+d0)`) into the multiplicative
increment hypothesis of `dkt_dhj_of_increment_mult`, with the same boost constant `γ`.

The point is that for a subset `T ⊆ [k]^n` one has `|T| ≤ k^n`, so the additive excess
`γ · k^(n+d0) = γ · k^n · k^d0` alone already dominates `γ · |T| · k^d0`; hence the affinity
count `|T| · k^d0 + γ · k^(n+d0)` is at least `(1 + γ) · |T| · k^d0`. -/
theorem dkt_dhj_of_increment_unif (k : ℕ) (hk : 1 ≤ k)
    (hinc : ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∃ γ : ℝ, 0 < γ ∧ ∀ d0 : ℕ, 1 ≤ d0 → ∃ n₀ : ℕ,
      ∀ n : ℕ, n₀ ≤ n → ∀ T : Finset (Fin n → Fin k),
        δ * (k : ℝ) ^ n ≤ (T.card : ℝ) →
        (∃ l : Combinatorics.Line (Fin k) (Fin n), ∀ x : Fin k, l x ∈ T) ∨
        ∃ S : Combinatorics.Subspace (Fin d0) (Fin k) (Fin n),
          (T.card : ℝ) * (k : ℝ) ^ d0 + γ * (k : ℝ) ^ (n + d0)
            ≤ ((Finset.univ : Finset (Fin d0 → Fin k)).filter (fun x => S x ∈ T)).card
                * (k : ℝ) ^ n) :
    ∀ δ : ℝ, 0 < δ → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ T : Finset (Fin n → Fin k),
      δ * (k : ℝ) ^ n ≤ (T.card : ℝ) →
        ∃ l : Combinatorics.Line (Fin k) (Fin n), ∀ x : Fin k, l x ∈ T := by
  refine dkt_dhj_of_increment_mult k hk ?_
  intro δ hδ0 hδ1
  obtain ⟨γ, hγpos, hγ⟩ := hinc δ hδ0 hδ1
  refine ⟨γ, hγpos, ?_⟩
  intro d0 hd0
  obtain ⟨n₀, hn₀⟩ := hγ d0 hd0
  refine ⟨n₀, ?_⟩
  intro n hn T hT
  rcases hn₀ n hn T hT with hline | ⟨S, hS⟩
  · exact Or.inl hline
  · refine Or.inr ⟨S, ?_⟩
    have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    have hkdpos : (0 : ℝ) < (k : ℝ) ^ d0 := pow_pos hkpos d0
    -- `|T| ≤ k^n`
    have hcard_le : (T.card : ℝ) ≤ (k : ℝ) ^ n := by
      have h1 : T.card ≤ Fintype.card (Fin n → Fin k) := Finset.card_le_univ T
      have h2 : Fintype.card (Fin n → Fin k) = k ^ n := by
        rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
      calc (T.card : ℝ) ≤ (Fintype.card (Fin n → Fin k) : ℝ) := by exact_mod_cast h1
        _ = ((k ^ n : ℕ) : ℝ) := by rw [h2]
        _ = (k : ℝ) ^ n := by push_cast; ring
    have hpow : (k : ℝ) ^ (n + d0) = (k : ℝ) ^ n * (k : ℝ) ^ d0 := pow_add _ _ _
    rw [hpow] at hS
    -- The excess `γ · k^(n+d0)` dominates `γ · |T| · k^d0`.
    have hA : γ * (T.card : ℝ) * (k : ℝ) ^ d0 ≤ γ * (k : ℝ) ^ n * (k : ℝ) ^ d0 := by
      have h1 : γ * (T.card : ℝ) ≤ γ * (k : ℝ) ^ n :=
        mul_le_mul_of_nonneg_left hcard_le (le_of_lt hγpos)
      exact mul_le_mul_of_nonneg_right h1 (le_of_lt hkdpos)
    have key : (1 + γ) * (T.card : ℝ) * (k : ℝ) ^ d0 ≤
        (((Finset.univ : Finset (Fin d0 → Fin k)).filter (fun x => S x ∈ T)).card : ℝ)
          * (k : ℝ) ^ n := by
      nlinarith [hS, hA]
    exact key

end Commons.Combinatorics.Ramsey
