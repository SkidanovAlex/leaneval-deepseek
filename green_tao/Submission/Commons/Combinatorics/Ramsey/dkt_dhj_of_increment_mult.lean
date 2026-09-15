import Submission.Commons.Combinatorics.Ramsey.dkt_dhj_of_increment

namespace Commons.Combinatorics.Ramsey

/-- The multiplicative-increment form of the density-increment hypothesis implies the
additive (parameterised-density) form: from the hypothesis that a set of density `≥ δ`
has a subspace whose density is boosted by the factor `(1 + c)`, one gets the same with
the boost measured against any `d ∈ [δ, 1]` with `d ≤ dens T`. -/
theorem dkt_dhj_of_increment_mult (k : ℕ) (hk : 1 ≤ k)
    (hinc : ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∃ c : ℝ, 0 < c ∧ ∀ d0 : ℕ, 1 ≤ d0 → ∃ n₀ : ℕ,
      ∀ n : ℕ, n₀ ≤ n → ∀ T : Finset (Fin n → Fin k),
        δ * (k : ℝ) ^ n ≤ (T.card : ℝ) →
        (∃ l : Combinatorics.Line (Fin k) (Fin n), ∀ x : Fin k, l x ∈ T) ∨
        ∃ S : Combinatorics.Subspace (Fin d0) (Fin k) (Fin n),
          (1 + c) * (T.card : ℝ) * (k : ℝ) ^ d0
            ≤ ((Finset.univ : Finset (Fin d0 → Fin k)).filter (fun x => S x ∈ T)).card
                * (k : ℝ) ^ n) :
    ∀ δ : ℝ, 0 < δ → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ T : Finset (Fin n → Fin k),
      δ * (k : ℝ) ^ n ≤ (T.card : ℝ) →
        ∃ l : Combinatorics.Line (Fin k) (Fin n), ∀ x : Fin k, l x ∈ T := by
  refine dkt_dhj_of_increment k hk ?_
  -- Build the hypothesis of `dkt_dhj_of_increment` from `hinc`.
  intro δ hδ0 hδ1
  obtain ⟨c, hcpos, hrest⟩ := hinc δ hδ0 hδ1
  refine ⟨c, hcpos, ?_⟩
  intro d0 hd0
  obtain ⟨n₀, hn₀⟩ := hrest d0 hd0
  refine ⟨n₀, ?_⟩
  intro n hn d hdδ hd1 T hT
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < (k : ℝ) ^ n := pow_pos (by linarith) n
  -- Density `≥ d ≥ δ`, so the multiplicative hypothesis applies to `T`.
  have hT' : δ * (k : ℝ) ^ n ≤ (T.card : ℝ) := by
    have h := mul_le_mul_of_nonneg_right hdδ (le_of_lt hkpos)
    linarith [h, hT]
  rcases hn₀ n hn T hT' with hline | ⟨S, hS⟩
  · exact Or.inl hline
  · refine Or.inr ⟨S, ?_⟩
    have hc1 : (0 : ℝ) < 1 + c := by linarith
    have hkd : (0 : ℝ) < (k : ℝ) ^ d0 := pow_pos (by linarith) d0
    -- Convert `(1+c) * T.card * k^d0 ≤ pullback.card * k^n` (with `d * k^n ≤ T.card`)
    -- into `(1+c) * d * k^d0 ≤ pullback.card`.
    have key : (1 + c) * d * (k : ℝ) ^ d0 * (k : ℝ) ^ n ≤
        (((Finset.univ : Finset (Fin d0 → Fin k)).filter (fun x => S x ∈ T)).card : ℝ)
          * (k : ℝ) ^ n := by
      calc (1 + c) * d * (k : ℝ) ^ d0 * (k : ℝ) ^ n
          = ((1 + c) * (k : ℝ) ^ d0) * (d * (k : ℝ) ^ n) := by ring
        _ ≤ ((1 + c) * (k : ℝ) ^ d0) * (T.card : ℝ) :=
              mul_le_mul_of_nonneg_left hT (by positivity)
        _ = (1 + c) * (T.card : ℝ) * (k : ℝ) ^ d0 := by ring
        _ ≤ (((Finset.univ : Finset (Fin d0 → Fin k)).filter (fun x => S x ∈ T)).card : ℝ)
              * (k : ℝ) ^ n := hS
    exact le_of_mul_le_mul_right key hkpos

end Commons.Combinatorics.Ramsey
