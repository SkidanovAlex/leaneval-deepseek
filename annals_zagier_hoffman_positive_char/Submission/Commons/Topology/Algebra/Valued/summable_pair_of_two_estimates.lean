import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import Mathlib.Topology.Algebra.Valued.ValuationTopology

open scoped Topology WithZero
open Filter

namespace Commons.Topology.Algebra.Valued

/-- Combinatorial core of `summable_pair_of_two_estimates`.

For a doubly indexed family `a` in a valued field with the two geometric estimates
`v (a p) ≤ C * δ ^ p.1` and `v (a p) ≤ γ ^ (q ^ p.2) * θv ^ p.1` (with `δ < 1`, `γ < 1`,
`C ≠ 0`, `2 ≤ q`, and powers of elements `< 1` tending to `0`), only finitely many indices
carry a term of valuation `≥ ε`.

The first estimate makes every term with large first index small; the second estimate makes
each vertical fibre `{p.1 < N}` eventually small in the second index. -/
private lemma eventually_cofinite_v_lt_pair {K Γ₀ : Type*} [Field K]
    [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    {a : ℕ × ℕ → K} {C δ γ θv ε : Γ₀} {q : ℕ} (hq : 2 ≤ q)
    (hδ : δ < 1) (hγ : γ < 1) (hC : C ≠ 0)
    (harch : ∀ x : Γ₀, x < 1 → ∀ ε : Γ₀, ε ≠ 0 → ∃ n : ℕ, x ^ n < ε)
    (h1 : ∀ p : ℕ × ℕ, Valued.v (a p) ≤ C * δ ^ p.1)
    (h2 : ∀ p : ℕ × ℕ, Valued.v (a p) ≤ γ ^ (q ^ p.2) * θv ^ p.1)
    (hε : ε ≠ 0) :
    ∀ᶠ p : ℕ × ℕ in Filter.cofinite, Valued.v (a p) < ε := by
  -- First estimate: all terms with first index `≥ N` are small.
  obtain ⟨N, hN⟩ := harch δ hδ (ε / C) (div_ne_zero hε hC)
  have hCpos : (0 : Γ₀) < C := lt_of_le_of_ne (zero_le : (0 : Γ₀) ≤ C) (Ne.symm hC)
  have hCN : C * δ ^ N < ε := by
    have h := mul_lt_mul_of_pos_left hN hCpos
    rwa [mul_div_cancel₀ ε hC] at h
  have hStep1 : ∀ p : ℕ × ℕ, N ≤ p.1 → Valued.v (a p) < ε := by
    intro p hp
    have hle : δ ^ p.1 ≤ δ ^ N :=
      pow_le_pow_of_le_one (zero_le : (0 : Γ₀) ≤ δ) (le_of_lt hδ) hp
    have hmul : C * δ ^ p.1 ≤ C * δ ^ N :=
      mul_le_mul_of_nonneg_left hle (zero_le : (0 : Γ₀) ≤ C)
    exact lt_of_le_of_lt (h1 p) (lt_of_le_of_lt hmul hCN)
  -- The factor `θv ^ p.1` stays bounded by `M` for `p.1 < N`.
  let M : Γ₀ := max 1 (θv ^ N)
  have hM1 : (1 : Γ₀) ≤ M := le_max_left (1 : Γ₀) (θv ^ N)
  have hMpos : (0 : Γ₀) < M := lt_of_lt_of_le zero_lt_one hM1
  have hMne : M ≠ 0 := ne_of_gt hMpos
  -- Choose `n` so that `γ ^ n * M < ε`.
  obtain ⟨n, hn⟩ := harch γ hγ (ε / M) (div_ne_zero hε hMne)
  have hnM : γ ^ n * M < ε := by
    have h := mul_lt_mul_of_pos_right hn hMpos
    rwa [div_mul_cancel₀ ε hMne] at h
  -- Second estimate: for first index `< N` and second index `≥ n` the terms are small.
  have hStep2 : ∀ p : ℕ × ℕ, p.1 < N → n ≤ p.2 → Valued.v (a p) < ε := by
    intro p hp1 hp2
    have hqge : n ≤ q ^ p.2 :=
      le_trans hp2 (le_trans (le_of_lt (Nat.lt_two_pow_self (n := p.2)))
        (Nat.pow_le_pow_left hq p.2))
    have hpow : γ ^ (q ^ p.2) ≤ γ ^ n :=
      pow_le_pow_of_le_one (zero_le : (0 : Γ₀) ≤ γ) (le_of_lt hγ) hqge
    have hθ : θv ^ p.1 ≤ M := by
      rcases le_or_gt (1 : Γ₀) θv with h | h
      · exact le_trans (pow_le_pow_right₀ h (le_of_lt hp1)) (le_max_right _ _)
      · exact le_trans (pow_le_one₀ (zero_le : (0 : Γ₀) ≤ θv) (le_of_lt h)) (le_max_left _ _)
    have hb : γ ^ (q ^ p.2) * θv ^ p.1 ≤ γ ^ n * M := mul_le_mul' hpow hθ
    exact lt_of_le_of_lt (h2 p) (lt_of_le_of_lt hb hnM)
  -- Only the finite box `{p.1 < N, p.2 < n}` can carry a large term.
  rw [Filter.eventually_cofinite]
  refine (Set.Finite.prod (Set.finite_Iio N) (Set.finite_Iio n)).subset ?_
  intro p hp
  simp only [Set.mem_ofPred_eq] at hp
  have hNlt : p.1 < N := by
    by_contra hcon
    exact absurd (hStep1 p (not_lt.mp hcon)) hp
  have hnlt : p.2 < n := by
    by_contra hcon
    exact absurd (hStep2 p hNlt (not_lt.mp hcon)) hp
  rw [Set.mem_prod, Set.mem_Iio, Set.mem_Iio]
  exact ⟨hNlt, hnlt⟩

theorem summable_pair_of_two_estimates {K Γ₀ : Type*} [Field K]
    [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K]
    [NonarchimedeanAddGroup K] {a : ℕ × ℕ → K} {C δ γ θv : Γ₀} {q : ℕ} (hq : 2 ≤ q)
    (hδ : δ < 1) (hγ : γ < 1) (hC : C ≠ 0)
    (harch : ∀ a₀ : Γ₀, a₀ < 1 → ∀ ε : Γ₀, ε ≠ 0 → ∃ n : ℕ, a₀ ^ n < ε)
    (h1 : ∀ p : ℕ × ℕ, Valued.v (a p) ≤ C * δ ^ p.1)
    (h2 : ∀ p : ℕ × ℕ, Valued.v (a p) ≤ γ ^ (q ^ p.2) * θv ^ p.1) : Summable a := by
  rw [NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero]
  rw [Filter.tendsto_def]
  intro U hU
  obtain ⟨γ₀, hγ₀U⟩ := Valued.mem_nhds_zero.mp hU
  -- Translate the neighbourhood basis element to a ball `{x | v x < ε}` in `Γ₀`.
  set ε : Γ₀ :=
    MonoidWithZeroHom.ValueGroup₀.embedding
      (f := MonoidWithZeroHom.ofClass (Valued.v : Valuation K Γ₀)) (γ₀.1) with hε
  have hε0 : ε ≠ 0 := by
    rw [hε]
    intro hh
    refine Units.ne_zero γ₀ (MonoidWithZeroHom.ValueGroup₀.embedding_injective ?_)
    rw [hh, map_zero]
  filter_upwards [eventually_cofinite_v_lt_pair hq hδ hγ hC harch h1 h2 hε0] with k hk
  refine hγ₀U ?_
  show Valued.v.restrict (a k) < (γ₀ : _)
  rw [Valuation.restrict_lt_iff_lt_embedding]
  exact hk

end Commons.Topology.Algebra.Valued
