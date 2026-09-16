import Mathlib
import Submission.Commons.Topology.Algebra.Valued.summable_pair_of_two_estimates
import Submission.Commons.Topology.Algebra.Valued.summable_pair_of_two_estimates_arch

open scoped Topology WithZero
open Filter

namespace Commons.Topology.Algebra.Valued

/-- Variant of `eventually_cofinite_v_lt_pair` in which the second estimate carries an extra
nonzero constant `C₂`.  Only finitely many indices carry a term of valuation `≥ ε`. -/
private lemma eventually_cofinite_v_lt_pair_const {K Γ₀ : Type*} [Field K]
    [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    {a : ℕ × ℕ → K} {C C₂ δ γ θv ε : Γ₀} {q : ℕ} (hq : 2 ≤ q)
    (hδ : δ < 1) (hγ : γ < 1) (hC : C ≠ 0) (hC₂ : C₂ ≠ 0)
    (harch : ∀ x : Γ₀, x < 1 → ∀ ε : Γ₀, ε ≠ 0 → ∃ n : ℕ, x ^ n < ε)
    (h1 : ∀ p : ℕ × ℕ, Valued.v (a p) ≤ C * δ ^ p.1)
    (h2 : ∀ p : ℕ × ℕ, Valued.v (a p) ≤ C₂ * γ ^ (q ^ p.2) * θv ^ p.1)
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
  have hC₂pos : (0 : Γ₀) < C₂ := lt_of_le_of_ne (zero_le : (0 : Γ₀) ≤ C₂) (Ne.symm hC₂)
  -- Choose `n` so that `C₂ * γ ^ n * M < ε`.
  obtain ⟨n, hn⟩ := harch γ hγ (ε / (C₂ * M)) (div_ne_zero hε (mul_ne_zero hC₂ hMne))
  have hnM : C₂ * γ ^ n * M < ε := by
    have h := mul_lt_mul_of_pos_right hn (mul_pos hC₂pos hMpos)
    rw [div_mul_cancel₀ ε (mul_ne_zero hC₂ hMne)] at h
    rwa [← mul_assoc, mul_comm (γ ^ n) C₂] at h
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
    have hb : C₂ * γ ^ (q ^ p.2) * θv ^ p.1 ≤ C₂ * γ ^ n * M :=
      mul_le_mul (mul_le_mul_of_nonneg_left hpow (le_of_lt hC₂pos)) hθ
        (show (0 : Γ₀) ≤ θv ^ p.1 from zero_le)
        (show (0 : Γ₀) ≤ C₂ * γ ^ n from zero_le)
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

theorem summable_pair_of_two_estimates_const {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [NonarchimedeanAddGroup K] {a : ℕ × ℕ → K} {C C₂ δ γ θv : Γ₀} {q : ℕ} (hq : 2 ≤ q) (hδ : δ < 1) (hγ : γ < 1) (hC : C ≠ 0) (hC₂ : C₂ ≠ 0) (harch : ∀ a₀ : Γ₀, a₀ < 1 → ∀ ε : Γ₀, ε ≠ 0 → ∃ n : ℕ, a₀ ^ n < ε) (h1 : ∀ p : ℕ × ℕ, Valued.v (a p) ≤ C * δ ^ p.1) (h2 : ∀ p : ℕ × ℕ, Valued.v (a p) ≤ C₂ * γ ^ (q ^ p.2) * θv ^ p.1) : Summable a := by
  refine summable_of_tendsto_cofinite_v_zero_general (f := a) fun ε hε => ?_
  exact eventually_cofinite_v_lt_pair_const hq hδ hγ hC hC₂ harch h1 h2 hε

end Commons.Topology.Algebra.Valued
