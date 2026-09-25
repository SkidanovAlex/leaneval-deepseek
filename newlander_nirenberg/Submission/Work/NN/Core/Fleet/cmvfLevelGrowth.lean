import Mathlib

namespace Work.NN.Core.Fleet

/-- For the recursion `k (m+1) = ⌊k m * θ⌋₊` with `θ = 1 + 1/K` (`K ≥ 1`) and `k 0 = K`,
the sequence grows at least exponentially and is everywhere positive. -/
theorem cmvfLevelGrowth {θ : ℝ} (hθ : 1 < θ) {K : ℕ} (hK : 1 ≤ K)
    (hKθ : (K : ℝ) * (θ - 1) = 1) {k : ℕ → ℕ} (h0 : k 0 = K)
    (hrec : ∀ m, k (m+1) = ⌊(k m : ℝ) * θ⌋₊) :
    ∃ c ρ : ℝ, 0 < c ∧ 1 < ρ ∧ (∀ m, c * ρ ^ m ≤ (k m : ℝ)) ∧ (∀ m, 1 ≤ k m) := by
  have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hKne : (K : ℝ) ≠ 0 := ne_of_gt hKpos
  -- `θ - 1 = 1/K`
  have hθsub : θ - 1 = (K : ℝ)⁻¹ := eq_inv_of_mul_eq_one_right hKθ
  have hθeq : θ = 1 + (K : ℝ)⁻¹ := by linarith
  -- The crude linear growth: `K + m ≤ k m`.
  have hmain : ∀ m, K + m ≤ k m := by
    intro m
    induction m with
    | zero => simp [h0]
    | succ m ih =>
        have hkmK : (K : ℝ) ≤ (k m : ℝ) := by
          have h1 : (K : ℝ) ≤ ((K + m : ℕ) : ℝ) := by push_cast; linarith
          exact le_trans h1 (by exact_mod_cast ih)
        -- Since `k m ≥ K`, we have `k m * θ ≥ k m + 1`.
        have hge : (k m : ℝ) + 1 ≤ (k m : ℝ) * θ := by
          have hinv : (1 : ℝ) ≤ (k m : ℝ) * (K : ℝ)⁻¹ := by
            rw [← div_eq_mul_inv, one_le_div hKpos]
            exact hkmK
          calc (k m : ℝ) + 1 ≤ (k m : ℝ) + (k m : ℝ) * (K : ℝ)⁻¹ := by linarith
            _ = (k m : ℝ) * θ := by rw [hθeq]; ring
        have hfloor : ⌊(k m : ℝ) + 1⌋₊ = k m + 1 := by
          rw [Nat.floor_add_one (by positivity), Nat.floor_natCast]
        have hstep : k m + 1 ≤ k (m+1) := by
          rw [hrec m]
          calc k m + 1 = ⌊(k m : ℝ) + 1⌋₊ := hfloor.symm
            _ ≤ ⌊(k m : ℝ) * θ⌋₊ := Nat.floor_mono hge
        omega
  have hKle : ∀ m, K ≤ k m := by
    intro m
    have := hmain m
    omega
  -- Choose `1 < ρ < θ`, namely the midpoint.
  set ρ : ℝ := (θ + 1) / 2 with hρdef
  have hρ1 : 1 < ρ := by rw [hρdef]; linarith
  have hρ0 : 0 < ρ := by linarith
  have hθρ : θ - ρ = 1 / (2 * (K:ℝ)) := by
    rw [hρdef]
    have h1 : θ - (θ + 1) / 2 = (θ - 1) / 2 := by ring
    rw [h1, hθsub]
    field_simp
  -- Once `k m ≥ 2K`, the floor error `1` is dominated by `k m * (θ - ρ)`.
  have hgeo : ∀ j, (k K : ℝ) * ρ ^ j ≤ (k (K + j) : ℝ) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
        -- floor lower bound: `k (m+1) ≥ k m * θ - 1`
        have hstep : (k (K + j) : ℝ) * θ - 1 ≤ (k (K + j + 1) : ℝ) := by
          have h := Nat.lt_floor_add_one ((k (K + j) : ℝ) * θ)
          rw [← hrec (K + j)] at h
          linarith
        have h2K : 2 * (K:ℝ) ≤ (k (K + j) : ℝ) := by
          have hh : ((K + (K + j) : ℕ) : ℝ) ≤ (k (K + j) : ℝ) := by
            exact_mod_cast hmain (K + j)
          push_cast at hh
          linarith
        have hphi0 : 0 ≤ θ - ρ := by rw [hθρ]; positivity
        have hmul : 1 ≤ (k (K + j) : ℝ) * (θ - ρ) := by
          calc (1:ℝ) = 2 * (K:ℝ) * (θ - ρ) := by rw [hθρ]; field_simp
            _ ≤ (k (K + j) : ℝ) * (θ - ρ) := mul_le_mul_of_nonneg_right h2K hphi0
        have hmul' : 1 ≤ (k (K + j) : ℝ) * θ - (k (K + j) : ℝ) * ρ := by
          rw [mul_sub] at hmul; exact hmul
        have hkey : (k (K+j) : ℝ) * ρ ≤ (k (K+j+1) : ℝ) := by linarith
        calc (k K : ℝ) * ρ ^ (j+1) = (k K : ℝ) * ρ^j * ρ := by ring
          _ ≤ (k (K + j) : ℝ) * ρ := mul_le_mul_of_nonneg_right ih (le_of_lt hρ0)
          _ ≤ (k (K + j + 1) : ℝ) := hkey
  have hKc : (K:ℝ) ≤ (k K : ℝ) := by exact_mod_cast hKle K
  refine ⟨(K:ℝ) / ρ^K, ρ, ?_, hρ1, ?_, ?_⟩
  · exact div_pos hKpos (pow_pos hρ0 K)
  · intro m
    by_cases hm : m ≤ K
    · -- For `m ≤ K` use `ρ^m ≤ ρ^K` and `k m ≥ K`.
      have hρmle : ρ^m ≤ ρ^K := pow_le_pow_right₀ (le_of_lt hρ1) hm
      have hρKpos : 0 < ρ^K := pow_pos hρ0 K
      have h1 : (K:ℝ) / ρ^K * ρ^m ≤ (K:ℝ) := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hρKpos]
        exact mul_le_mul_of_nonneg_left hρmle (le_of_lt hKpos)
      exact le_trans h1 (by exact_mod_cast hKle m)
    · -- For `m ≥ K` use the geometric growth from level `K`.
      rw [not_le] at hm
      obtain ⟨j, rfl⟩ : ∃ j, m = K + j := ⟨m - K, (Nat.add_sub_cancel' hm.le).symm⟩
      have hρKne : ρ^K ≠ 0 := ne_of_gt (pow_pos hρ0 K)
      have hceq : (K:ℝ) / ρ^K * ρ^(K+j) = (K:ℝ) * ρ^j := by
        rw [pow_add, div_mul_eq_mul_div]
        rw [show (K:ℝ) * (ρ^K * ρ^j) = ρ^K * ((K:ℝ) * ρ^j) by ring]
        rw [mul_div_cancel_left₀ _ hρKne]
      rw [hceq]
      calc (K:ℝ) * ρ^j ≤ (k K : ℝ) * ρ^j := mul_le_mul_of_nonneg_right hKc (pow_nonneg (le_of_lt hρ0) j)
        _ ≤ (k (K+j) : ℝ) := hgeo j
  · intro m
    exact le_trans hK (hKle m)

end Work.NN.Core.Fleet
