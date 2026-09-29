import Mathlib
import Submission.Work.TMComp.MAnalytic.propagate_defs

/-!
# Growing a ball in place

Given a state `(y, R) ∈ G W r a m` whose doubled ball `closedBall y (2R)` lies inside `W`,
and given a larger room `closedBall y ρ ⊆ W`, we can grow the radius in place: repeatedly
applying `Step` at the *same* centre `y` multiplies the radius by `√2` while the doubled ball
stays inside `W`, i.e. while the radius stays at most `ρ/2`.  Hence some state `(y, R')` is
reachable with `closedBall y (2R') ⊆ W` and `R' * √2 ≥ ρ/2`.

Concretely, with `T = ρ/(2√2)` and the sequence `M_j = R (√2)^j`, the least index `k` with
`M_k ≥ T` satisfies `M_k < T√2 = ρ/2` (when `k ≥ 1`), so `R' = M_k` is admissible; the case
`k = 0` is covered by the given hypothesis `closedBall y (2R) ⊆ W`.
-/

namespace Work.TMComp.MAnalytic

theorem grow_inplace_geom {W : Set ℂ} {r : ℝ} {a : ℂ} {m : ℕ} {y : ℂ} {R ρ : ℝ}
    (hq : (y, R) ∈ G W r a m) (hR : 0 < R) (hρ : 0 < ρ)
    (hdeep : Metric.closedBall y (2 * R) ⊆ W) (hroom : Metric.closedBall y ρ ⊆ W) :
    ∃ m' R', (y, R') ∈ G W r a m' ∧ Metric.closedBall y (2 * R') ⊆ W ∧
      ρ / 2 ≤ R' * Real.sqrt 2 := by
  classical
  have hcpos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hc1 : (1 : ℝ) < Real.sqrt 2 := Real.one_lt_sqrt_two
  have hTpos : 0 < ρ / (2 * Real.sqrt 2) := by positivity
  have hmul : (2 * Real.sqrt 2) * (ρ / (2 * Real.sqrt 2)) = ρ := by
    rw [mul_comm]
    exact div_mul_cancel₀ ρ (by positivity)
  -- a radius below the threshold has its doubled ball inside `W`
  have hsmall : ∀ s : ℝ, s < ρ / (2 * Real.sqrt 2) → 2 * s ≤ ρ := by
    intro s hs
    have h1 : 2 * s < 2 * (ρ / (2 * Real.sqrt 2)) := by linarith
    have hc2 : (2 : ℝ) ≤ 2 * Real.sqrt 2 := by linarith
    have h2 : 2 * (ρ / (2 * Real.sqrt 2)) ≤ ρ := by
      have := mul_le_mul_of_nonneg_right hc2 (le_of_lt hTpos)
      linarith [this, hmul]
    linarith
  have hball₂ : ∀ s : ℝ, 2 * s ≤ ρ → Metric.closedBall y (2 * s) ⊆ W :=
    fun s hs => subset_trans (Metric.closedBall_subset_closedBall hs) hroom
  -- reaching the threshold gives the required final radius
  have hfin : ∀ s : ℝ, ρ / (2 * Real.sqrt 2) ≤ s → ρ / 2 ≤ s * Real.sqrt 2 := by
    intro s hs
    have h2 : ρ / (2 * Real.sqrt 2) * Real.sqrt 2 = ρ / 2 := by field_simp
    have h1 := mul_le_mul_of_nonneg_right hs (le_of_lt hcpos)
    linarith
  -- iterating the step at the fixed centre `y` gives the state `(y, R * (√2)^j)`
  have hiter : ∀ j : ℕ, (∀ i < j, R * (Real.sqrt 2)^i < ρ / (2 * Real.sqrt 2)) →
      (y, R * (Real.sqrt 2)^j) ∈ G W r a (m + j) := by
    intro j
    induction j with
    | zero => intro _; simpa using hq
    | succ j ih =>
      intro h
      have hstep : Step W y (R * (Real.sqrt 2)^j) y (R * (Real.sqrt 2)^(j+1)) :=
        ⟨by positivity, hball₂ _ (hsmall _ (h j (Nat.lt_succ_self j))), by
          simp only [sub_self, norm_zero, zero_add]
          rw [pow_succ]
          exact le_of_eq (by ring)⟩
      have hmem : (y, R * (Real.sqrt 2)^j) ∈ G W r a (m + j) :=
        ih (fun i hi => h i (hi.trans (Nat.lt_succ_self j)))
      show (y, R * (Real.sqrt 2)^(j+1)) ∈
        G W r a (m + j) ∪ {p | ∃ q ∈ G W r a (m + j), Step W q.1 q.2 p.1 p.2}
      exact Or.inr ⟨(y, R * (Real.sqrt 2)^j), hmem, hstep⟩
  -- Archimedean: the least index at which the radius crosses the threshold
  have hex : ∃ k : ℕ, ρ / (2 * Real.sqrt 2) ≤ R * (Real.sqrt 2)^k ∧
      ∀ i < k, R * (Real.sqrt 2)^i < ρ / (2 * Real.sqrt 2) := by
    have hP : ∃ j : ℕ, ρ / (2 * Real.sqrt 2) ≤ R * (Real.sqrt 2)^j := by
      obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (ρ / (2 * Real.sqrt 2) / R) hc1
      refine ⟨N, ?_⟩
      have hN' : ρ / (2 * Real.sqrt 2) < (Real.sqrt 2)^N * R := by
        have h := mul_lt_mul_of_pos_right hN hR
        rwa [div_mul_cancel₀ _ (ne_of_gt hR)] at h
      linarith
    refine ⟨Nat.find hP, Nat.find_spec hP, ?_⟩
    intro i hi
    exact lt_of_not_ge (Nat.find_min hP hi)
  obtain ⟨k, hk_ge, hk_lt⟩ := hex
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · -- already at least the threshold: the given state works
    subst hk0
    refine ⟨m, R, hq, hdeep, hfin R ?_⟩
    rw [pow_zero, mul_one] at hk_ge
    exact hk_ge
  · -- grow the radius to `R * (√2)^k`
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    exact ⟨m + (j+1), R * (Real.sqrt 2)^(j+1), hiter (j+1) hk_lt, hball₂ _ (by
      have hjlt : R * (Real.sqrt 2)^j < ρ / (2 * Real.sqrt 2) := hk_lt j (by omega)
      have hden : (0 : ℝ) < 2 * Real.sqrt 2 := by positivity
      have h1 : R * (Real.sqrt 2)^j * (2 * Real.sqrt 2) < ρ := (lt_div_iff₀ hden).mp hjlt
      have hkey : 2 * (R * (Real.sqrt 2)^(j+1)) =
          R * (Real.sqrt 2)^j * (2 * Real.sqrt 2) := by
        rw [pow_succ]; ring
      linarith), hfin _ hk_ge⟩

end Work.TMComp.MAnalytic
