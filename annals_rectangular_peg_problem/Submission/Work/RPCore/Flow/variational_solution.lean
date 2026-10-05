import Mathlib

/-!
# The fundamental solution of a linear ODE `M' = A t ∘L M`, `M 0 = 1`

For a time-dependent family of endomorphisms `A t` of a Banach space `E`, continuous on `[-T, T]`
and bounded by `K` there with `T * K < 1`, we produce one `M : ℝ → E →L[ℝ] E` with

* `M 0 = 1`,
* `HasDerivWithinAt M (A t ∘L M t) (Icc (-T) T) t` for all `t ∈ [-T, T]`,

together with the two Grönwall estimates on `[0, T]`

* `‖M t‖ ≤ exp (K * t)`,
* `‖M t - 1‖ ≤ exp (K * t) - 1`.

The solution is obtained by applying the Picard–Lindelöf theorem
(`IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt₀`) to the *operator* ODE
`M' = A t ∘L M` on the Banach space `E →L[ℝ] E`, with initial value the identity `1`; the smallness
condition `T * K < 1` is exactly what makes the radius `a = K T / (1 - K T)` of the
Picard–Lindelöf ball satisfy `K (a + 1) T ≤ a`, since the field `M ↦ A t ∘L M` is bounded by
`K (a + 1)` on the closed ball of radius `a` around `1`.

The two Grönwall estimates are proved below by the classical Grönwall lemma
`norm_le_gronwallBound_of_norm_deriv_right_le` applied with `(δ, ε) = (1, 0)` and `(δ, ε) = (0, K)`
on the interval `[0, T]`; the pointwise derivative hypothesis on the two-sided interval `[-T, T]` is
turned into one on `(0, T)` using `HasDerivWithinAt.hasDerivAt`, since every point of `(0, T)` is an
interior point of `[-T, T]`.
-/

open Set Metric
open scoped NNReal

set_option autoImplicit false

noncomputable section

namespace Work.RPCore.Flow

/-- Existence of a fundamental solution of the linear ODE `M' = A t ∘L M` with `M 0 = 1` on the
interval `[-T, T]`. -/
theorem variational_solution_exists {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (A : ℝ → E →L[ℝ] E) {K T : ℝ} (hT : 0 < T)
    (hA : ContinuousOn A (Set.Icc (-T) T)) (hK : ∀ t ∈ Set.Icc (-T) T, ‖A t‖ ≤ K)
    (hTK : T * K < 1) :
    ∃ M : ℝ → E →L[ℝ] E, M 0 = 1 ∧
      (∀ t ∈ Set.Icc (-T) T, HasDerivWithinAt M (A t ∘L M t) (Set.Icc (-T) T) t) := by
  have hK0 : 0 ≤ K := le_trans (norm_nonneg (A 0)) (hK 0 ⟨by linarith, by linarith⟩)
  have hc0 : 0 ≤ K * T := mul_nonneg hK0 hT.le
  have ha0 : 0 ≤ K * T / (1 - K * T) := div_nonneg hc0 (by linarith)
  have hL0 : 0 ≤ K * (K * T / (1 - K * T) + 1) := mul_nonneg hK0 (by linarith)
  -- radius of the closed ball on which the Picard–Lindelöf assumptions are checked
  set a : ℝ≥0 := ⟨K * T / (1 - K * T), ha0⟩ with ha
  -- bound on the norm of the vector field `M ↦ A t ∘L M` on that ball
  set L : ℝ≥0 := ⟨K * (K * T / (1 - K * T) + 1), hL0⟩ with hL
  have hLe : (L : ℝ) = K * (K * T / (1 - K * T) + 1) := rfl
  have hae : (a : ℝ) = K * T / (1 - K * T) := rfl
  have ht₀ : (0 : ℝ) ∈ Set.Icc (-T) T := ⟨by linarith, by linarith⟩
  -- the vector field is Lipschitz in the operator variable with the same constant `K`
  have hlips : ∀ t ∈ Set.Icc (-T) T,
      LipschitzOnWith ⟨K, hK0⟩ (fun (M : E →L[ℝ] E) => A t ∘L M)
        (closedBall (1 : E →L[ℝ] E) ↑a) := by
    intro t ht
    refine LipschitzOnWith.of_dist_le_mul fun x _ y _ => ?_
    rw [dist_eq_norm, dist_eq_norm]
    calc ‖A t ∘L x - A t ∘L y‖ = ‖A t ∘L (x - y)‖ := by
          rw [← ContinuousLinearMap.comp_sub]
      _ ≤ ‖A t‖ * ‖x - y‖ := ContinuousLinearMap.opNorm_comp_le (A t) (x - y)
      _ ≤ K * ‖x - y‖ := mul_le_mul_of_nonneg_right (hK t ht) (norm_nonneg _)
  -- continuity in time
  have hcont : ∀ x ∈ closedBall (1 : E →L[ℝ] E) ↑a,
      ContinuousOn (fun t => A t ∘L x) (Set.Icc (-T) T) := by
    intro x _
    simpa using hA.clm_comp (continuousOn_const :
      ContinuousOn (fun _ : ℝ => x) (Set.Icc (-T) T))
  -- norm bound on the ball, with constant `L = K * (a + 1)`
  have hnorm : ∀ t ∈ Set.Icc (-T) T, ∀ x ∈ closedBall (1 : E →L[ℝ] E) ↑a,
      ‖A t ∘L x‖ ≤ (L : ℝ) := by
    intro t ht x hx
    have h1n : ‖(1 : E →L[ℝ] E)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    have hx' : ‖x‖ ≤ K * T / (1 - K * T) + 1 := by
      have h1 : ‖x - 1‖ ≤ K * T / (1 - K * T) := by
        rw [← dist_eq_norm]
        exact mem_closedBall.mp hx
      calc ‖x‖ = ‖(x - 1) + 1‖ := by rw [sub_add_cancel]
        _ ≤ ‖x - 1‖ + ‖1‖ := norm_add_le _ _
        _ ≤ K * T / (1 - K * T) + 1 := by linarith
    rw [hLe]
    calc ‖A t ∘L x‖ ≤ ‖A t‖ * ‖x‖ := ContinuousLinearMap.opNorm_comp_le (A t) x
      _ ≤ K * ‖x‖ := mul_le_mul_of_nonneg_right (hK t ht) (norm_nonneg _)
      _ ≤ K * (K * T / (1 - K * T) + 1) := mul_le_mul_of_nonneg_left hx' hK0
  -- the time-length constraint of the Picard–Lindelöf theorem
  have hmul : (L : ℝ) * max (T - (0 : ℝ)) (0 - (-T)) ≤ (a : ℝ) - 0 := by
    have key : K * (K * T / (1 - K * T) + 1) * T = K * T / (1 - K * T) := by
      have h1c : (1 : ℝ) - K * T ≠ 0 := by linarith
      field_simp
      ring
    have hmax : max (T - (0 : ℝ)) (0 - (-T)) = T := by simp
    rw [hLe, hae, hmax, key, sub_zero]
  have hPL : IsPicardLindelof (fun t (M : E →L[ℝ] E) => A t ∘L M) (tmin := -T) (tmax := T)
      ⟨0, ht₀⟩ (1 : E →L[ℝ] E) a 0 L ⟨K, hK0⟩ := ⟨hlips, hcont, hnorm, hmul⟩
  obtain ⟨M, hM0, hMder⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  exact ⟨M, hM0, hMder⟩

theorem variational_solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (A : ℝ → E →L[ℝ] E) {K T : ℝ} (hT : 0 < T)
    (hA : ContinuousOn A (Set.Icc (-T) T)) (hK : ∀ t ∈ Set.Icc (-T) T, ‖A t‖ ≤ K)
    (hTK : T * K < 1) :
    ∃ M : ℝ → E →L[ℝ] E, M 0 = 1 ∧
      (∀ t ∈ Set.Icc (-T) T, HasDerivWithinAt M (A t ∘L M t) (Set.Icc (-T) T) t) ∧
      (∀ t ∈ Set.Icc 0 T, ‖M t‖ ≤ Real.exp (K * t)) ∧
      (∀ t ∈ Set.Icc 0 T, ‖M t - 1‖ ≤ Real.exp (K * t) - 1) := by
  obtain ⟨M, hM0, hMder⟩ := variational_solution_exists A hT hA hK hTK
  have hK0 : 0 ≤ K := le_trans (norm_nonneg (A 0)) (hK 0 ⟨by linarith, by linarith⟩)
  -- Grönwall on `[0, T]`, where `M` is only known to satisfy the ODE on `[-T, T]`
  have hfull : ContinuousOn M (Set.Icc (-T) T) := fun t ht => (hMder t ht).continuousWithinAt
  have hcont : ContinuousOn M (Set.Icc (0 : ℝ) T) :=
    hfull.mono (Set.Icc_subset_Icc (by linarith) le_rfl)
  have hder : ∀ t ∈ Set.Ico (0 : ℝ) T, HasDerivWithinAt M (A t ∘L M t) (Set.Ici t) t := by
    intro t ht
    exact ((hMder t ⟨by linarith [ht.1], ht.2.le⟩).hasDerivAt
      (Icc_mem_nhds (by linarith [ht.1]) ht.2)).hasDerivWithinAt
  have hb1 : ∀ t ∈ Set.Icc 0 T, ‖M t‖ ≤ Real.exp (K * t) := by
    intro x hx
    have h := norm_le_gronwallBound_of_norm_deriv_right_le (a := (0 : ℝ)) (b := T)
      (f := M) (f' := fun t => A t ∘L M t) (δ := 1) (K := K) (ε := 0) hcont hder ?_ ?_ x hx
    · rw [gronwallBound_ε0] at h
      simpa only [one_mul, sub_zero] using h
    · rw [hM0]
      exact ContinuousLinearMap.norm_id_le
    · intro t ht
      calc ‖A t ∘L M t‖ ≤ ‖A t‖ * ‖M t‖ := ContinuousLinearMap.opNorm_comp_le (A t) (M t)
        _ ≤ K * ‖M t‖ := mul_le_mul_of_nonneg_right (hK t ⟨by linarith [ht.1], ht.2.le⟩) (norm_nonneg _)
        _ = K * ‖M t‖ + 0 := by ring
  have hb2 : ∀ t ∈ Set.Icc 0 T, ‖M t - 1‖ ≤ Real.exp (K * t) - 1 := by
    intro x hx
    have hbound : ∀ t ∈ Set.Ico (0 : ℝ) T, ‖A t ∘L M t‖ ≤ K * ‖M t - 1‖ + K := by
      intro t ht
      have h1n : ‖(1 : E →L[ℝ] E)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
      calc ‖A t ∘L M t‖ ≤ ‖A t‖ * ‖M t‖ := ContinuousLinearMap.opNorm_comp_le (A t) (M t)
        _ ≤ K * ‖M t‖ := mul_le_mul_of_nonneg_right (hK t ⟨by linarith [ht.1], ht.2.le⟩) (norm_nonneg _)
        _ ≤ K * (‖M t - 1‖ + 1) := by
              have hsplit : ‖M t‖ = ‖(M t - 1) + 1‖ := by rw [sub_add_cancel]
              rw [hsplit]
              nlinarith [norm_add_le (M t - 1) (1 : E →L[ℝ] E), norm_nonneg (M t - 1),
                norm_nonneg (M t - 1 + 1), h1n, hK0]
        _ = K * ‖M t - 1‖ + K := by ring
    have h := norm_le_gronwallBound_of_norm_deriv_right_le (a := (0 : ℝ)) (b := T)
      (f := fun t => M t - 1) (f' := fun t => A t ∘L M t) (δ := 0) (K := K) (ε := K)
      (hcont.sub continuousOn_const) (fun t ht => (hder t ht).sub_const 1) ?_ hbound x hx
    · rcases eq_or_ne K 0 with hK0' | hK0'
      · subst hK0'
        simpa [gronwallBound_K0] using h
      · rw [gronwallBound_of_K_ne_0 hK0'] at h
        simpa only [zero_mul, zero_add, div_self hK0', one_mul, sub_zero] using h
    · rw [hM0]
      simp
  exact ⟨M, hM0, hMder, hb1, hb2⟩

end Work.RPCore.Flow
