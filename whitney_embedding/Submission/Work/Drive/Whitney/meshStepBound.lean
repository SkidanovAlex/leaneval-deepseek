import Mathlib

set_option linter.unusedVariables false

namespace Work.Drive.Whitney

/-- Given a `C^∞` family `P` of continuous linear endomorphisms of `EuclideanSpace ℝ (Fin m)`
parametrised by `ℝ × ℝ`, and a function `c` bounded by `M` on `[-X', X']`, there is a number of
mesh steps `N > 0` such that, uniformly over all `x ∈ [-X', X']` and all `0 ≤ y ≤ c x`, the
`N`-fold subdivision of the segment `[y, c x]` has all its successive increments of `P`-values
of operator norm `< 1`. -/
theorem meshStepBound {m : ℕ}
    (P : ℝ × ℝ → EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (hP : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : (ℝ × ℝ) × EuclideanSpace ℝ (Fin m) => P q.1 q.2))
    {c : ℝ → ℝ} {X' M : ℝ} (hX : 0 ≤ X') (hM0 : 0 ≤ M)
    (hM : ∀ x ∈ Set.Icc (-X') X', |c x| ≤ M) :
    ∃ N : ℕ, 0 < N ∧ ∀ x : ℝ, |x| ≤ X' → ∀ y : ℝ, 0 ≤ y → y ≤ c x → ∀ j : ℕ, j < N →
      ‖P (x, y + (j : ℝ) / (N : ℝ) * (c x - y)) - P (x, y + ((j : ℝ) + 1) / (N : ℝ) * (c x - y))‖ < 1 := by
  -- The family `q ↦ P q` is continuous as a map into the Banach space of continuous linear maps:
  -- it suffices to test continuity against every vector, which is exactly what `hP` provides.
  have hFcont : Continuous (fun q : ℝ × ℝ => P q) := by
    rw [continuous_clm_apply]
    intro v
    exact hP.continuous.comp (Continuous.prodMk continuous_id continuous_const)
  -- The parameter set on which everything happens is compact.
  let K : Set (ℝ × ℝ) := Set.Icc (-X') X' ×ˢ Set.Icc 0 M
  have hK : IsCompact K := by
    show IsCompact (Set.Icc (-X') X' ×ˢ Set.Icc 0 M)
    exact isCompact_Icc.prod isCompact_Icc
  -- Heine–Cantor: `P` is uniformly continuous on `K`.
  have huc : UniformContinuousOn (fun q : ℝ × ℝ => P q) K :=
    hK.uniformContinuousOn_of_continuous hFcont.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδpos, hδ⟩ := huc 1 (by norm_num)
  -- Choose the mesh size `N` so that the step length `M / N` is below `δ`.
  obtain ⟨N, hN⟩ := exists_nat_gt (M / δ)
  have hNposR : (0:ℝ) < (N:ℝ) := lt_of_le_of_lt (div_nonneg hM0 (le_of_lt hδpos)) hN
  have hNpos : 0 < N := by exact_mod_cast hNposR
  have hMN : M / (N:ℝ) < δ := by
    rw [div_lt_iff₀ hNposR, mul_comm]
    exact (div_lt_iff₀ hδpos).mp hN
  refine ⟨N, hNpos, ?_⟩
  intro x hx y hy0 hyc j hj
  have hxIcc : x ∈ Set.Icc (-X') X' := by
    rw [Set.mem_Icc]; exact abs_le.mp hx
  have hcM : c x ≤ M := (abs_le.mp (hM x hxIcc)).2
  have hcy : 0 ≤ c x - y := sub_nonneg.mpr hyc
  -- The two consecutive mesh points.
  set a : ℝ := y + (j:ℝ)/(N:ℝ)*(c x - y) with ha
  set b : ℝ := y + ((j:ℝ)+1)/(N:ℝ)*(c x - y) with hb
  -- Both mesh points lie in `[0, M]`.
  have ha_ge : 0 ≤ a := by
    rw [ha]
    have h1 : 0 ≤ (j:ℝ)/(N:ℝ) := div_nonneg (Nat.cast_nonneg j) (le_of_lt hNposR)
    have := mul_nonneg h1 hcy
    linarith
  have ha_le : a ≤ M := by
    rw [ha]
    have h1 : (j:ℝ)/(N:ℝ) ≤ 1 := by
      rw [div_le_iff₀ hNposR]
      have : (j:ℝ) ≤ (N:ℝ) := by exact_mod_cast le_of_lt hj
      linarith
    have h3 := mul_le_mul_of_nonneg_right h1 hcy
    linarith
  have hb_ge : 0 ≤ b := by
    rw [hb]
    have h1 : 0 ≤ ((j:ℝ)+1)/(N:ℝ) := div_nonneg (by positivity) (le_of_lt hNposR)
    have := mul_nonneg h1 hcy
    linarith
  have hb_le : b ≤ M := by
    rw [hb]
    have h1 : ((j:ℝ)+1)/(N:ℝ) ≤ 1 := by
      rw [div_le_iff₀ hNposR]
      have hle : (j:ℝ) + 1 ≤ (N:ℝ) := by
        have h : ((j + 1 : ℕ) : ℝ) ≤ (N : ℝ) := Nat.cast_le.mpr (Nat.succ_le_of_lt hj)
        simpa [Nat.cast_add_one] using h
      linarith
    have h3 := mul_le_mul_of_nonneg_right h1 hcy
    linarith
  -- Membership in the compact parameter set.
  have hmem_a : (x, a) ∈ K := by
    change (x, a) ∈ Set.Icc (-X') X' ×ˢ Set.Icc 0 M
    exact ⟨hxIcc, ha_ge, ha_le⟩
  have hmem_b : (x, b) ∈ K := by
    change (x, b) ∈ Set.Icc (-X') X' ×ˢ Set.Icc 0 M
    exact ⟨hxIcc, hb_ge, hb_le⟩
  -- The two mesh points are within `δ` of each other.
  have hdist : dist (x, a) (x, b) < δ := by
    have hdiff : a - b = -((c x - y)/(N:ℝ)) := by
      rw [ha, hb]; ring
    rw [Prod.dist_eq, dist_self, max_eq_right dist_nonneg, Real.dist_eq, hdiff, abs_neg,
        abs_of_nonneg (div_nonneg hcy (le_of_lt hNposR))]
    calc (c x - y)/(N:ℝ) ≤ M/(N:ℝ) := div_le_div_of_nonneg_right (by linarith) (le_of_lt hNposR)
      _ < δ := hMN
  have hδab := hδ (x, a) hmem_a (x, b) hmem_b hdist
  simpa [dist_eq_norm] using hδab

end Work.Drive.Whitney
