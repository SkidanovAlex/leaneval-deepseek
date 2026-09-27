import Mathlib
import Submission.Work.Drive.seeleyDefs

/-!
# The tail sums `ε_n` of the Seeley correction

For a moment sequence `(a, b)` we define

  `ε_n(s) = Σ_j a_j (1 - ρ (b_j s)) b_j^n`,

the "tail" sum controlling the obstruction to the polynomial part of the Seeley correction being
flat at `s = 0`.  We also record a uniform bound for the iterated derivatives of the cutoff `ρ`.
-/

open scoped ContDiff Topology

namespace Work.Drive

/-- `ε_n(s) = Σ_j a_j (1 - ρ(b_j s)) b_j^n`. -/
noncomputable def seeleyEps (a b : ℕ → ℝ) (n : ℕ) (s : ℝ) : ℝ :=
  ∑' j : ℕ, a j * (b j) ^ n * (1 - seeleyRho (b j * s))

/-- `S_q = Σ_j |a_j| b_j^q`, the `q`-th absolute moment of the weight sequence. -/
noncomputable def seeleyS (a b : ℕ → ℝ) (q : ℕ) : ℝ := ∑' j : ℕ, |a j| * (b j) ^ q

lemma seeleyS_nonneg {a b : ℕ → ℝ} (hb : ∀ j : ℕ, 0 < b j) (q : ℕ) : 0 ≤ seeleyS a b q := by
  rw [seeleyS]
  exact tsum_nonneg fun j => mul_nonneg (abs_nonneg _) (pow_nonneg (le_of_lt (hb j)) q)

/-- For each `k` there is a uniform bound for the `k`-th derivative of the cutoff `ρ`
(it has compact support and is smooth). -/
lemma seeleyRho_deriv_bdd (k : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y : ℝ, |iteratedDeriv k seeleyRho y| ≤ M := by
  have hcont : Continuous (fun y : ℝ => iteratedDeriv k seeleyRho y) :=
    seeleyRho_contDiff.continuous_iteratedDeriv k (WithTop.coe_le_coe.mpr le_top)
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (f := fun y : ℝ => iteratedDeriv k seeleyRho y) hcont.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun y => ?_⟩
  by_cases hy : |y| ≤ 1
  · have hy' : y ∈ Set.Icc (-1 : ℝ) 1 := by
      rw [Set.mem_Icc]
      exact ⟨neg_le_of_abs_le hy, le_of_abs_le hy⟩
    have h := hC y hy'
    rw [Real.norm_eq_abs] at h
    exact h.trans (le_max_left _ _)
  · have hy' : 1 < |y| := not_le.mp hy
    have hev : seeleyRho =ᶠ[𝓝 y] (fun _ => (0 : ℝ)) := by
      filter_upwards [Metric.ball_mem_nhds y (by linarith : (0:ℝ) < |y| - 1)] with z hz
      rw [Metric.mem_ball, dist_eq_norm, Real.norm_eq_abs] at hz
      have h1 : 1 ≤ |z| := by
        have h2 := abs_sub_abs_le_abs_sub y z
        have h3 : |y - z| < |y| - 1 := by rwa [abs_sub_comm] at hz
        linarith
      exact seeleyRho_eq_zero h1
    rw [Filter.EventuallyEq.iteratedDeriv_eq k hev, iteratedDeriv_const]
    split_ifs <;> simpa using le_max_right C 0

/-- A uniform bound for the `k`-th derivative of `ρ`. -/
noncomputable def seeleyRhoD (k : ℕ) : ℝ := Classical.choose (seeleyRho_deriv_bdd k)

lemma seeleyRhoD_nonneg (k : ℕ) : 0 ≤ seeleyRhoD k :=
  (Classical.choose_spec (seeleyRho_deriv_bdd k)).1

lemma seeleyRhoD_bound (k : ℕ) (y : ℝ) : |iteratedDeriv k seeleyRho y| ≤ seeleyRhoD k :=
  (Classical.choose_spec (seeleyRho_deriv_bdd k)).2 y

end Work.Drive
