import Mathlib
import Submission.Commons.GeometryOfNumbers.minkowski_polar_lower

namespace Commons.GeometryOfNumbers.EllNorm

open MeasureTheory Metric Filter Finset
open scoped Topology

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-- For a fixed vector `x`, the map `B ↦ B x` (through `Matrix.toLpLin`) is continuous. -/
private lemma continuous_toLpLin_apply {m : ℕ} (x : EuclideanSpace ℝ (Fin m)) :
    Continuous (fun B : Matrix (Fin m) (Fin m) ℝ => Matrix.toLpLin 2 2 B x) := by
  rw [show (fun B : Matrix (Fin m) (Fin m) ℝ => Matrix.toLpLin 2 2 B x)
      = fun B => WithLp.toLp 2 (fun i : Fin m => ∑ j, B i j * (WithLp.ofLp x) j) from by
    funext B
    exact PiLp.ext (fun i => by
      rw [Matrix.toLpLin_apply, PiLp.toLp_apply, Matrix.mulVec]
      rfl)]
  exact (PiLp.continuous_toLp 2 (fun _ : Fin m => ℝ)).comp
    (continuous_pi (fun i => continuous_finsetSum _ (fun j _ => by fun_prop)))

/-- Uniform bound on `‖B x‖²` for matrices with entries bounded by `ρ`. -/
private lemma norm_toLpLin_sq_le {m : ℕ} (B : Matrix (Fin m) (Fin m) ℝ) (ρ : ℝ)
    (hB : ∀ i j, |B i j| ≤ ρ) (x : EuclideanSpace ℝ (Fin m)) :
    ‖Matrix.toLpLin 2 2 B x‖ ^ 2 ≤ (m : ℝ) ^ 3 * ρ ^ 2 * ‖x‖ ^ 2 := by
  set c : ℝ := |ρ| with hc
  have hc0 : 0 ≤ c := by rw [hc]; exact abs_nonneg _
  have hBc : ∀ i j, |B i j| ≤ c := by
    intro i j
    by_cases hρ : 0 ≤ ρ
    · have h := hB i j
      rwa [hc, abs_of_nonneg hρ]
    · exfalso
      push Not at hρ
      have h := hB i j
      have h2 := abs_nonneg (B i j)
      linarith
  have hnorm : ‖Matrix.toLpLin 2 2 B x‖ ^ 2 = ∑ i, (∑ j, B i j * x j) ^ 2 := by
    rw [Matrix.toLpLin_apply, EuclideanSpace.real_norm_sq_eq]
    simp [Matrix.mulVec, dotProduct]
  have hsum : ∀ i : Fin m, (∑ j, B i j * x j) ^ 2 ≤ (c * ((m : ℝ) * ‖x‖)) ^ 2 := by
    intro i
    have h1 : |∑ j, B i j * x j| ≤ c * ∑ j, |x j| := by
      calc |∑ j, B i j * x j| ≤ ∑ j, |B i j * x j| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ j, |B i j| * |x j| := by simp [abs_mul]
        _ ≤ ∑ j, c * |x j| :=
            Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hBc i j) (abs_nonneg _))
        _ = c * ∑ j, |x j| := (Finset.mul_sum _ _ _).symm
    have h2 : ∑ j : Fin m, |x j| ≤ (m : ℝ) * ‖x‖ := by
      calc ∑ j : Fin m, |x j| ≤ ∑ j : Fin m, ‖x‖ :=
            Finset.sum_le_sum (fun j _ => by simpa using PiLp.norm_apply_le x j)
        _ = (m : ℝ) * ‖x‖ := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    calc (∑ j, B i j * x j) ^ 2 = |∑ j, B i j * x j| ^ 2 := (sq_abs _).symm
      _ ≤ (c * ∑ j, |x j|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
      _ ≤ (c * ((m : ℝ) * ‖x‖)) ^ 2 := by
            apply pow_le_pow_left₀ (mul_nonneg hc0 (Finset.sum_nonneg (fun j _ => abs_nonneg _)))
            exact mul_le_mul_of_nonneg_left h2 hc0
  calc ‖Matrix.toLpLin 2 2 B x‖ ^ 2 = ∑ i, (∑ j, B i j * x j) ^ 2 := hnorm
    _ ≤ ∑ i : Fin m, (c * ((m : ℝ) * ‖x‖)) ^ 2 := Finset.sum_le_sum (fun i _ => hsum i)
    _ = (m : ℝ) * (c * ((m : ℝ) * ‖x‖)) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = (m : ℝ) ^ 3 * ρ ^ 2 * ‖x‖ ^ 2 := by rw [hc, mul_pow, mul_pow, sq_abs]; ring

theorem continuousOn_integral_gauge_sq_gaussian {m : ℕ} (K : Set (EuclideanSpace ℝ (Fin m)))
    (hKcpt : IsCompact K) (hKcvx : Convex ℝ K)
    (hK0 : (0 : EuclideanSpace ℝ (Fin m)) ∈ interior K) (ρ : ℝ) :
    ContinuousOn (fun B : Matrix (Fin m) (Fin m) ℝ =>
        ∫ x : EuclideanSpace ℝ (Fin m),
          (gauge K (Matrix.toLpLin 2 2 B x)) ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2))
      {B : Matrix (Fin m) (Fin m) ℝ | ∀ i j, |B i j| ≤ ρ} := by
  obtain ⟨r, hr, hrK⟩ :
      ∃ r : ℝ, 0 < r ∧ Metric.ball (0 : EuclideanSpace ℝ (Fin m)) r ⊆ K := by
    obtain ⟨ε, hε, hεK⟩ := Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hK0)
    exact ⟨ε, hε, fun x hx => interior_subset (hεK hx)⟩
  have hKnhds : K ∈ 𝓝 (0 : EuclideanSpace ℝ (Fin m)) :=
    mem_of_superset (isOpen_interior.mem_nhds hK0) interior_subset
  have hgauge_cont : Continuous (gauge K) := continuous_gauge hKcvx hKnhds
  have hgauge_le : ∀ y : EuclideanSpace ℝ (Fin m), gauge K y ≤ ‖y‖ / r := by
    intro y
    have h := gauge_mono (absorbent_ball_zero hr) hrK y
    rwa [gauge_ball hr.le] at h
  haveI : FirstCountableTopology (Matrix (Fin m) (Fin m) ℝ) :=
    inferInstanceAs (FirstCountableTopology (Fin m → Fin m → ℝ))
  set C : ℝ := (m : ℝ) ^ 3 * ρ ^ 2 / r ^ 2 with hC
  refine continuousOn_of_dominated (bound := fun x : EuclideanSpace ℝ (Fin m) =>
      C * ‖x‖ ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2)) ?_ ?_ ?_ ?_
  · intro B _
    have hcont : Continuous (fun x : EuclideanSpace ℝ (Fin m) =>
        (gauge K (Matrix.toLpLin 2 2 B x)) ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2)) :=
      ((hgauge_cont.comp (by fun_prop :
          Continuous (fun x : EuclideanSpace ℝ (Fin m) => Matrix.toLpLin 2 2 B x))).pow 2).mul
        (by fun_prop)
    exact hcont.aestronglyMeasurable
  · intro B hB
    refine Eventually.of_forall (fun x => ?_)
    have hsq : (gauge K (Matrix.toLpLin 2 2 B x)) ^ 2 ≤ C * ‖x‖ ^ 2 := by
      calc (gauge K (Matrix.toLpLin 2 2 B x)) ^ 2
          ≤ (‖Matrix.toLpLin 2 2 B x‖ / r) ^ 2 :=
            pow_le_pow_left₀ (gauge_nonneg _) (hgauge_le _) 2
        _ = ‖Matrix.toLpLin 2 2 B x‖ ^ 2 / r ^ 2 := by rw [div_pow]
        _ ≤ ((m : ℝ) ^ 3 * ρ ^ 2 * ‖x‖ ^ 2) / r ^ 2 :=
            div_le_div_of_nonneg_right (norm_toLpLin_sq_le B ρ hB x) (sq_nonneg r)
        _ = C * ‖x‖ ^ 2 := by rw [hC]; ring
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)]
    exact mul_le_mul_of_nonneg_right hsq (Real.exp_pos _).le
  · refine ((Commons.GeometryOfNumbers.integrable_norm_sq_exp_pi (n := m)).const_mul C).congr ?_
    filter_upwards with x
    ring
  · refine Eventually.of_forall (fun x => ?_)
    have hcont : Continuous (fun B : Matrix (Fin m) (Fin m) ℝ =>
        (gauge K (Matrix.toLpLin 2 2 B x)) ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2)) :=
      ((hgauge_cont.comp (continuous_toLpLin_apply x)).pow 2).mul continuous_const
    exact hcont.continuousOn

end Commons.GeometryOfNumbers.EllNorm
