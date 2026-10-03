import Mathlib

/-!
# A packing bound for separated points in a disc

Given a finite set `t` of points of `ℂ` contained in the closed disc of radius `M` around `x`,
and with pairwise distance at least `2ρ` (`ρ > 0`), the cardinality of `t` is at most a
constant times `(1 + M/ρ)^2`.  The constant `1` works.

The proof is the usual area estimate: the open discs of radius `ρ` centred at the points of `t`
are pairwise disjoint (separation `≥ 2ρ`), each of them is contained in the closed disc of
radius `M + ρ` around `x`, and the area of a disc of radius `r` in `ℂ` is `r^2 * π`.
-/

namespace Work.Dim.Packing

open MeasureTheory Metric

/-- The area of an open disc of nonnegative radius `r` in `ℂ` is `r^2 * π`. -/
lemma volume_real_ball (a : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    volume.real (Metric.ball a r) = r ^ 2 * Real.pi := by
  rw [MeasureTheory.measureReal_def, Complex.volume_ball, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hr, ENNReal.coe_toReal, NNReal.coe_real_pi]

/-- The area of a closed disc of nonnegative radius `r` in `ℂ` is `r^2 * π`. -/
lemma volume_real_closedBall (a : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    volume.real (Metric.closedBall a r) = r ^ 2 * Real.pi := by
  rw [MeasureTheory.measureReal_def, Complex.volume_closedBall, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hr, ENNReal.coe_toReal, NNReal.coe_real_pi]

theorem packing :
    ∃ C : ℝ, 0 < C ∧ ∀ (x : ℂ) (M ρ : ℝ), 0 < ρ → ∀ t : Finset ℂ,
      (∀ c ∈ t, c ∈ Metric.closedBall x M) →
      (∀ c ∈ t, ∀ c' ∈ t, c ≠ c' → 2 * ρ ≤ dist c c') →
      (t.card : ℝ) ≤ C * (1 + M / ρ) ^ 2 := by
  refine ⟨1, one_pos, ?_⟩
  intro x M ρ hρ t hsub hsep
  rcases lt_or_ge M 0 with hM | hM
  · -- then the disc is empty and so is `t`
    have ht : t = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro c hc
      have hcx : dist c x ≤ M := by
        have h := hsub c hc
        rwa [Metric.mem_closedBall] at h
      have := dist_nonneg (x := c) (y := x)
      linarith
    rw [ht]
    simp only [Finset.card_empty, Nat.cast_zero, one_mul]
    exact sq_nonneg _
  · -- the discs of radius `ρ` around the points are disjoint and lie in the disc of radius `M + ρ`
    have hdisj : Set.PairwiseDisjoint (↑t : Set ℂ) (fun c => Metric.ball c ρ) := by
      intro a ha b hb hab
      change Disjoint (Metric.ball a ρ) (Metric.ball b ρ)
      rw [Set.disjoint_left]
      intro z hza hzb
      rw [Metric.mem_ball] at hza hzb
      rw [dist_comm] at hza
      have h2 := hsep a (Finset.mem_coe.mp ha) b (Finset.mem_coe.mp hb) hab
      linarith [dist_triangle a z b]
    have hsum : volume.real (⋃ c ∈ t, Metric.ball c ρ)
        = ∑ c ∈ t, volume.real (Metric.ball c ρ) :=
      measureReal_biUnion_finset hdisj (fun b _ => measurableSet_ball) (fun b _ => by
        rw [Complex.volume_ball]
        exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) ENNReal.coe_ne_top)
    have hmono : volume.real (⋃ c ∈ t, Metric.ball c ρ)
        ≤ volume.real (Metric.closedBall x (M + ρ)) := by
      refine measureReal_mono ?_ ?_
      · intro z hz
        simp only [Set.mem_iUnion] at hz
        obtain ⟨c, hc, hzc⟩ := hz
        rw [Metric.mem_ball] at hzc
        rw [Metric.mem_closedBall]
        have hcx : dist c x ≤ M := by
          have h := hsub c (Finset.mem_coe.mp hc)
          rwa [Metric.mem_closedBall] at h
        have : dist z x < M + ρ := by
          calc dist z x ≤ dist z c + dist c x := dist_triangle z c x
            _ < ρ + M := by linarith
            _ = M + ρ := by ring
        exact this.le
      · rw [Complex.volume_closedBall]
        exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) ENNReal.coe_ne_top
    have hsumval : ∑ c ∈ t, volume.real (Metric.ball c ρ)
        = (t.card : ℝ) * (ρ ^ 2 * Real.pi) := by
      trans ∑ c ∈ t, (ρ ^ 2 * Real.pi)
      · exact Finset.sum_congr rfl (fun c _ => volume_real_ball c hρ.le)
      · rw [Finset.sum_const, nsmul_eq_mul]
    have hclosed : volume.real (Metric.closedBall x (M + ρ)) = (M + ρ) ^ 2 * Real.pi :=
      volume_real_closedBall x (by linarith)
    have hineq : (t.card : ℝ) * (ρ ^ 2 * Real.pi) ≤ (M + ρ) ^ 2 * Real.pi := by
      rw [← hsumval, ← hsum, ← hclosed]
      exact hmono
    have h4 : (t.card : ℝ) * ρ ^ 2 ≤ (M + ρ) ^ 2 := by
      have h := hineq
      rw [← mul_assoc] at h
      exact le_of_mul_le_mul_right h Real.pi_pos
    have hsq : (M + ρ) ^ 2 / ρ ^ 2 = (1 + M / ρ) ^ 2 := by
      field_simp
      ring
    have hfinal : (t.card : ℝ) ≤ (1 + M / ρ) ^ 2 := by
      rw [← hsq]
      exact (le_div_iff₀ (pow_pos hρ 2)).mpr h4
    simpa using hfinal

end Work.Dim.Packing
