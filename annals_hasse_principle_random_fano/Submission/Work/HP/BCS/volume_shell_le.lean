import Mathlib

/-!
# `Work.HP.BCS.volume_shell_le`

The volume of the shell `{v : A ≤ ‖v‖ ≤ B}` in a finite-dimensional real inner product space `V`
of dimension `m ≥ 1` is at most `vol(B(0,1)) * m * max 0 (B - A) * B^{m-1}`.

The proof is the exact formula `vol{A ≤ ‖v‖ ≤ B} = vol(B(0,1)) * (B^m - A^m)` (for `A ≤ B`),
which combines `MeasureTheory.Measure.addHaar_real_closedBall` with the additivity of a measure,
together with the mean-value estimate `B^m - A^m ≤ m * (B - A) * B^{m-1}` for `0 ≤ A ≤ B`.
-/

open MeasureTheory

namespace Work.HP.BCS

/-- Mean-value estimate for `t ↦ t^m` on `[A,B]`: `B^m - A^m ≤ m * (B - A) * B^{m-1}`
for `0 ≤ A ≤ B` and `m ≥ 1`. -/
private lemma pow_sub_pow_le (m : ℕ) (hm1 : 1 ≤ m) {A B : ℝ} (hA : 0 ≤ A) (hAB : A ≤ B) :
    B ^ m - A ^ m ≤ (m : ℝ) * (B - A) * B ^ (m - 1) := by
  have hB : 0 ≤ B := hA.trans hAB
  -- geometric-sum identity: `B^m - A^m = (∑_{i<m} A^i B^{m-1-i}) * (B - A)`
  have key : (∑ i ∈ Finset.range m, A ^ i * B ^ (m - 1 - i)) * (B - A) = B ^ m - A ^ m :=
    geom_sum₂_mul_of_le hAB m
  rw [← key]
  have hsum : ∑ i ∈ Finset.range m, A ^ i * B ^ (m - 1 - i) ≤ (m : ℝ) * B ^ (m - 1) := by
    calc ∑ i ∈ Finset.range m, A ^ i * B ^ (m - 1 - i)
        ≤ ∑ _i ∈ Finset.range m, B ^ (m - 1) := by
          apply Finset.sum_le_sum
          intro i hi
          rw [Finset.mem_range] at hi
          have hii : i + (m - 1 - i) = m - 1 := by omega
          calc A ^ i * B ^ (m - 1 - i) ≤ B ^ i * B ^ (m - 1 - i) :=
                mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hA hAB i) (pow_nonneg hB _)
            _ = B ^ (m - 1) := by rw [← pow_add, hii]
      _ = (m : ℝ) * B ^ (m - 1) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  calc (∑ i ∈ Finset.range m, A ^ i * B ^ (m - 1 - i)) * (B - A)
      ≤ ((m : ℝ) * B ^ (m - 1)) * (B - A) := mul_le_mul_of_nonneg_right hsum (by linarith)
    _ = (m : ℝ) * (B - A) * B ^ (m - 1) := by ring

theorem volume_shell_le {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (m : ℕ) (hm : Module.finrank ℝ V = m) (hm1 : 1 ≤ m) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    (MeasureTheory.volume {v : V | A ≤ ‖v‖ ∧ ‖v‖ ≤ B}) ≤
      ENNReal.ofReal (MeasureTheory.volume.real (Metric.ball (0 : V) 1) * (m : ℝ)
        * max 0 (B - A) * B ^ (m - 1)) := by
  classical
  have hnt : Nontrivial V := Module.nontrivial_of_finrank_pos (by rw [hm]; omega)
  by_cases hBA : B < A
  · -- the shell is empty
    have hSempty : {v : V | A ≤ ‖v‖ ∧ ‖v‖ ≤ B} = ∅ := by
      ext v
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro h1 h2
      linarith
    rw [hSempty, measure_empty]
    positivity
  · -- `A ≤ B`: compute the volume of the shell exactly
    have hBA' : A ≤ B := le_of_not_gt hBA
    have hSteq : {v : V | A ≤ ‖v‖ ∧ ‖v‖ ≤ B}
        = Metric.closedBall (0 : V) B \ Metric.ball (0 : V) A := by
      ext v
      simp only [Set.mem_ofPred_eq, Set.mem_sdiff, Metric.mem_closedBall, Metric.mem_ball,
        dist_zero_right]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h2, not_lt.mpr h1⟩
      · rintro ⟨h2, h1⟩; exact ⟨not_lt.mp h1, h2⟩
    have htmeas : MeasurableSet (Metric.ball (0 : V) A) := Metric.isOpen_ball.measurableSet
    have hsub : Metric.ball (0 : V) A ⊆ Metric.closedBall (0 : V) B := by
      intro v hv
      rw [Metric.mem_ball, dist_zero_right] at hv
      rw [Metric.mem_closedBall, dist_zero_right]
      linarith
    have hsfin : volume (Metric.closedBall (0 : V) B) ≠ ⊤ := measure_closedBall_lt_top.ne
    have hreal : volume.real {v : V | A ≤ ‖v‖ ∧ ‖v‖ ≤ B}
        = volume.real (Metric.closedBall (0 : V) B) - volume.real (Metric.ball (0 : V) A) := by
      rw [hSteq]
      exact measureReal_sdiff hsub htmeas hsfin
    have hV1nn : 0 ≤ volume.real (Metric.ball (0 : V) 1) := measureReal_nonneg
    have hs_val : volume.real (Metric.closedBall (0 : V) B)
        = B ^ m * volume.real (Metric.ball (0 : V) 1) := by
      have h := Measure.addHaar_real_closedBall (volume : Measure V) (0 : V) hB
      simpa only [hm] using h
    have ht_val : volume.real (Metric.ball (0 : V) A)
        = A ^ m * volume.real (Metric.ball (0 : V) 1) := by
      have h1 := Measure.addHaar_real_closedBall (volume : Measure V) (0 : V) hA
      have h2 := Measure.addHaar_real_closedBall_eq_addHaar_real_ball (volume : Measure V) (0 : V) A
      rw [← h2, h1, hm]
    have hSfin : volume {v : V | A ≤ ‖v‖ ∧ ‖v‖ ≤ B} ≠ ⊤ := by
      rw [hSteq]
      exact ((measure_mono Set.sdiff_subset).trans_lt measure_closedBall_lt_top).ne
    -- replace `volume` by `ENNReal.ofReal (volume.real ·)`
    rw [show volume {v : V | A ≤ ‖v‖ ∧ ‖v‖ ≤ B}
          = ENNReal.ofReal (volume.real {v : V | A ≤ ‖v‖ ∧ ‖v‖ ≤ B}) from
        (ENNReal.ofReal_toReal hSfin).symm]
    have hmax : max 0 (B - A) = B - A := max_eq_right (by linarith)
    rw [hmax]
    apply ENNReal.ofReal_le_ofReal
    rw [hreal, hs_val, ht_val]
    have hkey := pow_sub_pow_le m hm1 hA hBA'
    calc B ^ m * volume.real (Metric.ball (0 : V) 1)
          - A ^ m * volume.real (Metric.ball (0 : V) 1)
        = (B ^ m - A ^ m) * volume.real (Metric.ball (0 : V) 1) := by ring
      _ ≤ ((m : ℝ) * (B - A) * B ^ (m - 1)) * volume.real (Metric.ball (0 : V) 1) :=
          mul_le_mul_of_nonneg_right hkey hV1nn
      _ = volume.real (Metric.ball (0 : V) 1) * (m : ℝ) * (B - A) * B ^ (m - 1) := by ring

end Work.HP.BCS
