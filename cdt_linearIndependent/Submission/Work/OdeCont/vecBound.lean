import Mathlib

namespace Work.OdeCont

/-- Uniform operator bound: a matrix family `A` continuous on a closed ball admits a constant `C` with
`‖A z · v‖ ≤ C ‖v‖` for every `z` in the open ball and every vector `v`. -/
lemma vecBound {k : ℕ} {A : ℂ → Fin k → Fin k → ℂ} {w : ℂ} {R : ℝ}
    (hA : ∀ i j : Fin k, ContinuousOn (fun z : ℂ => A z i j) (Metric.closedBall w R)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ Metric.ball w R, ∀ v : Fin k → ℂ,
      ‖(fun i : Fin k => ∑ j, A z i j * v j)‖ ≤ C * ‖v‖ := by
  by_cases hR : R ≤ 0
  · -- the open ball is empty, so any constant works
    refine ⟨0, le_refl 0, ?_⟩
    intro z hz v
    exfalso
    rw [Metric.mem_ball] at hz
    have : 0 ≤ dist z w := dist_nonneg
    linarith
  · replace hR : 0 < R := lt_of_not_ge hR
    -- each entry is bounded on the (nonempty, compact) closed ball
    have hne : (Metric.closedBall w R).Nonempty := ⟨w, Metric.mem_closedBall_self hR.le⟩
    have hb : ∀ i j : Fin k, ∃ M : ℝ, 0 ≤ M ∧ ∀ z ∈ Metric.closedBall w R, ‖A z i j‖ ≤ M := by
      intro i j
      obtain ⟨x, _hx, hxmax⟩ := (isCompact_closedBall w R).exists_isMaxOn hne (hA i j).norm
      exact ⟨‖A x i j‖, norm_nonneg _, fun z hz => hxmax hz⟩
    choose M' hM'0 hM'bound using hb
    -- a single constant dominating all entries on the closed ball
    set S : ℝ := ∑ i, ∑ j, M' i j with hS
    have hS0 : 0 ≤ S := by
      rw [hS]; exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hM'0 i j))
    have hMbound : ∀ z ∈ Metric.closedBall w R, ∀ i j, ‖A z i j‖ ≤ S := by
      intro z hz i j
      rw [hS]
      refine le_trans (hM'bound i j z hz) ?_
      calc M' i j ≤ ∑ j, M' i j := Finset.single_le_sum (fun b _ => hM'0 i b) (Finset.mem_univ j)
        _ ≤ ∑ i, ∑ j, M' i j :=
            Finset.single_le_sum (fun a _ => Finset.sum_nonneg (fun b _ => hM'0 a b)) (Finset.mem_univ i)
    refine ⟨(k : ℝ) * S, mul_nonneg (Nat.cast_nonneg _) hS0, ?_⟩
    intro z hz v
    have hz' : z ∈ Metric.closedBall w R := Metric.ball_subset_closedBall hz
    refine (pi_norm_le_iff_of_nonneg
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hS0) (norm_nonneg _))).2 ?_
    intro i
    calc ‖∑ j, A z i j * v j‖
        ≤ ∑ j, ‖A z i j * v j‖ := norm_sum_le _ _
      _ = ∑ j, ‖A z i j‖ * ‖v j‖ := by simp only [norm_mul]
      _ ≤ ∑ j, S * ‖v j‖ := by
            apply Finset.sum_le_sum
            intro j _
            exact mul_le_mul_of_nonneg_right (hMbound z hz' i j) (norm_nonneg _)
      _ = S * ∑ j, ‖v j‖ := by rw [Finset.mul_sum]
      _ ≤ S * ((k : ℝ) * ‖v‖) := by
            apply mul_le_mul_of_nonneg_left _ hS0
            calc ∑ j, ‖v j‖ ≤ ∑ j, ‖v‖ := Finset.sum_le_sum (fun j _ => norm_le_pi_norm v j)
              _ = (k : ℝ) * ‖v‖ := by
                    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ = (k : ℝ) * S * ‖v‖ := by ring

end Work.OdeCont
