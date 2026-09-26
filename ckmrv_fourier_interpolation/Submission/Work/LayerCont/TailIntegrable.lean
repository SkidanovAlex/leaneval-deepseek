import Mathlib

open MeasureTheory Filter

namespace Work.LayerCont

/-- Exponential domination: `t ↦ (1+t)^M e^{-a t}` is integrable on `[1,∞)` for `a > 0`
(and any real `M ≥ 0`).  This is the dominator for the tail of the CKMRV trunc integrand
`(Kaxis - Aexp)·e^{-πr²t}`, whose cusp-expansion bound is
`C(1+t)^M e^{-π(t-T₀)}`. -/
theorem TailIntegrable {M a : ℝ} (hM : 0 ≤ M) (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => (1 + t) ^ M * Real.exp (-(a * t))) (Set.Ici (1 : ℝ)) := by
  -- polynomial growth is dominated by the half-rate exponential on a tail
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.mp
    ((isLittleO_rpow_exp_pos_mul_atTop M (by linarith : 0 < a / 2)).bound one_pos)
  set B : ℝ := max X 1 with hB
  have hB1 : 1 ≤ B := le_max_right X 1
  set C : ℝ := max (2 ^ M) ((1 + B) ^ M * Real.exp ((a / 2) * B)) with hC
  have hCge1 : (2 : ℝ) ^ M ≤ C := le_max_left _ _
  have hCge2 : (1 + B) ^ M * Real.exp ((a / 2) * B) ≤ C := le_max_right _ _
  have hCnn : 0 ≤ C := le_trans (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) M) hCge1
  have hdom : ∀ t : ℝ, 1 ≤ t →
      (1 + t) ^ M * Real.exp (-(a * t)) ≤ C * Real.exp (-(a / 2) * t) := by
    intro t ht
    have ht0 : 0 ≤ t := le_trans zero_le_one ht
    by_cases htB : t ≤ B
    · -- head: `t ≤ B`
      have h1 : (1 + t) ^ M ≤ (1 + B) ^ M :=
        Real.rpow_le_rpow (by linarith) (by linarith) hM
      have h2 : Real.exp (-(a * t)) ≤ 1 := by
        rw [Real.exp_le_one_iff]; nlinarith [ha, ht0]
      have h3 : (1 + t) ^ M * Real.exp (-(a * t)) ≤ (1 + B) ^ M := by
        calc (1 + t) ^ M * Real.exp (-(a * t)) ≤ (1 + B) ^ M * 1 :=
              mul_le_mul h1 h2 (Real.exp_nonneg _) (Real.rpow_nonneg (by linarith) M)
          _ = (1 + B) ^ M := mul_one _
      have h4 : (1 + B) ^ M ≤ C * Real.exp (-(a / 2) * B) := by
        have hid : ((1 + B) ^ M * Real.exp ((a / 2) * B)) * Real.exp (-(a / 2) * B)
            = (1 + B) ^ M := by
          rw [mul_assoc, ← Real.exp_add]
          have hz : (a / 2) * B + -(a / 2) * B = 0 := by ring
          rw [hz, Real.exp_zero, mul_one]
        calc (1 + B) ^ M
            = ((1 + B) ^ M * Real.exp ((a / 2) * B)) * Real.exp (-(a / 2) * B) := hid.symm
          _ ≤ C * Real.exp (-(a / 2) * B) :=
              mul_le_mul_of_nonneg_right hCge2 (Real.exp_nonneg _)
      have htB2 : (a / 2) * t ≤ (a / 2) * B :=
        mul_le_mul_of_nonneg_left htB (by linarith)
      have h5 : C * Real.exp (-(a / 2) * B) ≤ C * Real.exp (-(a / 2) * t) := by
        apply mul_le_mul_of_nonneg_left _ hCnn
        rw [Real.exp_le_exp]
        linarith
      exact h3.trans (h4.trans h5)
    · -- tail: `t > B ≥ X`
      have htB' : B < t := lt_of_not_ge htB
      have hX' : t ^ M ≤ Real.exp ((a / 2) * t) := by
        have h := hX t (le_trans (le_max_left X 1) htB'.le)
        rwa [Real.norm_of_nonneg (Real.rpow_nonneg ht0 M),
          Real.norm_of_nonneg (Real.exp_pos _).le, one_mul] at h
      have h2 : (1 + t) ^ M ≤ (2 * t) ^ M :=
        Real.rpow_le_rpow (by linarith) (by linarith) hM
      have h3 : (2 * t) ^ M = 2 ^ M * t ^ M := Real.mul_rpow (by norm_num) ht0
      rw [h3] at h2
      have h4 : (2 ^ M * t ^ M) * Real.exp (-(a * t))
          ≤ (2 ^ M * Real.exp ((a / 2) * t)) * Real.exp (-(a * t)) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hX' (Real.rpow_nonneg (by norm_num) M))
          (Real.exp_nonneg _)
      have h5 : (2 ^ M * Real.exp ((a / 2) * t)) * Real.exp (-(a * t))
          = 2 ^ M * Real.exp (-(a / 2) * t) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring
      calc (1 + t) ^ M * Real.exp (-(a * t))
          ≤ (2 ^ M * t ^ M) * Real.exp (-(a * t)) :=
            mul_le_mul_of_nonneg_right h2 (Real.exp_nonneg _)
        _ ≤ (2 ^ M * Real.exp ((a / 2) * t)) * Real.exp (-(a * t)) := h4
        _ = 2 ^ M * Real.exp (-(a / 2) * t) := h5
        _ ≤ C * Real.exp (-(a / 2) * t) :=
            mul_le_mul_of_nonneg_right hCge1 (Real.exp_nonneg _)
  -- the dominator is integrable
  have hdomint : IntegrableOn (fun t : ℝ => C * Real.exp (-(a / 2) * t)) (Set.Ici (1 : ℝ)) := by
    have h0 : IntegrableOn (fun t : ℝ => Real.exp ((-(a / 2)) * t)) (Set.Ioi (0 : ℝ)) :=
      integrableOn_exp_mul_Ioi (by linarith) 0
    have h1 : IntegrableOn (fun t : ℝ => Real.exp ((-(a / 2)) * t)) (Set.Ici (1 : ℝ)) :=
      h0.mono_set (fun x hx => Set.mem_Ioi.mpr (lt_of_lt_of_le zero_lt_one hx))
    have h2 : IntegrableOn (fun t : ℝ => C * Real.exp ((-(a / 2)) * t)) (Set.Ici (1 : ℝ)) :=
      h1.const_mul C
    refine h2.congr_fun (fun t _ => ?_) measurableSet_Ici
    ring_nf
  -- conclude by dominated convergence
  show Integrable (fun t : ℝ => (1 + t) ^ M * Real.exp (-(a * t)))
    (volume.restrict (Set.Ici (1 : ℝ)))
  refine Integrable.mono' (g := fun t : ℝ => C * Real.exp (-(a / 2) * t)) ?_ ?_ ?_
  · rw [← IntegrableOn]; exact hdomint
  · exact ((by fun_prop : Measurable (fun t : ℝ => (1 + t) ^ M)).mul
      (by fun_prop : Measurable (fun t : ℝ => Real.exp (-(a * t))))).aestronglyMeasurable
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with t ht
    have ht1 : (1 : ℝ) ≤ t := ht
    rw [Real.norm_of_nonneg
      (mul_nonneg (Real.rpow_nonneg (by linarith [ht1]) M) (Real.exp_nonneg _))]
    exact hdom t ht1

end Work.LayerCont
