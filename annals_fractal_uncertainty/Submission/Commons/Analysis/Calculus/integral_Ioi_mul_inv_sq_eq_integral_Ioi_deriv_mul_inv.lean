import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Order.CompletePartialOrder

namespace Commons.Analysis.Calculus

open MeasureTheory Filter Set Topology

open scoped Topology

/-- If `f : ℝ → ℝ` has compact support then it vanishes to the right of some point. -/
theorem exists_forall_ge_eq_zero_of_hasCompactSupport {f : ℝ → ℝ} (hf : HasCompactSupport f) :
    ∃ N : ℝ, ∀ t : ℝ, N ≤ t → f t = 0 := by
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).1 hf.isCompact.isBounded
  refine ⟨max R 0 + 1, fun t ht => ?_⟩
  apply image_eq_zero_of_notMem_tsupport
  intro hmem
  have hRt : t ∈ Metric.closedBall (0 : ℝ) R := hR hmem
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at hRt
  have ht0 : 0 < t := by linarith [le_max_right R 0]
  rw [abs_of_pos ht0] at hRt
  linarith [le_max_left R 0]

theorem integral_Ioi_mul_inv_sq_eq_integral_Ioi_deriv_mul_inv {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hsupp : HasCompactSupport φ)
    (h0 : ∀ t : ℝ, 0 < t → t ≤ 1 → φ t = 0) :
    (∫ t in Set.Ioi (0 : ℝ), φ t * (t ^ 2)⁻¹) = ∫ t in Set.Ioi (0 : ℝ), deriv φ t * t⁻¹ := by
  obtain ⟨N, hN⟩ := exists_forall_ge_eq_zero_of_hasCompactSupport hsupp
  let M : ℝ := max N 1
  have hM_ge : 1 ≤ M := le_max_right N 1
  have hM : ∀ t : ℝ, M ≤ t → φ t = 0 := fun t ht => hN t (le_trans (le_max_left N 1) ht)
  have hcont1 : ContinuousOn (fun t : ℝ => φ t * (t ^ 2)⁻¹) (Set.Icc 1 M) := by
    apply ContinuousOn.mul
    · exact hφ.continuous.continuousOn
    · apply ContinuousOn.inv₀
      · exact (continuous_id.pow 2).continuousOn
      · intro t ht
        exact pow_ne_zero 2 (ne_of_gt (by linarith [ht.1] : (0 : ℝ) < t))
  have hcont2 : ContinuousOn (fun t : ℝ => deriv φ t * (-(t)⁻¹)) (Set.Icc 1 M) := by
    apply ContinuousOn.mul
    · exact (hφ.continuous_deriv le_rfl).continuousOn
    · exact ContinuousOn.neg (ContinuousOn.inv₀ continuousOn_id
        (fun t ht => ne_of_gt (by linarith [ht.1] : (0 : ℝ) < t)))
  have hf1 : IntegrableOn (fun t : ℝ => φ t * (t ^ 2)⁻¹) (Set.Ioi (0 : ℝ)) := by
    have hbase : IntegrableOn (fun t : ℝ => φ t * (t ^ 2)⁻¹) (Set.Icc 1 M) :=
      ContinuousOn.integrableOn_compact isCompact_Icc hcont1
    refine hbase.of_forall_sdiff_eq_zero measurableSet_Ioi ?_
    intro t ht
    rcases ht with ⟨htpos, htnot⟩
    have hφt0 : φ t = 0 := by
      rcases not_and_or.mp htnot with hlt | hgt
      · exact h0 t htpos (le_of_lt (not_le.mp hlt))
      · exact hM t (le_of_lt (not_le.mp hgt))
    simp [hφt0]
  have hf2 : IntegrableOn (fun t : ℝ => deriv φ t * (-(t)⁻¹)) (Set.Ioi (0 : ℝ)) := by
    have hbase : IntegrableOn (fun t : ℝ => deriv φ t * (-(t)⁻¹)) (Set.Icc 1 M) :=
      ContinuousOn.integrableOn_compact isCompact_Icc hcont2
    refine hbase.of_forall_sdiff_eq_zero measurableSet_Ioi ?_
    intro t ht
    rcases ht with ⟨htpos, htnot⟩
    have hd0 : deriv φ t = 0 := by
      rcases not_and_or.mp htnot with hlt | hgt
      · have hmem : Set.Ioo (0 : ℝ) 1 ∈ 𝓝 t := Ioo_mem_nhds htpos (not_le.mp hlt)
        have heq : φ =ᶠ[𝓝 t] (fun _ => (0 : ℝ)) := by
          apply Filter.eventually_of_mem hmem
          intro s hs
          exact h0 s hs.1 (le_of_lt hs.2)
        simpa using heq.deriv_eq
      · have hmem : Set.Ioi M ∈ 𝓝 t := Ioi_mem_nhds (not_le.mp hgt)
        have heq : φ =ᶠ[𝓝 t] (fun _ => (0 : ℝ)) := by
          apply Filter.eventually_of_mem hmem
          intro s hs
          exact hM s (le_of_lt hs)
        simpa using heq.deriv_eq
    simp [hd0]
  have hzero : Tendsto (fun t : ℝ => φ t * (-(t)⁻¹)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hmem : Set.Ioc (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) := by
      rw [mem_nhdsGT_iff_exists_Ioc_subset]
      exact ⟨1, by norm_num, subset_rfl⟩
    have heq : (fun t : ℝ => φ t * (-(t)⁻¹)) =ᶠ[𝓝[>] (0 : ℝ)] (fun _ => (0 : ℝ)) := by
      apply Filter.eventually_of_mem hmem
      intro t ht
      change φ t * (-(t)⁻¹) = 0
      rw [h0 t ht.1 ht.2]
      ring
    exact tendsto_const_nhds.congr' heq.symm
  have hinfty : Tendsto (fun t : ℝ => φ t * (-(t)⁻¹)) atTop (𝓝 0) := by
    have heq : (fun t : ℝ => φ t * (-(t)⁻¹)) =ᶠ[atTop] (fun _ => (0 : ℝ)) := by
      filter_upwards [eventually_ge_atTop M] with t ht
      rw [hM t ht]
      ring
    exact tendsto_const_nhds.congr' heq.symm
  have hu : ∀ x ∈ Set.Ioi (0 : ℝ), HasDerivAt φ (deriv φ x) x := by
    intro x _
    exact (hφ.differentiable one_ne_zero x).hasDerivAt
  have hv : ∀ x ∈ Set.Ioi (0 : ℝ), HasDerivAt (fun t : ℝ => -(t)⁻¹) ((x ^ 2)⁻¹) x := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt hx
    have h : HasDerivAt (fun t : ℝ => (t⁻¹)) (-(x ^ 2)⁻¹) x := hasDerivAt_inv hx0
    exact h.neg.congr_deriv (by ring)
  have key := MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul (a := (0 : ℝ)) (a' := (0 : ℝ))
    (b' := (0 : ℝ)) (u := φ) (u' := deriv φ) (v := fun t : ℝ => -(t)⁻¹)
    (v' := fun t : ℝ => (t ^ 2)⁻¹) hu hv hf1 hf2 hzero hinfty
  rw [key]
  have hab : (∫ t in Set.Ioi (0 : ℝ), deriv φ t * (-(t)⁻¹)) =
      - ∫ t in Set.Ioi (0 : ℝ), deriv φ t * t⁻¹ := by
    have hneg : (fun t : ℝ => deriv φ t * (-(t)⁻¹)) =
        (fun t : ℝ => -(deriv φ t * t⁻¹)) := by
      funext t
      ring
    rw [hneg, MeasureTheory.integral_neg]
  rw [hab]
  ring

end Commons.Analysis.Calculus