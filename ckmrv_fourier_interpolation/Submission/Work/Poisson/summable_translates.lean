import Mathlib
import Submission.Work.Modular.Poisson.Std

namespace Work.Poisson

open scoped SchwartzMap
open Filter Topology MeasureTheory

/-- Auxiliary: the Schwartz decay estimate expressed as an inverse-power bound. -/
lemma norm_le_mul_inv_pow {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : SchwartzMap E ℂ) (k : ℕ)
    {C : ℝ} (hC : ∀ x, ‖x‖ ^ k * ‖f x‖ ≤ C) (x : E) (hx : ‖x‖ ≠ 0) :
    ‖f x‖ ≤ C * (‖x‖⁻¹) ^ k := by
  have h : (‖x‖ ^ k) ≠ 0 := pow_ne_zero _ hx
  calc ‖f x‖ = (‖x‖ ^ k)⁻¹ * (‖x‖ ^ k * ‖f x‖) := by
        rw [← mul_assoc, inv_mul_cancel₀ h, one_mul]
    _ ≤ (‖x‖ ^ k)⁻¹ * C := mul_le_mul_of_nonneg_left (hC x) (by positivity)
    _ = C * (‖x‖⁻¹) ^ k := by rw [inv_pow]; ring

theorem summable_translates {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L]
    (f : SchwartzMap E ℂ) :
    Summable fun x' : L =>
      ContinuousMap.comp (f : ContinuousMap E ℂ) (ContinuousMap.addRight (x' : E)) := by
  classical
  refine ContinuousMap.summable_of_locally_summable_norm (fun K => ?_)
  obtain ⟨r, hr1, hrK⟩ := K.isCompact.isBounded.subset_closedBall_lt 1 0
  have hr0 : 0 < r := lt_trans zero_lt_one hr1
  set k := Module.finrank ℤ L + 1 with hkdef
  have hkfin : Module.finrank ℤ L < k := Nat.lt_succ_self _
  obtain ⟨C, hCpos, hC'⟩ := f.decay k 0
  have hC : ∀ x : E, ‖x‖ ^ k * ‖f x‖ ≤ C := by
    intro x; simpa using hC' x
  have hg : Summable fun z : L => (2 : ℝ) ^ k * C * ((‖(z : E)‖)⁻¹) ^ k :=
    (ZLattice.summable_norm_pow_inv L k hkfin).mul_left ((2 : ℝ) ^ k * C)
  refine Summable.of_norm_bounded_eventually hg ?_
  have hfin : ({z : L | ‖(z : E)‖ ≤ 2 * r} : Set L).Finite := by
    have hclosed : IsClosed (L : Set E) :=
      AddSubgroup.isClosed_of_discrete (U := L.toAddSubgroup)
    have hfinE : ((Metric.closedBall (0 : E) (2 * r)) ∩ (L : Set E)).Finite :=
      Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete
        Metric.isBounded_closedBall hclosed
    refine Set.Finite.of_finite_image ?_ (fun a _ b _ h => Subtype.ext h)
    refine hfinE.subset ?_
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨by simpa [Metric.mem_closedBall, dist_eq_norm] using hz, z.2⟩
  filter_upwards [hfin.eventually_cofinite_notMem] with z hzn
  have hzle : 2 * r < ‖(z : E)‖ := not_le.mp hzn
  rw [Real.norm_of_nonneg (norm_nonneg _)]
  rw [ContinuousMap.norm_le _ (by positivity)]
  intro y
  rw [ContinuousMap.restrict_apply, ContinuousMap.comp_apply, ContinuousMap.coe_addRight]
  have hy : ‖(y : E)‖ ≤ r := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hrK y.2
  have hzpos : 0 < ‖(z : E)‖ := lt_of_lt_of_le (by linarith) hzle.le
  have hpge : ‖(z : E)‖ / 2 ≤ ‖(y : E) + (z : E)‖ := by
    have h1 : ‖(z : E)‖ ≤ ‖(y : E) + (z : E)‖ + ‖(y : E)‖ := by
      calc ‖(z : E)‖ = ‖((y : E) + (z : E)) - (y : E)‖ := by rw [add_sub_cancel_left]
        _ ≤ ‖(y : E) + (z : E)‖ + ‖(y : E)‖ := norm_sub_le _ _
    linarith
  have hppos : 0 < ‖(y : E) + (z : E)‖ := lt_of_lt_of_le (by linarith) hpge
  have hbinv : ((‖(y : E) + (z : E)‖)⁻¹) ≤ 2 * (‖(z : E)‖)⁻¹ := by
    have h := (inv_le_inv₀ hppos (by positivity : (0 : ℝ) < ‖(z : E)‖ / 2)).mpr hpge
    simpa [inv_div, div_eq_mul_inv] using h
  calc ‖f ((y : E) + (z : E))‖
      ≤ C * ((‖(y : E) + (z : E)‖)⁻¹) ^ k :=
        norm_le_mul_inv_pow f k hC _ (ne_of_gt hppos)
    _ ≤ C * (2 * (‖(z : E)‖)⁻¹) ^ k := by
        refine mul_le_mul_of_nonneg_left ?_ hCpos.le
        exact pow_le_pow_left₀ (by positivity) hbinv k
    _ = (2 : ℝ) ^ k * C * ((‖(z : E)‖)⁻¹) ^ k := by rw [mul_pow]; ring

end Work.Poisson
