import Mathlib

open MeasureTheory
open scoped ENNReal

namespace Work.Mostow

/-- The `c`-strip of an isometry `R` of Euclidean space that fixes a nonzero vector `w` has
infinite Lebesgue measure.  Indeed `{W | ‖R W - W‖ ≤ c}` contains the closed ball of radius `c/2`
about the origin and is invariant under translation along the line `ℝ • w`; translating that ball
by the multiples of `w` gives a pairwise disjoint family of balls of positive measure. -/
theorem geeVolStripTop (m : ℕ) (R : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin m)) (c : ℝ)
    (hc : 0 < c) (hw : ∃ w : EuclideanSpace ℝ (Fin m), w ≠ 0 ∧ R w = w) :
    (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin m)))
      {W : EuclideanSpace ℝ (Fin m) | ‖R W - W‖ ≤ c} = ⊤ := by
  obtain ⟨w, hwne, hwfix⟩ := hw
  have hwnorm : 0 < ‖w‖ := norm_pos_iff.mpr hwne
  have hr : 0 < c / 2 := by linarith
  set ε : ℝ := min (c/2) (‖w‖ / 3) with hε_def
  have hεpos : 0 < ε := lt_min hr (by positivity)
  have hεr : ε ≤ c/2 := by rw [hε_def]; exact min_le_left _ _
  have hεw : 2 * ε < ‖w‖ := by
    have h := min_le_right (c/2) (‖w‖ / 3)
    rw [hε_def]; linarith
  -- `S` contains the closed ball of radius `c/2` about the origin
  have hball : Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) (c/2)
      ⊆ {W : EuclideanSpace ℝ (Fin m) | ‖R W - W‖ ≤ c} := by
    intro W hW
    have hW' : ‖W‖ ≤ c/2 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hW
    calc ‖R W - W‖ ≤ ‖R W‖ + ‖W‖ := norm_sub_le _ _
      _ = ‖W‖ + ‖W‖ := by rw [LinearIsometryEquiv.norm_map]
      _ ≤ c := by linarith
  -- `S` is invariant under translation by multiples of `w`
  have hshift : ∀ (t : ℝ) (W : EuclideanSpace ℝ (Fin m)),
      ‖R W - W‖ ≤ c → ‖R (W + t • w) - (W + t • w)‖ ≤ c := by
    intro t W hW
    have h : R (W + t • w) - (W + t • w) = R W - W := by
      rw [map_add, map_smul, hwfix]; abel
    rw [h]
    exact hW
  set A : ℕ → Set (EuclideanSpace ℝ (Fin m)) :=
    fun n => Metric.closedBall ((n : ℝ) • w) ε with hA_def
  have hA_sub : ∀ n, A n ⊆ {W : EuclideanSpace ℝ (Fin m) | ‖R W - W‖ ≤ c} := by
    intro n W hW
    have h1 : ‖W - (n : ℝ) • w‖ ≤ ε := by
      have hh := hW
      simp only [hA_def, Metric.mem_closedBall, dist_eq_norm] at hh
      exact hh
    have h2 : (W - (n:ℝ) • w) ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) (c/2) := by
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
      linarith
    have h3 := hball h2
    have h4 := hshift (n:ℝ) (W - (n:ℝ)•w) h3
    have heq : W - (n:ℝ)•w + (n:ℝ)•w = W := sub_add_cancel _ _
    simpa [heq] using h4
  have hdisj : Pairwise (Function.onFun Disjoint A) := by
    intro n m' hnm
    change Disjoint (A n) (A m')
    have hw_nm : ‖w‖ ≤ dist ((n:ℝ)•w) ((m':ℝ)•w) := by
      rw [dist_eq_norm]
      rw [show (n:ℝ) • w - (m':ℝ) • w = ((n:ℝ) - (m':ℝ)) • w by rw [sub_smul]]
      rw [norm_smul, Real.norm_eq_abs]
      have h1 : (1:ℝ) ≤ |(n:ℝ) - (m':ℝ)| := by
        have h : ((n:ℤ) - m') ≠ 0 := by
          intro hh
          exact hnm (by exact_mod_cast (sub_eq_zero.mp hh : (n:ℤ) = m'))
        have := Int.one_le_abs h
        calc (1:ℝ) = ((1:ℤ):ℝ) := by norm_num
          _ ≤ ((|((n:ℤ) - m')| : ℤ) : ℝ) := by exact_mod_cast this
          _ = |((n:ℤ):ℝ) - (m':ℝ)| := by rw [Int.cast_abs, Int.cast_sub]; norm_num
          _ = |(n:ℝ) - (m':ℝ)| := by norm_num
      calc ‖w‖ = 1 * ‖w‖ := by ring
        _ ≤ |(n:ℝ) - (m':ℝ)| * ‖w‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    refine Metric.closedBall_disjoint_closedBall ?_
    linarith
  have hmeas : ∀ n, MeasurableSet (A n) := by
    intro n; rw [hA_def]; exact Metric.isClosed_closedBall.measurableSet
  have hmono : (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin m)))
      (⋃ n, A n)
      ≤ (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin m)))
        {W : EuclideanSpace ℝ (Fin m) | ‖R W - W‖ ≤ c} :=
    MeasureTheory.measure_mono (Set.iUnion_subset hA_sub)
  rw [MeasureTheory.measure_iUnion hdisj hmeas] at hmono
  have hconst : ∀ n, (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin m))) (A n)
      = (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin m)))
          (Metric.closedBall (0:EuclideanSpace ℝ (Fin m)) ε) := by
    intro n
    rw [hA_def]
    have h := MeasureTheory.measure_preimage_add
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin m)))
      ((n:ℝ)•w) (Metric.closedBall ((n:ℝ)•w) ε)
    have hpre : (fun h : EuclideanSpace ℝ (Fin m) => (n:ℝ)•w + h) ⁻¹'
        Metric.closedBall ((n:ℝ)•w) ε
        = Metric.closedBall (0:EuclideanSpace ℝ (Fin m)) ε := by
      ext h; simp [Metric.mem_closedBall, dist_eq_norm]
    rw [hpre] at h
    exact h.symm
  have hne : (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin m)))
      (Metric.closedBall (0:EuclideanSpace ℝ (Fin m)) ε) ≠ 0 :=
    (Metric.measure_closedBall_pos (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin m))) (0:EuclideanSpace ℝ (Fin m)) hεpos).ne'
  have htop : (∑' n : ℕ, (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin m)))
      (A n)) = ⊤ := by
    simp_rw [hconst]
    exact ENNReal.tsum_const_eq_top_of_ne_zero hne
  rw [htop] at hmono
  exact top_le_iff.mp hmono

end Work.Mostow
