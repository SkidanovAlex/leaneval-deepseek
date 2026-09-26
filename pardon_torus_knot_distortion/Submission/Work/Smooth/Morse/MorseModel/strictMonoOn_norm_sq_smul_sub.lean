import Mathlib

namespace Work.Smooth.Morse.MorseModel

open Set
open scoped RealInnerProductSpace

/-- If `u` is a `C¹` map with `u 0 = x` whose differential on the unit ball stays within `ε`
of a linear map `A` with `‖A w‖ ≥ c ‖w‖`, and `4 ε ≤ c`, then along any unit direction `v`
the squared distance `t ↦ ‖u (t • v) - x‖ ^ 2` is strictly increasing on `[0,1]`. -/
theorem strictMonoOn_norm_sq_smul_sub {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {u : ℂ → F} {x : F} {A : ℂ →L[ℝ] F} {c ε : ℝ}
    (hc : 0 < c) (hε : 0 ≤ ε) (hεc : 4 * ε ≤ c)
    (hAc : ∀ v : ℂ, c * ‖v‖ ≤ ‖A v‖) (h0 : u 0 = x)
    (hdiff : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, HasFDerivAt u (fderiv ℝ u z) z)
    (hbound : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, ‖fderiv ℝ u z - A‖ ≤ ε)
    (v : ℂ) (hv : ‖v‖ = 1) :
    StrictMonoOn (fun t : ℝ => ‖u (t • v) - x‖ ^ 2) (Set.Icc 0 1) := by
  have hmem : ∀ t ∈ Set.Icc (0:ℝ) 1, t • v ∈ Metric.closedBall (0 : ℂ) 1 := by
    intro t ht
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, norm_smul, hv, mul_one, Real.norm_eq_abs]
    rw [abs_le]
    exact ⟨by linarith [ht.1], ht.2⟩
  have hγ : ∀ t : ℝ, HasDerivAt (fun s : ℝ => s • v) v t := by
    intro t
    simpa using (hasDerivAt_id t).smul_const v
  have hcurve : ∀ t ∈ Set.Icc (0:ℝ) 1,
      HasDerivAt (fun s : ℝ => u (s • v)) ((fderiv ℝ u (t • v)) v) t := by
    intro t ht
    exact (hdiff (t • v) (hmem t ht)).comp_hasDerivAt t (hγ t)
  have hderiv_bound : ∀ t ∈ Set.Icc (0:ℝ) 1,
      ‖(fderiv ℝ u (t • v)) v - A v‖ ≤ ε := by
    intro t ht
    have h1 : (fderiv ℝ u (t • v)) v - A v = (fderiv ℝ u (t • v) - A) v := rfl
    rw [h1]
    calc ‖(fderiv ℝ u (t • v) - A) v‖ ≤ ‖fderiv ℝ u (t • v) - A‖ * ‖v‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ = ‖fderiv ℝ u (t • v) - A‖ := by rw [hv, mul_one]
      _ ≤ ε := hbound (t • v) (hmem t ht)
  have hmvt : ∀ r ∈ Set.Icc (0:ℝ) 1, ‖u (r • v) - x - r • (A v)‖ ≤ ε * r := by
    intro r hr
    have hfderiv : ∀ t ∈ Set.Icc (0:ℝ) r,
        HasDerivWithinAt (fun s : ℝ => u (s • v) - x - s • (A v))
          ((fderiv ℝ u (t • v)) v - A v) (Set.Icc (0:ℝ) r) t := by
      intro t ht
      have htv : t ∈ Set.Icc (0:ℝ) 1 := ⟨ht.1, le_trans ht.2 hr.2⟩
      have h1 : HasDerivAt (fun s : ℝ => u (s • v) - x) ((fderiv ℝ u (t • v)) v) t :=
        (hcurve t htv).sub_const x
      have h2 : HasDerivAt (fun s : ℝ => s • (A v)) (A v) t := by
        simpa using (hasDerivAt_id t).smul_const (A v)
      exact (h1.sub h2).hasDerivWithinAt (s := Set.Icc (0:ℝ) r)
    have hbound' : ∀ t ∈ Set.Ico (0:ℝ) r, ‖(fderiv ℝ u (t • v)) v - A v‖ ≤ ε := by
      intro t ht
      exact hderiv_bound t ⟨ht.1, le_trans (le_of_lt ht.2) hr.2⟩
    have hmain := norm_image_sub_le_of_norm_deriv_le_segment' hfderiv hbound' r ⟨hr.1, le_refl r⟩
    have hzero : u 0 - x = 0 := by rw [h0, sub_self]
    simpa [hzero] using hmain
  have hinner_pos : ∀ t ∈ Set.Ioo (0:ℝ) 1,
      0 < inner ℝ (u (t • v) - x) ((fderiv ℝ u (t • v)) v) := by
    have hpos : ∀ a b : F, -(‖a‖ * ‖b‖) ≤ inner ℝ a b := by
      intro a b
      have h := abs_real_inner_le_norm a b
      rw [abs_le] at h
      exact h.1
    intro t ht
    have htI : t ∈ Set.Icc (0:ℝ) 1 := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    have hρ : c ≤ ‖A v‖ := by
      have := hAc v
      rwa [hv, mul_one] at this
    have hkey : 0 < ‖A v‖ ^ 2 - 2 * ε * ‖A v‖ - ε ^ 2 := by nlinarith [hρ, hεc, hε, hc]
    have hq : ‖u (t • v) - x - t • (A v)‖ ≤ ε * t := hmvt t htI
    have he : ‖(fderiv ℝ u (t • v)) v - A v‖ ≤ ε := hderiv_bound t htI
    have hnormAv : (0:ℝ) ≤ ‖A v‖ := norm_nonneg _
    have hqnorm : ‖u (t • v) - x‖ ≤ ε * t + t * ‖A v‖ := by
      have hsplit : u (t • v) - x = (u (t • v) - x - t • (A v)) + t • (A v) := by abel
      calc ‖u (t • v) - x‖ = ‖(u (t • v) - x - t • (A v)) + t • (A v)‖ := congrArg norm hsplit
        _ ≤ ‖u (t • v) - x - t • (A v)‖ + ‖t • (A v)‖ := norm_add_le _ _
        _ = ‖u (t • v) - x - t • (A v)‖ + t * ‖A v‖ := by
              rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht.1]
        _ ≤ ε * t + t * ‖A v‖ := by linarith
    have h1 : t * ‖A v‖ ^ 2 - (ε * t) * ‖A v‖ ≤ inner ℝ (u (t • v) - x) (A v) := by
      have hqq : u (t • v) - x = (u (t • v) - x - t • (A v)) + t • (A v) := by abel
      rw [hqq, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
      have hcs : -(‖u (t • v) - x - t • (A v)‖ * ‖A v‖) ≤
          inner ℝ (u (t • v) - x - t • (A v)) (A v) := hpos _ _
      nlinarith [hcs, hq, hnormAv, norm_nonneg (u (t • v) - x - t • (A v)), hε, ht.1]
    have h2 : -((ε * t + t * ‖A v‖) * ε) ≤
        inner ℝ (u (t • v) - x) ((fderiv ℝ u (t • v)) v - A v) := by
      have hcs : -(‖u (t • v) - x‖ * ‖(fderiv ℝ u (t • v)) v - A v‖) ≤
          inner ℝ (u (t • v) - x) ((fderiv ℝ u (t • v)) v - A v) := hpos _ _
      nlinarith [hcs, hqnorm, he, norm_nonneg (u (t • v) - x),
        norm_nonneg ((fderiv ℝ u (t • v)) v - A v), ht.1, hε]
    have hsplit : inner ℝ (u (t • v) - x) ((fderiv ℝ u (t • v)) v)
        = inner ℝ (u (t • v) - x) (A v)
          + inner ℝ (u (t • v) - x) ((fderiv ℝ u (t • v)) v - A v) := by
      rw [← inner_add_right]
      congr 1
      abel
    rw [hsplit]
    have hthis : 0 < t * (‖A v‖ ^ 2 - 2 * ε * ‖A v‖ - ε ^ 2) := mul_pos ht.1 hkey
    nlinarith [h1, h2, hthis]
  have hGderiv : ∀ t ∈ Set.Ioo (0:ℝ) 1,
      HasDerivAt (fun s : ℝ => ‖u (s • v) - x‖ ^ 2)
        (2 * inner ℝ (u (t • v) - x) ((fderiv ℝ u (t • v)) v)) t := by
    intro t ht
    have htI : t ∈ Set.Icc (0:ℝ) 1 := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    have h1 : HasDerivAt (fun s : ℝ => u (s • v) - x) ((fderiv ℝ u (t • v)) v) t :=
      (hcurve t htI).sub_const x
    simpa using h1.norm_sq
  have hcont : ContinuousOn (fun t : ℝ => ‖u (t • v) - x‖ ^ 2) (Set.Icc 0 1) := by
    have hd : DifferentiableOn ℝ (fun s : ℝ => u (s • v)) (Set.Icc 0 1) :=
      fun t ht => (hcurve t ht).differentiableAt.differentiableWithinAt
    exact ((hd.continuousOn.sub continuousOn_const).norm).pow 2
  refine strictMonoOn_of_deriv_pos (convex_Icc 0 1) hcont ?_
  rw [interior_Icc]
  intro t ht
  rw [(hGderiv t ht).deriv]
  have := hinner_pos t ht
  linarith

end Work.Smooth.Morse.MorseModel
