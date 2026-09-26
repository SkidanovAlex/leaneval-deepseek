import Mathlib

namespace Work.Drive.Mono

/-- **A `C²` function with a double zero at the left endpoint of `[0, ρ]` is `O(t²)` there.**

This is Taylor's theorem with the mean-value form of the remainder (`exists_taylor_mean_remainder_bound`,
applied with `n = 1`): the Taylor polynomial of degree one at `0` is `g 0 + t · g'(0)`, which vanishes
by hypothesis, and the remainder is bounded by `C · t²` for some constant `C`.  We work with the
*within*-derivative of `g` on `[0, ρ]` so that no genuine differentiability of `g` at the boundary
point `0` has to be assumed. -/
private lemma sqBound_Icc_of_derivWithin_zero {g : ℝ → ℝ} {ρ : ℝ} (hρ : 0 < ρ)
    (hg : ContDiffOn ℝ 2 g (Set.Icc 0 ρ)) (h0 : g 0 = 0)
    (h1 : derivWithin g (Set.Icc 0 ρ) 0 = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Icc 0 ρ, |g t| ≤ C * t ^ 2 := by
  obtain ⟨C, hC⟩ :=
    exists_taylor_mean_remainder_bound (f := g) (a := 0) (b := ρ) (n := 1) hρ.le hg
  have htw : ∀ x : ℝ, taylorWithinEval g 1 (Set.Icc 0 ρ) 0 x = 0 := by
    intro x
    rw [taylorWithinEval_succ, taylor_within_zero_eval, iteratedDerivWithin_one, h0, h1]
    norm_num
  refine ⟨max C 0, le_max_right _ _, fun t ht => ?_⟩
  have := hC t ht
  rw [htw t, sub_zero, Real.norm_eq_abs, sub_zero] at this
  exact this.trans (mul_le_mul_of_nonneg_right (le_max_left C 0) (sq_nonneg t))

theorem quadBoundDerivZero {f : ℝ → ℝ} {ρ : ℝ} (hρ : 0 < ρ)
    (hf : ContDiffOn ℝ 2 f (Set.Icc (-ρ) ρ)) (h0 : f 0 = 0) (h1 : deriv f 0 = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Ioo (-ρ) ρ, |f t| ≤ C * t ^ 2 := by
  -- `0` is an interior point, so `f` is genuinely `C²` (hence differentiable) there.
  have h0mem : (0 : ℝ) ∈ Set.Ioo (-ρ) ρ := ⟨by linarith, hρ⟩
  have hCA : ContDiffAt ℝ 2 f 0 :=
    (hf.mono Set.Ioo_subset_Icc_self).contDiffAt (isOpen_Ioo.mem_nhds h0mem)
  have hd : DifferentiableAt ℝ f 0 := hCA.differentiableAt (by norm_num)
  have hU : UniqueDiffWithinAt ℝ (Set.Icc 0 ρ) 0 :=
    (uniqueDiffOn_Icc hρ).uniqueDiffWithinAt ⟨le_rfl, hρ.le⟩
  -- the bound on the right half `[0, ρ]`
  obtain ⟨C₁, hC₁0, hC₁⟩ : ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Icc 0 ρ, |f t| ≤ C * t ^ 2 :=
    sqBound_Icc_of_derivWithin_zero hρ
      (hf.mono (Set.Icc_subset_Icc (by linarith) le_rfl)) h0
      (by rw [hd.hasDerivAt.hasDerivWithinAt.derivWithin hU, h1])
  -- the bound on the left half, by applying the right-half statement to `t ↦ f (-t)`
  have hneg : ContDiffOn ℝ 2 (fun t : ℝ => f (-t)) (Set.Icc 0 ρ) :=
    hf.comp (contDiff_neg.contDiffOn)
      (fun x hx => ⟨by linarith [hx.2], by linarith [hx.1]⟩)
  have hnegw : derivWithin (fun t : ℝ => f (-t)) (Set.Icc 0 ρ) 0 = 0 := by
    have hCAg : ContDiffAt ℝ 2 (fun t : ℝ => f (-t)) 0 :=
      (show ContDiffAt ℝ 2 f (-0) from by simpa using hCA).comp 0
        ((contDiff_neg (n := 2)).contDiffAt)
    have hdg : DifferentiableAt ℝ (fun t : ℝ => f (-t)) 0 :=
      hCAg.differentiableAt (by norm_num)
    rw [hdg.hasDerivAt.hasDerivWithinAt.derivWithin hU, deriv_comp_neg f 0, neg_zero, h1,
      neg_zero]
  obtain ⟨C₂, hC₂0, hC₂⟩ : ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Icc 0 ρ, |f (-t)| ≤ C * t ^ 2 :=
    sqBound_Icc_of_derivWithin_zero hρ hneg (by simpa using h0) hnegw
  refine ⟨max C₁ C₂, le_max_of_le_left hC₁0, fun t ht => ?_⟩
  by_cases h : 0 ≤ t
  · have ht' : t ∈ Set.Icc 0 ρ := ⟨h, ht.2.le⟩
    exact (hC₁ t ht').trans (mul_le_mul_of_nonneg_right (le_max_left C₁ C₂) (sq_nonneg t))
  · have hlt : t < 0 := not_le.mp h
    have ht' : -t ∈ Set.Icc 0 ρ := ⟨by linarith, by linarith [ht.1]⟩
    have hb := hC₂ (-t) ht'
    rw [neg_neg, neg_sq] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right (le_max_right C₁ C₂) (sq_nonneg t))

end Work.Drive.Mono
