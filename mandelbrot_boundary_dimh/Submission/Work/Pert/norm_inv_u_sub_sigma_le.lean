import Mathlib

namespace Work.Pert

/-- Cauchy's estimate for the complex derivative on a half-radius sub-disc: if `f` is holomorphic
on the disc of radius `R` about the origin and bounded by `M` there, then `‖deriv f w‖ ≤ 4 M / R`
at every point of the closed disc of radius `R / 2`.

We bound the derivative at `w` by Cauchy's estimate on the disc of radius `R / 4` centred at `w`;
that disc is contained in the closed disc of radius `3 R / 4`, hence in the original disc, so no
boundary regularity is needed. -/
theorem norm_deriv_le_of_mem_closedBall_half {R M : ℝ} {f : ℂ → ℂ}
    (hR : 0 < R) (hf : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) R))
    (hM : ∀ z ∈ Metric.ball (0 : ℂ) R, ‖f z‖ ≤ M) :
    ∀ w ∈ Metric.closedBall (0 : ℂ) (R / 2), ‖deriv f w‖ ≤ 4 * M / R := by
  intro w hw
  have hw' : ‖w‖ ≤ R / 2 := by
    simpa [Metric.mem_closedBall, Complex.dist_eq, sub_zero] using hw
  -- the small disc around `w` stays well inside the original disc
  have hsub : Metric.closedBall w (R / 4) ⊆ Metric.ball (0 : ℂ) R := by
    intro z hz
    have hz' : ‖z - w‖ ≤ R / 4 := by
      simpa [Metric.mem_closedBall, Complex.dist_eq] using hz
    rw [Metric.mem_ball, Complex.dist_eq, sub_zero]
    calc ‖z‖ = ‖(z - w) + w‖ := by ring_nf
      _ ≤ ‖z - w‖ + ‖w‖ := norm_add_le _ _
      _ ≤ R / 4 + R / 2 := by linarith
      _ < R := by linarith
  have hd : DiffContOnCl ℂ f (Metric.ball w (R / 4)) :=
    DifferentiableOn.diffContOnCl_ball hf hsub
  have hC : ∀ z ∈ Metric.sphere w (R / 4), ‖f z‖ ≤ M := by
    intro z hz
    have hz' : ‖z - w‖ = R / 4 := by
      simpa [Metric.mem_sphere, Complex.dist_eq] using hz
    apply hM
    rw [Metric.mem_ball, Complex.dist_eq, sub_zero]
    calc ‖z‖ = ‖(z - w) + w‖ := by ring_nf
      _ ≤ ‖z - w‖ + ‖w‖ := norm_add_le _ _
      _ = R / 4 + ‖w‖ := by rw [hz']
      _ ≤ R / 4 + R / 2 := by linarith
      _ < R := by linarith
  have hres := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (c := w) (R := R / 4) (C := M)
    (by linarith) hd hC
  have heq : M / (R / 4) = 4 * M / R := by field_simp
  rwa [heq] at hres

theorem norm_inv_u_sub_sigma_le {rr : ℝ} {u : ℂ → ℂ} {σ : ℂ}
    (hrr : 0 < rr) (hu : DifferentiableOn ℂ u (Metric.ball (0 : ℂ) rr))
    (hu2 : ∀ w ∈ Metric.ball (0 : ℂ) rr, 1 / 2 ≤ ‖u w‖ ∧ ‖u w‖ ≤ 2)
    (hσ : ‖σ‖ ≤ rr / 2) :
    ‖1 / u σ - 1 / u 0 + σ‖ ≤ ‖σ‖ * (1 + 8 / rr) := by
  set g : ℂ → ℂ := fun w => 1 / u w with hg
  -- `u` does not vanish on the disc, so `1 / u` is holomorphic there
  have hne : ∀ w ∈ Metric.ball (0 : ℂ) rr, u w ≠ 0 := by
    intro w hw h
    have h1 := (hu2 w hw).1
    rw [h, norm_zero] at h1
    norm_num at h1
  have hgdiff : DifferentiableOn ℂ g (Metric.ball (0 : ℂ) rr) := by
    have h : DifferentiableOn ℂ (fun w => 1 / u w) (Metric.ball (0 : ℂ) rr) :=
      DifferentiableOn.div (differentiableOn_const (1 : ℂ)) hu hne
    simpa [hg] using h
  -- and it is bounded by `2` there
  have hgbd : ∀ w ∈ Metric.ball (0 : ℂ) rr, ‖g w‖ ≤ 2 := by
    intro w hw
    have h1 := (hu2 w hw).1
    have h2 : ‖g w‖ = 1 / ‖u w‖ := by simp [hg, one_div, norm_inv]
    rw [h2]
    have h3 : (0 : ℝ) < 1 / 2 := by norm_num
    have h4 := one_div_le_one_div_of_le h3 h1
    norm_num at h4
    simpa [one_div] using h4
  -- Cauchy's estimate: `‖(1/u)'‖ ≤ 4·2/rr = 8/rr` on the half-disc
  have hderiv : ∀ w ∈ Metric.closedBall (0 : ℂ) (rr / 2), ‖deriv g w‖ ≤ 8 / rr := by
    intro w hw
    have h := norm_deriv_le_of_mem_closedBall_half hrr hgdiff hgbd w hw
    have h2 : (4 : ℝ) * 2 / rr = 8 / rr := by ring
    rw [h2] at h
    exact h
  have hσmem : σ ∈ Metric.closedBall (0 : ℂ) (rr / 2) := by
    rw [Metric.mem_closedBall, Complex.dist_eq, sub_zero]
    exact hσ
  have h0mem : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) (rr / 2) := by
    rw [Metric.mem_closedBall, Complex.dist_eq, sub_zero, norm_zero]
    linarith
  -- mean value inequality along the segment from `0` to `σ`
  have hMVT : ‖g σ - g 0‖ ≤ (8 / rr) * ‖σ‖ := by
    have h := Convex.norm_image_sub_le_of_norm_deriv_le
      (s := Metric.closedBall (0 : ℂ) (rr / 2)) (C := 8 / rr)
      (f := g) ?_ ?_ (convex_closedBall _ _) h0mem hσmem
    · simpa using h
    · intro z hz
      have hz' : z ∈ Metric.ball (0 : ℂ) rr := by
        have hz'' : ‖z‖ ≤ rr / 2 := by
          simpa [Metric.mem_closedBall, Complex.dist_eq, sub_zero] using hz
        rw [Metric.mem_ball, Complex.dist_eq, sub_zero]
        linarith
      have hh : DifferentiableAt ℂ (fun w => 1 / u w) z :=
        DifferentiableAt.div (differentiableAt_const (1 : ℂ))
          (hu.differentiableAt (Metric.isOpen_ball.mem_nhds hz')) (hne z hz')
      simpa [hg] using hh
    · intro z hz
      exact hderiv z hz
  calc ‖1 / u σ - 1 / u 0 + σ‖ = ‖g σ - g 0 + σ‖ := by simp [hg]
    _ ≤ ‖g σ - g 0‖ + ‖σ‖ := norm_add_le _ _
    _ ≤ (8 / rr) * ‖σ‖ + ‖σ‖ := by linarith
    _ = ‖σ‖ * (1 + 8 / rr) := by ring

end Work.Pert
