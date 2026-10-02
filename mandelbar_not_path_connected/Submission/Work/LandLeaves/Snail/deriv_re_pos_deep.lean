import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.LandLeaves.Snail

/-- If `F` is complex differentiable on the half-plane `{re < X}` and `F Z - Z` converges
uniformly to a constant `c` as `re Z → -∞` (i.e. `F` is eventually a `c`-perturbation of the
identity), then on a smaller half-plane `{re < X₂}` the derivative of `F` has strictly positive
real part.

The proof is Cauchy's estimate: writing `G = F - id - c`, the hypothesis bounds `‖G‖` by `1/2`
deep in the half-plane; on a disc of radius `1` around any `Z` with `re Z < β - 1` the function
`G` is holomorphic and bounded by `1/2` on the boundary, so `‖deriv G Z‖ ≤ 1/2`. Since
`F = id + c + G`, `deriv F Z = 1 + deriv G Z`, whose real part is `≥ 1 - ‖deriv G Z‖ ≥ 1/2 > 0`. -/
theorem deriv_re_pos_deep {F : ℂ → ℂ} {X : ℝ} {c : ℂ}
    (hdiff : DifferentiableOn ℂ F {Z : ℂ | Z.re < X})
    (hzero : ∀ ε : ℝ, 0 < ε → ∃ β : ℝ, β < X ∧ ∀ Z : ℂ, Z.re < β → ‖(F Z - Z) - c‖ < ε) :
    ∃ X₂ : ℝ, X₂ < X ∧ ∀ Z : ℂ, Z.re < X₂ → 0 < (deriv F Z).re := by
  obtain ⟨β, hβX, hβ⟩ := hzero (1/2) (by norm_num)
  refine ⟨β - 1, by linarith, ?_⟩
  intro Z hZ
  have hZβ : Z.re < β := by linarith
  have hs_open : IsOpen {w : ℂ | w.re < X} :=
    isOpen_lt Complex.continuous_re continuous_const
  have hZmem : Z ∈ {w : ℂ | w.re < X} := by
    simp only [Set.mem_ofPred_eq]; linarith
  have hF_at : DifferentiableAt ℂ F Z := hdiff.differentiableAt (hs_open.mem_nhds hZmem)
  have hball_mem : ∀ w : ℂ, w ∈ Metric.ball Z 1 → w ∈ {w : ℂ | w.re < X} := by
    intro w hw
    have h1 : ‖w - Z‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hw
    simp only [Set.mem_ofPred_eq]
    linarith [Complex.re_le_norm (w - Z), Complex.sub_re w Z]
  have hcl_mem : ∀ w : ℂ, w ∈ Metric.closedBall Z 1 → w ∈ {w : ℂ | w.re < X} := by
    intro w hw
    have h1 : ‖w - Z‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hw
    simp only [Set.mem_ofPred_eq]
    linarith [Complex.re_le_norm (w - Z), Complex.sub_re w Z]
  have hFdc : DiffContOnCl ℂ F (Metric.ball Z 1) :=
    DiffContOnCl.mk_ball (hdiff.mono hball_mem) (hdiff.continuousOn.mono hcl_mem)
  have hIdc : DiffContOnCl ℂ (id : ℂ → ℂ) (Metric.ball Z 1) :=
    differentiable_id.diffContOnCl
  have hCc : DiffContOnCl ℂ (fun _ : ℂ => c) (Metric.ball Z 1) := diffContOnCl_const
  have hfun : ((F - id) - (fun _ : ℂ => c)) = (fun w : ℂ => F w - w - c) := by
    funext w; rfl
  have hGdc : DiffContOnCl ℂ (fun w : ℂ => F w - w - c) (Metric.ball Z 1) := by
    have h := (hFdc.sub hIdc).sub hCc
    rw [hfun] at h
    exact h
  have hbound : ‖deriv (fun w : ℂ => F w - w - c) Z‖ ≤ (1:ℝ)/2 := by
    have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (c := Z) (R := 1) (C := (1:ℝ)/2)
      (f := fun w : ℂ => F w - w - c) one_pos hGdc ?_
    · simpa using h
    · intro w hw
      have hwr : w.re < β := by
        have h1 : ‖w - Z‖ = 1 := mem_sphere_iff_norm.mp hw
        linarith [Complex.re_le_norm (w - Z), Complex.sub_re w Z]
      exact le_of_lt (hβ w hwr)
  have hderiv : deriv (fun w : ℂ => F w - w - c) Z = deriv F Z - 1 := by
    have hd : HasDerivAt ((F - id) - (fun _ : ℂ => c)) ((deriv F Z - 1) - 0) Z :=
      (hF_at.hasDerivAt.sub (hasDerivAt_id Z)).sub (hasDerivAt_const Z c)
    have h := hd.deriv
    rw [hfun] at h
    simpa using h
  rw [hderiv] at hbound
  have hre : (deriv F Z).re = (deriv F Z - 1).re + 1 := by
    rw [Complex.sub_re, Complex.one_re]; ring
  have hlow : -(1/2:ℝ) ≤ (deriv F Z - 1).re := by
    have h1 : |(deriv F Z - 1).re| ≤ ‖deriv F Z - 1‖ := Complex.abs_re_le_norm _
    have h2 : -((deriv F Z - 1).re) ≤ |(deriv F Z - 1).re| := neg_le_abs _
    linarith
  rw [hre]
  linarith

end Work.LandLeaves.Snail
