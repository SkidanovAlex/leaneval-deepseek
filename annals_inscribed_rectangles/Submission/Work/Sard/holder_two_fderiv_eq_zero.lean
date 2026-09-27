import Mathlib

open Set Metric

namespace Work.Sard

/-- **`2`-Hölder estimate for maps with vanishing derivative.**  A smooth map whose derivative vanishes
at `x` is, locally on the zero set of its derivative, Hölder continuous with exponent `2`.

Corrected proof sketch (the pairwise bound needs the vanishing of the derivative at *both* endpoints):
let `S := {x : E | fderiv ℝ f x = 0}`.  Since `f` is smooth, `fderiv ℝ f` is locally Lipschitz at `x`,
so there are `r > 0` and `L : NNReal` with `‖fderiv ℝ f z - fderiv ℝ f x‖ ≤ L * ‖z - x‖` for
`‖z - x‖ ≤ r` (mean value inequality applied to `fderiv ℝ f` on a ball, using that
`fderiv ℝ (fderiv ℝ f)` is continuous at `x`).  Take `t := S ∩ K ∩ closedBall x r`; for `y, y' ∈ t`
both derivatives vanish, and for `z` on the segment `[y,y']`,
`‖fderiv ℝ f z‖ ≤ L * min (‖z-y‖) (‖z-y'‖)`; the convex mean value inequality
(`Convex.norm_image_sub_le_of_norm_fderivWithin_le` with `s = segment ℝ y y'`) then gives
`‖f y - f y'‖ ≤ L * ‖y-y'‖ ^ 2`.  Hence `HolderOnWith L 2 f t`, and
`t ∈ nhdsWithin x (S ∩ K)` since `closedBall x r ∈ nhds x`. -/
theorem holder_two_fderiv_eq_zero {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (f : E → F) (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (K : Set E) :
    ∀ x ∈ {x : E | fderiv ℝ f x = 0} ∩ K,
      ∃ C : NNReal, ∃ t ∈ nhdsWithin x ({x : E | fderiv ℝ f x = 0} ∩ K),
        HolderOnWith C 2 f t := by
  intro x hx
  obtain ⟨hxS, _hxK⟩ := hx
  -- `f` is differentiable and its derivative is smooth, hence `fderiv ℝ f` is locally Lipschitz.
  have hdf : Differentiable ℝ f := (contDiff_infty_iff_fderiv.mp hf).1
  have hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fderiv ℝ f) :=
    (contDiff_infty_iff_fderiv.mp hf).2
  obtain ⟨L, t₀, ht₀, hLip⟩ := (hg.contDiffAt.of_le (by simp)).exists_lipschitzOnWith
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp ht₀
  refine ⟨L, ({x : E | fderiv ℝ f x = 0} ∩ K) ∩ Metric.closedBall x (r/2), ?_, ?_⟩
  · exact inter_mem_nhdsWithin _ (Metric.closedBall_mem_nhds x (by linarith))
  · -- both endpoints `u`, `v` have vanishing derivative, and the mean value inequality is applied
    -- on the convex set `closedBall u ‖v - u‖ ∩ closedBall x (r/2)`, where `‖fderiv ℝ f‖` is
    -- bounded by `L * ‖v - u‖`.
    intro u hu v hv
    obtain ⟨huS, huB⟩ := hu
    obtain ⟨hvS, hvB⟩ := hv
    have hu0 : fderiv ℝ f u = 0 := huS.1
    have hu_t₀ : u ∈ t₀ := hrsub (Metric.closedBall_subset_ball (by linarith) huB)
    have hv_t₀ : v ∈ t₀ := hrsub (Metric.closedBall_subset_ball (by linarith) hvB)
    have hbound : ∀ z ∈ Metric.closedBall u ‖v - u‖ ∩ Metric.closedBall x (r/2),
        ‖fderiv ℝ f z‖ ≤ (L : ℝ) * ‖v - u‖ := by
      intro z hz
      obtain ⟨hz1, hz2⟩ := hz
      have hzu : dist z u ≤ ‖v - u‖ := Metric.mem_closedBall.mp hz1
      have hz_t₀ : z ∈ t₀ := hrsub (Metric.closedBall_subset_ball (by linarith) hz2)
      have h := hLip.dist_le_mul z hz_t₀ u hu_t₀
      rw [dist_eq_norm, hu0, sub_zero, dist_eq_norm] at h
      rw [dist_eq_norm] at hzu
      calc ‖fderiv ℝ f z‖ ≤ (L : ℝ) * ‖z - u‖ := h
        _ ≤ (L : ℝ) * ‖v - u‖ := mul_le_mul_of_nonneg_left hzu (by positivity)
    have hmvt : ‖f v - f u‖ ≤ ((L : ℝ) * ‖v - u‖) * ‖v - u‖ :=
      Convex.norm_image_sub_le_of_norm_fderiv_le
        (s := Metric.closedBall u ‖v - u‖ ∩ Metric.closedBall x (r/2))
        (C := (L : ℝ) * ‖v - u‖)
        (fun z _ => hdf z)
        hbound
        ((convex_closedBall u _).inter (convex_closedBall x _))
        ⟨Metric.mem_closedBall_self (norm_nonneg _), huB⟩
        ⟨by simp [Metric.mem_closedBall, dist_eq_norm], hvB⟩
    have hmain : dist (f u) (f v) ≤ (L : ℝ) * dist u v ^ (2 : ℝ) := by
      have h1 : ‖f u - f v‖ = ‖f v - f u‖ := by rw [← norm_neg (f u - f v), neg_sub]
      have h2 : ‖u - v‖ = ‖v - u‖ := by rw [← norm_neg (u - v), neg_sub]
      rw [dist_eq_norm, dist_eq_norm, h1, h2, Real.rpow_two]
      calc ‖f v - f u‖ ≤ ((L : ℝ) * ‖v - u‖) * ‖v - u‖ := hmvt
        _ = (L : ℝ) * ‖v - u‖ ^ 2 := by ring
    rw [NNReal.coe_two, edist_dist, edist_dist, ENNReal.coe_nnreal_eq,
      ENNReal.ofReal_rpow_of_nonneg dist_nonneg (by norm_num : (0:ℝ) ≤ 2),
      ← ENNReal.ofReal_mul (NNReal.coe_nonneg L)]
    exact ENNReal.ofReal_le_ofReal hmain

end Work.Sard
