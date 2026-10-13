import Mathlib

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.RegPkgGal.R1b

open Set Filter Topology MeasureTheory
open scoped Topology Real

set_option autoImplicit false

/-! ## A general gluing lemma -/

/-- **Gluing of derivatives along two pieces covering a neighbourhood.**  If `f` agrees with `f₁`
on `s` and with `f₂` on `t`, if `s ∪ t` is a neighbourhood of `x`, and if `f₁`, `f₂` both have
derivative `L` at `x`, then so does `f`. -/
theorem hasFDerivAt_of_union {f f₁ f₂ : ℝ × ℝ → ℝ} {L : (ℝ × ℝ) →L[ℝ] ℝ} {x : ℝ × ℝ}
    {s t : Set (ℝ × ℝ)} (hst : s ∪ t ∈ 𝓝 x) (hxs : x ∈ s) (hxt : x ∈ t)
    (h1 : ∀ y ∈ s, f y = f₁ y) (h2 : ∀ y ∈ t, f y = f₂ y)
    (hf₁ : HasFDerivAt f₁ L x) (hf₂ : HasFDerivAt f₂ L x) : HasFDerivAt f L x :=
  ((hf₁.hasFDerivWithinAt.congr h1 (h1 x hxs)).union
    (hf₂.hasFDerivWithinAt.congr h2 (h2 x hxt))).hasFDerivAt hst

/-! ## General auxiliary facts -/

/-- The Fréchet derivative of `f : ℝ × ℝ → ℝ` is the sum of its two partial derivatives
(evaluated on the two basis vectors). -/
theorem fderiv_eq_partials {f : ℝ × ℝ → ℝ} {x : ℝ × ℝ} (hf : DifferentiableAt ℝ f x) :
    fderiv ℝ f x
      = (deriv (fun z => f (z, x.2)) x.1) • ContinuousLinearMap.fst ℝ ℝ ℝ
        + (deriv (fun s => f (x.1, s)) x.2) • ContinuousLinearMap.snd ℝ ℝ ℝ := by
  refine ContinuousLinearMap.ext fun v => ?_
  obtain ⟨u, w⟩ := v
  have h1 : (fderiv ℝ f x) (1, 0) = deriv (fun z => f (z, x.2)) x.1 := by
    have hc : HasDerivAt (fun z : ℝ => (z, x.2)) ((1, 0) : ℝ × ℝ) x.1 := by
      simpa using (hasDerivAt_id x.1).prodMk (hasDerivAt_const x.1 x.2)
    have hh := (hf.hasFDerivAt.comp_hasDerivAt (x.1) hc).deriv
    simpa [Function.comp_def] using hh.symm
  have h2 : (fderiv ℝ f x) (0, 1) = deriv (fun s => f (x.1, s)) x.2 := by
    have hc : HasDerivAt (fun s : ℝ => (x.1, s)) ((0, 1) : ℝ × ℝ) x.2 := by
      simpa using (hasDerivAt_const x.2 x.1).prodMk (hasDerivAt_id x.2)
    have hh := (hf.hasFDerivAt.comp_hasDerivAt (x.2) hc).deriv
    simpa [Function.comp_def] using hh.symm
  have hsplit : (u, w) = u • (1, 0) + w • (0, 1) := by ext <;> simp
  have hL : (fderiv ℝ f x) (u, w)
      = deriv (fun z => f (z, x.2)) x.1 * u + deriv (fun s => f (x.1, s)) x.2 * w := by
    rw [hsplit, map_add, map_smul, map_smul, h1, h2]
    simp only [smul_eq_mul]
    ring
  have hR : ((deriv (fun z => f (z, x.2)) x.1) • ContinuousLinearMap.fst ℝ ℝ ℝ
        + (deriv (fun s => f (x.1, s)) x.2) • ContinuousLinearMap.snd ℝ ℝ ℝ) (u, w)
      = deriv (fun z => f (z, x.2)) x.1 * u + deriv (fun s => f (x.1, s)) x.2 * w := by
    simp [smul_eq_mul]
  rw [hL, hR]

/-- The partial derivative of a `C¹` function in the first variable is continuous. -/
theorem continuousOn_deriv_z_slice {f : ℝ × ℝ → ℝ} {s : Set (ℝ × ℝ)} (hs : IsOpen s)
    (hf : ContDiffOn ℝ 1 f s) :
    ContinuousOn (fun q : ℝ × ℝ => deriv (fun z => f (z, q.2)) q.1) s := by
  have hf' : ContinuousOn (fderiv ℝ f) s := hf.continuousOn_fderiv_of_isOpen hs (by norm_num)
  have hc : ContinuousOn (fun q : ℝ × ℝ => (fderiv ℝ f q) (1, 0)) s :=
    hf'.clm_apply continuousOn_const
  refine hc.congr fun q hq => ?_
  have hd : DifferentiableAt ℝ f q :=
    (hf.differentiableOn one_ne_zero q hq).differentiableAt (hs.mem_nhds hq)
  have hcurve : HasDerivAt (fun z : ℝ => (z, q.2)) ((1, 0) : ℝ × ℝ) q.1 := by
    simpa using (hasDerivAt_id q.1).prodMk (hasDerivAt_const q.1 q.2)
  have hh := (hd.hasFDerivAt.comp_hasDerivAt (q.1) hcurve).deriv
  simpa [Function.comp_def] using hh

/-- The partial derivative of a `C¹` function in the second variable is continuous. -/
theorem continuousOn_deriv_t_slice {f : ℝ × ℝ → ℝ} {s : Set (ℝ × ℝ)} (hs : IsOpen s)
    (hf : ContDiffOn ℝ 1 f s) :
    ContinuousOn (fun q : ℝ × ℝ => deriv (fun t => f (q.1, t)) q.2) s := by
  have hf' : ContinuousOn (fderiv ℝ f) s := hf.continuousOn_fderiv_of_isOpen hs (by norm_num)
  have hc : ContinuousOn (fun q : ℝ × ℝ => (fderiv ℝ f q) (0, 1)) s :=
    hf'.clm_apply continuousOn_const
  refine hc.congr fun q hq => ?_
  have hd : DifferentiableAt ℝ f q :=
    (hf.differentiableOn one_ne_zero q hq).differentiableAt (hs.mem_nhds hq)
  have hcurve : HasDerivAt (fun t : ℝ => (q.1, t)) ((0, 1) : ℝ × ℝ) q.2 := by
    simpa using (hasDerivAt_const q.2 q.1).prodMk (hasDerivAt_id q.2)
  have hh := (hd.hasFDerivAt.comp_hasDerivAt (q.2) hcurve).deriv
  simpa [Function.comp_def] using hh

/-- Extraction of a two-sided `ε`-`δ` statement (a box in `(z,τ)`) from a joint limit as
`(z,τ) → (0,τ₀)` within `z > 0`. -/
theorem tendsto_box {F : ℝ × ℝ → ℝ} {τ₀ c : ℝ}
    (h : Tendsto F (nhdsWithin (0, τ₀) (Ioi (0:ℝ) ×ˢ univ)) (nhds c)) :
    ∀ ε > 0, ∃ δ > 0, ∀ z τ : ℝ, 0 < z → z < δ → |τ - τ₀| < δ → |F (z, τ) - c| < ε := by
  intro ε hε
  have hmem : {p : ℝ × ℝ | |F p - c| < ε} ∈ nhdsWithin (0, τ₀) (Ioi (0:ℝ) ×ˢ univ) :=
    (Metric.tendsto_nhds.mp h) ε hε
  rcases mem_nhdsWithin.mp hmem with ⟨V, hVopen, hxV, hVsub⟩
  rcases Metric.mem_nhds_iff.mp (hVopen.mem_nhds hxV) with ⟨δ, hδ, hδV⟩
  refine ⟨δ, hδ, fun z τ hz hzδ hτδ => hVsub ⟨hδV ?_, ⟨hz, trivial⟩⟩⟩
  rw [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_zero, abs_of_pos hz]
  exact max_lt hzδ hτδ


/-! ## More auxiliary lemmas for the corner analysis -/

/-- Near `(0,τ₀)`, any point with `0 < z` has `z < δ` and `|τ - τ₀| < δ`. -/
theorem eventually_box (τ₀ δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ y : ℝ × ℝ in 𝓝 (0, τ₀), 0 < y.1 → y.1 < δ ∧ |y.2 - τ₀| < δ := by
  have hbox : Ioo (-δ) δ ×ˢ Ioo (τ₀ - δ) (τ₀ + δ) ∈ 𝓝 ((0, τ₀) : ℝ × ℝ) := by
    apply (isOpen_Ioo.prod isOpen_Ioo).mem_nhds
    show (0:ℝ) ∈ Ioo (-δ) δ ∧ τ₀ ∈ Ioo (τ₀ - δ) (τ₀ + δ)
    exact ⟨⟨by linarith, hδ⟩, ⟨by linarith, by linarith⟩⟩
  filter_upwards [hbox] with y hy _
  exact ⟨hy.1.2, abs_lt.mpr ⟨by linarith [hy.2.1], by linarith [hy.2.2]⟩⟩

/-- From `|z⁻¹ * v| < c` with `0 < z` deduce `|v| < c * z`. -/
theorem abs_lt_mul_of_abs_inv_mul_lt {z v c : ℝ} (hz : 0 < z) (h : |z⁻¹ * v| < c) :
    |v| < c * z := by
  have h' : z⁻¹ * |v| < c := by rwa [abs_mul, abs_inv, abs_of_pos hz] at h
  have h'' := mul_lt_mul_of_pos_left h' hz
  rwa [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hz), one_mul, mul_comm z c] at h''

/-- From a joint limit as `(z,τ) → (0,τ₀)` within `z > 0` (to `0`) we get an eventual bound. -/
theorem eventually_of_tendsto_box {F : ℝ × ℝ → ℝ} {τ₀ c : ℝ} (hc : 0 < c)
    (h : Tendsto F (nhdsWithin (0, τ₀) (Ioi 0 ×ˢ univ)) (nhds 0)) :
    ∀ᶠ y : ℝ × ℝ in 𝓝 (0, τ₀), 0 < y.1 → |F y| < c := by
  rcases tendsto_box h c hc with ⟨δ, hδ, H⟩
  filter_upwards [eventually_box τ₀ δ hδ] with y hy hy1
  exact by simpa using H y.1 y.2 hy1 (hy hy1).1 (hy hy1).2

/-- The slice at `τ = τ₀` of a joint limit as `(z,τ) → (0,τ₀)`. -/
theorem slice_bound_of_tendsto {F : ℝ × ℝ → ℝ} {τ₀ c : ℝ} (hc : 0 < c)
    (h : Tendsto F (nhdsWithin (0, τ₀) (Ioi 0 ×ˢ univ)) (nhds 0)) :
    ∃ δ > 0, ∀ z : ℝ, 0 < z → z < δ → |F (z, τ₀)| < c := by
  rcases tendsto_box h c hc with ⟨δ, hδ, H⟩
  exact ⟨δ, hδ, fun z hz hzδ => by simpa using H z τ₀ hz hzδ (by simpa using hδ)⟩

/-- Norm bound for the combination `a • fst + b • snd`. -/
theorem norm_smul_fst_add_smul_snd_le (a b : ℝ) :
    ‖a • ContinuousLinearMap.fst ℝ ℝ ℝ + b • ContinuousLinearMap.snd ℝ ℝ ℝ‖ ≤ |a| + |b| := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  obtain ⟨u, w⟩ := v
  have hv : (a • ContinuousLinearMap.fst ℝ ℝ ℝ + b • ContinuousLinearMap.snd ℝ ℝ ℝ) (u, w)
      = a * u + b * w := by simp
  have hmax : max |u| |w| = ‖(u, w)‖ := by rw [Prod.norm_def]; simp
  rw [hv]
  calc ‖a * u + b * w‖ ≤ ‖a * u‖ + ‖b * w‖ := norm_add_le _ _
    _ = |a| * |u| + |b| * |w| := by
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul]
    _ ≤ (|a| + |b|) * max |u| |w| := by
        have h1 : |u| ≤ max |u| |w| := le_max_left _ _
        have h2 : |w| ≤ max |u| |w| := le_max_right _ _
        nlinarith [abs_nonneg a, abs_nonneg b, abs_nonneg u, abs_nonneg w]
    _ = (|a| + |b|) * ‖(u, w)‖ := by rw [hmax]

end Work.FTS.RegPkgGal.R1b
