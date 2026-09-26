import Mathlib

namespace Work.Smooth.Morse.Regular

open Set

/-! # The implicit function theorem in the plane, solving for the second variable

The local model of a regular level of a `C¹` function of two variables when the partial derivative
in the second variable is invertible: the level set is locally the graph of a function of the
first variable, presented as an arc `σ` through `p`. -/

/-- The level set of a `C¹` function of two variables near a point where the partial
derivative in the *second* variable is an isomorphism is locally an arc. -/
theorem local_arc_snd {f : ℝ × ℝ → ℝ} {f' : ℝ × ℝ →L[ℝ] ℝ}
    {p : ℝ × ℝ} {t : ℝ} (hf : HasStrictFDerivAt f f' p) (hp : f p = t)
    (hinv : (f' ∘L ContinuousLinearMap.inr ℝ ℝ ℝ).IsInvertible) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ σ : ℝ → ℝ × ℝ, σ 0 = p ∧
      ContinuousOn σ (Set.Ioo (-1 : ℝ) 1) ∧ Set.InjOn σ (Set.Ioo (-1 : ℝ) 1) ∧
      (∀ s ∈ Set.Ioo (-1 : ℝ) 1, f (σ s) = t) ∧
      (∀ q : ℝ × ℝ, f q = t → ‖q - p‖ < ε → ∃ s ∈ Set.Ioo (-1 : ℝ) 1, σ s = q) := by
  classical
  -- The implicit function data associated with `f`, together with its open partial
  -- homeomorphism `e : ℝ × ℝ → ℝ × ℝ`, `e y = (f y, y.1)`.
  set φ : ImplicitFunctionData ℝ (ℝ × ℝ) ℝ ℝ := hf.implicitFunctionDataOfProdDomain hinv with hφ
  set e := φ.toOpenPartialHomeomorph with he
  -- `p` lies in the source of `e`, and `(t, p.1) = e p` lies in its target.
  have hsrc : p ∈ e.source := by
    simpa [hφ] using φ.pt_mem_toOpenPartialHomeomorph_source
  have hpt_mem_tgt : (t, p.1) ∈ e.target := by
    simpa [hφ, hp] using φ.map_pt_mem_toOpenPartialHomeomorph_target
  have he_apply : ∀ y : ℝ × ℝ, e y = (f y, y.1) := by
    intro y
    rw [he, ImplicitFunctionData.toOpenPartialHomeomorph_coe, ImplicitFunctionData.prodFun_apply]
    simp [hφ]
  -- Radii of balls around `p` inside `e.source` and around `(t, p.1)` inside `e.target`.
  obtain ⟨r_s, hr_s, hball_s⟩ := Metric.mem_nhds_iff.mp (e.open_source.mem_nhds hsrc)
  obtain ⟨r_t, hr_t, hball_t⟩ := Metric.mem_nhds_iff.mp (e.open_target.mem_nhds hpt_mem_tgt)
  -- The horizontal half-width `c` of the arc, small enough for both balls.
  set c := min r_s r_t / 2 with hc_def
  have hc : 0 < c := by
    rw [hc_def]; have := lt_min hr_s hr_t; linarith
  have hc_rs : c < r_s := by
    rw [hc_def]; have := min_le_left r_s r_t; linarith
  have hc_rt : c < r_t := by
    rw [hc_def]; have := min_le_right r_s r_t; linarith
  -- `e.symm` is continuous and injective on `e.target`.
  have hcont_e : ContinuousOn e.symm e.target :=
    fun x hx => (e.continuousAt_symm hx).continuousWithinAt
  have hinj_e : InjOn e.symm e.target := by
    intro a ha b hb hab
    have h : e (e.symm a) = e (e.symm b) := congrArg (fun x => e x) hab
    rwa [e.right_inv ha, e.right_inv hb] at h
  -- The horizontal line `g s = (t, p.1 + c * s)`.
  set g : ℝ → ℝ × ℝ := fun s => (t, p.1 + c * s) with hg_def
  have hcont_g : ContinuousOn g (Set.Ioo (-1:ℝ) 1) := by rw [hg_def]; fun_prop
  have hinj_g : InjOn g (Set.Ioo (-1:ℝ) 1) := by
    intro a _ b _ hab
    have h2 : p.1 + c * a = p.1 + c * b := by
      have := congrArg Prod.snd hab
      simpa [hg_def] using this
    have h3 : c * a = c * b := by linarith
    exact mul_left_cancel₀ (ne_of_gt hc) h3
  -- For `|s| < 1` the point `g s` stays inside `e.target`.
  have hMaps : MapsTo g (Set.Ioo (-1:ℝ) 1) e.target := by
    intro s hs
    apply hball_t
    rw [Metric.mem_ball]
    have hs1 : |s| < 1 := abs_lt.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have hnorm : dist (g s) (t, p.1) = c * |s| := by
      rw [dist_eq_norm]
      have h1 : g s - (t, p.1) = ((0 : ℝ), c * s) := by
        rw [hg_def]; simp
      rw [h1, Prod.norm_def, norm_zero, Real.norm_eq_abs, abs_mul, abs_of_pos hc,
        max_eq_right (by positivity)]
    rw [hnorm]
    nlinarith [hc, hs1, hc_rt]
  -- The arc `σ s = e.symm (g s)`.
  set σ : ℝ → ℝ × ℝ := e.symm ∘ g with hσ_def
  refine ⟨c, hc, σ, ?_, ?_, ?_, ?_, ?_⟩
  · -- `σ 0 = p`
    rw [hσ_def]; simp only [Function.comp_apply]
    have hg0 : g 0 = e p := by
      rw [hg_def, he_apply]; simp [hp]
    rw [hg0, e.left_inv hsrc]
  · -- continuity
    rw [hσ_def]; exact hcont_e.comp hcont_g hMaps
  · -- injectivity
    rw [hσ_def]; exact hinj_e.comp hinj_g hMaps
  · -- the arc lies in the level set
    intro s hs
    rw [hσ_def]; simp only [Function.comp_apply]
    simpa [he_apply, hg_def] using congrArg Prod.fst (e.right_inv (hMaps hs))
  · -- the arc exhausts the level set near `p`
    intro q hfq hqn
    have hq_src : q ∈ e.source := by
      apply hball_s
      rw [Metric.mem_ball, dist_eq_norm]
      exact lt_trans hqn hc_rs
    have hq1 : |q.1 - p.1| < c := by
      have h1 : ‖(q - p).1‖ ≤ ‖q - p‖ := norm_fst_le (q - p)
      have h2 : ‖(q - p).1‖ = |q.1 - p.1| := by simp [Real.norm_eq_abs]
      rw [h2] at h1
      linarith
    refine ⟨(q.1 - p.1)/c, ?_, ?_⟩
    · -- the parameter lies in `(-1, 1)`
      have habs : |(q.1 - p.1)/c| < 1 := by
        rw [abs_div, abs_of_pos hc, div_lt_one hc]
        exact hq1
      rwa [Set.mem_Ioo, ← abs_lt]
    · -- `σ` hits `q`
      rw [hσ_def]; simp only [Function.comp_apply]
      have hgs : g ((q.1 - p.1)/c) = e q := by
        rw [hg_def, he_apply, hfq]
        ext <;> simp
        rw [mul_div_cancel₀ _ (ne_of_gt hc)]; ring
      rw [hgs, e.left_inv hq_src]

end Work.Smooth.Morse.Regular
