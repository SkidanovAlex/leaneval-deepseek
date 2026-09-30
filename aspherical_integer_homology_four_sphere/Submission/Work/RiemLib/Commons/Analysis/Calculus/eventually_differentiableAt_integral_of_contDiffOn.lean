import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Commons.Analysis.Calculus

open MeasureTheory Filter Set
open scoped Topology MeasureTheory Interval ContDiff

/-- Pointwise first-variable derivative of a two-variable function that is `C^∞` at a point:
the derivative of `s ↦ G (s, t)` at `σ` is `fderiv ℝ G (σ, t) (1, 0)`. -/
private lemma hasDerivAt_fst_of_contDiffAt
    {G : ℝ × ℝ → ℝ} {p : ℝ × ℝ} (hG : ContDiffAt ℝ ∞ G p) :
    HasDerivAt (fun s : ℝ => G (s, p.2)) (fderiv ℝ G p (1, 0)) p.1 := by
  have hd : DifferentiableAt ℝ G p := hG.differentiableAt (by simp)
  have hφ : HasFDerivAt (fun s : ℝ => (s, p.2)) (ContinuousLinearMap.inl ℝ ℝ ℝ) p.1 :=
    hasFDerivAt_prodMk_left (𝕜 := ℝ) p.1 p.2
  have h := (hd.hasFDerivAt.comp p.1 hφ).hasDerivAt
  have h' : HasDerivAt (fun s : ℝ => G (s, p.2))
      ((fderiv ℝ G p).comp (ContinuousLinearMap.inl ℝ ℝ ℝ) 1) p.1 := by
    simpa only [Function.comp_def] using h
  have hval : (fderiv ℝ G p).comp (ContinuousLinearMap.inl ℝ ℝ ℝ) 1 = fderiv ℝ G p (1, 0) := by
    simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]
  rwa [hval] at h'

/-- **Differentiation under the integral sign on a compact rectangle**, at an arbitrary
basepoint `σ₀`: if `g` and its `σ`-derivative `g'` are continuous on the rectangle
`[σ₀ - δ, σ₀ + δ] × [a, b]` and `g'` is the pointwise `σ`-derivative of `g` on the interior,
then `σ ↦ ∫_a^b g(σ, t) dt` is differentiable at `σ₀` with derivative `∫_a^b g'(σ₀, t) dt`. -/
private theorem hasDerivAt_integral_of_continuousOn_Icc_prod_at
    {g g' : ℝ → ℝ → ℝ} {a b σ₀ δ : ℝ} (hab : a ≤ b) (hδ : 0 < δ)
    (hg : ContinuousOn (fun p : ℝ × ℝ => g p.1 p.2)
      (Set.Icc (σ₀ - δ) (σ₀ + δ) ×ˢ Set.Icc a b))
    (hg' : ContinuousOn (fun p : ℝ × ℝ => g' p.1 p.2)
      (Set.Icc (σ₀ - δ) (σ₀ + δ) ×ˢ Set.Icc a b))
    (hderiv : ∀ σ ∈ Set.Ioo (σ₀ - δ) (σ₀ + δ), ∀ t ∈ Set.Icc a b,
      HasDerivAt (fun σ' : ℝ => g σ' t) (g' σ t) σ) :
    HasDerivAt (fun σ : ℝ => ∫ t in a..b, g σ t) (∫ t in a..b, g' σ₀ t) σ₀ := by
  have hmem : σ₀ ∈ Set.Ioo (σ₀ - δ) (σ₀ + δ) := ⟨by linarith, by linarith⟩
  have h0 : σ₀ ∈ Set.Icc (σ₀ - δ) (σ₀ + δ) := ⟨le_of_lt hmem.1, le_of_lt hmem.2⟩
  have sliceCont : ∀ x ∈ Set.Icc (σ₀ - δ) (σ₀ + δ),
      ContinuousOn (fun t : ℝ => g x t) (Set.Icc a b) := by
    intro x hx
    have h1 : ContinuousOn (fun t : ℝ => (x, t)) (Set.Icc a b) :=
      ((continuous_const : Continuous fun _ : ℝ => x).prodMk continuous_id).continuousOn
    have h2 := hg.comp h1 (fun t ht => ⟨hx, ht⟩)
    convert h2 using 1
    ext t; rfl
  have sliceCont' : ∀ x ∈ Set.Icc (σ₀ - δ) (σ₀ + δ),
      ContinuousOn (fun t : ℝ => g' x t) (Set.Icc a b) := by
    intro x hx
    have h1 : ContinuousOn (fun t : ℝ => (x, t)) (Set.Icc a b) :=
      ((continuous_const : Continuous fun _ : ℝ => x).prodMk continuous_id).continuousOn
    have h2 := hg'.comp h1 (fun t ht => ⟨hx, ht⟩)
    convert h2 using 1
    ext t; rfl
  have hF_meas : ∀ᶠ x in 𝓝 (σ₀:ℝ),
      AEStronglyMeasurable (fun t : ℝ => g x t) (volume.restrict (Ι a b)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hmem] with x hx
    exact ContinuousOn.aestronglyMeasurable_of_subset_isCompact
      (sliceCont x ⟨le_of_lt hx.1, le_of_lt hx.2⟩) isCompact_Icc measurableSet_uIoc
      (by rw [Set.uIoc_of_le hab]; exact Set.Ioc_subset_Icc_self)
  have hF_int : IntervalIntegrable (fun t : ℝ => g σ₀ t) volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab (sliceCont σ₀ h0)
  have hF'_meas : AEStronglyMeasurable (fun t : ℝ => g' σ₀ t) (volume.restrict (Ι a b)) :=
    ContinuousOn.aestronglyMeasurable_of_subset_isCompact
      (sliceCont' σ₀ h0) isCompact_Icc measurableSet_uIoc
      (by rw [Set.uIoc_of_le hab]; exact Set.Ioc_subset_Icc_self)
  obtain ⟨C, hC⟩ :=
    ((isCompact_Icc (a := σ₀ - δ) (b := σ₀ + δ)).prod
      (isCompact_Icc (a := a) (b := b))).exists_bound_of_continuousOn hg'
  have h_bound : ∀ᵐ t ∂volume, t ∈ Ι a b →
      ∀ x ∈ Set.Ioo (σ₀ - δ) (σ₀ + δ), ‖g' x t‖ ≤ C := by
    filter_upwards with t ht x hx
    rw [Set.uIoc_of_le hab] at ht
    exact hC (x, t) ⟨⟨le_of_lt hx.1, le_of_lt hx.2⟩, ⟨le_of_lt ht.1, ht.2⟩⟩
  have hbound_int : IntervalIntegrable (fun _ : ℝ => C) volume a b := intervalIntegrable_const
  have h_diff : ∀ᵐ t ∂volume, t ∈ Ι a b → ∀ x ∈ Set.Ioo (σ₀ - δ) (σ₀ + δ),
      HasDerivAt (fun x => g x t) (g' x t) x := by
    filter_upwards with t ht x hx
    rw [Set.uIoc_of_le hab] at ht
    exact hderiv x hx t ⟨le_of_lt ht.1, ht.2⟩
  exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun x t => g x t) (F' := fun x t => g' x t)
    (s := Set.Ioo (σ₀ - δ) (σ₀ + δ)) (bound := fun _ => C)
    (isOpen_Ioo.mem_nhds hmem) hF_meas hF_int hF'_meas h_bound hbound_int h_diff).2

/-- If `(σ, t) ↦ g σ t` is `C^∞` on the open set `U ×ˢ Ioo (a-1) (b+1)`, then for every
`σ₀ ∈ U` the function `σ ↦ ∫_a^b g σ t dt` is differentiable at `σ₀` (and its derivative is
`∫_a^b ∂g/∂σ (σ₀, t) dt`). -/
private lemma differentiableAt_integral_of_contDiffOn
    {g : ℝ → ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) {U : Set ℝ} (hU : IsOpen U)
    {σ₀ : ℝ} (hσ₀ : σ₀ ∈ U)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ => g p.1 p.2)
      (U ×ˢ Set.Ioo (a - 1) (b + 1))) :
    DifferentiableAt ℝ (fun σ : ℝ => ∫ t in a..b, g σ t) σ₀ := by
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hσ₀)
  set δ : ℝ := ε / 2 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  have hrectU : Set.Icc (σ₀ - δ) (σ₀ + δ) ⊆ U := by
    intro x hx
    apply hεU
    rw [Metric.mem_ball, Real.dist_eq]
    have hle : |x - σ₀| ≤ δ := abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hlt : δ < ε := by rw [hδdef]; linarith
    linarith
  have hVopen : IsOpen (U ×ˢ Set.Ioo (a - 1) (b + 1)) := hU.prod isOpen_Ioo
  have hrectV : Set.Icc (σ₀ - δ) (σ₀ + δ) ×ˢ Set.Icc a b
      ⊆ U ×ˢ Set.Ioo (a - 1) (b + 1) := by
    intro p hp
    exact ⟨hrectU hp.1, by linarith [hp.2.1], by linarith [hp.2.2]⟩
  have hcontG : ContinuousOn (fun p : ℝ × ℝ => g p.1 p.2)
      (Set.Icc (σ₀ - δ) (σ₀ + δ) ×ˢ Set.Icc a b) :=
    hg.continuousOn.mono hrectV
  have hcontg' : ContinuousOn
      (fun p : ℝ × ℝ => fderiv ℝ (fun q : ℝ × ℝ => g q.1 q.2) (p.1, p.2) (1, 0))
      (Set.Icc (σ₀ - δ) (σ₀ + δ) ×ˢ Set.Icc a b) := by
    have hfd : ContDiffOn ℝ ∞ (fun y : ℝ × ℝ =>
        fderiv ℝ (fun q : ℝ × ℝ => g q.1 q.2) y ((1 : ℝ), (0 : ℝ)))
        (U ×ˢ Set.Ioo (a - 1) (b + 1)) :=
      (ContinuousLinearMap.apply ℝ ℝ ((1 : ℝ), (0 : ℝ))).contDiff.fun_comp_contDiffOn
        (hg.fderiv_of_isOpen hVopen (m := ∞) le_rfl)
    exact hfd.continuousOn.mono hrectV
  have hderiv : ∀ σ ∈ Set.Ioo (σ₀ - δ) (σ₀ + δ), ∀ t ∈ Set.Icc a b,
      HasDerivAt (fun σ' : ℝ => g σ' t)
        (fderiv ℝ (fun q : ℝ × ℝ => g q.1 q.2) (σ, t) (1, 0)) σ := by
    intro σ hσ t ht
    have hσU : σ ∈ U := hrectU ⟨le_of_lt hσ.1, le_of_lt hσ.2⟩
    have htV : t ∈ Set.Ioo (a - 1) (b + 1) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hmemV : (σ, t) ∈ U ×ˢ Set.Ioo (a - 1) (b + 1) := ⟨hσU, htV⟩
    have hGat : ContDiffAt ℝ ∞ (fun q : ℝ × ℝ => g q.1 q.2) (σ, t) :=
      hg.contDiffAt (hVopen.mem_nhds hmemV)
    exact hasDerivAt_fst_of_contDiffAt hGat
  exact (hasDerivAt_integral_of_continuousOn_Icc_prod_at hab hδ hcontG hcontg' hderiv).differentiableAt

open MeasureTheory Filter Set in
open scoped Topology MeasureTheory Interval in
theorem eventually_differentiableAt_integral_of_contDiffOn
    {g : ℝ → ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) {U : Set ℝ} (hU : IsOpen U) (h0U : (0 : ℝ) ∈ U)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ => g p.1 p.2) (U ×ˢ Set.Ioo (a - 1) (b + 1))) :
    ∀ᶠ σ in 𝓝 (0 : ℝ), DifferentiableAt ℝ (fun σ : ℝ => ∫ t in a..b, g σ t) σ := by
  filter_upwards [hU.mem_nhds h0U] with σ hσ
  exact differentiableAt_integral_of_contDiffOn hab hU hσ hg

end Commons.Analysis.Calculus