import Mathlib

open scoped ContDiff Topology

namespace Work.RPB.B5

/-- If two functions are continuous at `x₀` and agree on the open interval `(x₀, x₀ + δ)`
with `δ > 0`, then they agree at `x₀`. -/
theorem eq_of_continuousAt_of_eqOn_Ioo_right {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F G : ℝ → E} {x₀ δ : ℝ} (hδ : 0 < δ) (hF : ContinuousAt F x₀) (hG : ContinuousAt G x₀)
    (h : ∀ x ∈ Set.Ioo x₀ (x₀ + δ), F x = G x) : F x₀ = G x₀ := by
  have hmem : Set.Ioo x₀ (x₀ + δ) ∈ 𝓝[Set.Ioi x₀] x₀ := by
    rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
    exact ⟨Set.Iio (x₀ + δ), Iio_mem_nhds (by linarith), fun x hx => ⟨hx.2, hx.1⟩⟩
  have hFG : F =ᶠ[𝓝[Set.Ioi x₀] x₀] G := Filter.mem_of_superset hmem h
  exact tendsto_nhds_unique ((hF.tendsto.mono_left nhdsWithin_le_nhds).congr' hFG)
    (hG.tendsto.mono_left nhdsWithin_le_nhds)

/-- If two functions are differentiable at `x₀`, agree at `x₀`, and agree on the open interval
`(x₀, x₀ + δ)` with `δ > 0`, then their derivatives at `x₀` agree. -/
theorem deriv_eq_of_eqOn_Ioo_right {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F G : ℝ → E} {x₀ δ : ℝ} (hδ : 0 < δ) (hF : DifferentiableAt ℝ F x₀)
    (hG : DifferentiableAt ℝ G x₀) (hx : F x₀ = G x₀)
    (h : ∀ x ∈ Set.Ioo x₀ (x₀ + δ), F x = G x) : deriv F x₀ = deriv G x₀ := by
  have hmem : Set.Ioo x₀ (x₀ + δ) ∈ 𝓝[Set.Ioi x₀] x₀ := by
    rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
    exact ⟨Set.Iio (x₀ + δ), Iio_mem_nhds (by linarith), fun x hx => ⟨hx.2, hx.1⟩⟩
  have hle : 𝓝[Set.Ioi x₀] x₀ ≤ 𝓝[({x₀}ᶜ : Set ℝ)] x₀ :=
    nhdsWithin_mono x₀ (fun y hy => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; exact ne_of_gt hy)
  have hslope : slope F x₀ =ᶠ[𝓝[Set.Ioi x₀] x₀] slope G x₀ := by
    filter_upwards [hmem] with x hx'
    simp only [slope, h x hx', hx]
  have hFt : Filter.Tendsto (slope F x₀) (𝓝[Set.Ioi x₀] x₀) (𝓝 (deriv F x₀)) :=
    hF.hasDerivAt.tendsto_slope.mono_left hle
  have hGt : Filter.Tendsto (slope G x₀) (𝓝[Set.Ioi x₀] x₀) (𝓝 (deriv G x₀)) :=
    hG.hasDerivAt.tendsto_slope.mono_left hle
  exact tendsto_nhds_unique (hFt.congr' hslope) hGt

/-- A `C^n` function at `x` has `C^{n-k}` iterated `k`-th derivative at `x`, for `k ≤ n`. -/
theorem contDiffAt_iteratedDeriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {x : ℝ} {n : ℕ} (hf : ContDiffAt ℝ n f x) {k : ℕ} (hk : k ≤ n) :
    ContDiffAt ℝ ((n - k : ℕ) : ℕ∞ω) (iteratedDeriv k f) x := by
  revert hk
  induction k with
  | zero => intro hk; simpa using hf
  | succ k ih =>
    intro hk
    have hk' : k ≤ n := by omega
    have ih' := ih hk'
    rw [iteratedDeriv_succ]
    refine ContDiffAt.derivWithin ih' ?_
    have h1 : n - (k + 1) + 1 = n - k := by omega
    rw [← h1]
    push_cast
    exact le_rfl

theorem iteratedDeriv_eq_of_eqOn_Ioo_right {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f g : ℝ → E} {x₀ δ : ℝ} (hδ : 0 < δ) {n : ℕ} (hf : ContDiffAt ℝ n f x₀) (hg : ContDiffAt ℝ n g x₀) (h : ∀ x ∈ Set.Ioo x₀ (x₀ + δ), f x = g x) {k : ℕ} (hk : k ≤ n) : iteratedDeriv k f x₀ = iteratedDeriv k g x₀ := by
  have hstep : ∀ j, ∀ x ∈ Set.Ioo x₀ (x₀ + δ), iteratedDeriv j f x = iteratedDeriv j g x :=
    fun j x hx => Set.EqOn.iteratedDeriv_of_isOpen (fun x hx => h x hx) isOpen_Ioo j hx
  revert hk
  induction k with
  | zero =>
    intro hk
    simpa using eq_of_continuousAt_of_eqOn_Ioo_right hδ hf.continuousAt hg.continuousAt h
  | succ m ih =>
    intro hk
    have hm : m ≤ n := by omega
    have hih : iteratedDeriv m f x₀ = iteratedDeriv m g x₀ := ih hm
    have hdiffF : DifferentiableAt ℝ (iteratedDeriv m f) x₀ :=
      (contDiffAt_iteratedDeriv hf hm).differentiableAt (by
        simp only [ne_eq, Nat.cast_eq_zero]; omega)
    have hdiffG : DifferentiableAt ℝ (iteratedDeriv m g) x₀ :=
      (contDiffAt_iteratedDeriv hg hm).differentiableAt (by
        simp only [ne_eq, Nat.cast_eq_zero]; omega)
    rw [iteratedDeriv_succ, iteratedDeriv_succ]
    exact deriv_eq_of_eqOn_Ioo_right hδ hdiffF hdiffG hih (fun x hx => hstep m x hx)

end Work.RPB.B5
