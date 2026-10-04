import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.flat

open Filter Set Asymptotics

open scoped Topology

/-- Uniform bound on the difference of `g` and `f n`, obtained from the uniform convergence of the
derivatives via the mean value theorem on a convex set.

If each `f n` (for `n ≥ N₀`) is differentiable on the convex set `s` with derivative `f' n`, the
`f n` converge pointwise on `s` to `g`, and the `f' n` converge uniformly on `s` to `g'`, then for
every `ε > 0` there is `N ≥ N₀` such that for all `n ≥ N` and all `x, y ∈ s`
`‖(g y - g x) - (f n y - f n x)‖ ≤ ε * ‖y - x‖`. -/
lemma norm_sub_sub_le_of_tendstoUniformlyOn_deriv {s : Set ℝ} (hs : Convex ℝ s)
    {f f' : ℕ → ℝ → ℂ} {g g' : ℝ → ℂ} {N₀ : ℕ}
    (hderiv : ∀ n ≥ N₀, ∀ z ∈ s, HasDerivAt (f n) (f' n z) z)
    (hf : ∀ z ∈ s, Tendsto (fun n => f n z) atTop (𝓝 (g z)))
    (hf' : TendstoUniformlyOn f' g' atTop s) {ε : ℝ} (hε : 0 < ε) :
    ∃ N ≥ N₀, ∀ n ≥ N, ∀ x ∈ s, ∀ y ∈ s,
      ‖(g y - g x) - (f n y - f n x)‖ ≤ ε * ‖y - x‖ := by
  have h2 : 0 < ε / 2 := by linarith
  obtain ⟨N, hN0, hN⟩ : ∃ N ≥ N₀, ∀ n ≥ N, ∀ z ∈ s, ‖f' n z - g' z‖ ≤ ε / 2 := by
    have h := (Metric.tendstoUniformlyOn_iff.mp hf') (ε / 2) h2
    obtain ⟨N, hN⟩ := eventually_atTop.mp h
    refine ⟨max N N₀, le_max_right _ _, fun n hn z hz => ?_⟩
    have hn' : N ≤ n := le_trans (le_max_left _ _) hn
    have hz' := hN n hn' z hz
    rw [dist_eq_norm, norm_sub_rev] at hz'
    exact le_of_lt hz'
  refine ⟨N, hN0, fun n hn x hx y hy => ?_⟩
  have hn0 : N₀ ≤ n := le_trans hN0 hn
  have hmvt : ∀ m ≥ N, ‖(f m y - f n y) - (f m x - f n x)‖ ≤ ε * ‖y - x‖ := by
    intro m hm
    have hm0 : N₀ ≤ m := le_trans hN0 hm
    have hdiff : ∀ z ∈ s, DifferentiableAt ℝ (fun w => f m w - f n w) z := fun z hz =>
      ((hderiv m hm0 z hz).differentiableAt).sub ((hderiv n hn0 z hz).differentiableAt)
    have hbound : ∀ z ∈ s, ‖deriv (fun w => f m w - f n w) z‖ ≤ ε := by
      intro z hz
      have hdm : DifferentiableAt ℝ (f m) z := (hderiv m hm0 z hz).differentiableAt
      have hdn : DifferentiableAt ℝ (f n) z := (hderiv n hn0 z hz).differentiableAt
      have hd : deriv (fun w => f m w - f n w) z = f' m z - f' n z := by
        change deriv (f m - f n) z = f' m z - f' n z
        rw [deriv_sub hdm hdn, (hderiv m hm0 z hz).deriv, (hderiv n hn0 z hz).deriv]
      rw [hd]
      have heq : (f' m z - g' z) - (f' n z - g' z) = f' m z - f' n z := by ring
      rw [← heq]
      have h1 := hN m hm z hz
      have h2' := hN n hn z hz
      linarith [norm_sub_le (f' m z - g' z) (f' n z - g' z)]
    exact Convex.norm_image_sub_le_of_norm_deriv_le (f := fun w => f m w - f n w) (C := ε)
      hdiff hbound hs hx hy
  have hconv : Tendsto (fun m => (f m y - f n y) - (f m x - f n x)) atTop
      (𝓝 ((g y - g x) - (f n y - f n x))) := by
    have h1 : Tendsto (fun m => f m y - f n y) atTop (𝓝 (g y - f n y)) :=
      Tendsto.sub (hf y hy) tendsto_const_nhds
    have h2 : Tendsto (fun m => f m x - f n x) atTop (𝓝 (g x - f n x)) :=
      Tendsto.sub (hf x hx) tendsto_const_nhds
    have hsub := Tendsto.sub h1 h2
    rwa [show (g y - f n y) - (g x - f n x) = (g y - g x) - (f n y - f n x) from by ring]
      at hsub
  exact le_of_tendsto hconv.norm (eventually_atTop.mpr ⟨N, fun m hm => hmvt m hm⟩)

theorem hasDerivWithinAt_of_tendstoUniformlyOn {T : ℝ} {f f' : ℕ → ℝ → ℂ} {g g' : ℝ → ℂ}
    (hderiv : ∃ M₀ : ℕ, ∀ m ≥ M₀, ∀ t ∈ Set.Ico (0 : ℝ) T, HasDerivAt (f m) (f' m t) t)
    (hf : TendstoUniformlyOn (fun m => f m) g Filter.atTop (Set.Ico (0 : ℝ) T))
    (hf' : TendstoUniformlyOn (fun m => f' m) g' Filter.atTop (Set.Ico (0 : ℝ) T)) :
    ∀ t ∈ Set.Ico (0 : ℝ) T, HasDerivWithinAt g (g' t) (Set.Ico (0 : ℝ) T) t := by
  obtain ⟨M₀, hM₀⟩ := hderiv
  intro t ht
  rw [hasDerivWithinAt_iff_isLittleO, isLittleO_iff]
  intro c hc
  have hc3 : 0 < c / 3 := by positivity
  obtain ⟨N, hN0, hN⟩ :=
    norm_sub_sub_le_of_tendstoUniformlyOn_deriv (s := Set.Ico (0 : ℝ) T) (convex_Ico 0 T)
      (N₀ := M₀) (fun n hn z hz => hM₀ n hn z hz) (fun z hz => hf.tendsto_at hz) hf' hc3
  have hf'ε : ∀ᶠ n in atTop, ∀ z ∈ Set.Ico (0 : ℝ) T, ‖f' n z - g' z‖ ≤ c / 3 := by
    have h := (Metric.tendstoUniformlyOn_iff.mp hf') (c / 3) hc3
    filter_upwards [h] with n hn
    intro z hz
    have hnz := hn z hz
    rw [dist_eq_norm, norm_sub_rev] at hnz
    exact le_of_lt hnz
  obtain ⟨N', hN'⟩ := eventually_atTop.mp hf'ε
  set n := max N N' with hn_def
  have hn1 : N ≤ n := le_max_left _ _
  have hn2 : N' ≤ n := le_max_right _ _
  have hn0 : M₀ ≤ n := le_trans hN0 hn1
  have hderivn : HasDerivAt (f n) (f' n t) t := hM₀ n hn0 t ht
  have e1 : ∀ᶠ y in 𝓝[Set.Ico (0 : ℝ) T] t,
      ‖(g y - g t) - (f n y - f n t)‖ ≤ c / 3 * ‖y - t‖ :=
    eventually_nhdsWithin_iff.mpr
      (Eventually.of_forall (fun y hy => hN n hn1 t ht y hy))
  have e2 : ∀ᶠ y in 𝓝[Set.Ico (0 : ℝ) T] t,
      ‖(f n y - f n t) - (y - t) • f' n t‖ ≤ c / 3 * ‖y - t‖ :=
    IsLittleO.def (hderivn.hasDerivWithinAt.isLittleO (s := Set.Ico (0 : ℝ) T)) hc3
  have e3 : ∀ᶠ y in 𝓝[Set.Ico (0 : ℝ) T] t,
      ‖(y - t) • (f' n t - g' t)‖ ≤ c / 3 * ‖y - t‖ := by
    rw [eventually_nhdsWithin_iff]
    refine Eventually.of_forall (fun y _ => ?_)
    rw [norm_smul]
    calc ‖y - t‖ * ‖f' n t - g' t‖ ≤ ‖y - t‖ * (c / 3) :=
          mul_le_mul_of_nonneg_left (hN' n hn2 t ht) (norm_nonneg _)
      _ = c / 3 * ‖y - t‖ := by ring
  filter_upwards [e1, e2, e3] with y h1 h2 h3
  have hid : g y - g t - (y - t) • g' t
      = ((g y - g t) - (f n y - f n t)) + ((f n y - f n t) - (y - t) • f' n t)
        + ((y - t) • (f' n t - g' t)) := by
    rw [smul_sub]
    abel
  rw [hid]
  have h4 : ‖((g y - g t) - (f n y - f n t)) + ((f n y - f n t) - (y - t) • f' n t)‖
      ≤ c / 3 * ‖y - t‖ + c / 3 * ‖y - t‖ := le_trans (norm_add_le _ _) (add_le_add h1 h2)
  calc ‖(((g y - g t) - (f n y - f n t)) + ((f n y - f n t) - (y - t) • f' n t))
        + ((y - t) • (f' n t - g' t))‖
      ≤ ‖((g y - g t) - (f n y - f n t)) + ((f n y - f n t) - (y - t) • f' n t)‖
        + ‖(y - t) • (f' n t - g' t)‖ := norm_add_le _ _
    _ ≤ (c / 3 * ‖y - t‖ + c / 3 * ‖y - t‖) + c / 3 * ‖y - t‖ := add_le_add h4 h3
    _ = c * ‖y - t‖ := by ring

end Work.Diff.STE.flat

