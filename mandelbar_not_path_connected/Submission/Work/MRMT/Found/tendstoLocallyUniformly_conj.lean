import Mathlib
import Submission.Work.MRMT.Found.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Locally uniform convergence of the conjugates `star ∘ F n ∘ f ∘ F n⁻¹`

If `F n` are homeomorphisms of `ℂ` converging locally uniformly to the homeomorphism `φ`
(and `(F n)⁻¹` to `φ⁻¹`), then for every continuous `f : ℂ → ℂ` the conjugates
`z ↦ star (F n (f ((F n)⁻¹ z)))` converge locally uniformly to
`z ↦ star (φ (f (φ⁻¹ z)))`.

The two ingredients are the standard stability properties of locally uniform convergence
on the locally compact space `ℂ`:

* post-composition with a continuous map: `g ∘ F n → g ∘ f` when `F n → f` locally
  uniformly and `g` is continuous (here `g` is uniformly continuous on the relevant
  compact ball by Heine–Cantor, and `F n` is eventually confined to that ball);
* composition of two locally uniformly convergent families: `F n ∘ G n → f ∘ g`.

The `PrincipalData` of the mandelbar/MRMT construction provides `Fn → φ` and
`Fn.symm → φ.symm` locally uniformly, which yields the claim for `star ∘ Fn ∘ f ∘ Fn.symm`.
-/

open Filter Topology Function

namespace Work.MRMT.Found

/-- **Post-composition with a continuous map** preserves locally uniform convergence:
if `F n → f` locally uniformly and `g` is continuous, then `g ∘ F n → g ∘ f` locally
uniformly.

Proof: on a neighbourhood of a point `x` the functions `F n` eventually stay in a fixed
closed ball containing the (bounded) image of `f`, and `g` is uniformly continuous there
by Heine–Cantor. -/
theorem tendstoLocallyUniformly_comp_continuous {ι : Type*} {p : Filter ι}
    {F : ι → ℂ → ℂ} {f : ℂ → ℂ} (hF : TendstoLocallyUniformly F f p) (hf : Continuous f)
    {g : ℂ → ℂ} (hg : Continuous g) :
    TendstoLocallyUniformly (fun n => g ∘ F n) (g ∘ f) p := by
  rw [Metric.tendstoLocallyUniformly_iff] at hF ⊢
  intro ε hε x
  obtain ⟨r, hr⟩ : ∃ r : ℝ, f '' Metric.closedBall x 1 ⊆ Metric.closedBall (0 : ℂ) r :=
    (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mp
      (((isCompact_closedBall x (1 : ℝ)).image hf).isBounded)
  have hr0 : 0 ≤ r := by
    have hx1 : x ∈ Metric.closedBall x (1 : ℝ) := by simp
    have := hr (Set.mem_image_of_mem f hx1)
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at this
    exact le_trans (norm_nonneg (f x)) this
  have huc : UniformContinuousOn g (Metric.closedBall (0 : ℂ) (r + ‖x‖ + 2)) :=
    (isCompact_closedBall (0 : ℂ) (r + ‖x‖ + 2)).uniformContinuousOn_of_continuous
      hg.continuousOn
  obtain ⟨δ, hδ0, hδ⟩ := (Metric.uniformContinuousOn_iff.mp huc) ε hε
  obtain ⟨t, ht, htend⟩ := hF (min δ 1) (lt_min hδ0 one_pos) x
  refine ⟨t ∩ Metric.ball x 1, Filter.inter_mem ht (Metric.ball_mem_nhds x one_pos), ?_⟩
  filter_upwards [htend] with n hn y hy
  obtain ⟨hyt, hyb⟩ := hy
  simp only [Function.comp_apply]
  have hdl : dist (f y) (F n y) < min δ 1 := hn y hyt
  have hdδ : dist (f y) (F n y) < δ := lt_of_lt_of_le hdl (min_le_left _ _)
  have hfy : f y ∈ Metric.closedBall (0 : ℂ) (r + ‖x‖ + 2) := by
    have h1 : f y ∈ f '' Metric.closedBall x (1 : ℝ) :=
      ⟨y, Metric.ball_subset_closedBall hyb, rfl⟩
    have h2 := hr h1
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at h2
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    linarith [norm_nonneg x]
  have hFny : F n y ∈ Metric.closedBall (0 : ℂ) (r + ‖x‖ + 2) := by
    have h1 : ‖F n y - f y‖ < 1 := by
      have h := lt_of_lt_of_le hdl (min_le_right _ _)
      rwa [dist_comm, dist_eq_norm] at h
    have h2 : ‖f y‖ ≤ r := by
      have h := hr ⟨y, Metric.ball_subset_closedBall hyb, rfl⟩
      rwa [Metric.mem_closedBall, dist_eq_norm, sub_zero] at h
    have h3 : ‖F n y‖ ≤ ‖F n y - f y‖ + ‖f y‖ := by
      simpa using norm_add_le (F n y - f y) (f y)
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    linarith [norm_nonneg x]
  exact hδ (f y) hfy (F n y) hFny hdδ

/-- **Composition** of two locally uniformly convergent families: if `F n → f` and
`G n → g` locally uniformly on `ℂ` and both limits are continuous, then
`F n ∘ G n → f ∘ g` locally uniformly.

Proof: near `x` the values `G n y` eventually lie in a fixed closed ball `B` of `ℂ`
containing the (bounded) image of `g`; `f` is uniformly continuous on `B` by
Heine–Cantor, and `F n → f` uniformly on the compact ball `B`. -/
theorem tendstoLocallyUniformly_comp {ι : Type*} {p : Filter ι}
    {F G : ι → ℂ → ℂ} {f g : ℂ → ℂ} (hF : TendstoLocallyUniformly F f p)
    (hG : TendstoLocallyUniformly G g p) (hf : Continuous f) (hg : Continuous g) :
    TendstoLocallyUniformly (fun n => F n ∘ G n) (f ∘ g) p := by
  rw [Metric.tendstoLocallyUniformly_iff] at hG ⊢
  intro ε hε x
  have hε2 : 0 < ε / 2 := by linarith
  obtain ⟨r, hr⟩ : ∃ r : ℝ, g '' Metric.closedBall x 1 ⊆ Metric.closedBall (0 : ℂ) r :=
    (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mp
      (((isCompact_closedBall x (1 : ℝ)).image hg).isBounded)
  have huc : UniformContinuousOn f (Metric.closedBall (0 : ℂ) (r + 1)) :=
    (isCompact_closedBall (0 : ℂ) (r + 1)).uniformContinuousOn_of_continuous hf.continuousOn
  obtain ⟨δ, hδ0, hδ⟩ := (Metric.uniformContinuousOn_iff.mp huc) (ε / 2) hε2
  have hFB : TendstoUniformlyOn F f p (Metric.closedBall (0 : ℂ) (r + 1)) :=
    (tendstoLocallyUniformly_iff_forall_isCompact.mp hF) _
      (isCompact_closedBall (0 : ℂ) (r + 1))
  have hFend : ∀ᶠ n in p, ∀ w ∈ Metric.closedBall (0 : ℂ) (r + 1),
      dist (f w) (F n w) < ε / 2 :=
    (Metric.tendstoUniformlyOn_iff.mp hFB) (ε / 2) hε2
  obtain ⟨t, ht, htend⟩ := hG (min δ 1) (lt_min hδ0 one_pos) x
  refine ⟨t ∩ Metric.ball x 1, Filter.inter_mem ht (Metric.ball_mem_nhds x one_pos), ?_⟩
  filter_upwards [htend, hFend] with n hn hFn y hy
  obtain ⟨hyt, hyb⟩ := hy
  simp only [Function.comp_apply]
  have hdl : dist (g y) (G n y) < min δ 1 := hn y hyt
  have hdδ : dist (g y) (G n y) < δ := lt_of_lt_of_le hdl (min_le_left _ _)
  have hgy_mem : g y ∈ Metric.closedBall (0 : ℂ) (r + 1) := by
    have h := hr ⟨y, Metric.ball_subset_closedBall hyb, rfl⟩
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at h
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    linarith
  have hGy_mem : G n y ∈ Metric.closedBall (0 : ℂ) (r + 1) := by
    have h1 : ‖G n y - g y‖ < 1 := by
      have h := lt_of_lt_of_le hdl (min_le_right _ _)
      rwa [dist_comm, dist_eq_norm] at h
    have h2 : ‖g y‖ ≤ r := by
      have h := hr ⟨y, Metric.ball_subset_closedBall hyb, rfl⟩
      rwa [Metric.mem_closedBall, dist_eq_norm, sub_zero] at h
    have h3 : ‖G n y‖ ≤ ‖G n y - g y‖ + ‖g y‖ := by
      simpa using norm_add_le (G n y - g y) (g y)
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    linarith
  have h1 : dist (f (g y)) (f (G n y)) < ε / 2 := hδ (g y) hgy_mem (G n y) hGy_mem hdδ
  have h2 : dist (f (G n y)) (F n (G n y)) < ε / 2 := hFn (G n y) hGy_mem
  calc dist (f (g y)) (F n (G n y))
      ≤ dist (f (g y)) (f (G n y)) + dist (f (G n y)) (F n (G n y)) := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add h1 h2
    _ = ε := by ring

theorem tendstoLocallyUniformly_conj {μ : ℂ → ℂ} (d : Work.MRMT.Found.PrincipalData μ)
    {f : ℂ → ℂ} (hf : Continuous f) :
    TendstoLocallyUniformly
      (fun n => star ∘ ((d.Fn n : ℂ → ℂ)) ∘ f ∘ ((d.Fn n).symm : ℂ → ℂ))
      (star ∘ (d.φ : ℂ → ℂ) ∘ f ∘ ((d.φ).symm : ℂ → ℂ)) Filter.atTop := by
  -- `f ∘ Fn.symm → f ∘ φ.symm`: post-composition of `Fn.symm → φ.symm` with `f`.
  have h1 : TendstoLocallyUniformly (fun n => f ∘ ((d.Fn n).symm : ℂ → ℂ))
      (f ∘ ((d.φ).symm : ℂ → ℂ)) Filter.atTop :=
    tendstoLocallyUniformly_comp_continuous d.tendsto_symm_Fn d.φ.symm.continuous hf
  -- compose with `Fn → φ`.
  have h2 : TendstoLocallyUniformly
      (fun n => ((d.Fn n : ℂ → ℂ)) ∘ (f ∘ ((d.Fn n).symm : ℂ → ℂ)))
      (((d.φ : ℂ → ℂ)) ∘ (f ∘ ((d.φ).symm : ℂ → ℂ))) Filter.atTop :=
    tendstoLocallyUniformly_comp d.tendsto_Fn h1 d.φ.continuous (hf.comp d.φ.symm.continuous)
  -- and post-compose with the continuous map `star`.
  have h3 := tendstoLocallyUniformly_comp_continuous h2
    (d.φ.continuous.comp (hf.comp d.φ.symm.continuous))
    (continuous_star : Continuous (star : ℂ → ℂ))
  simpa only [Function.comp_assoc] using h3

end Work.MRMT.Found
