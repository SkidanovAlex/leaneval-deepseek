import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Order.CompletePartialOrder

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr.RegSlab

open Set MeasureTheory Filter
open scoped Topology

/-- The `σ`-slice of a function which is continuous on the slab `Z ×ˢ (Θ ×ˢ Icc 0 δ)` is
continuous on `Icc 0 δ`. -/
lemma continuousOn_slice_of_continuousOn_slab {E : Type*} [NormedAddCommGroup E]
    {Z Θ : Set ℝ} {δ : ℝ} {B : ℝ × ℝ × ℝ → E}
    (hB : ContinuousOn B (Z ×ˢ (Θ ×ˢ Icc (0 : ℝ) δ)))
    {z θ : ℝ} (hz : z ∈ Z) (hθ : θ ∈ Θ) :
    ContinuousOn (fun σ : ℝ => B (z, θ, σ)) (Icc (0 : ℝ) δ) := by
  refine hB.comp ((continuous_const.prodMk (continuous_const.prodMk continuous_id)).continuousOn)
    (fun σ hσ => ⟨hz, hθ, hσ⟩)

/-- `uIcc 0 τ₀ ⊆ Icc 0 δ` whenever `τ₀ ∈ Icc 0 δ`. -/
lemma uIcc_zero_subset_Icc {δ τ₀ : ℝ} (hτ₀ : τ₀ ∈ Icc (0 : ℝ) δ) :
    uIcc (0 : ℝ) τ₀ ⊆ Icc (0 : ℝ) δ :=
  uIcc_subset_Icc ⟨le_rfl, le_trans hτ₀.1 hτ₀.2⟩ hτ₀

/-- Replacing the last coordinate of `p` by a number closer to the last coordinate of `p₀` than
`p.2.2` cannot increase the distance to `p₀`. -/
lemma dist_replace_last_le {p p₀ : ℝ × ℝ × ℝ} {σ : ℝ}
    (h : dist σ p₀.2.2 ≤ dist p.2.2 p₀.2.2) :
    dist (p.1, (p.2.1, σ)) p₀ ≤ dist p p₀ := by
  simp only [Prod.dist_eq]
  exact max_le_max_left _ (max_le_max_left _ h)

/-- **Uniform control forced by continuity on the slab.**  If `B` is continuous on the slab
`Z ×ˢ (Θ ×ˢ Icc 0 δ)` then, near any point `(z₀, θ₀) ∈ Z × Θ`, the difference
`B (z, θ, σ) - B (z₀, θ₀, σ)` is small *uniformly* in `σ ∈ Icc 0 δ`.  (The compactness of the
last slice `Icc 0 δ` is what makes the bound uniform; the first two coordinates are arbitrary
subsets of `ℝ`.) -/
lemma slab_eventually_uniform {E : Type*} [NormedAddCommGroup E]
    {Z Θ : Set ℝ} {δ : ℝ} {B : ℝ × ℝ × ℝ → E}
    (hB : ContinuousOn B (Z ×ˢ (Θ ×ˢ Icc (0 : ℝ) δ)))
    {z₀ : ℝ} (hz₀ : z₀ ∈ Z) {θ₀ : ℝ} (hθ₀ : θ₀ ∈ Θ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ p : ℝ × ℝ in 𝓝[Z ×ˢ Θ] (z₀, θ₀),
      ∀ σ ∈ Icc (0 : ℝ) δ, dist (B (p.1, p.2, σ)) (B (z₀, θ₀, σ)) < ε := by
  haveI : CompactSpace ↥(Icc (0 : ℝ) δ) := isCompact_iff_compactSpace.mp isCompact_Icc
  let Φ : ↥(Z ×ˢ Θ) × ↥(Icc (0 : ℝ) δ) → E × E :=
    fun x => (B ((x.1 : ℝ × ℝ).1, ((x.1 : ℝ × ℝ).2, (x.2 : ℝ))), B (z₀, θ₀, (x.2 : ℝ)))
  have hΦcont : Continuous Φ := by
    have h1 : Continuous fun x : ↥(Z ×ˢ Θ) × ↥(Icc (0 : ℝ) δ) =>
        B ((x.1 : ℝ × ℝ).1, ((x.1 : ℝ × ℝ).2, (x.2 : ℝ))) :=
      hB.comp_continuous
        ((continuous_fst.comp (continuous_subtype_val.comp continuous_fst)).prodMk
          ((continuous_snd.comp (continuous_subtype_val.comp continuous_fst)).prodMk
            (continuous_subtype_val.comp continuous_snd)))
        (fun x => ⟨x.1.2.1, x.1.2.2, x.2.2⟩)
    have h2 : Continuous fun x : ↥(Z ×ˢ Θ) × ↥(Icc (0 : ℝ) δ) => B (z₀, θ₀, (x.2 : ℝ)) := by
      have hslice : ContinuousOn (fun σ : ℝ => B (z₀, θ₀, σ)) (Icc (0 : ℝ) δ) :=
        continuousOn_slice_of_continuousOn_slab hB hz₀ hθ₀
      exact hslice.comp_continuous (continuous_subtype_val.comp continuous_snd) (fun x => x.2.2)
    exact h1.prodMk h2
  have hTclosed : IsClosed {y : E × E | ε ≤ dist y.1 y.2} := by
    simpa using isClosed_le (continuous_const : Continuous fun _ : E × E => ε)
      (continuous_dist.comp continuous_id : Continuous fun y : E × E => dist y.1 y.2)
  have hT : IsClosed (Φ ⁻¹' {y : E × E | ε ≤ dist y.1 y.2}) := hTclosed.preimage hΦcont
  have hproj : IsClosed (Prod.fst '' (Φ ⁻¹' {y : E × E | ε ≤ dist y.1 y.2})) :=
    isClosedMap_fst_of_compactSpace (X := ↥(Z ×ˢ Θ)) (Y := ↥(Icc (0 : ℝ) δ)) _ hT
  have hnotmem : (⟨(z₀, θ₀), ⟨hz₀, hθ₀⟩⟩ : ↥(Z ×ˢ Θ)) ∉
      Prod.fst '' (Φ ⁻¹' {y : E × E | ε ≤ dist y.1 y.2}) := by
    rintro ⟨y, hy, hyfst⟩
    have h1 : (y.1 : ℝ × ℝ) = (z₀, θ₀) := by
      have := congrArg Subtype.val hyfst
      simpa using this
    have h2 : (Φ y).1 = (Φ y).2 := by
      dsimp only [Φ]
      rw [h1]
    have hy' : ε ≤ dist (Φ y).1 (Φ y).2 := hy
    rw [h2, dist_self] at hy'
    linarith
  have hcompl : (Prod.fst '' (Φ ⁻¹' {y : E × E | ε ≤ dist y.1 y.2}))ᶜ ∈
      𝓝 (⟨(z₀, θ₀), ⟨hz₀, hθ₀⟩⟩ : ↥(Z ×ˢ Θ)) :=
    hproj.isOpen_compl.mem_nhds hnotmem
  obtain ⟨u, hu, hsub⟩ :=
    (mem_nhds_subtype (Z ×ˢ Θ) ⟨(z₀, θ₀), ⟨hz₀, hθ₀⟩⟩
      ((Prod.fst '' (Φ ⁻¹' {y : E × E | ε ≤ dist y.1 y.2}))ᶜ)).mp hcompl
  filter_upwards [show u ∈ 𝓝[Z ×ˢ Θ] (z₀, θ₀) from nhdsWithin_le_nhds hu,
    self_mem_nhdsWithin] with p hp hpmem
  intro σ hσ
  have hq : (⟨p, hpmem⟩ : ↥(Z ×ˢ Θ)) ∉
      Prod.fst '' (Φ ⁻¹' {y : E × E | ε ≤ dist y.1 y.2}) := hsub hp
  have : ¬ (ε ≤ dist (B (p.1, p.2, σ)) (B (z₀, θ₀, σ))) := by
    intro hle
    apply hq
    exact ⟨(⟨p, hpmem⟩, ⟨σ, hσ⟩), hle, rfl⟩
  exact not_le.mp this

/-- Continuity of the interval integral in the first two variables only (fixed upper limit `τ₀`),
on the slab of parameters. -/
lemma continuousOn_intervalIntegral_fixed {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {Z Θ : Set ℝ} {δ τ₀ : ℝ} {B : ℝ × ℝ × ℝ → E}
    (hB : ContinuousOn B (Z ×ˢ (Θ ×ˢ Icc (0 : ℝ) δ))) (hτ₀ : τ₀ ∈ Icc (0 : ℝ) δ) :
    ContinuousOn (fun p : ℝ × ℝ => ∫ σ in (0 : ℝ)..τ₀, B (p.1, p.2, σ)) (Z ×ˢ Θ) := by
  intro p₀ hp₀
  obtain ⟨z₀, θ₀⟩ := p₀
  rcases hp₀ with ⟨hz₀, hθ₀⟩
  refine intervalIntegral.continuousWithinAt_of_dominated_interval
    (F := fun p : ℝ × ℝ => fun σ : ℝ => B (p.1, p.2, σ))
    (bound := fun σ : ℝ => ‖B (z₀, θ₀, σ)‖ + 1) (a := 0) (b := τ₀) (s := Z ×ˢ Θ)
    ?_ ?_ ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with p hp
    exact ((continuousOn_slice_of_continuousOn_slab hB hp.1 hp.2).mono
      (uIoc_subset_uIcc.trans (uIcc_zero_subset_Icc hτ₀))).aestronglyMeasurable measurableSet_uIoc
  · filter_upwards [slab_eventually_uniform hB hz₀ hθ₀ (ε := 1) one_pos] with p hp
    filter_upwards with σ hσ
    have h1 : σ ∈ Icc (0 : ℝ) δ := (uIoc_subset_uIcc.trans (uIcc_zero_subset_Icc hτ₀)) hσ
    have h2 : dist (B (p.1, p.2, σ)) (B (z₀, θ₀, σ)) < 1 := hp σ h1
    have h3 : ‖B (p.1, p.2, σ) - B (z₀, θ₀, σ)‖ < 1 := by
      rwa [dist_eq_norm] at h2
    calc ‖B (p.1, p.2, σ)‖
        ≤ ‖B (z₀, θ₀, σ)‖ + ‖B (p.1, p.2, σ) - B (z₀, θ₀, σ)‖ := by
          have := norm_add_le (B (z₀, θ₀, σ)) (B (p.1, p.2, σ) - B (z₀, θ₀, σ))
          simpa using this
      _ ≤ ‖B (z₀, θ₀, σ)‖ + 1 := by linarith
  · have hslice : ContinuousOn (fun σ : ℝ => ‖B (z₀, θ₀, σ)‖ + 1) (Icc (0 : ℝ) δ) :=
      (continuousOn_slice_of_continuousOn_slab hB hz₀ hθ₀).norm.add continuousOn_const
    exact (hslice.mono (uIcc_zero_subset_Icc hτ₀)).intervalIntegrable
  · filter_upwards with σ hσ
    have h1 : σ ∈ Icc (0 : ℝ) δ := (uIoc_subset_uIcc.trans (uIcc_zero_subset_Icc hτ₀)) hσ
    have hcont : ContinuousOn (fun x : ℝ × ℝ => B (x.1, x.2, σ)) (Z ×ˢ Θ) :=
      hB.comp
        ((continuous_fst.prodMk (continuous_snd.prodMk continuous_const)).continuousOn)
        (fun x hx => ⟨hx.1, hx.2, h1⟩)
    exact hcont.continuousWithinAt ⟨hz₀, hθ₀⟩

theorem continuousOn_intervalIntegral_slab_normed {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {Z Θ : Set ℝ} {δ : ℝ} {B : ℝ × ℝ × ℝ → E}
    (hB : ContinuousOn B (Z ×ˢ (Θ ×ˢ Set.Icc (0 : ℝ) δ))) :
    ContinuousOn (fun p : ℝ × ℝ × ℝ => ∫ σ in (0 : ℝ)..p.2.2, B (p.1, p.2.1, σ))
      (Z ×ˢ (Θ ×ˢ Set.Icc (0 : ℝ) δ)) := by
  intro p₀ hp₀
  obtain ⟨z₀, θ₀, τ₀⟩ := p₀
  rcases hp₀ with ⟨hz₀, hθ₀, hτ₀⟩
  -- the fixed part `(z,θ) ↦ ∫₀^{τ₀} B (z,θ,σ) dσ`
  have hfirst : ContinuousWithinAt
      (fun p : ℝ × ℝ × ℝ => ∫ σ in (0 : ℝ)..τ₀, B (p.1, p.2.1, σ))
      (Z ×ˢ (Θ ×ˢ Icc (0 : ℝ) δ)) (z₀, θ₀, τ₀) :=
    ((continuousOn_intervalIntegral_fixed hB hτ₀).comp
      ((continuous_fst.prodMk (continuous_fst.comp continuous_snd)).continuousOn)
      (fun p hp => ⟨hp.1, hp.2.1⟩)).continuousWithinAt ⟨hz₀, hθ₀, hτ₀⟩
  -- the moving part `p ↦ ∫_{τ₀}^{p.2.2} B (p.1,p.2.1,σ) dσ` vanishes at `p₀`
  have hΨ : Tendsto (fun p : ℝ × ℝ × ℝ => ∫ σ in τ₀..p.2.2, B (p.1, p.2.1, σ))
      (𝓝[Z ×ˢ (Θ ×ˢ Icc (0 : ℝ) δ)] (z₀, θ₀, τ₀)) (𝓝 0) := by
    have hbound : ∀ᶠ p : ℝ × ℝ × ℝ in 𝓝[Z ×ˢ (Θ ×ˢ Icc (0 : ℝ) δ)] (z₀, θ₀, τ₀),
        ‖∫ σ in τ₀..p.2.2, B (p.1, p.2.1, σ)‖ ≤ |p.2.2 - τ₀| * (‖B (z₀, θ₀, τ₀)‖ + 1) := by
      have hcont : ∀ᶠ x : ℝ × ℝ × ℝ in 𝓝[Z ×ˢ (Θ ×ˢ Icc (0 : ℝ) δ)] (z₀, θ₀, τ₀),
          ‖B x‖ ≤ ‖B (z₀, θ₀, τ₀)‖ + 1 := by
        have ht := (hB (z₀, θ₀, τ₀) ⟨hz₀, hθ₀, hτ₀⟩).tendsto.norm
        filter_upwards [ht.eventually_lt_const (lt_add_one _)] with x hx
        exact le_of_lt hx
      obtain ⟨u, hu, hsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hcont
      obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hu
      filter_upwards [show Metric.ball (z₀, θ₀, τ₀) (r / 2) ∈
          𝓝[Z ×ˢ (Θ ×ˢ Icc (0 : ℝ) δ)] (z₀, θ₀, τ₀) from
        nhdsWithin_le_nhds (Metric.ball_mem_nhds _ (by positivity)),
        self_mem_nhdsWithin] with p hpball hpS
      have hpdist : dist p (z₀, θ₀, τ₀) < r / 2 := by
        simpa [Metric.mem_ball] using hpball
      have hstep : ‖∫ σ in τ₀..p.2.2, B (p.1, p.2.1, σ)‖ ≤
          (‖B (z₀, θ₀, τ₀)‖ + 1) * |p.2.2 - τ₀| := by
        refine intervalIntegral.norm_integral_le_of_norm_le_const (fun σ hσ => ?_)
        have hσIcc : σ ∈ Icc (0 : ℝ) δ := (uIoc_subset_uIcc.trans (uIcc_subset_Icc hτ₀ hpS.2.2)) hσ
        have hmemslab : (p.1, (p.2.1, σ)) ∈ Z ×ˢ (Θ ×ˢ Icc (0 : ℝ) δ) :=
          ⟨hpS.1, hpS.2.1, hσIcc⟩
        have hσdist : dist σ τ₀ ≤ dist p.2.2 τ₀ := by
          rw [Real.dist_eq, Real.dist_eq]
          rcases (mem_uIcc.mp (uIoc_subset_uIcc hσ)) with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ σ - τ₀),
              abs_of_nonneg (by linarith : (0 : ℝ) ≤ p.2.2 - τ₀)]
            linarith
          · rw [abs_of_nonpos (by linarith : σ - τ₀ ≤ 0),
              abs_of_nonpos (by linarith : p.2.2 - τ₀ ≤ 0)]
            linarith
        have hclose : dist (p.1, (p.2.1, σ)) (z₀, θ₀, τ₀) < r := by
          have := dist_replace_last_le (p := p) (p₀ := (z₀, θ₀, τ₀)) hσdist
          linarith
        exact hsub ⟨hball hclose, hmemslab⟩
      rw [mul_comm] at hstep
      exact hstep
    refine squeeze_zero_norm' hbound ?_
    have h2 : Tendsto (fun p : ℝ × ℝ × ℝ => p.2.2)
        (𝓝[Z ×ˢ (Θ ×ˢ Icc (0 : ℝ) δ)] (z₀, θ₀, τ₀)) (𝓝 τ₀) :=
      (continuous_snd.comp continuous_snd).tendsto (z₀, θ₀, τ₀) |>.mono_left nhdsWithin_le_nhds
    have h3 : Tendsto (fun p : ℝ × ℝ × ℝ => |p.2.2 - τ₀| * (‖B (z₀, θ₀, τ₀)‖ + 1))
        (𝓝[Z ×ˢ (Θ ×ˢ Icc (0 : ℝ) δ)] (z₀, θ₀, τ₀)) (𝓝 0) := by
      have h5 : Tendsto (fun p : ℝ × ℝ × ℝ => p.2.2 - τ₀)
          (𝓝[Z ×ˢ (Θ ×ˢ Icc (0 : ℝ) δ)] (z₀, θ₀, τ₀)) (𝓝 0) := by
        simpa using h2.sub_const τ₀
      have h6 : Tendsto (fun p : ℝ × ℝ × ℝ => |p.2.2 - τ₀|)
          (𝓝[Z ×ˢ (Θ ×ˢ Icc (0 : ℝ) δ)] (z₀, θ₀, τ₀)) (𝓝 0) := by
        simpa using h5.abs
      simpa using h6.mul_const (‖B (z₀, θ₀, τ₀)‖ + 1)
    exact h3
  -- the value of the moving part at `p₀` is `0`
  have hΨc : ContinuousWithinAt (fun p : ℝ × ℝ × ℝ => ∫ σ in τ₀..p.2.2, B (p.1, p.2.1, σ))
      (Z ×ˢ (Θ ×ˢ Icc (0 : ℝ) δ)) (z₀, θ₀, τ₀) := by
    show Tendsto (fun p : ℝ × ℝ × ℝ => ∫ σ in τ₀..p.2.2, B (p.1, p.2.1, σ))
      (𝓝[Z ×ˢ (Θ ×ˢ Icc (0 : ℝ) δ)] (z₀, θ₀, τ₀))
      (𝓝 ((fun p : ℝ × ℝ × ℝ => ∫ σ in τ₀..p.2.2, B (p.1, p.2.1, σ)) (z₀, θ₀, τ₀)))
    rw [show (fun p : ℝ × ℝ × ℝ => ∫ σ in τ₀..p.2.2, B (p.1, p.2.1, σ)) (z₀, θ₀, τ₀) = 0
      from intervalIntegral.integral_same]
    exact hΨ
  -- split the integral at `τ₀`
  have hsplit : ∀ p ∈ Z ×ˢ (Θ ×ˢ Icc (0 : ℝ) δ),
      (∫ σ in (0 : ℝ)..p.2.2, B (p.1, p.2.1, σ)) =
        (∫ σ in (0 : ℝ)..τ₀, B (p.1, p.2.1, σ)) + (∫ σ in τ₀..p.2.2, B (p.1, p.2.1, σ)) := by
    intro p hp
    have hslice : ContinuousOn (fun σ : ℝ => B (p.1, p.2.1, σ)) (Icc (0 : ℝ) δ) :=
      continuousOn_slice_of_continuousOn_slab hB hp.1 hp.2.1
    have h1 : IntervalIntegrable (fun σ : ℝ => B (p.1, p.2.1, σ)) volume 0 τ₀ :=
      (hslice.mono (uIcc_zero_subset_Icc hτ₀)).intervalIntegrable
    have h2 : IntervalIntegrable (fun σ : ℝ => B (p.1, p.2.1, σ)) volume τ₀ p.2.2 :=
      (hslice.mono (uIcc_subset_Icc hτ₀ hp.2.2)).intervalIntegrable
    exact (intervalIntegral.integral_add_adjacent_intervals h1 h2).symm
  have hgoal : ContinuousWithinAt
      (fun p : ℝ × ℝ × ℝ =>
        (∫ σ in (0 : ℝ)..τ₀, B (p.1, p.2.1, σ)) + (∫ σ in τ₀..p.2.2, B (p.1, p.2.1, σ)))
      (Z ×ˢ (Θ ×ˢ Icc (0 : ℝ) δ)) (z₀, θ₀, τ₀) := hfirst.add hΨc
  have heq : (fun p : ℝ × ℝ × ℝ => ∫ σ in (0 : ℝ)..p.2.2, B (p.1, p.2.1, σ)) =ᶠ[
      𝓝[Z ×ˢ (Θ ×ˢ Icc (0 : ℝ) δ)] (z₀, θ₀, τ₀)]
      (fun p : ℝ × ℝ × ℝ =>
        (∫ σ in (0 : ℝ)..τ₀, B (p.1, p.2.1, σ)) + (∫ σ in τ₀..p.2.2, B (p.1, p.2.1, σ))) := by
    filter_upwards [self_mem_nhdsWithin] with p hp
    exact hsplit p hp
  have hval : (∫ σ in (0 : ℝ)..(z₀, θ₀, τ₀).2.2, B ((z₀, θ₀, τ₀).1, (z₀, θ₀, τ₀).2.1, σ)) =
      (∫ σ in (0 : ℝ)..τ₀, B (z₀, θ₀, σ)) + (∫ σ in τ₀..τ₀, B (z₀, θ₀, σ)) :=
    hsplit (z₀, θ₀, τ₀) ⟨hz₀, hθ₀, hτ₀⟩
  exact hgoal.congr_of_eventuallyEq heq hval

end Work.FTS.StrongEps.EpsE4Thr.RegSlab
