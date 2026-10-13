import Mathlib.Algebra.Order.Ring.Star
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace Work.FTS.StrongEps.EpsE4Thr

/-- Slices of an almost-everywhere-measurable function of two variables are almost everywhere
measurable at a point `τ`, provided the `t`-slices are a.e. continuous on a fixed interval
`[a, b]` containing `τ` in its interior.

Proof route: replace `uncurry F` by an a.e. equal measurable `G`.  Then for a.e. `t` the slices
`F t ·` and `G t ·` agree `μ`-a.e.; since the good set of `t` is conull it is dense, so we may
pick a sequence `t n → τ` of good times inside a shrinking neighbourhood of `τ`.  For a.e. `p`,
continuity of `F · p` at `τ` gives `F (t n) p → F τ p`, each `F (t n) ·` is AEMeasurable, and
`AEMeasurable` is closed under pointwise limits (via `liminf`). -/
theorem aemeasurable_slice_continuousOn
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α} [MeasureTheory.SFinite μ]
    {F : ℝ → α → ℝ} {a b τ : ℝ} (ha : a < τ) (hb : τ < b)
    (hmeas : AEMeasurable (Function.uncurry F) (MeasureTheory.volume.prod μ))
    (hcont : ∀ᵐ p ∂μ, ContinuousOn (fun t : ℝ => F t p) (Set.Icc a b)) :
    AEMeasurable (fun p => F τ p) μ := by
  classical
  obtain ⟨G, hGmeas, hGF⟩ := hmeas
  have hG_eq : Function.uncurry (fun t p => G (t, p)) = G := by
    funext q
    simp [Function.uncurry]
  have hGF' : Function.uncurry F =ᵐ[volume.prod μ] Function.uncurry (fun t p => G (t, p)) := by
    rw [hG_eq]; exact hGF
  -- for a.e. time `t` the two slices agree `μ`-a.e.
  have hslice : ∀ᵐ t ∂volume, (fun p => F t p) =ᵐ[μ] (fun p => G (t, p)) :=
    MeasureTheory.Measure.ae_ae_eq_of_ae_eq_uncurry hGF'
  have hbad : volume {t : ℝ | ¬ ((fun p => F t p) =ᵐ[μ] (fun p => G (t, p)))} = 0 :=
    MeasureTheory.ae_iff.mp hslice
  -- the set of good times is conull, hence dense: pick a good sequence tending to `τ`
  have hex : ∀ n : ℕ, ∃ t : ℝ,
      t ∈ Set.Ioo (max a (τ - 1 / ((n : ℝ) + 1))) (min b (τ + 1 / ((n : ℝ) + 1))) ∧
        (fun p => F t p) =ᵐ[μ] (fun p => G (t, p)) := by
    intro n
    have he : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hne : max a (τ - 1 / ((n : ℝ) + 1)) < min b (τ + 1 / ((n : ℝ) + 1)) := by
      rw [max_lt_iff, lt_min_iff, lt_min_iff]
      exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
    by_contra h
    push Not at h
    have hsub : Set.Ioo (max a (τ - 1 / ((n : ℝ) + 1))) (min b (τ + 1 / ((n : ℝ) + 1))) ⊆
        {t : ℝ | ¬ ((fun p => F t p) =ᵐ[μ] (fun p => G (t, p)))} := fun t ht => h t ht
    have hnull := measure_mono_null hsub hbad
    have hpos : 0 < volume (Set.Ioo (max a (τ - 1 / ((n : ℝ) + 1)))
        (min b (τ + 1 / ((n : ℝ) + 1)))) := by
      rw [Real.volume_Ioo, ENNReal.ofReal_pos]
      linarith
    exact absurd hnull (ne_of_gt hpos)
  choose t ht_mem ht_P using hex
  have h1 : Tendsto (fun n : ℕ => τ - 1 / ((n : ℝ) + 1)) atTop (𝓝 τ) := by
    have := Tendsto.const_sub τ (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa using this
  have h2 : Tendsto (fun n : ℕ => τ + 1 / ((n : ℝ) + 1)) atTop (𝓝 τ) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_add τ
    simpa [add_comm] using this
  have htendsto : Tendsto t atTop (𝓝 τ) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le h1 h2
      (fun n => le_of_lt (lt_of_le_of_lt (le_max_right _ _) (ht_mem n).1))
      (fun n => le_of_lt (lt_of_lt_of_le (ht_mem n).2 (min_le_right _ _)))
  -- each slice at a good time is AEMeasurable
  have hAEn : ∀ n : ℕ, AEMeasurable (fun p => F (t n) p) μ := fun n =>
    ⟨fun p => G (t n, p), hGmeas.comp (measurable_const.prodMk measurable_id), ht_P n⟩
  -- the `liminf` of those slices is AEMeasurable and equals the slice at `τ` a.e.
  have hH : AEMeasurable (fun p => Filter.liminf (fun n => F (t n) p) atTop) μ :=
    AEMeasurable.liminf hAEn
  refine hH.congr ?_
  filter_upwards [hcont] with p hp
  have hτ : τ ∈ Set.Icc a b := ⟨le_of_lt ha, le_of_lt hb⟩
  have hIcc : Set.Icc a b ∈ 𝓝 τ :=
    Filter.mem_of_superset (isOpen_Ioo.mem_nhds ⟨ha, hb⟩) Set.Ioo_subset_Icc_self
  have hcAt : ContinuousAt (fun s : ℝ => F s p) τ :=
    (continuousWithinAt_iff_continuousAt hIcc).mp (hp.continuousWithinAt hτ)
  exact (hcAt.tendsto.comp htendsto).liminf_eq

end Work.FTS.StrongEps.EpsE4Thr
