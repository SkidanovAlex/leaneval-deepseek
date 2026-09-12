import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Topology.MetricSpace.Thickening

open Set Filter
open scoped Topology

namespace Commons.Topology

/-- If `a ≤ b`, then the interval `[a - δ, b + δ]` is contained in the closed `δ`-thickening of
`[a, b]`. -/
private lemma Icc_sub_add_subset_cthickening {a b δ : ℝ} (hab : a ≤ b) (hδ : 0 ≤ δ) :
    Set.Icc (a - δ) (b + δ) ⊆ Metric.cthickening δ (Set.Icc a b) := by
  intro t ht
  refine Metric.mem_cthickening_of_dist_le t (max a (min b t)) δ (Set.Icc a b) ?_ ?_
  · exact ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩
  · have hmin : t - δ ≤ min b t := by
      rcases le_total b t with hbt | hbt
      · rw [min_eq_left hbt]; linarith [ht.2]
      · rw [min_eq_right hbt]; linarith
    have hc_ge : t - δ ≤ max a (min b t) := le_trans hmin (le_max_right _ _)
    have hc_le : max a (min b t) ≤ t + δ :=
      max_le (by linarith [ht.1]) (by linarith [min_le_right b t, hδ])
    rw [Real.dist_eq, abs_le]
    exact ⟨by linarith, by linarith⟩

theorem continuousAt_sSup_image_Icc {α : Type*} [TopologicalSpace α] {f : α → ℝ → ℝ}
    {a b : α → ℝ} {x₀ : α} (hf : Continuous fun p : α × ℝ => f p.1 p.2)
    (ha : ContinuousAt a x₀) (hb : ContinuousAt b x₀) (hab : a x₀ < b x₀) :
    ContinuousAt (fun x => sSup (f x '' Set.Icc (a x) (b x))) x₀ := by
  rw [ContinuousAt]
  have hcont : ∀ x : α, Continuous (fun t : ℝ => f x t) :=
    fun x => hf.comp (Continuous.prodMk_right x)
  obtain ⟨t₀, ht₀K, ht₀eq, ht₀max⟩ :=
    (isCompact_Icc (a := a x₀) (b := b x₀)).exists_sSup_image_eq_and_ge
      (nonempty_Icc.mpr hab.le) (f := f x₀) ((hcont x₀).continuousOn)
  rw [ht₀eq]
  have hab_ev : ∀ᶠ x in 𝓝 x₀, a x < b x := ha.eventually_lt hb hab
  rw [tendsto_order]
  constructor
  · -- lower semicontinuity
    intro u hu
    set p : α → ℝ := fun x => max (a x) (min t₀ (b x)) with hp
    have hp_tend : Tendsto p (𝓝 x₀) (𝓝 t₀) := by
      have h1 : Tendsto (fun x => min t₀ (b x)) (𝓝 x₀) (𝓝 (min t₀ (b x₀))) :=
        tendsto_const_nhds.min hb
      have h2 : Tendsto (fun x => max (a x) (min t₀ (b x))) (𝓝 x₀)
          (𝓝 (max (a x₀) (min t₀ (b x₀)))) := ha.max h1
      have h3 : max (a x₀) (min t₀ (b x₀)) = t₀ := by
        rw [min_eq_left ht₀K.2, max_eq_right ht₀K.1]
      rwa [h3] at h2
    have hp_mem : ∀ᶠ x in 𝓝 x₀, p x ∈ Set.Icc (a x) (b x) := by
      filter_upwards [hab_ev] with x habx
      exact ⟨le_max_left _ _, max_le habx.le (min_le_right _ _)⟩
    have hfp : Tendsto (fun x => f x (p x)) (𝓝 x₀) (𝓝 (f x₀ t₀)) :=
      hf.continuousAt.tendsto.comp (tendsto_id.prodMk_nhds hp_tend)
    have hev : ∀ᶠ x in 𝓝 x₀, u < f x (p x) := (tendsto_order.mp hfp).1 u hu
    filter_upwards [hev, hp_mem] with x hu' hmem
    exact lt_of_lt_of_le hu'
      (le_csSup ((isCompact_Icc (a := a x) (b := b x)).image (hcont x)).bddAbove
        (mem_image_of_mem _ hmem))
  · -- upper semicontinuity
    intro v hv
    have hU : IsOpen {p : α × ℝ | f p.1 p.2 < v} := isOpen_Iio.preimage hf
    have hsub : ({x₀} : Set α) ×ˢ Set.Icc (a x₀) (b x₀) ⊆ {p : α × ℝ | f p.1 p.2 < v} := by
      rintro ⟨x, t⟩ ⟨hx, ht⟩
      simp only [Set.mem_singleton_iff] at hx
      subst hx
      exact lt_of_le_of_lt (ht₀max t ht) hv
    obtain ⟨V, W, hVopen, hWopen, hx₀V, hK₀W, hVW⟩ :=
      generalized_tube_lemma isCompact_singleton (isCompact_Icc (a := a x₀) (b := b x₀)) hU hsub
    obtain ⟨δ, hδpos, hδW⟩ :=
      (isCompact_Icc (a := a x₀) (b := b x₀)).exists_cthickening_subset_open hWopen hK₀W
    have ha_ev : ∀ᶠ x in 𝓝 x₀, a x₀ - δ ≤ a x :=
      ((tendsto_order.mp ha).1 (a x₀ - δ) (by linarith)).mono fun x hx => hx.le
    have hb_ev : ∀ᶠ x in 𝓝 x₀, b x ≤ b x₀ + δ :=
      ((tendsto_order.mp hb).2 (b x₀ + δ) (by linarith)).mono fun x hx => hx.le
    filter_upwards [hVopen.mem_nhds (hx₀V (by simp)), ha_ev, hb_ev, hab_ev] with x hxV hax hbx habx
    rw [(isCompact_Icc (a := a x) (b := b x)).sSup_lt_iff_of_continuous
      (nonempty_Icc.mpr habx.le) (hcont x).continuousOn v]
    intro t ht
    have htI : t ∈ Set.Icc (a x₀ - δ) (b x₀ + δ) := ⟨le_trans hax ht.1, le_trans ht.2 hbx⟩
    have htW : t ∈ W :=
      hδW (Icc_sub_add_subset_cthickening (a := a x₀) (b := b x₀) (δ := δ) hab.le hδpos.le htI)
    exact hVW (show (x, t) ∈ V ×ˢ W from ⟨hxV, htW⟩)

end Commons.Topology