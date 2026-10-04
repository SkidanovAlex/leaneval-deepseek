import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT.JetGap

open Set Filter

/-- **Mean value inequality in the form used below.**  If `F : ℝ → β` is differentiable on the
open interval `(σ,T)` with `‖F' t‖ ≤ C` there, then for `a b ∈ (σ,T)` the increment is bounded by
`C |b - a|`.  (The interval `(σ,T)` is convex, so this is the classical mean value inequality
applied on `Icc (min a b) (max a b)`, which is contained in `(σ,T)`.) -/
private lemma norm_sub_le_of_hasDerivAt_of_norm_deriv_le
    {β : Type*} [NormedAddCommGroup β] [NormedSpace ℝ β]
    {σ T C : ℝ} {F : ℝ → β} {F' : ℝ → β}
    (h : ∀ t ∈ Set.Ioo σ T, HasDerivAt F (F' t) t)
    (hb : ∀ t ∈ Set.Ioo σ T, ‖F' t‖ ≤ C)
    {a b : ℝ} (ha : a ∈ Set.Ioo σ T) (hb' : b ∈ Set.Ioo σ T) :
    ‖F b - F a‖ ≤ C * |b - a| := by
  have hsub : Set.Icc (min a b) (max a b) ⊆ Set.Ioo σ T := fun x hx =>
    ⟨lt_of_lt_of_le (lt_min ha.1 hb'.1) hx.1, lt_of_le_of_lt hx.2 (max_lt ha.2 hb'.2)⟩
  exact Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := F) (f' := F') (s := Set.Icc (min a b) (max a b))
    (fun x hx => (h x (hsub hx)).hasDerivWithinAt)
    (fun x hx => hb x (hsub hx))
    (convex_Icc _ _) ⟨min_le_left _ _, le_max_left _ _⟩ ⟨min_le_right _ _, le_max_right _ _⟩

/-- A family of curves, differentiable on `(σ,T)` with derivatives uniformly bounded by `C`, has a
limit at `T` from below, with the explicit rate `‖F y t - L y‖ ≤ C (T - t)`, uniformly in the
family index.  The argument is: the mean value inequality exhibits each curve as `C`-Lipschitz on
`(σ,T)`, whence it is Cauchy as `t → T⁻`; `β` is complete so the limit exists; the rate follows by
passing to the limit in the mean value inequality. -/
theorem exists_tendsto_of_hasDerivAt_uniform_bound
    {β : Type*} [NormedAddCommGroup β] [NormedSpace ℝ β] [CompleteSpace β]
    {σ T : ℝ} (hσT : σ < T) {ι : Type*} (U : Set ι)
    {F : ι → ℝ → β} {F' : ℝ → ι → β} {C : ℝ}
    (h : ∀ t ∈ Set.Ioo σ T, ∀ y ∈ U, HasDerivAt (F y) (F' t y) t)
    (hb : ∀ t ∈ Set.Ioo σ T, ∀ y ∈ U, ‖F' t y‖ ≤ C) :
    ∃ L : ι → β, (∀ y ∈ U, Filter.Tendsto (F y) (nhdsWithin T (Set.Iio T)) (nhds (L y))) ∧
      ∀ t ∈ Set.Ioo σ T, ∀ y ∈ U, ‖F y t - L y‖ ≤ C * (T - t) := by
  classical
  -- the one-sided neighbourhood filter at `T` is nontrivial
  have hl : (nhdsWithin T (Set.Iio T)).NeBot := nhdsWithin_Iio_neBot le_rfl
  rcases U.eq_empty_or_nonempty with hU | hUne
  · -- vacuous case: nothing to bound
    rw [hU]
    exact ⟨fun _ => 0, by simp, by simp⟩
  obtain ⟨y₀, hy₀⟩ := hUne
  -- on a nonempty family the bound on the derivatives forces `0 ≤ C`
  have hC : 0 ≤ C := by
    have ht : (σ + T) / 2 ∈ Set.Ioo σ T := ⟨by linarith, by linarith⟩
    exact (norm_nonneg (F' ((σ + T) / 2) y₀)).trans (hb _ ht _ hy₀)
  -- mean value estimate, in symmetric form
  have hdist : ∀ y ∈ U, ∀ a ∈ Set.Ioo σ T, ∀ b ∈ Set.Ioo σ T,
      dist (F y a) (F y b) ≤ C * |a - b| := by
    intro y hy a ha b hb'
    have hlip := norm_sub_le_of_hasDerivAt_of_norm_deriv_le
      (F := F y) (F' := fun t => F' t y) (fun t ht => h t ht y hy)
      (fun t ht => hb t ht y hy) ha hb'
    rw [dist_eq_norm, norm_sub_rev, abs_sub_comm]
    exact hlip
  -- each curve has a limit at `T` from below, by Cauchy-ness and completeness
  have hex : ∀ y ∈ U, ∃ L : β, Filter.Tendsto (F y) (nhdsWithin T (Set.Iio T)) (nhds L) := by
    intro y hy
    have hcauchy : Cauchy (Filter.map (F y) (nhdsWithin T (Set.Iio T))) := by
      have hnb : (Filter.map (F y) (nhdsWithin T (Set.Iio T))).NeBot :=
        (Filter.map_neBot_iff (F y)).mpr hl
      rw [Metric.cauchy_iff]
      refine ⟨hnb, fun ε hε => ?_⟩
      -- work inside a window `(T - δ, T)` short enough that `C δ < ε`
      obtain ⟨δ₀, hδ₀pos, hδ₀lt⟩ := exists_pos_mul_lt hε C
      set δ : ℝ := min δ₀ ((T - σ) / 2)
      have hδpos : 0 < δ := lt_min hδ₀pos (by linarith)
      have hδδ₀ : δ ≤ δ₀ := min_le_left _ _
      have hδhalf : δ ≤ (T - σ) / 2 := min_le_right _ _
      have hδlt : C * δ < ε := lt_of_le_of_lt (mul_le_mul_of_nonneg_left hδδ₀ hC) hδ₀lt
      have hsub : Set.Ioo (T - δ) T ⊆ Set.Ioo σ T := fun x hx =>
        ⟨by linarith [hδhalf, hx.1], hx.2⟩
      have hmem : Set.Ioo (T - δ) T ∈ nhdsWithin T (Set.Iio T) := by
        refine eventually_nhdsWithin_iff.mpr ?_
        filter_upwards [Ioo_mem_nhds (by linarith : T - δ < T) (by linarith : T < T + 1)]
          with x hx hxT
        exact ⟨hx.1, hxT⟩
      refine ⟨F y '' Set.Ioo (T - δ) T, Filter.image_mem_map hmem, ?_⟩
      rintro u ⟨a, ha, rfl⟩ v ⟨b, hbI, rfl⟩
      have habs : |a - b| ≤ δ := by
        rw [abs_le]
        exact ⟨by linarith [ha.1, hbI.2], by linarith [ha.2, hbI.1]⟩
      calc dist (F y a) (F y b) ≤ C * |a - b| := hdist y hy a (hsub ha) b (hsub hbI)
        _ ≤ C * δ := mul_le_mul_of_nonneg_left habs hC
        _ < ε := hδlt
    obtain ⟨L, hL⟩ := CompleteSpace.complete hcauchy
    exact ⟨L, hL⟩
  -- package the pointwise limits into a single family `L : ι → β`
  have hexAll : ∀ y : ι, ∃ L : β, y ∈ U → Filter.Tendsto (F y) (nhdsWithin T (Set.Iio T)) (nhds L) := by
    intro y
    by_cases hy : y ∈ U
    · obtain ⟨L, hL⟩ := hex y hy
      exact ⟨L, fun _ => hL⟩
    · exact ⟨0, fun hh => absurd hh hy⟩
  refine ⟨fun y => Classical.choose (hexAll y), ?_, ?_⟩
  · intro y hy
    exact Classical.choose_spec (hexAll y) hy
  · -- the explicit rate, by passing to the limit in the mean value inequality
    intro t ht y hy
    have hL : Filter.Tendsto (F y) (nhdsWithin T (Set.Iio T)) (nhds (Classical.choose (hexAll y))) :=
      Classical.choose_spec (hexAll y) hy
    have h1 : Filter.Tendsto (fun s => ‖F y t - F y s‖) (nhdsWithin T (Set.Iio T))
        (nhds ‖F y t - Classical.choose (hexAll y)‖) :=
      (tendsto_const_nhds.sub hL).norm
    have h2 : Filter.Tendsto (fun s => C * (s - t)) (nhdsWithin T (Set.Iio T))
        (nhds (C * (T - t))) :=
      ((tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).sub tendsto_const_nhds).const_mul C
    have h3 : ∀ᶠ s in nhdsWithin T (Set.Iio T), ‖F y t - F y s‖ ≤ C * (s - t) := by
      have hmem : Set.Ioo t T ∈ nhdsWithin T (Set.Iio T) := by
        refine eventually_nhdsWithin_iff.mpr ?_
        filter_upwards [Ioo_mem_nhds ht.2 (by linarith : T < T + 1)] with x hx hxT
        exact ⟨hx.1, hxT⟩
      filter_upwards [hmem] with s hs
      have hs' : s ∈ Set.Ioo σ T := ⟨ht.1.trans hs.1, hs.2⟩
      have hbnd := hdist y hy t ht s hs'
      rw [dist_eq_norm, abs_of_nonpos (sub_nonpos.mpr hs.1.le), neg_sub] at hbnd
      exact hbnd
    exact le_of_tendsto_of_tendsto (hb := hl) h1 h2 h3

end Work.Diff.EXT.JetGap
