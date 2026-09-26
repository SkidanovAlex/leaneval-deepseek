import Mathlib
import Submission.Work.Smooth.SphereJordan.LocalArc.ArcRange
import Submission.Work.Smooth.SphereJordan.LocalArc.EndStructure

/-!
# An arc with distinct ends can be strictly extended

Let `α : ℝ → X` be an injective continuous arc in a locally-arc Hausdorff space whose two ends
`p` (at `+∞`) and `q` (at `-∞`) are **distinct**.  Then, in any chart at `p`, one of the two
halves of a chart interval is missed by `α` entirely (`EndStructure.exists_chart_side_subset_compl`).
We use the missed half as a "spike": reparametrise `α` so that it is traversed on `(-∞,0)` (via the
homeomorphism `t ↦ -log(-t) : (-∞,0) → ℝ`), let it converge to `p` at `0`, and for `t > 0` follow
the missed germ into the chart.  The result is a continuous injective `E : ℝ → X` whose range
strictly contains the range of `α`.

The main results are `exists_arc_range_strictly_larger_of_spike` (the gluing step, with the spike
abstract) and the two chart cases.
-/

namespace Work.Smooth.SphereJordan.LocalArc

open Set Function Filter
open scoped Topology

noncomputable section

variable {X : Type*} [TopologicalSpace X] [T2Space X]

/-! ## Elementary one-sided facts -/

theorem tendsto_neg_nhdsLT_nhdsGT : Tendsto (fun t : ℝ => -t) (𝓝[<] (0:ℝ)) (𝓝[>] (0:ℝ)) := by
  rw [(nhdsLT_basis (0:ℝ)).tendsto_iff (nhdsGT_basis (0:ℝ))]
  intro u hu
  exact ⟨-u, neg_lt_zero.mpr hu, fun t ht => ⟨by linarith [ht.2], by linarith [ht.1]⟩⟩

theorem tendsto_neg_log_neg_nhdsLT_atTop :
    Tendsto (fun t : ℝ => -Real.log (-t)) (𝓝[<] (0:ℝ)) atTop := by
  have h1 : Tendsto (fun t : ℝ => Real.log (-t)) (𝓝[<] (0:ℝ)) atBot :=
    Real.tendsto_log_nhdsGT_zero.comp tendsto_neg_nhdsLT_nhdsGT
  have h2 : Tendsto (fun t : ℝ => -(Real.log (-t))) (𝓝[<] (0:ℝ)) atTop :=
    tendsto_neg_atBot_atTop.comp h1
  exact h2

theorem exists_neg_log_neg_eq (v : ℝ) : ∃ t : ℝ, t < 0 ∧ -Real.log (-t) = v :=
  ⟨-Real.exp (-v), neg_lt_zero.mpr (Real.exp_pos _), by rw [neg_neg, Real.log_exp, neg_neg]⟩

theorem injOn_neg_log_neg : Set.InjOn (fun t : ℝ => -Real.log (-t)) (Iio 0) := by
  intro a ha b hb hab
  have ha0 : a < 0 := ha
  have hb0 : b < 0 := hb
  have h1 : -a ∈ Ioi (0:ℝ) := neg_pos.mpr ha0
  have h2 : -b ∈ Ioi (0:ℝ) := neg_pos.mpr hb0
  have : -a = -b := Real.strictMonoOn_log.injOn h1 h2 (by linarith)
  linarith

/-! ## The spike maps `t ↦ ± ε t / (1+t)` on `(0,∞)` -/

theorem continuousAt_spike (ε : ℝ) : ContinuousAt (fun t : ℝ => ε * t / (1 + t)) 0 := by
  have h1 : ContinuousAt (fun t : ℝ => ε * t) 0 := continuousAt_const.mul continuousAt_id
  have h2 : ContinuousAt (fun t : ℝ => 1 + t) 0 := continuousAt_const.add continuousAt_id
  have h3 : (1 + (0:ℝ)) ≠ 0 := by norm_num
  convert h1.div h2 h3 using 1

theorem continuousOn_spike (ε : ℝ) :
    ContinuousOn (fun t : ℝ => ε * t / (1 + t)) (Ioi 0) := by
  have h1 : ContinuousOn (fun t : ℝ => ε * t) (Ioi 0) := continuousOn_const.mul continuousOn_id
  have h2 : ContinuousOn (fun t : ℝ => 1 + t) (Ioi 0) := continuousOn_const.add continuousOn_id
  have h3 : ∀ t ∈ Ioi (0:ℝ), (1 + t) ≠ 0 := by
    intro t ht
    have ht' : (0:ℝ) < t := ht
    have : (0:ℝ) < 1 + t := by linarith
    linarith
  exact h1.div h2 h3

theorem injOn_spike (ε : ℝ) (hε : 0 < ε) :
    Set.InjOn (fun t : ℝ => ε * t / (1 + t)) (Ioi 0) := by
  intro a ha b hb hab
  have ha' : (0:ℝ) < a := ha
  have hb' : (0:ℝ) < b := hb
  have h1a : (0:ℝ) < 1 + a := by linarith
  have h1b : (0:ℝ) < 1 + b := by linarith
  have h1 : (1 + a) ≠ 0 := by linarith
  have h2 : (1 + b) ≠ 0 := by linarith
  have h3 : ε * a * (1 + b) = ε * b * (1 + a) := (div_eq_div_iff h1 h2).mp hab
  nlinarith [h3, hε]

theorem spike_mem_Ioo (ε : ℝ) (hε : 0 < ε) {t : ℝ} (ht : 0 < t) :
    ε * t / (1 + t) ∈ Ioo 0 ε := by
  have h1 : (0:ℝ) < 1 + t := by linarith
  constructor
  · exact div_pos (mul_pos hε ht) h1
  · rw [div_lt_iff₀ h1]
    nlinarith [hε]

/-! ## The gluing step -/

/-- **Gluing a spike onto an arc whose end is missed on one side.**

If `α` is an injective arc with `α t → p` as `t → +∞`, and `β` is a *spike* at `p` (continuous on
`(0,∞)`, with limit `p` at `0⁺`, injective there, and avoiding `range α ∪ {p}`), then
`t ↦ (if t < 0 then α (-log (-t)) else β t)` is an embedding whose range strictly contains
`range α`. -/
theorem exists_arc_range_strictly_larger_of_spike
    {α : ℝ → X} (hcont : Continuous α) (hinj : Function.Injective α) {p : X}
    (hp : p ∉ Set.range α) (htop : Tendsto α atTop (𝓝 p))
    {β : ℝ → X} (hβ0 : β 0 = p) (hβc : ContinuousOn β (Ioi 0))
    (hβt : Tendsto β (𝓝[>] (0:ℝ)) (𝓝 p)) (hβinj : Set.InjOn β (Ioi 0))
    (hβmiss : ∀ t : ℝ, 0 < t → β t ∉ Set.range α ∪ {p}) :
    ∃ γ : ℝ → X, Continuous γ ∧ Function.Injective γ ∧ Set.range α ⊂ Set.range γ := by
  set E : ℝ → X := fun t => if t < 0 then α (-Real.log (-t)) else β t with hE
  have hE0 : E 0 = p := by simp [hE, hβ0]
  have hEs : ∀ t : ℝ, t < 0 → E t = α (-Real.log (-t)) := by
    intro t ht; simp [hE, ht]
  have hEnt : ∀ t : ℝ, ¬ t < 0 → E t = β t := by
    intro t ht; simp [hE, ht]
  have hsub : Set.range α ⊆ Set.range E := by
    rintro y ⟨s, rfl⟩
    obtain ⟨t, ht, ht'⟩ := exists_neg_log_neg_eq s
    exact ⟨t, by rw [hEs t ht, ht']⟩
  have hpE : p ∈ Set.range E := ⟨0, hE0⟩
  have hcontE : Continuous E := by
    rw [continuous_iff_continuousAt]
    intro t
    rcases lt_trichotomy t 0 with ht | ht | ht
    · have hEq : E =ᶠ[𝓝 t] (fun s : ℝ => α (-Real.log (-s))) := by
        filter_upwards [isOpen_Iio.mem_nhds ht] with s hs
        exact hEs s hs
      have hc : ContinuousAt (fun s : ℝ => α (-Real.log (-s))) t :=
        hcont.continuousAt.comp
          (((Real.continuousAt_log (by linarith : (-t) ≠ 0)).comp
            continuous_neg.continuousAt).neg)
      exact hc.congr hEq.symm
    · subst ht
      rw [continuousAt_iff_continuous_left'_right', ContinuousWithinAt, ContinuousWithinAt, hE0]
      constructor
      · have hEq : E =ᶠ[𝓝[<] (0:ℝ)] (fun s : ℝ => α (-Real.log (-s))) := by
          filter_upwards [self_mem_nhdsWithin] with s hs
          exact hEs s hs
        exact (Filter.Tendsto.congr' hEq.symm (htop.comp tendsto_neg_log_neg_nhdsLT_atTop))
      · have hEq : E =ᶠ[𝓝[>] (0:ℝ)] β := by
          filter_upwards [self_mem_nhdsWithin] with s hs
          exact hEnt s (not_lt.mpr (le_of_lt hs))
        exact (Filter.Tendsto.congr' hEq.symm hβt)
    · have hEq : E =ᶠ[𝓝 t] β := by
        filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
        exact hEnt s (not_lt.mpr (le_of_lt hs))
      have hc : ContinuousAt β t := (hβc.continuousWithinAt ht).continuousAt (isOpen_Ioi.mem_nhds ht)
      exact hc.congr hEq.symm
  have hinjE : Function.Injective E := by
    intro s t hst
    rcases lt_trichotomy s 0 with hs | hs | hs
    · rcases lt_trichotomy t 0 with ht | ht | ht
      · rw [hEs s hs, hEs t ht] at hst
        exact injOn_neg_log_neg hs ht (hinj hst)
      · subst ht
        rw [hEs s hs, hE0] at hst
        exact absurd (hst ▸ Set.mem_range_self (-Real.log (-s))) hp
      · rw [hEs s hs, hEnt t (not_lt.mpr (le_of_lt ht))] at hst
        exact (hβmiss t ht (Or.inl (hst ▸ Set.mem_range_self (-Real.log (-s))))).elim
    · subst hs
      rcases lt_trichotomy t 0 with ht | ht | ht
      · rw [hEs t ht, hE0] at hst
        exact absurd (hst.symm ▸ Set.mem_range_self (-Real.log (-t))) hp
      · exact ht.symm
      · rw [hE0, hEnt t (not_lt.mpr (le_of_lt ht))] at hst
        exact (hβmiss t ht (Or.inr hst.symm)).elim
    · rcases lt_trichotomy t 0 with ht | ht | ht
      · rw [hEnt s (not_lt.mpr (le_of_lt hs)), hEs t ht] at hst
        exact (hβmiss s hs (Or.inl (hst.symm ▸ Set.mem_range_self (-Real.log (-t))))).elim
      · subst ht
        rw [hEnt s (not_lt.mpr (le_of_lt hs)), hE0] at hst
        exact (hβmiss s hs (Or.inr hst)).elim
      · rw [hEnt s (not_lt.mpr (le_of_lt hs)), hEnt t (not_lt.mpr (le_of_lt ht))] at hst
        exact hβinj hs ht hst
  refine ⟨E, hcontE, hinjE, hsub, ?_⟩
  intro hcon
  exact hp (hcon hpE)

/-! ## Producing the spike from a missed chart half -/

/-- If the chart half `σ • (0,ε)` is missed by `α`, then `t ↦ c.map (σ * ε t/(1+t))` is a spike
in the sense of `exists_arc_range_strictly_larger_of_spike`. -/
theorem exists_spike_of_miss {α : ℝ → X} {p : X} (c : Work.Smooth.SphereJordan.ArcChart X p)
    {ε : ℝ} (hε : 0 < ε) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (hmiss : ∀ v ∈ Set.Ioo (0:ℝ) ε, c.map (σ * v) ∉ Set.range α) :
    ∃ β : ℝ → X, β 0 = p ∧ ContinuousOn β (Ioi 0) ∧ Tendsto β (𝓝[>] (0:ℝ)) (𝓝 p) ∧
      Set.InjOn β (Ioi 0) ∧ ∀ t : ℝ, 0 < t → β t ∉ Set.range α ∪ {p} := by
  refine ⟨fun t => c.map (σ * (ε * t / (1 + t))), ?_, ?_, ?_, ?_, ?_⟩
  · show c.map (σ * (ε * 0 / (1 + 0))) = p
    rw [show σ * (ε * 0 / (1 + 0)) = (0:ℝ) by ring]
    exact Work.Smooth.SphereJordan.ArcChart.map_zero c
  · exact c.continuous_map.comp_continuousOn (continuousOn_const.mul (continuousOn_spike ε))
  · have hinner : Tendsto (fun t : ℝ => σ * (ε * t / (1 + t))) (𝓝[>] (0:ℝ)) (𝓝 (0:ℝ)) := by
      have h1 : Tendsto (fun t : ℝ => σ * (ε * t / (1 + t))) (𝓝 (0:ℝ))
          (𝓝 (σ * (ε * 0 / (1 + 0)))) :=
        (continuousAt_const.mul (continuousAt_spike ε)).tendsto
      have h2 : σ * (ε * 0 / (1 + 0)) = (0:ℝ) := by ring
      rw [h2] at h1
      exact h1.mono_left nhdsWithin_le_nhds
    have h4 : Tendsto c.map (𝓝 (0:ℝ)) (𝓝 (c.map 0)) := c.continuous_map.continuousAt.tendsto
    have h3 : Tendsto c.map (𝓝 (0:ℝ)) (𝓝 p) := by
      rwa [show c.map 0 = p from Work.Smooth.SphereJordan.ArcChart.map_zero c] at h4
    exact h3.comp hinner
  · rintro a ha b hb hab
    have ha' : (0:ℝ) < a := ha
    have hb' : (0:ℝ) < b := hb
    have hkey : σ * (ε * a / (1 + a)) = σ * (ε * b / (1 + b)) := c.injective_map hab
    rcases hσ with h1 | h1
    · rw [h1, one_mul, one_mul] at hkey
      exact injOn_spike ε hε ha hb hkey
    · rw [h1, neg_one_mul, neg_one_mul] at hkey
      exact injOn_spike ε hε ha hb (neg_injective hkey)
  · intro t ht
    have hv : ε * t / (1 + t) ∈ Set.Ioo (0:ℝ) ε := spike_mem_Ioo ε hε ht
    intro hcon
    rcases hcon with h1 | h1
    · exact hmiss _ hv h1
    · have h1' : c.map (σ * (ε * t / (1 + t))) = p := h1
      have hv0 : σ * (ε * t / (1 + t)) = 0 :=
        c.injective_map (by
          rw [h1', Work.Smooth.SphereJordan.ArcChart.map_zero])
      rcases hσ with h2 | h2
      · rw [h2, one_mul] at hv0
        exact absurd hv0 (ne_of_gt hv.1)
      · rw [h2, neg_one_mul] at hv0
        exact absurd (by linarith : ε * t / (1 + t) = 0) (ne_of_gt hv.1)

/-! ## The extension lemma -/

/-- **An arc with distinct ends can be strictly extended.**

`α : ℝ → X` is injective continuous with `α t → p` at `+∞` and `α t → q` at `-∞`, where `p ≠ q`.
Then there is an embedding `γ` with `γ 0 = x₀` (for any prescribed `x₀ ∈ range α`) whose range
strictly contains `range α`. -/
theorem exists_arc_range_strictly_larger
    (H : Work.Smooth.SphereJordan.IsLocallyArc X) {α : ℝ → X} (hcont : Continuous α)
    (hinj : Function.Injective α) {p q x₀ : X} (hp : p ∉ Set.range α)
    (htop : Tendsto α atTop (𝓝 p)) (hbot : Tendsto α atBot (𝓝 q)) (hpq : p ≠ q)
    (hx₀ : x₀ ∈ Set.range α) :
    ∃ γ : ℝ → X, Continuous γ ∧ Function.Injective γ ∧ γ 0 = x₀ ∧ Set.range α ⊂ Set.range γ := by
  set c : Work.Smooth.SphereJordan.ArcChart X p := Work.Smooth.SphereJordan.chartOf H p with hc
  obtain ⟨ε, hε, -, hside⟩ :=
    exists_chart_side_subset_compl H hcont hinj hpq htop hbot c
  have key : ∀ (σ : ℝ), (σ = 1 ∨ σ = -1) →
      (∀ v ∈ Set.Ioo (0:ℝ) ε, c.map (σ * v) ∉ Set.range α) →
      ∃ γ : ℝ → X, Continuous γ ∧ Function.Injective γ ∧ Set.range α ⊂ Set.range γ := by
    intro σ hσ hm
    obtain ⟨β, hβ0, hβc, hβt, hβinj, hβmiss⟩ := exists_spike_of_miss c hε σ hσ hm
    exact exists_arc_range_strictly_larger_of_spike hcont hinj hp htop hβ0 hβc hβt hβinj hβmiss
  have hfin : ∃ γ : ℝ → X, Continuous γ ∧ Function.Injective γ ∧ Set.range α ⊂ Set.range γ := by
    rcases hside with hneg | hpos
    · refine key (-1) (Or.inr rfl) ?_
      intro v hv
      have hv' : (-1:ℝ) * v ∈ Set.Ioo (-ε) 0 := by
        constructor
        · rw [neg_one_mul]; linarith [hv.2]
        · rw [neg_one_mul]; linarith [hv.1]
      intro hx
      exact (hneg (Set.mem_image_of_mem c.map hv')) hx
    · refine key 1 (Or.inl rfl) ?_
      intro v hv
      have hv' : (1:ℝ) * v ∈ Set.Ioo 0 ε := by
        rw [one_mul]; exact hv
      intro hx
      exact (hpos (Set.mem_image_of_mem c.map hv')) hx
  obtain ⟨γ, hγc, hγi, hγss⟩ := hfin
  have hsub : Set.range α ⊆ Set.range γ := hγss.1
  obtain ⟨t₀, ht₀⟩ : ∃ t₀, γ t₀ = x₀ := hsub hx₀
  have hrange : Set.range (fun t : ℝ => γ (t + t₀)) = Set.range γ := by
    ext x
    constructor
    · rintro ⟨t, rfl⟩; exact ⟨t + t₀, rfl⟩
    · rintro ⟨s, rfl⟩; exact ⟨s - t₀, by ring_nf⟩
  refine ⟨fun t => γ (t + t₀), hγc.comp (continuous_id.add continuous_const), ?_, by simp [ht₀], ?_⟩
  · intro a b hab
    exact add_right_cancel (hγi hab)
  · rw [hrange]; exact hγss

end

end Work.Smooth.SphereJordan.LocalArc
