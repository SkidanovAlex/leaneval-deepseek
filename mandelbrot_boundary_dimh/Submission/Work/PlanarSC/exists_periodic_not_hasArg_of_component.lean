import Mathlib
import Submission.Work.PlanarSC.Tools
import Submission.Work.PlanarSC.exists_compact_gap_of_component
import Submission.Work.PlanarSC.exists_loop_not_hasArg_of_gap

/-!
# A loop detecting a compact complementary component

Target (`Work.PlanarSC.exists_periodic_not_hasArg_of_component`): if `Ω ⊆ ℂ` is a domain, `K` a
compact connected component of `Ωᶜ` (i.e. a maximal preconnected subset of `Ωᶜ`) and `a ∈ K`, then
there is a continuous `1`-periodic loop `f` with values in `Ω` whose argument around `a` is not
periodic (`¬ HasArg (f · - a) 0`), i.e. a loop of nonzero winding number about `a`.
-/

namespace Work.PlanarSC

open Set Metric

/-- **Vanishing of the winding number is constant along a preconnected set disjoint from the
curve.**  For a continuous `1`-periodic `f : ℝ → ℂ`, the predicate `HasArg f ·` is locally constant
on the complement of the curve `t ↦ f t`, hence constant on any preconnected subset of it. -/
theorem hasArg_iff_of_isPreconnected {f : ℝ → ℂ} (hf : Continuous f)
    (hper : Function.Periodic f 1) {K : Set ℂ} (hK : IsPreconnected K)
    (hKsub : K ⊆ (Set.range f)ᶜ) {p a : ℂ} (hp : p ∈ K) (ha : a ∈ K) :
    (Commons.Topology.Winding.HasArg f p ↔ Commons.Topology.Winding.HasArg f a) := by
  have hKcpt : IsCompact (Set.range f) :=
    Commons.Topology.Winding.isCompact_range_of_periodic hf hper
  have hKclosed : IsClosed (Set.range f) := hKcpt.isClosed
  have hKne : (Set.range f).Nonempty := ⟨f 0, Set.mem_range_self 0⟩
  have hρpos : ∀ x ∉ Set.range f, 0 < Metric.infDist x (Set.range f) := fun x hx =>
    (hKclosed.notMem_iff_infDist_pos hKne).mp hx
  have hAopen : IsOpen ({x : ℂ | Commons.Topology.Winding.HasArg f x} ∩ (Set.range f)ᶜ) := by
    rw [isOpen_iff_mem_nhds]
    rintro x ⟨hxA, hxV⟩
    obtain ⟨θ, hθc, hθper, hθrep⟩ := hxA
    refine Filter.mem_of_superset (Metric.ball_mem_nhds x (by linarith [hρpos x hxV] :
      (0 : ℝ) < Metric.infDist x (Set.range f) / 2)) ?_
    intro y hy
    have hyd : ‖y - x‖ < Metric.infDist x (Set.range f) / 2 := by
      simpa [Metric.mem_ball, dist_eq_norm] using hy
    refine ⟨Commons.Topology.Curve.argument_lift_of_close hf hper hxV hθc hθper hθrep hyd, ?_⟩
    intro hyK
    have hdist : dist x y < Metric.infDist x (Set.range f) := by
      rw [dist_eq_norm, norm_sub_rev]
      linarith [hρpos x hxV]
    exact Metric.notMem_of_dist_lt_infDist (s := Set.range f) hdist hyK
  have hAcompl : IsOpen ((Set.range f)ᶜ \ {x : ℂ | Commons.Topology.Winding.HasArg f x}) := by
    rw [isOpen_iff_mem_nhds]
    rintro x ⟨hxV, hxA⟩
    refine Filter.mem_of_superset (Metric.ball_mem_nhds x (by linarith [hρpos x hxV] :
      (0 : ℝ) < Metric.infDist x (Set.range f) / 4)) ?_
    rintro y hy
    have hd : ‖y - x‖ < Metric.infDist x (Set.range f) / 4 := by
      simpa [Metric.mem_ball, dist_eq_norm] using hy
    refine ⟨?_, ?_⟩
    · intro hyK
      have h1 := Metric.infDist_le_dist_of_mem (s := Set.range f) (x := x) (y := y) hyK
      rw [dist_eq_norm, norm_sub_rev] at h1
      linarith [hρpos x hxV]
    · intro hyA
      obtain ⟨φ, hφc, hφper, hφrep⟩ := hyA
      have hyV' : y ∉ Set.range f := by
        intro hyK
        have h1 := Metric.infDist_le_dist_of_mem (s := Set.range f) (x := x) (y := y) hyK
        rw [dist_eq_norm, norm_sub_rev] at h1
        linarith [hρpos x hxV]
      have h2 := Metric.infDist_le_infDist_add_dist (s := Set.range f) (x := x) (y := y)
      rw [dist_eq_norm, norm_sub_rev] at h2
      have h3 : ‖x - y‖ < Metric.infDist y (Set.range f) / 2 := by
        rw [norm_sub_rev]
        linarith [hρpos x hxV, hρpos y hyV']
      exact hxA (Commons.Topology.Curve.argument_lift_of_close hf hper hyV' hφc hφper hφrep h3)
  have hcover : K ⊆ ({x : ℂ | Commons.Topology.Winding.HasArg f x} ∩ (Set.range f)ᶜ) ∪
      ((Set.range f)ᶜ \ {x : ℂ | Commons.Topology.Winding.HasArg f x}) := by
    intro z hz
    by_cases hzA : Commons.Topology.Winding.HasArg f z
    · exact Or.inl ⟨hzA, hKsub hz⟩
    · exact Or.inr ⟨hKsub hz, hzA⟩
  have hdisj : Disjoint ({x : ℂ | Commons.Topology.Winding.HasArg f x} ∩ (Set.range f)ᶜ)
      ((Set.range f)ᶜ \ {x : ℂ | Commons.Topology.Winding.HasArg f x}) := by
    rw [Set.disjoint_left]
    rintro z ⟨hzA, -⟩ ⟨-, hzA'⟩
    exact hzA' hzA
  rcases hK.subset_or_subset hAopen hAcompl hdisj hcover with hs | hs
  · exact ⟨fun _ => (hs ha).1, fun _ => (hs hp).1⟩
  · exact ⟨fun h => absurd h (hs hp).2, fun h => absurd h (hs ha).2⟩

/-- The unit-speed ray from `a` in direction `θ`. -/
private noncomputable def ray (a : ℂ) (θ : ℝ) : ℝ → ℂ :=
  fun t => a + (t : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)

private lemma continuous_ray (a : ℂ) (θ : ℝ) : Continuous (ray a θ) := by
  unfold ray; fun_prop

private lemma ray_zero (a : ℂ) (θ : ℝ) : ray a θ 0 = a := by simp [ray]

private lemma norm_ray_ge (a : ℂ) (θ : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    t ≤ ‖ray a θ t‖ + ‖a‖ := by
  have h := norm_sub_le (ray a θ t) a
  have h1 : ray a θ t - a = (t : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by simp [ray]
  have h2 : ‖ray a θ t - a‖ = t := by
    rw [h1, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
    simp [abs_of_nonneg ht]
  linarith

/-- **The radial star of a compact complementary component.**  For a domain `Ω` and a compact
connected component `K` of `Ωᶜ` with base point `a ∈ K`, the intersection of `K` with every ray
emanating from `a` is an initial segment described by a radius function `ρ`, and arbitrarily close
beyond `ρ θ` along the ray the domain `Ω` is met. -/
theorem exists_radial_star_of_component {Ω : Set ℂ} (hΩo : IsOpen Ω) (hΩc : IsConnected Ω)
    {K : Set ℂ} (hKcpt : IsCompact K) (hKconn : IsConnected K) (hKsub : K ⊆ Ωᶜ)
    (hKmax : ∀ S : Set ℂ, IsPreconnected S → K ⊆ S → S ⊆ Ωᶜ → S = K) {a : ℂ} (haK : a ∈ K) :
    ∃ ρ : ℝ → ℝ, (∀ θ, 0 ≤ ρ θ) ∧
      (∀ θ t : ℝ, 0 ≤ t → t < ρ θ → ray a θ t ∈ K) ∧
      (∀ θ ε : ℝ, 0 < ε → ∃ t : ℝ, ρ θ < t ∧ t < ρ θ + ε ∧ ray a θ t ∈ Ω) := by
  -- every ray from `a` leaves `Ωᶜ`
  have hexit : ∀ θ : ℝ, ∃ t : ℝ, 0 < t ∧ ray a θ t ∈ Ω := by
    intro θ
    by_contra hcon
    push Not at hcon
    have hrayΩ : ∀ t : ℝ, 0 ≤ t → ray a θ t ∈ Ωᶜ := by
      intro t ht
      rcases eq_or_lt_of_le ht with h | h
      · rw [← h, ray_zero]; exact hKsub haK
      · exact hcon t h
    have hpreR : IsPreconnected (ray a θ '' Set.Ici 0) :=
      (isPreconnected_Ici (a := (0 : ℝ))).image _ (continuous_ray a θ).continuousOn
    have haR : a ∈ ray a θ '' Set.Ici 0 := ⟨0, mem_Ici.mpr le_rfl, ray_zero a θ⟩
    have hpre : IsPreconnected (K ∪ ray a θ '' Set.Ici 0) :=
      hKconn.isPreconnected.union a haK haR hpreR
    have hsub : K ∪ ray a θ '' Set.Ici 0 ⊆ Ωᶜ := by
      rintro z (hz | hz)
      · exact hKsub hz
      · obtain ⟨t, ht, rfl⟩ := hz
        exact hrayΩ t ht
    have hunb : ¬ Bornology.IsBounded (ray a θ '' Set.Ici 0) := by
      intro hb
      obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hb
      set T : ℝ := max 0 (C + ‖a‖ + 1) with hT
      have hT0 : (0 : ℝ) ≤ T := le_max_left _ _
      have hmem : ray a θ T ∈ ray a θ '' Set.Ici 0 := ⟨T, mem_Ici.mpr hT0, rfl⟩
      have h1 : ‖ray a θ T‖ ≤ C := hC _ hmem
      have h2 : T ≤ ‖ray a θ T‖ + ‖a‖ := norm_ray_ge a θ hT0
      have h3 : C + ‖a‖ + 1 ≤ T := le_max_right _ _
      linarith
    have hKm : K ∪ ray a θ '' Set.Ici 0 = K :=
      hKmax _ hpre (fun z hz => Or.inl hz) hsub
    have hsubK : ray a θ '' Set.Ici 0 ⊆ K := by
      rw [← hKm]; exact fun z hz => Or.inr hz
    exact hunb (hKcpt.isBounded.subset hsubK)
  -- the radial radius function
  set ρ : ℝ → ℝ := fun θ => sInf {t : ℝ | 0 < t ∧ ray a θ t ∈ Ω} with hρdef
  have hSne : ∀ θ, ({t : ℝ | 0 < t ∧ ray a θ t ∈ Ω} : Set ℝ).Nonempty := by
    intro θ; obtain ⟨t, ht⟩ := hexit θ; exact ⟨t, ht⟩
  have hSbdd : ∀ θ, BddBelow ({t : ℝ | 0 < t ∧ ray a θ t ∈ Ω} : Set ℝ) :=
    fun θ => ⟨0, fun y hy => le_of_lt hy.1⟩
  have hSopen : ∀ θ, IsOpen ({t : ℝ | 0 < t ∧ ray a θ t ∈ Ω} : Set ℝ) := fun θ => by
    have h1 : IsOpen ((Set.Ioi (0 : ℝ)) ∩ (ray a θ ⁻¹' Ω)) :=
      IsOpen.inter isOpen_Ioi (hΩo.preimage (continuous_ray a θ))
    convert h1 using 1
    ext t
    simp [Set.mem_Ioi, Set.mem_preimage]
  have hρnn : ∀ θ, 0 ≤ ρ θ := fun θ => le_csInf (hSne θ) (fun y hy => le_of_lt hy.1)
  -- the point `ρ θ` itself is not in the set
  have hρnotmem : ∀ θ, ρ θ ∉ {t : ℝ | 0 < t ∧ ray a θ t ∈ Ω} := by
    intro θ hmem
    obtain ⟨δ, hδ, hδsub⟩ := Metric.isOpen_iff.mp (hSopen θ) (ρ θ) hmem
    have hmem' : ρ θ - δ / 2 ∈ {t : ℝ | 0 < t ∧ ray a θ t ∈ Ω} := by
      apply hδsub
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      exact ⟨by linarith, by linarith⟩
    have hle : ρ θ ≤ ρ θ - δ / 2 := csInf_le (hSbdd θ) hmem'
    linarith
  have hstarΩ : ∀ θ, ray a θ '' Set.Ico 0 (ρ θ) ⊆ Ωᶜ := by
    rintro θ z ⟨t, ht, rfl⟩
    rcases eq_or_lt_of_le ht.1 with h0 | h0
    · rw [← h0, ray_zero]; exact hKsub haK
    · intro hΩmem
      have htS : t ∈ {t : ℝ | 0 < t ∧ ray a θ t ∈ Ω} := ⟨h0, hΩmem⟩
      have hle : ρ θ ≤ t := csInf_le (hSbdd θ) htS
      exact absurd (lt_of_lt_of_le ht.2 hle) (lt_irrefl t)
  have hstarPre : ∀ θ, IsPreconnected (ray a θ '' Set.Ico 0 (ρ θ)) := fun θ =>
    (isPreconnected_Ico (a := (0 : ℝ))).image _ (continuous_ray a θ).continuousOn
  have hKmem : ∀ θ t : ℝ, 0 ≤ t → t < ρ θ → ray a θ t ∈ K := by
    intro θ t ht0 htlt
    have haStar : a ∈ ray a θ '' Set.Ico 0 (ρ θ) :=
      ⟨0, ⟨le_rfl, lt_of_le_of_lt ht0 htlt⟩, ray_zero a θ⟩
    have hpre : IsPreconnected (K ∪ ray a θ '' Set.Ico 0 (ρ θ)) :=
      hKconn.isPreconnected.union a haK haStar (hstarPre θ)
    have hsub : K ∪ ray a θ '' Set.Ico 0 (ρ θ) ⊆ Ωᶜ :=
      Set.union_subset hKsub (hstarΩ θ)
    have hKm : K ∪ ray a θ '' Set.Ico 0 (ρ θ) = K :=
      hKmax _ hpre (fun z hz => Or.inl hz) hsub
    have hsubK : ray a θ '' Set.Ico 0 (ρ θ) ⊆ K := by
      rw [← hKm]; exact fun z hz => Or.inr hz
    exact hsubK ⟨t, ⟨ht0, htlt⟩, rfl⟩
  refine ⟨ρ, hρnn, hKmem, ?_⟩
  intro θ ε hε
  have hlt : sInf {t : ℝ | 0 < t ∧ ray a θ t ∈ Ω} <
      sInf {t : ℝ | 0 < t ∧ ray a θ t ∈ Ω} + ε := by linarith
  obtain ⟨t, htS, htlt⟩ := (csInf_lt_iff (hSbdd θ) (hSne θ)).mp hlt
  have hle : ρ θ ≤ t := csInf_le (hSbdd θ) htS
  have hne : ρ θ ≠ t := fun h => hρnotmem θ (h ▸ htS)
  exact ⟨t, lt_of_le_of_ne hle hne, htlt, htS.2⟩

theorem exists_periodic_not_hasArg_of_component {Ω : Set ℂ} (hΩo : IsOpen Ω) (hΩc : IsConnected Ω)
    {K : Set ℂ} (hKcpt : IsCompact K) (hKconn : IsConnected K) (hKsub : K ⊆ Ωᶜ)
    (hKmax : ∀ S : Set ℂ, IsPreconnected S → K ⊆ S → S ⊆ Ωᶜ → S = K) {a : ℂ} (haK : a ∈ K) :
    ∃ f : ℝ → ℂ, Continuous f ∧ Function.Periodic f 1 ∧ (∀ t : ℝ, f t ∈ Ω) ∧
      ¬ Commons.Topology.Winding.HasArg (fun t : ℝ => f t - a) 0 := by
  obtain ⟨S, hScpt, haS, hSsub, δ, hδpos, hδ⟩ :=
    exists_compact_gap_of_component hΩo hΩc hKcpt hKconn hKsub hKmax haK
  -- `Ωᶜ \ S` is closed, because the gap bounds the distance to the compact `S`
  have hS'cl : IsClosed (Ωᶜ \ S) := by
    have hset : Ωᶜ \ S = Ωᶜ ∩ ⋂ (s : S), {w : ℂ | δ ≤ dist (s : ℂ) w} := by
      ext w
      simp only [Set.mem_sdiff, Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_iInter,
        Set.mem_setOf_eq]
      constructor
      · intro hw
        exact ⟨hw.1, fun s => hδ s s.2 w hw.1 hw.2⟩
      · rintro ⟨hw1, hw2⟩
        refine ⟨hw1, fun hwS => ?_⟩
        have h := hw2 ⟨w, hwS⟩
        rw [dist_self] at h
        exact absurd h (not_le.mpr hδpos)
    rw [hset]
    exact hΩo.isClosed_compl.inter (isClosed_iInter fun s : S =>
      isClosed_le continuous_const (continuous_const.dist continuous_id))
  have hgap' : ∃ δ' : ℝ, 0 < δ' ∧ ∀ s ∈ S, ∀ s' ∈ Ωᶜ \ S, δ' ≤ dist s s' :=
    ⟨δ, hδpos, fun s hs s' hs' => hδ s hs s' hs'.1 hs'.2⟩
  obtain ⟨f, hfc, hfper, hfout, hno⟩ :=
    exists_loop_not_hasArg_of_gap hScpt ⟨a, haS⟩ hS'cl hgap' haS
  refine ⟨f, hfc, hfper, ?_, hno⟩
  intro t
  have h1 : f t ∉ S ∪ (Ωᶜ \ S) := hfout t
  have h2 : S ∪ (Ωᶜ \ S) = Ωᶜ := by
    apply Set.Subset.antisymm
    · rintro z (hz | hz)
      · exact hSsub hz
      · exact hz.1
    · intro z hz
      by_cases hzS : z ∈ S
      · exact Or.inl hzS
      · exact Or.inr ⟨hz, hzS⟩
  rw [h2] at h1
  simpa using h1

end Work.PlanarSC
