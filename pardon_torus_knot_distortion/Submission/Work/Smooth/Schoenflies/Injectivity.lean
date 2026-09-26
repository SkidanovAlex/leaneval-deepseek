import Submission.Work.Smooth.Schoenflies.Geometry
import Submission.Work.Smooth.Schoenflies.Separation
import Submission.Work.Smooth.SphereJordan.thetaPlaneJordanCurve
import Submission.Work.Smooth.SphereJordan.Caratheodory.BoundaryUniqueness
import Submission.Work.SphereJordan.gammaInjOnArc

/-!
# Injectivity of the boundary values of a Carathéodory extension

This is the **boundary correspondence** step of the Jordan–Schoenflies theorem: if `Ω` is a Jordan
domain (open, bounded, simply connected, with frontier the trace of a simple closed curve `γ`) and
`f : 𝔻 → Ω` is a biholomorphism (here: differentiable and injective on the open unit disc with image
`Ω`) which extends continuously to the closed disc, then the extension `G` is **injective**.

The proof is the classical one (Wikipedia's proof of Carathéodory's theorem, see
`SphereJordan/Caratheodory/NOTES.md`).  Suppose `G x = G y = w` for distinct points of the closed
disc.  Neither can lie in the open disc (there `G = f` is injective, and an interior value lies in
`Ω` while a boundary value lies in `frontier Ω`), so both lie on the unit circle.  Let `L` be the
image of the chord `[x,y]` under `G`: a Jordan curve through `w` (the chord's two endpoints are
identified) contained in `Ω ∪ {w}`, and let `T` be a Jordan separation datum for it.

The chord cuts the disc into the two caps `capPos`, `capNeg`, and `Ω ∖ trace L = f(capPos) ⊔
f(capNeg)`.  Each cap's image is contained in one of the two sides of `L`; for the cap whose image
lies in the bounded side `T.V`, the arc `Z` of the circle on that side satisfies `ḡ(Z) = {w}`:
indeed `Z ⊆ closure cap` and `closure (f cap) ⊆ closure T.V`, while `closure T.V ∩ γ = {w}` because
`T.V ⊆ Ω` and `trace L ∩ γ = {w}`.  So the holomorphic function `g - w` vanishes on a relative
neighbourhood of a point of the circle, hence everywhere on `𝔻` by the boundary-uniqueness lemma
(`Caratheodory.eq_zero_of_eventuallyEq_zero_on_sphere`), contradicting injectivity.

## Main declarations

* `injOn_of_extension` — the extension `G` is injective on the closed disc.
-/

open Set Metric
open scoped Topology ComplexConjugate

namespace Work.Smooth.Schoenflies

noncomputable section

/-- The open unit disc. -/
abbrev unitBall : Set ℂ := Metric.ball (0 : ℂ) 1

/-- The closed unit disc. -/
abbrev unitClosedBall : Set ℂ := Metric.closedBall (0 : ℂ) 1

/-- **Injectivity of the extension on the closed disc.** -/
theorem injOn_of_extension {Ω : Set ℂ} (hΩo : IsOpen Ω) (hΩne : Ω.Nonempty)
    (hΩb : Bornology.IsBounded Ω) (hΩsc : SimplyConnectedSpace ↥Ω)
    {γ : ℝ → ℂ} (hγc : Continuous γ) (hγp : Function.Periodic γ (2 * Real.pi))
    (hγi : Set.InjOn γ (Set.Ico 0 (2 * Real.pi))) (hfr : frontier Ω = Set.range γ)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitBall) (hfinj : Set.InjOn f unitBall)
    (hfsurj : f '' unitBall = Ω)
    {G : ℂ → ℂ} (hGc : ContinuousOn G unitClosedBall)
    (hGf : ∀ z ∈ unitBall, G z = f z)
    (hGb : ∀ ζ : ℂ, ‖ζ‖ = 1 → G ζ ∈ frontier Ω) :
    Set.InjOn G unitClosedBall := by
  classical
  -- ## Setup
  intro x hx y hy hGxy
  by_contra hxy
  have hfr_disj : Disjoint (frontier Ω) Ω := disjoint_frontier_iff_isOpen.mpr hΩo
  have hxle : ‖x‖ ≤ 1 := by
    have h := Metric.mem_closedBall.mp hx
    rwa [dist_zero_right] at h
  have hyle : ‖y‖ ≤ 1 := by
    have h := Metric.mem_closedBall.mp hy
    rwa [dist_zero_right] at h
  -- ## both points are on the circle
  have hx1 : ‖x‖ = 1 := by
    rcases lt_or_eq_of_le hxle with hlt | h
    · exfalso
      rcases lt_or_eq_of_le hyle with hlt' | h'
      · have hx' : x ∈ unitBall := by rw [Metric.mem_ball, dist_zero_right]; exact hlt
        have hy' : y ∈ unitBall := by rw [Metric.mem_ball, dist_zero_right]; exact hlt'
        exact hxy (hfinj hx' hy' (by rw [← hGf x hx', ← hGf y hy']; exact hGxy))
      · have hx' : x ∈ unitBall := by rw [Metric.mem_ball, dist_zero_right]; exact hlt
        have hfxΩ : f x ∈ Ω := by rw [← hfsurj]; exact ⟨x, hx', rfl⟩
        obtain ⟨t, ht⟩ : f x ∈ Set.range γ := by
          rw [← hGf x hx', hGxy]
          rw [← hfr]
          exact hGb y h'
        have hγΩ : Set.range γ ⊆ Ωᶜ := by
          intro z hz
          have hzfr : z ∈ frontier Ω := by rw [hfr]; exact hz
          exact fun hzΩ => Set.disjoint_left.mp hfr_disj hzfr hzΩ
        exact (hγΩ ⟨t, ht⟩) hfxΩ
    · exact h
  have hy1 : ‖y‖ = 1 := by
    rcases lt_or_eq_of_le hyle with hlt | h
    · exfalso
      have hy' : y ∈ unitBall := by rw [Metric.mem_ball, dist_zero_right]; exact hlt
      have hfyΩ : f y ∈ Ω := by rw [← hfsurj]; exact ⟨y, hy', rfl⟩
      obtain ⟨t, ht⟩ : f y ∈ Set.range γ := by
        rw [← hGf y hy', ← hGxy]
        rw [← hfr]
        exact hGb x hx1
      have hγΩ : Set.range γ ⊆ Ωᶜ := by
        intro z hz
        have hzfr : z ∈ frontier Ω := by rw [hfr]; exact hz
        exact fun hzΩ => Set.disjoint_left.mp hfr_disj hzfr hzΩ
      exact (hγΩ ⟨t, ht⟩) hfyΩ
    · exact h
  set w : ℂ := G x with hwdef
  have hwy : G y = w := hGxy.symm
  have hwγ : w ∈ Set.range γ := by
    rw [← hfr]
    exact hGb x hx1
  have hwγ' : ∃ t : ℝ, γ t = w := hwγ
  obtain ⟨t₀, ht₀⟩ := hwγ'
  have hwfrontier : w ∈ frontier Ω := hGb x hx1
  have hwout : w ∉ Ω := fun hwΩ => Set.disjoint_left.mp hfr_disj hwfrontier hwΩ
  -- ## the separation datum of the curve
  set γc : Work.Smooth.Jordan.PlaneCurve := ⟨γ, hγc, hγp⟩ with hγcdef
  have hsimple : γc.IsSimple := hγi
  obtain ⟨S⟩ := Work.Smooth.SphereJordan.exists_jsep γc hsimple
  have hγctrace : γc.trace = Set.range γ := rfl
  have hpre : IsPreconnected Ω := by
    have h1 : IsPreconnected (Set.univ : Set ↥Ω) := isPreconnected_univ
    have himg : IsPreconnected (Set.range (Subtype.val : ↥Ω → ℂ)) := by
      simpa using h1.image (Subtype.val : ↥Ω → ℂ) continuous_subtype_val.continuousOn
    rwa [Subtype.range_coe] at himg
  have hfr' : frontier Ω = γc.trace := by rw [hγctrace]; exact hfr
  have hΩeq : Ω = S.V := eq_boundedSide_of_frontier S hΩo hpre hΩne hΩb hfr'
  -- ## the chord
  have hchord : chord x y = seg x y := chord_eq_seg hx1 hy1 hxy
  have hchord_ball : chord x y ∩ unitBall = seg x y \ {x, y} := by
    rw [hchord]
    ext z
    constructor
    · rintro ⟨hzseg, hzball⟩
      refine ⟨hzseg, ?_⟩
      intro hzmem
      rcases hzmem with h | h
      · rw [h] at hzball
        rw [Metric.mem_ball, dist_zero_right, hx1] at hzball
        exact absurd hzball (by norm_num)
      · rw [h] at hzball
        rw [Metric.mem_ball, dist_zero_right, hy1] at hzball
        exact absurd hzball (by norm_num)
    · rintro ⟨hzseg, hznot⟩
      exact ⟨hzseg, seg_diff_subset_ball hx1 hy1 hxy ⟨hzseg, hznot⟩⟩
  -- ## the loop
  have hsegmem : ∀ s : Set.Icc (0 : ℝ) 1, segPoint (s : ℝ) x y ∈ unitClosedBall :=
    fun s => seg_subset_closedBall (le_of_eq hx1) (le_of_eq hy1) ⟨s.1, s.2, rfl⟩
  have hcontseg : Continuous fun s : Set.Icc (0 : ℝ) 1 => segPoint (s : ℝ) x y :=
    (continuous_segPoint x y).comp continuous_subtype_val
  let p : C(Set.Icc (0 : ℝ) 1, ℂ) :=
    ⟨fun s => G (segPoint (s : ℝ) x y),
      ContinuousOn.comp_continuous hGc hcontseg hsegmem⟩
  have hp0 : p ⟨0, by norm_num⟩ = w := by
    simp only [p, ContinuousMap.coe_mk, segPoint_zero]
    exact hwdef.symm
  have hp1 : p ⟨1, by norm_num⟩ = w := by
    simp only [p, ContinuousMap.coe_mk, segPoint_one]
    exact hwy
  have hp : p ⟨0, by norm_num⟩ = p ⟨1, by norm_num⟩ := by rw [hp0, hp1]
  have hpinj : Set.InjOn p {t : Set.Icc (0 : ℝ) 1 | (t : ℝ) < 1} := by
    rintro ⟨s, hs⟩ hss ⟨t, ht⟩ htt hst
    simp only [Set.mem_setOf_eq] at hss htt
    have inball : ∀ u : Set.Icc (0 : ℝ) 1, (u : ℝ) ≠ 0 → (u : ℝ) < 1 →
        segPoint (u : ℝ) x y ∈ unitBall := by
      intro u hu0 hu1
      refine seg_diff_subset_ball hx1 hy1 hxy ⟨⟨u.1, u.2, rfl⟩, ?_⟩
      rintro (h | h)
      · exact hu0 (segPoint_injOn hxy u.2 (by norm_num)
          (by simpa [segPoint_zero] using h))
      · exact absurd (segPoint_injOn hxy u.2 (by norm_num)
          (by simpa [segPoint_one] using h)) (ne_of_lt hu1)
    have hpw : ∀ u : Set.Icc (0 : ℝ) 1, (u : ℝ) < 1 → p u = w → (u : ℝ) = 0 := by
      intro u hu hpu
      by_contra hu0
      have hball := inball u hu0 hu
      have hfw : f (segPoint (u : ℝ) x y) = w := by
        rw [← hGf _ hball]
        exact hpu
      exact hwout (by rw [← hfw, ← hfsurj]; exact ⟨_, hball, rfl⟩)
    by_cases hs0 : (s : ℝ) = 0
    · have hps : p ⟨s, hs⟩ = w :=
        (congrArg p (Subtype.ext hs0)).trans hp0
      have : (t : ℝ) = 0 := hpw ⟨t, ht⟩ htt (by rw [← hst]; exact hps)
      exact Subtype.ext (by
        show (s : ℝ) = (t : ℝ)
        rw [hs0, this])
    · have ht0 : (t : ℝ) ≠ 0 := by
        intro ht0
        refine hs0 (hpw ⟨s, hs⟩ hss ?_)
        exact (hst.trans (congrArg p (Subtype.ext ht0))).trans hp0
      have hsball := inball ⟨s, hs⟩ hs0 hss
      have htball := inball ⟨t, ht⟩ ht0 htt
      have hG : G (segPoint (s : ℝ) x y) = G (segPoint (t : ℝ) x y) := hst
      rw [hGf _ hsball, hGf _ htball] at hG
      exact Subtype.ext (segPoint_injOn hxy hs ht (hfinj hsball htball hG))
  let L : Work.Smooth.Jordan.PlaneCurve := Work.Smooth.SphereJordan.loopCurve p hp
  have hLsimple : L.IsSimple := Work.Smooth.SphereJordan.loopCurve_isSimple p hp hpinj
  have hLrange : Set.range L.γ = Set.range p := Work.Smooth.SphereJordan.range_loopCurve p hp
  obtain ⟨T⟩ := Work.Smooth.SphereJordan.exists_jsep L hLsimple
  have hLtrace : L.trace = Set.range p := hLrange
  have hUtrace : S.U ⊆ γc.traceᶜ := by
    rw [← S.union_eq]; exact subset_union_left
  have hVtrace : S.V ⊆ γc.traceᶜ := by
    rw [← S.union_eq]; exact subset_union_right
  -- ## the trace of the loop is contained in `S.V ∪ {w}`
  have hLsub : L.trace ⊆ S.V ∪ {w} := by
    rw [hLtrace]
    rintro z ⟨s, rfl⟩
    have hmem := hsegmem s
    have hle : ‖segPoint (s : ℝ) x y‖ ≤ 1 := by
      rw [Metric.mem_closedBall, dist_zero_right] at hmem
      exact hmem
    rcases lt_or_eq_of_le hle with hlt | heq
    · left
      have hball : segPoint (s : ℝ) x y ∈ unitBall := by
        rw [Metric.mem_ball, dist_zero_right]; exact hlt
      have hzs : p s = f (segPoint (s : ℝ) x y) := by
        simp only [p, ContinuousMap.coe_mk]
        exact hGf _ hball
      rw [hzs, ← hΩeq, ← hfsurj]
      exact ⟨_, hball, rfl⟩
    · right
      have hsph : segPoint (s : ℝ) x y ∈ Metric.sphere (0 : ℂ) 1 := by
        rw [Metric.mem_sphere, dist_zero_right]; exact heq
      have hmem2 : segPoint (s : ℝ) x y ∈ chord x y ∩ Metric.sphere (0 : ℂ) 1 :=
        ⟨by rw [hchord]; exact ⟨s.1, s.2, rfl⟩, hsph⟩
      rw [chord_inter_circle hx1 hy1 hxy] at hmem2
      have hpw' : p s = w := by
        rcases hmem2 with h | h
        · change G (segPoint (s : ℝ) x y) = w
          rw [h]
        · rw [Set.mem_singleton_iff] at h
          change G (segPoint (s : ℝ) x y) = w
          rw [h]
          exact hwy
      rw [hpw']
      exact Set.mem_singleton_iff.mpr rfl
  have hLγ : L.trace ∩ γc.trace = {w} := by
    refine Set.Subset.antisymm ?_ ?_
    · rintro z ⟨hzL, hzγ⟩
      rcases hLsub hzL with h | h
      · exact absurd hzγ (hVtrace h)
      · exact h
    · intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact ⟨by rw [hLtrace]; exact ⟨⟨0, by norm_num⟩, hp0⟩, hwγ⟩
  -- ## `S.U` and `γ ∖ {w}` lie in the unbounded side of `L`
  have hSU : S.U ⊆ T.U := by
    refine subset_U_of_preconnected_unbounded T S.preconn_U (not_bounded_U S) ?_
    rw [Set.disjoint_left]
    intro z hzU hzL
    rcases hLsub hzL with h | h
    · exact (Set.disjoint_left.mp S.disjoint_UV) hzU h
    · rw [Set.mem_singleton_iff] at h
      rw [h] at hzU
      exact (hUtrace hzU) hwγ
  have hgamma_ne : ∃ t : ℝ, γ t ≠ w := by
    refine ⟨t₀ + Real.pi, ?_⟩
    intro hcon
    have hcon' : γc.γ (t₀ + Real.pi) = γc.γ t₀ := by
      show γ (t₀ + Real.pi) = γ t₀
      rw [hcon, ht₀]
    obtain ⟨k, hk⟩ := Work.SphereJordan.gamma_eq_imp_mod (γ := γc) hsimple hcon'
    have hk' : (k : ℝ) = 1 / 2 := by
      have hpi := Real.pi_pos
      nlinarith [hk]
    have hint : (k : ℝ) ≤ 0 ∨ (1 : ℝ) ≤ (k : ℝ) := by
      by_cases h : k ≤ 0
      · exact Or.inl (by exact_mod_cast h)
      · exact Or.inr (by
          have : (1 : ℤ) ≤ k := by omega
          exact_mod_cast this)
    rcases hint with h | h <;> linarith
  have hgammaU : γc.trace \ {w} ⊆ T.U := by
    have hpre2 : IsPreconnected (γc.trace \ {w}) := isPreconnected_trace_diff hsimple hwγ
    have hdisj : Disjoint (γc.trace \ {w}) L.trace := by
      rw [Set.disjoint_left]
      rintro z ⟨hzγ, hznw⟩ hzL
      have : z ∈ ({w} : Set ℂ) := by
        rw [← hLγ]
        exact ⟨hzL, hzγ⟩
      exact hznw (by simpa using this)
    have hsub : γc.trace \ {w} ⊆ T.U ∪ T.V := by
      intro z hz
      have h1 : z ∈ L.traceᶜ := fun h2 => (Set.disjoint_left.mp hdisj) hz h2
      rw [T.union_eq]
      exact h1
    rcases IsPreconnected.subset_or_subset T.isOpen_U T.isOpen_V T.disjoint_UV hsub hpre2 with
      h | h
    · exact h
    · exfalso
      obtain ⟨t, ht⟩ := hgamma_ne
      have hzmem : γ t ∈ γc.trace \ {w} := ⟨⟨t, rfl⟩, by simpa using ht⟩
      have hzV : γ t ∈ T.V := h hzmem
      have hzcl : γ t ∈ closure S.U := by
        have hzfr : γ t ∈ frontier S.U := by rw [S.frontier_U]; exact ⟨t, rfl⟩
        exact frontier_subset_closure hzfr
      have hnhds : T.V ∈ 𝓝 (γ t) := T.isOpen_V.mem_nhds hzV
      obtain ⟨a, ha⟩ := (mem_closure_iff_nhds.mp hzcl) T.V hnhds
      exact (Set.disjoint_left.mp T.disjoint_UV) (hSU ha.2) ha.1
  -- ## `T.V ⊆ Ω`
  have hTVΩ : T.V ⊆ Ω := by
    rw [hΩeq]
    intro z hz
    have hznotU : z ∉ S.U := fun h => (Set.disjoint_left.mp T.disjoint_UV) (hSU h) hz
    have hznotγ : z ∉ γc.trace := by
      intro hzγ
      by_cases hw' : z = w
      · subst hw'
        have : w ∈ L.trace := by rw [hLtrace]; exact ⟨⟨0, by norm_num⟩, hp0⟩
        exact (Set.disjoint_left.mp (disjoint_frontier_iff_isOpen.mpr T.isOpen_V))
          (by rw [T.frontier_V]; exact this) hz
      · have : z ∈ γc.trace \ {w} := ⟨hzγ, by simpa using hw'⟩
        exact (Set.disjoint_left.mp T.disjoint_UV) (hgammaU this) hz
    have h1 : z ∈ S.U ∪ S.V := by
      rw [S.union_eq]
      exact hznotγ
    rcases h1 with h | h
    · exact absurd h hznotU
    · exact h
  -- ## the trace of the loop and the splitting of `Ω ∖ L.trace`
  have hLtrace_eq : L.trace = {w} ∪ f '' (chord x y ∩ unitBall) := by
    rw [hLtrace]
    ext z
    constructor
    · rintro ⟨s, rfl⟩
      have hmem := hsegmem s
      have hle : ‖segPoint (s : ℝ) x y‖ ≤ 1 := by
        rw [Metric.mem_closedBall, dist_zero_right] at hmem
        exact hmem
      rcases lt_or_eq_of_le hle with hlt | heq
      · right
        refine ⟨segPoint (s : ℝ) x y, ⟨by rw [hchord]; exact ⟨s.1, s.2, rfl⟩, ?_⟩, ?_⟩
        · rw [Metric.mem_ball, dist_zero_right]; exact hlt
        · simp only [p, ContinuousMap.coe_mk]
          exact (hGf _ (by rw [Metric.mem_ball, dist_zero_right]; exact hlt)).symm
      · left
        have hsph : segPoint (s : ℝ) x y ∈ Metric.sphere (0 : ℂ) 1 := by
          rw [Metric.mem_sphere, dist_zero_right]; exact heq
        have hmem2 : segPoint (s : ℝ) x y ∈ chord x y ∩ Metric.sphere (0 : ℂ) 1 :=
          ⟨by rw [hchord]; exact ⟨s.1, s.2, rfl⟩, hsph⟩
        rw [chord_inter_circle hx1 hy1 hxy] at hmem2
        have hpw' : p s = w := by
          rcases hmem2 with h | h
          · change G (segPoint (s : ℝ) x y) = w
            rw [h]
          · rw [Set.mem_singleton_iff] at h
            change G (segPoint (s : ℝ) x y) = w
            rw [h]
            exact hwy
        rw [hpw']
        exact Set.mem_singleton_iff.mpr rfl
    · rintro (h | ⟨u, hu, rfl⟩)
      · rw [Set.mem_singleton_iff] at h
        rw [h]
        exact ⟨⟨0, by norm_num⟩, hp0⟩
      · obtain ⟨huch, huball⟩ := hu
        rw [hchord] at huch
        obtain ⟨s, hs, hsu⟩ := huch
        refine ⟨⟨s, hs⟩, ?_⟩
        rw [← hsu]
        simp only [p, ContinuousMap.coe_mk]
        exact hGf _ (by simpa [hsu] using huball)
  have hΩsplit : Ω \ L.trace = f '' capPos x y ∪ f '' capNeg x y := by
    ext z
    constructor
    · intro hz
      obtain ⟨hzΩ, hzL⟩ := hz
      obtain ⟨u, hu, rfl⟩ := show z ∈ f '' unitBall from by rw [hfsurj]; exact hzΩ
      have hcases : u ∈ capPos x y ∨ u ∈ capNeg x y ∨ u ∈ chord x y ∩ unitBall := by
        have h1 : u ∈ capPos x y ∪ capNeg x y ∪ (chord x y ∩ unitBall) := by
          rw [← ball_eq_capPos_union_capNeg x y]; exact hu
        rcases h1 with (h | h) | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
      rcases hcases with h | h | h
      · exact Or.inl ⟨u, h, rfl⟩
      · exact Or.inr ⟨u, h, rfl⟩
      · exfalso
        exact hzL (by rw [hLtrace_eq]; exact Or.inr ⟨u, h, rfl⟩)
    · rintro (h | h)
      · obtain ⟨u, hu, rfl⟩ := h
        refine ⟨?_, ?_⟩
        · rw [← hfsurj]
          exact ⟨u, hu.1, rfl⟩
        · intro hcon
          rw [hLtrace_eq] at hcon
          rcases hcon with hcon | hcon
          · rw [Set.mem_singleton_iff] at hcon
            exact hwout (hcon ▸ (by rw [← hfsurj]; exact ⟨u, hu.1, rfl⟩))
          · obtain ⟨u', hu', heq⟩ := hcon
            have : u = u' := hfinj hu.1 hu'.2 heq.symm
            have hchord : chordFun x y u = 0 := by rw [this]; exact hu'.1.2
            linarith [hu.2, hchord]
      · obtain ⟨u, hu, rfl⟩ := h
        refine ⟨?_, ?_⟩
        · rw [← hfsurj]
          exact ⟨u, hu.1, rfl⟩
        · intro hcon
          rw [hLtrace_eq] at hcon
          rcases hcon with hcon | hcon
          · rw [Set.mem_singleton_iff] at hcon
            exact hwout (hcon ▸ (by rw [← hfsurj]; exact ⟨u, hu.1, rfl⟩))
          · obtain ⟨u', hu', heq⟩ := hcon
            have : u = u' := hfinj hu.1 hu'.2 heq.symm
            have hchord : chordFun x y u = 0 := by rw [this]; exact hu'.1.2
            linarith [hu.2, hchord]
  -- ## the closure of `T.V` meets `γ` exactly in `w`
  have hclTVγ : closure T.V ∩ γc.trace = {w} := by
    have hcl : closure T.V = T.V ∪ L.trace := by
      rw [closure_eq_self_union_frontier, T.frontier_V]
    have hTVmem : ∀ z, z ∈ T.V → z ∈ γc.trace → False := by
      intro z hzV hzγ
      by_cases hw' : z = w
      · subst hw'
        have : w ∈ L.trace := by rw [hLtrace]; exact ⟨⟨0, by norm_num⟩, hp0⟩
        exact (Set.disjoint_left.mp (disjoint_frontier_iff_isOpen.mpr T.isOpen_V))
          (by rw [T.frontier_V]; exact this) hzV
      · exact (Set.disjoint_left.mp T.disjoint_UV) (hgammaU ⟨hzγ, by simpa using hw'⟩) hzV
    rw [hcl]
    refine Set.Subset.antisymm ?_ ?_
    · rintro z hz
      rcases hz.1 with hzV | hzL
      · exact (hTVmem z hzV hz.2).elim
      · have : z ∈ ({w} : Set ℂ) := by
          rw [← hLγ]
          exact ⟨hzL, hz.2⟩
        exact this
    · intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact ⟨Or.inr (by rw [hLtrace]; exact ⟨⟨0, by norm_num⟩, hp0⟩), hwγ⟩
  -- ## each cap's image lies in one of the two sides
  have hcap_side : ∀ W : Set ℂ, (W = capPos x y ∨ W = capNeg x y) →
      f '' W ⊆ T.V ∨ f '' W ⊆ T.U := by
    intro W hW
    have hWpre : IsPreconnected W := by
      rcases hW with h | h
      · rw [h]; exact isPreconnected_capPos x y
      · rw [h]; exact isPreconnected_capNeg x y
    have hWball : W ⊆ unitBall := by
      rcases hW with h | h <;> rw [h] <;> intro z hz <;> exact hz.1
    have hfW : IsPreconnected (f '' W) := hWpre.image f (hf.continuousOn.mono hWball)
    have hsub : f '' W ⊆ T.V ∪ T.U := by
      intro z hz
      have h1 : z ∈ L.traceᶜ := by
        rintro hcon
        obtain ⟨u, hu, rfl⟩ := hz
        rw [hLtrace_eq] at hcon
        rcases hcon with hcon | hcon
        · rw [Set.mem_singleton_iff] at hcon
          have h2 : f u ∈ Ω := by rw [← hfsurj]; exact ⟨u, hWball hu, rfl⟩
          exact hwout (hcon ▸ h2)
        · obtain ⟨u', hu', heq⟩ := hcon
          have : u = u' := hfinj (hWball hu) hu'.2 heq.symm
          have hchord : chordFun x y u = 0 := by rw [this]; exact hu'.1.2
          have hne : chordFun x y u ≠ 0 := by
            rcases hW with h | h <;> rw [h] at hu
            · exact ne_of_gt hu.2
            · exact ne_of_lt hu.2
          exact hne hchord
      rw [← T.union_eq] at h1
      rcases h1 with h | h
      · exact Or.inr h
      · exact Or.inl h
    rcases IsPreconnected.subset_or_subset T.isOpen_V T.isOpen_U T.disjoint_UV.symm hsub hfW
      with h | h
    · exact Or.inl h
    · exact Or.inr h
  -- ## the arc on the side of the chosen cap
  have hdone : ∀ (W Z : Set ℂ), (W = capPos x y ∨ W = capNeg x y) → f '' W ⊆ T.V →
      (Z = arcPos x y ∨ Z = arcNeg x y) → Z ⊆ closure W → Z.Nonempty →
      ∀ ζ ∈ Z, G ζ = w := by
    intro W Z hW hWV hZ hZcl hZne ζ hζ
    have h1 : G ζ ∈ γc.trace := by
      rcases hZ with h | h
      · rw [h] at hζ
        have hζn : ‖ζ‖ = 1 := by simpa [Metric.mem_sphere, dist_eq_norm] using hζ.1
        have h2 : G ζ ∈ frontier Ω := hGb ζ hζn
        rw [hfr, ← hγctrace] at h2
        exact h2
      · rw [h] at hζ
        have hζn : ‖ζ‖ = 1 := by simpa [Metric.mem_sphere, dist_eq_norm] using hζ.1
        have h2 : G ζ ∈ frontier Ω := hGb ζ hζn
        rw [hfr, ← hγctrace] at h2
        exact h2
    have h2 : G ζ ∈ closure T.V := by
      have hcl : G ζ ∈ closure (G '' W) := by
        have hcont : ContinuousOn G (closure W) := by
          refine hGc.mono ?_
          have hW' : W ⊆ unitBall := by
            rcases hW with h | h <;> rw [h] <;> intro z hz <;> exact hz.1
          calc closure W ⊆ closure unitBall := closure_mono hW'
            _ = unitClosedBall := closure_ball (0 : ℂ) one_ne_zero
        exact ContinuousOn.image_closure hcont ⟨ζ, hZcl hζ, rfl⟩
      refine closure_mono ?_ hcl
      rintro z ⟨u, hu, rfl⟩
      rw [show G u = f u from by
        rcases hW with h | h
        · rw [h] at hu; exact hGf u hu.1
        · rw [h] at hu; exact hGf u hu.1]
      exact hWV ⟨u, hu, rfl⟩
    have h3 : G ζ ∈ ({w} : Set ℂ) := by
      rw [← hclTVγ]
      exact ⟨h2, h1⟩
    simpa using h3
  have hcapV : (f '' capPos x y ⊆ T.V) ∨ (f '' capNeg x y ⊆ T.V) := by
    rcases hcap_side (capPos x y) (Or.inl rfl) with h1 | h1 <;>
      rcases hcap_side (capNeg x y) (Or.inr rfl) with h2 | h2
    · exact Or.inl h1
    · exact Or.inl h1
    · exact Or.inr h2
    · exfalso
      obtain ⟨z, hz⟩ := T.nonempty_V
      have hz' : z ∈ f '' capPos x y ∪ f '' capNeg x y := by
        rw [← hΩsplit]
        refine ⟨hTVΩ hz, ?_⟩
        intro hcon
        exact (Set.disjoint_left.mp (disjoint_frontier_iff_isOpen.mpr T.isOpen_V))
          (by rw [T.frontier_V]; exact hcon) hz
      rcases hz' with h | h
      · obtain ⟨u, hu, huf⟩ := h
        exact (Set.disjoint_left.mp T.disjoint_UV) (h1 ⟨u, hu, huf⟩) hz
      · obtain ⟨u, hu, huf⟩ := h
        exact (Set.disjoint_left.mp T.disjoint_UV) (h2 ⟨u, hu, huf⟩) hz
  -- ## the boundary-uniqueness contradiction
  have key : (∀ z ∈ unitBall, G z - w = 0) → False := by
    intro hzero
    have hb0 : (0 : ℂ) ∈ unitBall := by rw [Metric.mem_ball, dist_zero_right]; norm_num
    have hb1 : (((1 / 2 : ℝ)) : ℂ) ∈ unitBall := by
      rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]
      norm_num
    have hfw0 : f 0 = w := by
      have h := hzero 0 hb0
      rw [hGf 0 hb0] at h
      exact sub_eq_zero.mp h
    have hfw1 : f (((1 / 2 : ℝ)) : ℂ) = w := by
      have h := hzero _ hb1
      rw [hGf _ hb1] at h
      exact sub_eq_zero.mp h
    have heq : (0 : ℂ) = ((1 / 2 : ℝ) : ℂ) := hfinj hb0 hb1 (by rw [hfw0, hfw1])
    norm_num at heq
  rcases hcapV with hV | hV
  · obtain ⟨z₀, hz₀⟩ := arcPos_nonempty hx1 hy1 hxy
    have hGarc : ∀ ζ ∈ arcPos x y, G ζ = w :=
      hdone (capPos x y) (arcPos x y) (Or.inl rfl) hV (Or.inl rfl)
        (arcPos_subset_closure_capPos x y) ⟨z₀, hz₀⟩
    refine key ?_
    have hz₀norm : ‖z₀‖ = 1 := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hz₀.1
    refine Work.Smooth.SphereJordan.Caratheodory.eq_zero_of_eventuallyEq_zero_on_sphere
      (f := fun z => G z - w) ?_ ?_ hz₀norm ?_
    · have h' : AnalyticOnNhd ℂ (fun z => f z - w) unitBall :=
        AnalyticOnNhd.sub (hf.analyticOnNhd isOpen_ball) (analyticOnNhd_const (v := w))
      exact h'.congr isOpen_ball (fun z hz => by rw [hGf z hz])
    · exact hGc.sub continuousOn_const
    · filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds ((isOpen_lt continuous_const (continuous_chordFun x y)).mem_nhds
          hz₀.2)] with ζ hζsph hζpos
      rw [hGarc ζ ⟨hζsph, hζpos⟩, sub_self]
  · obtain ⟨z₀, hz₀⟩ := arcNeg_nonempty hx1 hy1 hxy
    have hGarc : ∀ ζ ∈ arcNeg x y, G ζ = w :=
      hdone (capNeg x y) (arcNeg x y) (Or.inr rfl) hV (Or.inr rfl)
        (arcNeg_subset_closure_capNeg x y) ⟨z₀, hz₀⟩
    refine key ?_
    have hz₀norm : ‖z₀‖ = 1 := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hz₀.1
    refine Work.Smooth.SphereJordan.Caratheodory.eq_zero_of_eventuallyEq_zero_on_sphere
      (f := fun z => G z - w) ?_ ?_ hz₀norm ?_
    · have h' : AnalyticOnNhd ℂ (fun z => f z - w) unitBall :=
        AnalyticOnNhd.sub (hf.analyticOnNhd isOpen_ball) (analyticOnNhd_const (v := w))
      exact h'.congr isOpen_ball (fun z hz => by rw [hGf z hz])
    · exact hGc.sub continuousOn_const
    · filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds ((isOpen_lt (continuous_chordFun x y) continuous_const).mem_nhds
          hz₀.2)] with ζ hζsph hζneg
      rw [hGarc ζ ⟨hζsph, hζneg⟩, sub_self]

end

end Work.Smooth.Schoenflies
