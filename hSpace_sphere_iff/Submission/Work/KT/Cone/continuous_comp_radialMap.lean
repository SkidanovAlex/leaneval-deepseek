import Mathlib
import Submission.Work.KT.Cone.RadialDefs

namespace Work.KT.Cone

open Work.KT

noncomputable section

open Classical

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- `sphProj`, regarded as a map on the subtype of *nonzero* points of the ball.  (The ball
does not always have a canonical nonzero point, so a total map with a junk value at the origin
is not available; the subtype is the right home for this map.) -/
private def sphProjSub (x : {x : Ball V // (x : V) ≠ 0}) : Sph V :=
  sphProj x.1 x.2

/-- `sphProjSub` is continuous: on the nonzero part of the ball the direction map
`x ↦ ‖x‖⁻¹ • x` is given by a continuous formula. -/
private theorem continuous_sphProjSub : Continuous (sphProjSub (V := V)) := by
  apply Continuous.subtype_mk
  have hy : Continuous fun x : {x : Ball V // (x : V) ≠ 0} => ((x.1 : Ball V) : V) :=
    continuous_subtype_val.comp continuous_subtype_val
  refine (Continuous.inv₀ (continuous_norm.comp hy) ?_).smul hy
  intro x
  change (‖(((x.1 : Ball V)) : V)‖) ≠ 0
  exact norm_ne_zero_iff.mpr x.2

/-- The radial coordinate `1 - ‖x‖` is continuous on the ball. -/
private theorem continuous_radialCoord : Continuous (radialCoord (V := V)) := by
  apply Continuous.subtype_mk
  exact continuous_const.sub (continuous_norm.comp continuous_subtype_val)

/-- The second coordinate of `radialMapAll` is always the radial coordinate. -/
private theorem radialMapAll_snd {T : Type} [TopologicalSpace T]
    (f : C(Sph V, T)) (t₀ : T) (x : Ball V) :
    (radialMapAll f t₀ x).2 = radialCoord x := by
  by_cases hx : (x : V) = 0 <;> simp [radialMapAll, hx]

/-- A continuous function on `T × [0,1]` which is constant on the slice `T × {1}` is in fact
*uniformly* constant on a neighbourhood of that slice: for every `ε > 0` there is `δ > 0` such
that `‖K (t,s) - c‖ < ε` whenever `s > 1 - δ`.  This is the tube lemma, phrased through the
sup norm on `C(T,ℂ)`. -/
private theorem uniform_slice_const {T : Type} [TopologicalSpace T] [CompactSpace T]
    (K : C(T × unitInterval, ℂ)) (c : ℂ) (hc : ∀ t : T, K (t, 1) = c) :
    ∀ ε > 0, ∃ δ > 0, ∀ (t : T) (s : unitInterval), 1 - δ < (s : ℝ) → dist (K (t, s)) c < ε := by
  intro ε hε
  let Φ : C(unitInterval, C(T, ℂ)) :=
    (K.comp (ContinuousMap.prodSwap (α := unitInterval) (β := T))).curry
  have happ : ∀ (s : unitInterval) (t : T), Φ s t = K (t, s) := by
    intro s t
    simp [Φ]
  obtain ⟨δ, hδpos, hδ⟩ := Metric.continuousAt_iff.mp
    (Φ.continuous.continuousAt (x := (1 : unitInterval))) ε hε
  refine ⟨δ, hδpos, ?_⟩
  intro t s hs
  have hsd : dist s 1 < δ := by
    rw [Subtype.dist_eq, Real.dist_eq]
    have hs1 : ((s : ℝ) ≤ 1) := s.2.2
    have hc1 : (((1 : unitInterval)) : ℝ) = 1 := rfl
    rw [hc1, abs_of_nonpos (by linarith : (s:ℝ) - 1 ≤ 0)]
    linarith
  have hdel := hδ hsd
  have h1 : (Φ s - Φ 1) t = K (t, s) - c := by
    rw [ContinuousMap.sub_apply, happ, happ, hc]
  calc dist (K (t, s)) c = ‖K (t, s) - c‖ := dist_eq_norm _ _
    _ = ‖(Φ s - Φ 1) t‖ := by rw [h1]
    _ ≤ ‖Φ s - Φ 1‖ := ContinuousMap.norm_coe_le_norm _ t
    _ = dist (Φ s) (Φ 1) := (dist_eq_norm _ _).symm
    _ < ε := hdel

/-- If `K : C(T × [0,1], ℂ)` is constant on the slice `T × {1}`, then the radial pullback
`x ↦ K (radialMapAll f t₀ x)` is continuous on the closed unit ball.  The `T`-component of
`radialMapAll` is discontinuous at the origin, but `K` is uniformly constant near `T × {1}`
and `radialCoord x → 1` as `x → 0`. -/
theorem continuous_comp_radialMap {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {T : Type} [TopologicalSpace T] [CompactSpace T]
    (f : C(Sph V, T)) (t₀ : T) (K : C(T × unitInterval, ℂ)) (c : ℂ)
    (hc : ∀ t : T, K (t, 1) = c) :
    Continuous (fun x : Ball V => K (radialMapAll f t₀ x)) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : (x : V) = 0
  · -- the origin: `K` is uniformly close to `c` near the slice `T × {1}`, and `radialCoord → 1`
    have hx0 : x = 0 := Subtype.ext hx
    rw [hx0, Metric.continuousAt_iff]
    intro ε hε
    obtain ⟨δ, hδpos, hδ⟩ := uniform_slice_const K c hc ε hε
    refine ⟨δ, hδpos, ?_⟩
    intro y hy
    have hyle : ‖((y : Ball V) : V)‖ < δ := by
      rw [Subtype.dist_eq] at hy
      rw [dist_eq_norm] at hy
      simpa using hy
    have hcoord : 1 - δ < (((radialMapAll f t₀ y).2 : unitInterval) : ℝ) := by
      rw [radialMapAll_snd, radialCoord_coe]
      linarith
    have key := hδ (radialMapAll f t₀ y).1 (radialMapAll f t₀ y).2 hcoord
    rw [radialMapAll_zero, hc t₀]
    exact key
  · -- away from the origin both components of `radialMapAll` are continuous
    have hCOmap : ContinuousOn (radialMapAll f t₀) {y : Ball V | (y : V) ≠ 0} := by
      rw [continuousOn_iff_continuous_domRestrict]
      have hcont : Continuous (fun y : {y : Ball V // (y : V) ≠ 0} =>
          (f (sphProjSub y), radialCoord y.1)) :=
        (f.continuous.comp continuous_sphProjSub).prodMk
          (continuous_radialCoord.comp continuous_subtype_val)
      refine hcont.congr ?_
      intro y
      simp [Set.domRestrict, radialMapAll, y.2, sphProjSub]
    have hCOg : ContinuousOn (fun y : Ball V => K (radialMapAll f t₀ y))
        {y : Ball V | (y : V) ≠ 0} :=
      K.continuous.comp_continuousOn hCOmap
    exact hCOg.continuousAt ((isOpen_ne.preimage continuous_subtype_val).mem_nhds hx)

end

end Work.KT.Cone
