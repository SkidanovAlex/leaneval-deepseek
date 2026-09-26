import Mathlib
import Submission.Work.Drive.twiceWindingAPI

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant
open scoped Real Topology

set_option maxHeartbeats 1600000

noncomputable section

/-!
# The chord is non-tangent at the middle: transverse general position and the
regularity of the middle variable

This module isolates the geometric input which makes the *middle correspondence* of a family of
chords non-degenerate, and which is used by `Work.Drive.exists_periodic_middle_family`
(`Submission/Work/Drive/advancing_middle_family.lean`).

`EndpointTangentsOffChord r a b m` (`Submission/TrisecantTransverse.lean`) — part of the
*torus transverse general position* hypothesis — contains the condition
`cross3 (r a - r m) (velocity r m) ≠ 0` for every collinear triple.  Since a strict middle is
collinear and strictly between the chord endpoints, `r a - r m = t • (r a - r b)` with `t ≠ 0`, so
that condition is equivalent to `cross3 (r a - r b) (velocity r m) ≠ 0`, i.e. to the non-vanishing
of `∂/∂m  cross3 (r a - r b) (r a - r m)` — the derivative of the collinearity map in the *middle*
variable.  This is `chord_not_tangent_at_middle` below.

Consequences (used by the middle-continuation analysis): with `∂_m Φ ≠ 0` everywhere on the strict
data, the middle variable is a *regular* coordinate; in particular a middle never becomes
tangential to the moving chord, so the middle set cannot be created or destroyed by a tangency.
-/

/-- Congruent real parameters give equal velocities (velocity form of
`r_eq_of_coe_eq`): `x ≡ y` modulo the period implies `velocity r x = velocity r y`. -/
theorem velocity_eq_of_coe_eq {r : ℝ → Space} (h : IsSmoothKnot r) {x y : ℝ}
    (hxy : (x : KnotParam) = (y : KnotParam)) : velocity r x = velocity r y := by
  have hz : x - y ∈ AddSubgroup.zmultiples period := QuotientAddGroup.eq_iff_sub_mem.mp hxy
  rcases (AddSubgroup.mem_zmultiples_iff.mp hz) with ⟨k, hk⟩
  have hx : x = y + k • period := (sub_eq_iff_eq_add.mp hk.symm).trans (add_comm (k • period) y)
  have hvper : Function.Periodic (velocity r) period := h.velocity_periodic
  rw [hx]
  exact hvper.zsmul k y

/-- **`hgp` forces the chord to be non-tangent at the middle.**  For a smooth knot in transverse
torus general position, a strict middle `M` of the chord from `A` to `B` satisfies
`cross3 (r A - r B) (velocity r M) ≠ 0`.  Equivalently the directional derivative of the
collinearity map `(u, m) ↦ cross3 (r (a u) - r (b u)) (r (a u) - r m)` in the *middle* variable is
nonzero at every strict data point. -/
theorem chord_not_tangent_at_middle {r : ℝ → Space} (h : IsSmoothKnot r)
    (hgp : TorusGeneralPositionTransverse r) {A B M : ℝ}
    (hABp : (A : KnotParam) ≠ (B : KnotParam))
    (hmid : IsMiddleOnChord r (A : KnotParam) (B : KnotParam) (M : KnotParam)) :
    cross3 (r A - r B) (velocity r M) ≠ 0 := by
  have hreal : r M ∈ openSegment ℝ (r A) (r B) := by
    have h' := hmid
    rw [IsMiddleOnChord] at h'
    simpa [knotMap_eq_r h] using h'
  have hMAn : (M : KnotParam) ≠ (A : KnotParam) := (IsMiddleOnChord.ne_params h hABp hmid).1
  have hMBn : (M : KnotParam) ≠ (B : KnotParam) := (IsMiddleOnChord.ne_params h hABp hmid).2
  have hcol : torusCollinearity r (torusQuotient (A, (B, M))) = 0 := by
    have h0 : cross3 (r A - r B) (r A - r M) = 0 := mem_openSegment_cross3 hreal
    simpa [torusCollinearity, torusQuotient, knotMap_eq_r h] using h0
  have hoff : torusQuotient (A, (B, M)) ∈ TorusOffDiag r := by
    refine ⟨?_, ?_, ?_⟩
    · show knotMap r (A : KnotParam) ≠ knotMap r (B : KnotParam)
      exact fun hk => hABp ((knotMap_inj_iff h).mp hk)
    · show knotMap r (A : KnotParam) ≠ knotMap r (M : KnotParam)
      exact fun hk => hMAn ((knotMap_inj_iff h).mp hk).symm
    · show knotMap r (B : KnotParam) ≠ knotMap r (M : KnotParam)
      exact fun hk => hMBn ((knotMap_inj_iff h).mp hk).symm
  rcases hgp (torusQuotient (A, (B, M))) hcol hoff with
    ⟨a, b, m, _, _, _, hac, hbc, hmc, hGP⟩
  obtain ⟨-, -, -, h4, -, -⟩ := hGP.2
  have hra : r a = r A := r_eq_of_coe_eq h hac
  have hrm : r m = r M := r_eq_of_coe_eq h hmc
  have hvm : velocity r m = velocity r M := velocity_eq_of_coe_eq h hmc
  have h4' : cross3 (r A - r M) (velocity r M) ≠ 0 := by
    rw [← hra, ← hrm, ← hvm]
    exact h4
  rcases mem_openSegment_smul_sub hreal with ⟨t, ht0, ht1, ht⟩
  have hsub : r A - r M = t • (r A - r B) := by
    have h1 : r M = r A + t • (r B - r A) := by rw [← ht]; abel
    rw [h1]
    module
  have hmul : cross3 (r A - r M) (velocity r M) = t • cross3 (r A - r B) (velocity r M) := by
    rw [hsub, cross3_smul_left]
  intro hz
  apply h4'
  rw [hmul, hz, smul_zero]



open LeanEval.KnotTheory.Quadrisecant in
lemma hasDerivAt_coordProj_comp {f : ℝ → Space} {f' : Space} {t : ℝ} (i : Fin 3)
    (h : HasDerivAt f f' t) : HasDerivAt (fun x : ℝ => coordProj i (f x)) (coordProj i f') t := by
  have h4 : HasDerivAt ((coordProj i) ∘ f) ((coordProj i) f') t :=
    (coordProj i).hasFDerivAt.comp_hasDerivAt t h
  simpa only [Function.comp_def] using h4

open LeanEval.KnotTheory.Quadrisecant in
lemma continuous_coordProj_comp {f : ℝ → Space} (i : Fin 3) (h : Continuous f) :
    Continuous (fun x : ℝ => coordProj i (f x)) := by
  have h4 : Continuous ((coordProj i) ∘ f) := (coordProj i).continuous.comp h
  simpa only [Function.comp_def] using h4

open LeanEval.KnotTheory.Quadrisecant in
/-- **Local uniqueness of the middle along a family of chords.**  Near a strict middle of the chord
`{a u₀, b u₀}`, for `u` near `u₀`, the chord `{a u, b u}` has at most one middle. -/
theorem middle_local_unique {r : ℝ → Space} (hr : IsSmoothKnot r)
    (hgp : TorusGeneralPositionTransverse r)
    {a b : ℝ → ℝ} (haC : Continuous a) (hbC : Continuous b)
    {u₀ m₀ : ℝ} (hne : (a u₀ : KnotParam) ≠ (b u₀ : KnotParam))
    (hmid : IsMiddleOnChord r (a u₀ : KnotParam) (b u₀ : KnotParam) (m₀ : KnotParam)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ u m m' : ℝ, |u - u₀| < δ → |m - m₀| < δ → |m' - m₀| < δ →
      IsMiddleOnChord r (a u : KnotParam) (b u : KnotParam) (m : KnotParam) →
      IsMiddleOnChord r (a u : KnotParam) (b u : KnotParam) (m' : KnotParam) →
      (m : KnotParam) = (m' : KnotParam) := by
  have hs : collPartialM r (a u₀) (b u₀) m₀ ≠ 0 := by
    have h := chord_not_tangent_at_middle hr hgp hne hmid
    rw [collPartialM, cross3_anticomm]
    simpa using neg_ne_zero.mpr h
  obtain ⟨i, hi⟩ := exists_ofLp_ne_zero_of_ne_zero hs
  have hvelc : Continuous fun t : ℝ => velocity r t := hr.smooth.continuous_deriv le_top
  have hrc : Continuous r := hr.smooth.continuous
  let G : ℝ × ℝ → ℝ := fun p => coordProj i (collPartialM r (a p.1) (b p.1) p.2)
  have hGc : Continuous G := by
    have h1 : Continuous fun p : ℝ × ℝ => r (a p.1) := hrc.comp (haC.comp continuous_fst)
    have h2 : Continuous fun p : ℝ × ℝ => r (b p.1) := hrc.comp (hbC.comp continuous_fst)
    have h3 : Continuous fun p : ℝ × ℝ => velocity r p.2 := hvelc.comp continuous_snd
    exact (coordProj i).continuous.comp
      (continuous_cross3.comp (h3.prodMk (h1.sub h2)))
  have hG0 : G (u₀, m₀) ≠ 0 := by
    dsimp [G]
    rw [coordProj_apply]
    exact hi
  obtain ⟨ε, hε, hball⟩ : ∃ ε > 0, ∀ p : ℝ × ℝ, dist p (u₀, m₀) < ε → G p ≠ 0 := by
    have hopen : IsOpen {y : ℝ | y ≠ 0} := isOpen_ne
    have hmem : {y : ℝ | y ≠ 0} ∈ 𝓝 (G (u₀, m₀)) := hopen.mem_nhds hG0
    have hpre : G ⁻¹' {y : ℝ | y ≠ 0} ∈ 𝓝 ((u₀, m₀) : ℝ × ℝ) := hGc.continuousAt hmem
    rcases Metric.mem_nhds_iff.mp hpre with ⟨ε, hε, hsub⟩
    exact ⟨ε, hε, fun p hp => hsub hp⟩
  -- the `m`-derivative of the scalar collinearity function is the scalar middle partial
  have hderiv : ∀ u t : ℝ,
      deriv (fun x : ℝ => coordProj i (collinearityValue r (a u) (b u) x)) t
        = coordProj i (collPartialM r (a u) (b u) t) := by
    intro u t
    have h3 := hasDerivAt_collinearity_third hr (a u) (b u) t
    have h4 := hasDerivAt_coordProj_comp (f := fun x : ℝ => collinearityValue r (a u) (b u) x)
      (f' := cross3 (velocity r t) (r (a u) - r (b u))) i h3
    rw [h4.deriv]
    rfl
  -- vanishing of the scalar function at middles
  have hzero : ∀ u t : ℝ, IsMiddleOnChord r (a u : KnotParam) (b u : KnotParam) (t : KnotParam) →
      coordProj i (collinearityValue r (a u) (b u) t) = 0 := by
    intro u t ht
    have hreal : r t ∈ openSegment ℝ (r (a u)) (r (b u)) := by
      have h' := ht
      rw [IsMiddleOnChord] at h'
      simpa [knotMap_eq_r hr] using h'
    have h0 : collinearityValue r (a u) (b u) t = 0 := by
      rw [collinearityValue_eq]
      exact mem_openSegment_cross3 hreal
    rw [h0, map_zero]
  refine ⟨ε, hε, ?_⟩
  intro u m m' hu hm hm' hmidm hmidm'
  have hbox : ∀ p : ℝ × ℝ, |p.1 - u₀| < ε → |p.2 - m₀| < ε → G p ≠ 0 := by
    intro p h1 h2
    apply hball p
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, max_lt_iff]
    exact ⟨by simpa using h1, by simpa using h2⟩
  -- two middles at the same `u` give two zeros of a strictly monotone-in-`m` scalar function
  have hmvt : ∀ lo hi : ℝ, lo < hi → |lo - m₀| < ε → |hi - m₀| < ε →
      IsMiddleOnChord r (a u : KnotParam) (b u : KnotParam) (lo : KnotParam) →
      IsMiddleOnChord r (a u : KnotParam) (b u : KnotParam) (hi : KnotParam) → False := by
    intro lo hi hlt hlo hhi hmidlo hmidhi
    have hru : Continuous fun _ : ℝ => r (a u) := continuous_const
    have hrb : Continuous fun _ : ℝ => r (b u) := continuous_const
    have hcontc : Continuous fun x : ℝ => coordProj i (collinearityValue r (a u) (b u) x) :=
      continuous_coordProj_comp i
        (continuous_cross3.comp ((hru.sub hrb).prodMk (hru.sub hrc)))
    have hdiff : DifferentiableOn ℝ
        (fun x : ℝ => coordProj i (collinearityValue r (a u) (b u) x)) (Set.Ioo lo hi) := by
      intro x _
      have h3 := hasDerivAt_collinearity_third hr (a u) (b u) x
      have h4 := hasDerivAt_coordProj_comp (f := fun x : ℝ => collinearityValue r (a u) (b u) x)
        (f' := cross3 (velocity r x) (r (a u) - r (b u))) i h3
      exact h4.differentiableAt.differentiableWithinAt
    obtain ⟨ξ, hξ, hξd⟩ := exists_deriv_eq_slope
      (fun x : ℝ => coordProj i (collinearityValue r (a u) (b u) x)) hlt
      hcontc.continuousOn hdiff
    have hz1 : coordProj i (collinearityValue r (a u) (b u) lo) = 0 := hzero u lo hmidlo
    have hz2 : coordProj i (collinearityValue r (a u) (b u) hi) = 0 := hzero u hi hmidhi
    have hξ0 : coordProj i (collPartialM r (a u) (b u) ξ) = 0 := by
      rw [← hderiv u ξ, hξd, hz1, hz2]
      simp
    have hξbox : |ξ - m₀| < ε := by
      rw [abs_lt] at hlo hhi ⊢
      exact ⟨by linarith [hlo.1, hξ.1], by linarith [hhi.2, hξ.2]⟩
    exact hbox (u, ξ) hu hξbox hξ0
  by_contra hcls
  have hne' : m ≠ m' := by
    intro hEq
    exact hcls (congrArg (fun x : ℝ => (x : KnotParam)) hEq)
  rcases lt_or_gt_of_ne hne' with hlt | hlt
  · exact hmvt m m' hlt hm hm' hmidm hmidm'
  · exact hmvt m' m hlt hm' hm hmidm' hmidm

end

end Work.Drive
