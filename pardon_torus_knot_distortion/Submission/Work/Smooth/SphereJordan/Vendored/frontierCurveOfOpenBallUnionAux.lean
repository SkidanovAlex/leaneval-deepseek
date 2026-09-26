import Mathlib
import Submission.Work.Smooth.SphereJordan.outFrontierPath
import Submission.Work.Smooth.SphereJordan.jsepExterior
import Submission.Work.Smooth.SphereJordan.frontierComponentUnionSubset
import Submission.Work.Smooth.SphereJordan.Vendored.frontierComponentLocallyArc
import Submission.Work.Smooth.SphereJordan.existsSimpleClosedCurveOfLocallyArc

/-!
# The frontier curve of a union of open balls

**STATUS: complete.**  Everything below is proved and the module is axiom-clean
(`#print axioms` gives `[propext, Classical.choice, Quot.sound]`).  The proof rests on the two
geometric inputs

1. `Work.Smooth.SphereJordan.frontierComponentLocallyArc`
   (`Submission/Work/Smooth/SphereJordan/frontierComponentLocallyArc.lean`, now complete):
   the frontier of a complementary component of a finite union of equal closed discs whose *open*
   balls are preconnected is locally an arc.  Its proof splits on whether a *free* unit direction
   exists at `x`: the generic case is `localComplementPreconnected` +
   `frontierLocallyArc_of_freeDirection`, and the tangency case is
   `tangencyPair_of_not_generic` (the antipodal pair of active centres, `tangencyPair.lean`) plus
   the cusp analysis `frontierLocallyArc_of_cusp` (`localArcTangency.lean`) and, when the active set
   is exactly the pair, the separation `tangency_cusps_separated` (`tangencyCuspSeparation.lean`).
2. `Work.Smooth.SphereJordan.LocalArc.compactPreconnectedLocallyArc_isCircle`
   (used through the complete `existsSimpleClosedCurveOfLocallyArc`): the classification of a
   compact connected locally-arc space as a circle.

This module proves `frontierCurveOfOpenBallUnionAux`: for a finite family of equal discs with
`z ∈ ⋃ w ∈ P, ball w r` there is a `2π`-periodic curve `γ`, injective on `[0, 2π)`, whose range
lies in `frontier (⋃ w ∈ P, closedBall w r)` and which separates `z` from infinity (the component
of `z` in the complement of its range is bounded).

## Structure of the proof

Let `U = ⋃ w ∈ P, ball w r`, let `B` be the component of `z` in `U` and let
`Q = {w ∈ P : ball w r ⊆ B}`.  Then `B = ⋃ w ∈ Q, ball w r`, so `⋃ w ∈ Q, ball w r` is
preconnected, and the closed union `⋃ w ∈ Q, closedBall w r` is the closure of that preconnected
open union.

Choose `q` far outside `⋃ w ∈ Q, closedBall w r`; its component `O` in the complement is unbounded.
By `jordanCurveFrontierComponent` (the parametrisation of the outer boundary of a finite union of
equal closed discs whose open balls are preconnected), `frontier O` is the range of a curve `γ`.

* `frontier O ⊆ frontier (⋃ w ∈ Q, closedBall w r)`
  (`frontier_componentIn_subset`), and
* `frontier (⋃ w ∈ Q, closedBall w r) ⊆ frontier (⋃ w ∈ P, closedBall w r)`
  (`frontierComponentUnionSubset`, proved in `frontierComponentUnionSubset.lean`),

so `range γ ⊆ frontier (⋃ w ∈ P, closedBall w r)`.  Finally `z ∉ closure O` (because `z` lies in
the *interior* of `⋃ w ∈ Q, closedBall w r`), and `(frontier O)ᶜ = O ∪ (closure O)ᶜ` with both
parts open and disjoint; since the component of `z` in `(frontier O)ᶜ` is preconnected it lies in
one of them, and it cannot lie in `O`, so it lies in `(closure O)ᶜ` — which is contained in a
closed ball around `0`.  Hence it is bounded.
-/

namespace Work.Smooth.SphereJordan

open Set

noncomputable section

open scoped Classical

/-- The closed union of equal balls is the closure of the open union. -/
theorem closedBall_iUnion_eq_closure_ball_iUnion {Q : Finset ℂ} {r : ℝ} (hr : 0 < r) :
    (⋃ w ∈ Q, Metric.closedBall w r) = closure (⋃ w ∈ Q, Metric.ball w r) := by
  apply le_antisymm
  · intro y hy
    obtain ⟨w, hw, hyw⟩ := Set.mem_iUnion₂.mp hy
    rw [← closure_ball w hr.ne'] at hyw
    exact closure_mono (fun z hz => Set.mem_iUnion₂.mpr ⟨w, hw, hz⟩) hyw
  · refine closure_minimal ?_ (isClosed_biUnion_finset fun w _ => Metric.isClosed_closedBall)
    intro y hy
    obtain ⟨w, hw, hyw⟩ := Set.mem_iUnion₂.mp hy
    exact Set.mem_iUnion₂.mpr ⟨w, hw, Metric.ball_subset_closedBall hyw⟩

/-- Preconnectedness of the open union passes to the closed union. -/
theorem isPreconnected_closedBall_iUnion {Q : Finset ℂ} {r : ℝ} (hr : 0 < r)
    (hB : IsPreconnected (⋃ w ∈ Q, Metric.ball w r)) :
    IsPreconnected (⋃ w ∈ Q, Metric.closedBall w r) := by
  rw [closedBall_iUnion_eq_closure_ball_iUnion (Q := Q) hr]
  exact hB.closure

/-- **The outer boundary of a finite union of equal closed discs with preconnected open balls is
the range of a `2π`-periodic curve injective on `[0, 2π)`.** -/
theorem jordanCurveFrontierComponent {Q : Finset ℂ} {r : ℝ} (hr : 0 < r) (hQne : Q.Nonempty)
    {q : ℂ} (hq : q ∉ ⋃ w ∈ Q, Metric.closedBall w r)
    (hB : IsPreconnected (⋃ w ∈ Q, Metric.ball w r))
    (hunb : ¬ Bornology.IsBounded
      (connectedComponentIn ((⋃ w ∈ Q, Metric.closedBall w r)ᶜ) q)) :
    ∃ γ : ℝ → ℂ, Continuous γ ∧ Function.Periodic γ (2 * Real.pi) ∧
      Set.InjOn γ (Set.Ico 0 (2 * Real.pi)) ∧
      Set.range γ = frontier (connectedComponentIn ((⋃ w ∈ Q, Metric.closedBall w r)ᶜ) q) := by
  set O : Set ℂ := connectedComponentIn ((⋃ w ∈ Q, Metric.closedBall w r)ᶜ) q with hOdef
  set ω : Set ℂ := frontier O with hωdef
  have hLdef : ω = frontier (connectedComponentIn ((⋃ w ∈ Q, Metric.closedBall w r)ᶜ) q) := by
    rw [hωdef, hOdef]
  have hSclosed : IsClosed (⋃ w ∈ Q, Metric.closedBall w r) :=
    isClosed_biUnion_finset fun w _ => Metric.isClosed_closedBall
  have hOopen : IsOpen O := by
    rw [hOdef]; exact hSclosed.isOpen_compl.connectedComponentIn
  -- a radius exceeding all the discs
  set R : ℝ := Q.sup' hQne (fun w => ‖w‖ + r) + 1 with hRdef
  have hR : ∀ w ∈ Q, ‖w‖ + r < R := by
    intro w hw
    have h1 := Finset.le_sup' (fun w => ‖w‖ + r) hw
    rw [hRdef]; linarith
  have hRpos : 0 < R := by
    obtain ⟨w, hw⟩ := hQne
    have h1 := hR w hw
    have h2 : (0 : ℝ) ≤ ‖w‖ + r := by positivity
    linarith
  -- the far region lies in the component `O`
  have hfar : ∀ y : ℂ, R < ‖y‖ → y ∈ O := by
    intro y hy
    obtain ⟨y₀, hy₀O, hy₀R⟩ : ∃ y₀ ∈ O, R < ‖y₀‖ := by
      by_contra h
      push_neg at h
      refine hunb ?_
      rw [Metric.isBounded_iff]
      refine ⟨2 * R, ?_⟩
      intro a ha b hb
      have h1 : dist a b ≤ ‖a‖ + ‖b‖ := by
        rw [dist_eq_norm]
        calc ‖a - b‖ = ‖a + -b‖ := by ring_nf
          _ ≤ ‖a‖ + ‖-b‖ := norm_add_le _ _
          _ = ‖a‖ + ‖b‖ := by rw [norm_neg]
      linarith [h a ha, h b hb]
    have hpre : IsPreconnected {z : ℂ | R < ‖z‖} := by
      have h := isPreconnected_compl_closedBall (0 : ℂ) hRpos
      have heq : (Metric.closedBall (0 : ℂ) R)ᶜ = {z : ℂ | R < ‖z‖} := by
        ext z
        simp [Metric.mem_closedBall, dist_zero_right, not_le]
      rwa [heq] at h
    have hsub : {z : ℂ | R < ‖z‖} ⊆ ((⋃ w ∈ Q, Metric.closedBall w r)ᶜ) := by
      intro z hz hmem
      obtain ⟨w, hw, hzw⟩ := Set.mem_iUnion₂.mp hmem
      have h4 : ‖z - w‖ ≤ r := by
        rw [← dist_eq_norm]; exact Metric.mem_closedBall.mp hzw
      have h3 : ‖z‖ ≤ ‖w‖ + r := by
        calc ‖z‖ = ‖(z - w) + w‖ := by ring_nf
          _ ≤ ‖z - w‖ + ‖w‖ := norm_add_le _ _
          _ ≤ ‖w‖ + r := by linarith
      have hz' : R < ‖z‖ := hz
      linarith [h3, hz', hR w hw]
    have heqO : connectedComponentIn ((⋃ w ∈ Q, Metric.closedBall w r)ᶜ) y₀ = O := by
      rw [hOdef]; exact (connectedComponentIn_eq hy₀O).symm
    have hcomp := hpre.subset_connectedComponentIn hy₀R hsub
    rw [heqO] at hcomp
    exact hcomp hy
  -- `ω` is nonempty: a point of the closed union with an escaping ray lies on the outer boundary
  have hne : ω.Nonempty := by
    have hSne : (⋃ w ∈ Q, Metric.closedBall w r).Nonempty := by
      obtain ⟨w, hw⟩ := hQne
      exact ⟨w, Set.mem_iUnion₂.mpr ⟨w, hw, Metric.mem_closedBall_self hr.le⟩⟩
    have hScompact : IsCompact (⋃ w ∈ Q, Metric.closedBall w r) :=
      Q.finite_toSet.isCompact_biUnion fun w _ => isCompact_closedBall w r
    obtain ⟨p, hpS, hpmax⟩ :=
      hScompact.exists_isMaxOn hSne Complex.continuous_re.continuousOn
    obtain ⟨y₀, hy₀O, hy₀R⟩ : ∃ y₀ ∈ O, R < ‖y₀‖ := by
      by_contra h
      push_neg at h
      refine hunb ?_
      rw [Metric.isBounded_iff]
      refine ⟨2 * R, ?_⟩
      intro a ha b hb
      have h1 : dist a b ≤ ‖a‖ + ‖b‖ := by
        rw [dist_eq_norm]
        calc ‖a - b‖ = ‖a + -b‖ := by ring_nf
          _ ≤ ‖a‖ + ‖-b‖ := norm_add_le _ _
          _ = ‖a‖ + ‖b‖ := by rw [norm_neg]
      linarith [h a ha, h b hb]
    refine ⟨p, ?_⟩
    have hp := escapeRay_mem_frontier_component (P := Q) (r := r) (M := R) hr hR
      (n := (1 : ℂ)) (x := y₀) (p := p) (by norm_num) hy₀R hpS ?_
    · have heq : connectedComponentIn ((⋃ w ∈ Q, Metric.closedBall w r)ᶜ) y₀ = O := by
        rw [hOdef]; exact (connectedComponentIn_eq hy₀O).symm
      rw [heq] at hp
      rwa [hωdef]
    · intro t ht hmem
      obtain ⟨w, hw, htw⟩ := Set.mem_iUnion₂.mp hmem
      have hle : dist (p + (t : ℂ) * 1) w ≤ r := Metric.mem_closedBall.mp htw
      have h1 := hpmax (Set.mem_iUnion₂.mpr ⟨w, hw, Metric.mem_closedBall.mpr hle⟩)
      have h1' : (p + (t : ℂ) * 1).re ≤ p.re := h1
      have h2 : p.re < (p + (t : ℂ) * 1).re := by
        simp only [Complex.add_re, Complex.mul_re, Complex.one_re, Complex.one_im, mul_zero,
          sub_zero, Complex.ofReal_re, Complex.ofReal_im, mul_one]
        linarith
      linarith [h1', h2]
  -- `ω` is bounded, because it is the frontier of a set containing the whole far region
  have hbdd : Bornology.IsBounded ω := by
    refine Bornology.IsBounded.subset (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := R)) ?_
    intro y hy
    by_contra hcon
    rw [Metric.mem_closedBall, dist_zero_right, not_le] at hcon
    have hyO : y ∈ O := hfar y hcon
    have hnf : y ∉ frontier O := by
      rw [hOopen.frontier_eq]
      exact fun h => h.2 hyO
    exact hnf (hωdef ▸ hy)
  have hcompact : IsCompact ω := by
    rw [Metric.isCompact_iff_isClosed_bounded]
    exact ⟨hωdef ▸ isClosed_frontier, hbdd⟩
  have hpre : IsPreconnected ω := by
    rw [hωdef, hOdef]
    exact frontier_component_isPreconnected hr (isPreconnected_closedBall_iUnion hr hB) q
  -- `ω` is nontrivial, because it is locally an arc
  have hloc : ∀ x ∈ frontier (connectedComponentIn ((⋃ w ∈ Q, Metric.closedBall w r)ᶜ) q),
      ∃ (ε : ℝ) (γ : ℝ → ℂ), 0 < ε ∧ Continuous γ ∧ Function.Injective γ ∧ γ 0 = x ∧
        γ '' Set.Ioo (-1) 1 =
          frontier (connectedComponentIn ((⋃ w ∈ Q, Metric.closedBall w r)ᶜ) q) ∩ Metric.ball x ε := by
    intro x hx
    obtain ⟨ε, hεpos, γ, hcont, hinj, hγ0, hγr⟩ := frontierComponentLocallyArc Q hr hB q x hx
    exact ⟨ε, γ, hεpos, hcont, hinj, hγ0, hγr⟩
  have hnt : ω.Nontrivial := by
    obtain ⟨x, hx⟩ := hne
    obtain ⟨ε, γ, hεpos, hcont, hinj, hγ0, hγrange⟩ := hloc x (hLdef ▸ hx)
    refine ⟨x, hx, γ (1 / 2), ?_, ?_⟩
    · have h1 : γ (1 / 2) ∈ γ '' Set.Ioo (-1 : ℝ) 1 := ⟨1 / 2, by norm_num, rfl⟩
      rw [hγrange] at h1
      rw [hLdef]
      exact h1.1
    · intro hxy
      have h0 : (1 / 2 : ℝ) = 0 := hinj (by rw [hγ0]; exact hxy.symm)
      norm_num at h0
  exact hLdef.symm ▸ existsSimpleClosedCurveOfLocallyArc hcompact hpre hnt hloc

/-- **The frontier curve of a union of open balls.** -/
theorem frontierCurveOfOpenBallUnionAux (P : Finset ℂ) {r : ℝ} (hr : 0 < r) {z : ℂ}
    (hz : z ∈ ⋃ w ∈ P, Metric.ball w r) :
    ∃ γ : ℝ → ℂ, Continuous γ ∧ Function.Periodic γ (2 * Real.pi) ∧
      Set.InjOn γ (Set.Ico 0 (2 * Real.pi)) ∧
      Set.range γ ⊆ frontier (⋃ w ∈ P, Metric.closedBall w r) ∧
      Bornology.IsBounded (connectedComponentIn (Set.range γ)ᶜ z) := by
  classical
  set U : Set ℂ := ⋃ w ∈ P, Metric.ball w r with hUdef
  set B : Set ℂ := connectedComponentIn U z with hBdef
  set Q : Finset ℂ := P.filter (fun w => Metric.ball w r ⊆ B) with hQdef
  have hzB : z ∈ B := mem_connectedComponentIn hz
  have hBpre : IsPreconnected B := isPreconnected_connectedComponentIn
  have hballsub : ∀ w ∈ P, (Metric.ball w r ∩ B).Nonempty → Metric.ball w r ⊆ B := by
    rintro w hwP ⟨y, hyw, hyB⟩
    have hpre : IsPreconnected (Metric.ball w r ∪ B) :=
      IsPreconnected.union y hyw hyB Metric.isPreconnected_ball hBpre
    have hsubU : Metric.ball w r ∪ B ⊆ U := by
      rintro t (ht | ht)
      · exact Set.mem_iUnion₂.mpr ⟨w, hwP, ht⟩
      · exact connectedComponentIn_subset U z ht
    exact fun t ht => hpre.subset_connectedComponentIn (Or.inr hzB) hsubU (Or.inl ht)
  have hBeq : B = ⋃ w ∈ Q, Metric.ball w r := by
    refine Subset.antisymm ?_ ?_
    · intro y hy
      obtain ⟨w, hwP, hyw⟩ := Set.mem_iUnion₂.mp (hUdef ▸ connectedComponentIn_subset U z hy)
      exact Set.mem_iUnion₂.mpr
        ⟨w, Finset.mem_filter.mpr ⟨hwP, hballsub w hwP ⟨y, hyw, hy⟩⟩, hyw⟩
    · intro y hy
      obtain ⟨w, hw, hyw⟩ := Set.mem_iUnion₂.mp hy
      exact (Finset.mem_filter.mp hw).2 hyw
  have hQne : Q.Nonempty := by
    obtain ⟨w, hwP, hzw⟩ := Set.mem_iUnion₂.mp hz
    exact ⟨w, Finset.mem_filter.mpr ⟨hwP, hballsub w hwP ⟨z, hzw, hzB⟩⟩⟩
  have hQclosed : IsClosed (⋃ w ∈ Q, Metric.closedBall w r) :=
    isClosed_biUnion_finset fun w _ => Metric.isClosed_closedBall
  set M : ℝ := Q.sup' hQne (fun w => ‖w‖ + r) + 1 with hMdef
  have hM : ∀ w ∈ Q, ‖w‖ + r < M := by
    intro w hw
    have := Finset.le_sup' (fun w => ‖w‖ + r) hw
    rw [hMdef]; linarith
  have hMpos : 0 < M := by
    obtain ⟨w₀, hw₀⟩ := hQne
    have h1 := hM w₀ hw₀
    have h2 : (0 : ℝ) ≤ ‖w₀‖ + r := by positivity
    linarith
  set q : ℂ := ((M : ℝ) : ℂ) with hqdef
  have hqnorm : ∀ t : ℝ, 0 ≤ t → ‖q + (t : ℂ)‖ = M + t := by
    intro t ht
    have h1 : q + (t : ℂ) = (((M : ℝ) + t : ℝ) : ℂ) := by
      rw [hqdef]
      push_cast
      ring
    rw [h1, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith [hMpos, ht])]
  have hq : q ∉ ⋃ w ∈ Q, Metric.closedBall w r := by
    intro h
    obtain ⟨w, hw, hqw⟩ := Set.mem_iUnion₂.mp h
    rw [Metric.mem_closedBall, dist_eq_norm] at hqw
    have h1 : ‖q‖ ≤ ‖w‖ + r := by
      calc ‖q‖ = ‖(q - w) + w‖ := by ring_nf
        _ ≤ ‖q - w‖ + ‖w‖ := norm_add_le _ _
        _ ≤ r + ‖w‖ := by linarith
        _ = ‖w‖ + r := by ring
    have hq0 : ‖q‖ = M := by simpa using hqnorm 0 le_rfl
    rw [hq0] at h1
    linarith [hM w hw]
  have hseg : ∀ t : ℝ, 0 ≤ t → q + (t : ℂ) ∈ ((⋃ w ∈ Q, Metric.closedBall w r)ᶜ) := by
    intro t ht
    rw [Set.mem_compl_iff]
    intro hmem
    obtain ⟨w, hw, hqw⟩ := Set.mem_iUnion₂.mp hmem
    rw [Metric.mem_closedBall, dist_eq_norm] at hqw
    have h2 : M + t ≤ ‖w‖ + r := by
      calc M + t = ‖q + (t : ℂ)‖ := (hqnorm t ht).symm
        _ = ‖(q + (t : ℂ) - w) + w‖ := by ring_nf
        _ ≤ ‖(q + (t : ℂ) - w)‖ + ‖w‖ := norm_add_le _ _
        _ ≤ r + ‖w‖ := by linarith
        _ = ‖w‖ + r := by ring
    linarith [hM w hw]
  have hray : ∀ t : ℝ, 0 ≤ t →
      q + (t : ℂ) ∈ connectedComponentIn ((⋃ w ∈ Q, Metric.closedBall w r)ᶜ) q := by
    intro t ht
    have hpre : IsPreconnected ((fun s : ℝ => q + (s : ℂ)) '' Set.Icc 0 t) :=
      isPreconnected_Icc.image _ (by fun_prop)
    have hsub : ((fun s : ℝ => q + (s : ℂ)) '' Set.Icc 0 t) ⊆
        ((⋃ w ∈ Q, Metric.closedBall w r)ᶜ) := by
      rintro y ⟨s, hs, rfl⟩
      exact hseg s hs.1
    have hqmem : q ∈ ((fun s : ℝ => q + (s : ℂ)) '' Set.Icc 0 t) :=
      ⟨0, Set.left_mem_Icc.mpr ht, by simp⟩
    exact hpre.subset_connectedComponentIn hqmem hsub
      ⟨t, Set.right_mem_Icc.mpr ht, by simp⟩
  have hfarPre : IsPreconnected {y : ℂ | M + 1 < ‖y‖} := by
    have h := Work.Smooth.SphereJordan.isPreconnected_compl_closedBall (0 : ℂ)
      (by linarith : (0 : ℝ) < M + 1)
    have heq : (Metric.closedBall (0 : ℂ) (M + 1))ᶜ = {y : ℂ | M + 1 < ‖y‖} := by
      ext y
      simp [Metric.mem_closedBall, dist_zero_right, not_le]
    rwa [heq] at h
  have hfar : ∀ y : ℂ, M + 1 < ‖y‖ →
      y ∈ connectedComponentIn ((⋃ w ∈ Q, Metric.closedBall w r)ᶜ) q := by
    intro y hy
    have hrayPre : IsPreconnected ((fun s : ℝ => q + (s : ℂ)) '' Set.Ici 0) :=
      isPreconnected_Ici.image _ (by fun_prop)
    have hmeet1 : q + (2 : ℂ) ∈ {y : ℂ | M + 1 < ‖y‖} := by
      have h2 : ‖q + (2 : ℂ)‖ = M + 2 := hqnorm 2 (by norm_num)
      simp only [Set.mem_ofPred_eq]
      linarith
    have hmeet2 : q + (2 : ℂ) ∈ ((fun s : ℝ => q + (s : ℂ)) '' Set.Ici 0) :=
      ⟨2, by norm_num, by simp⟩
    have hpre : IsPreconnected
        ({y : ℂ | M + 1 < ‖y‖} ∪ ((fun s : ℝ => q + (s : ℂ)) '' Set.Ici 0)) :=
      IsPreconnected.union (q + (2 : ℂ)) hmeet1 hmeet2 hfarPre hrayPre
    have hsub : ({y : ℂ | M + 1 < ‖y‖} ∪ ((fun s : ℝ => q + (s : ℂ)) '' Set.Ici 0)) ⊆
        ((⋃ w ∈ Q, Metric.closedBall w r)ᶜ) := by
      rintro z' (hz' | hz')
      · rw [Set.mem_compl_iff]
        intro hmem
        obtain ⟨w, hw, hzw⟩ := Set.mem_iUnion₂.mp hmem
        rw [Metric.mem_closedBall, dist_eq_norm] at hzw
        have h1 : ‖z'‖ ≤ ‖z' - w‖ + ‖w‖ := by
          calc ‖z'‖ = ‖(z' - w) + w‖ := by ring_nf
            _ ≤ ‖z' - w‖ + ‖w‖ := norm_add_le _ _
        rw [Set.mem_ofPred_eq] at hz'
        linarith [hM w hw]
      · obtain ⟨s, hs, rfl⟩ := hz'
        exact hseg s (by simpa using hs)
    exact hpre.subset_connectedComponentIn (Or.inr ⟨0, by norm_num, by simp⟩) hsub (Or.inl hy)
  have hunb : ¬ Bornology.IsBounded (connectedComponentIn ((⋃ w ∈ Q, Metric.closedBall w r)ᶜ) q) := by
    intro hb
    obtain ⟨N, hN⟩ := hb.exists_norm_le
    have hq0 : ‖q‖ = M := by simpa using hqnorm 0 le_rfl
    have hNM : M ≤ N := by
      have h := hN q (mem_connectedComponentIn hq)
      rwa [hq0] at h
    have hmem : q + ((N + 1 : ℝ) : ℂ) ∈
        connectedComponentIn ((⋃ w ∈ Q, Metric.closedBall w r)ᶜ) q := hray _ (by linarith)
    have h2 := hN _ hmem
    rw [hqnorm _ (by linarith)] at h2
    linarith
  obtain ⟨γ, hcont, hper, hinj, hrange⟩ :=
    jordanCurveFrontierComponent hr hQne hq (hBeq ▸ hBpre) hunb
  refine ⟨γ, hcont, hper, hinj, ?_, ?_⟩
  · rw [hrange]
    have h1 : frontier (connectedComponentIn ((⋃ w ∈ Q, Metric.closedBall w r)ᶜ) q)
        ⊆ frontier (⋃ w ∈ Q, Metric.closedBall w r) := frontier_componentIn_subset hQclosed
    have hQsub' : ∀ w ∈ Q, w ∈ P := fun w hw => (Finset.mem_filter.mp hw).1
    have hQmem' : ∀ w ∈ Q, Metric.ball w r ⊆ B := fun w hw => (Finset.mem_filter.mp hw).2
    have hQmax' : ∀ w ∈ P, Metric.ball w r ⊆ B → w ∈ Q :=
      fun w hwP hwB => Finset.mem_filter.mpr ⟨hwP, hwB⟩
    have h2 : frontier (⋃ w ∈ Q, Metric.closedBall w r) ⊆
        frontier (⋃ w ∈ P, Metric.closedBall w r) :=
      frontierComponentUnionSubset P B hr hBdef Q hQsub' hQmem' hQmax'
    exact h1.trans h2
  · rw [hrange]
    set O : Set ℂ := connectedComponentIn ((⋃ w ∈ Q, Metric.closedBall w r)ᶜ) q with hOdef
    have hOopen : IsOpen O := hQclosed.isOpen_compl.connectedComponentIn
    have hzBunion : z ∈ ⋃ w ∈ Q, Metric.ball w r := hBeq ▸ hzB
    have hzO : z ∉ O := by
      intro h
      obtain ⟨w, hw, hzw⟩ := Set.mem_iUnion₂.mp hzBunion
      exact (connectedComponentIn_subset _ _ h)
        (Set.mem_iUnion₂.mpr ⟨w, hw, Metric.ball_subset_closedBall hzw⟩)
    have hzfr : z ∉ frontier (⋃ w ∈ Q, Metric.closedBall w r) := by
      intro h
      refine h.2 ?_
      obtain ⟨w, hw, hzw⟩ := Set.mem_iUnion₂.mp hzBunion
      have h2 : Metric.ball w r ⊆ interior (⋃ w ∈ Q, Metric.closedBall w r) :=
        (Metric.ball_subset_interior_closedBall (x := w) (ε := r)).trans
          (interior_mono (fun y hy => Set.mem_iUnion₂.mpr ⟨w, hw, hy⟩))
      exact h2 hzw
    have hzω : z ∉ frontier O := fun h => hzfr (frontier_componentIn_subset hQclosed h)
    have hzclO : z ∉ closure O := by
      have hclos : closure O = O ∪ frontier O := by
        rw [closure_eq_interior_union_frontier, hOopen.interior_eq]
      rw [hclos]
      rintro (h | h)
      · exact hzO h
      · exact hzω h
    refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := M + 1)).subset ?_
    intro y hy
    by_contra hyc
    have hy' : M + 1 < ‖y‖ := by
      rw [Metric.mem_closedBall, dist_zero_right, not_le] at hyc
      exact hyc
    have hyO : y ∈ O := hfar y hy'
    have hdec : (frontier O)ᶜ = O ∪ (closure O)ᶜ := by
      rw [hOopen.frontier_eq]
      ext x
      constructor
      · intro hx
        by_cases hxO : x ∈ O
        · exact Or.inl hxO
        · exact Or.inr fun hxc => hx ⟨hxc, hxO⟩
      · rintro (hx | hx)
        · exact fun h => h.2 hx
        · exact fun h => hx h.1
    have hdisj : Disjoint O (closure O)ᶜ := by
      rw [Set.disjoint_left]
      intro x hxO hx
      exact hx (subset_closure hxO)
    have hcase : connectedComponentIn (frontier O)ᶜ z ⊆ O ∨
        connectedComponentIn (frontier O)ᶜ z ⊆ (closure O)ᶜ :=
      IsPreconnected.subset_or_subset hOopen isClosed_closure.isOpen_compl hdisj
        (by rw [hdec]; exact connectedComponentIn_subset _ _) isPreconnected_connectedComponentIn
    rcases hcase with hc | hc
    · exact absurd (hc (mem_connectedComponentIn hzω)) hzO
    · exact absurd (subset_closure hyO) (hc hy)

end

end Work.Smooth.SphereJordan
