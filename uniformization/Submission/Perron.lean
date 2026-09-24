import ChallengeDeps
import Submission.RiemannSurface
import Submission.Commons.Analysis.Complex.Dirichlet.dirichlet_ball
import Submission.Commons.Analysis.Complex.Harmonic.harmonic_le_of_boundary_le
import Submission.Commons.Analysis.Complex.Harmonic.harmonic_eqOn_of_isMaxOn_open
import Submission.Commons.Analysis.Complex.Harmonic.harmonicOnNhd_of_monotone_pointwise_limit_ball
import Submission.Commons.Analysis.Complex.Harmonic.max_principle_localSubMeanValue

/-!
# Perron's theorem on a Riemann surface (Hubbard, Proposition 1.2.3)

If `F` is a nonempty Perron family bounded by `M` (Hubbard's Definition 1.2.2), then the upper
envelope `F̄ = sup F` is harmonic on `X`.

This module develops the machinery: the running-maxima sequence realizing the envelope, the
harmonic replacement in a chart disc, Harnack's convergence principle, and the maximum principle.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

noncomputable section

open Filter Set
open Classical

namespace Submission

/-! ## Basic consequences of the Perron family axioms -/

section Basic

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

theorem perronFamily_nonempty {F : Set (X → ℝ)} {M : ℝ} (h : IsPerronFamily F M) :
    F.Nonempty := h.1

theorem perronFamily_subharmonic {F : Set (X → ℝ)} {M : ℝ} (h : IsPerronFamily F M)
    {f : X → ℝ} (hf : f ∈ F) : SubharmonicOnX f univ := h.2.1 f hf

theorem perronFamily_bound {F : Set (X → ℝ)} {M : ℝ} (h : IsPerronFamily F M)
    {f : X → ℝ} (hf : f ∈ F) (x : X) : f x ≤ M := h.2.2.1 f hf x

theorem perronFamily_sup_mem {F : Set (X → ℝ)} {M : ℝ} (h : IsPerronFamily F M)
    {f g : X → ℝ} (hf : f ∈ F) (hg : g ∈ F) : max f g ∈ F := h.2.2.2.1 f hf g hg

theorem perronFamily_replace_mem {F : Set (X → ℝ)} {M : ℝ} (h : IsPerronFamily F M)
    {f : X → ℝ} (hf : f ∈ F) (c : OpenPartialHomeomorph X ℂ) (a : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hsub : Metric.closedBall a ρ ⊆ c.target) (u : ℂ → ℝ)
    (hu : ∀ z : ℂ, ‖z - a‖ < ρ → InnerProductSpace.HarmonicAt u z)
    (hG : ContinuousOn (gluedBall u (fun w => f (c.symm w)) a ρ) (Metric.closedBall a ρ)) :
    replaceOnDisc c a ρ u f ∈ F :=
  h.2.2.2.2 f hf c a ρ hρ hsub u hu hG

/-- The upper envelope is bounded above by `M`. -/
theorem upperEnvelope_le {F : Set (X → ℝ)} {M : ℝ} (hne : F.Nonempty)
    (hbd : ∀ f ∈ F, ∀ x : X, f x ≤ M) (x : X) : upperEnvelope F x ≤ M := by
  rw [upperEnvelope]
  refine csSup_le (hne.image _) ?_
  rintro y ⟨f, hf, rfl⟩
  exact hbd f hf x

/-- The upper envelope is bounded below by `-M`. -/
theorem neg_le_upperEnvelope {F : Set (X → ℝ)} {M : ℝ} (hne : F.Nonempty)
    (hub : ∀ f ∈ F, ∀ x : X, f x ≤ M) (hlb : ∀ f ∈ F, ∀ x : X, -M ≤ f x) (x : X) :
    -M ≤ upperEnvelope F x := by
  rw [upperEnvelope]
  obtain ⟨f, hf⟩ := hne
  have hbdd : BddAbove (F.image (fun f : X → ℝ => f x)) :=
    ⟨M, by rintro y ⟨g, hg, rfl⟩; exact hub g hg x⟩
  exact (hlb f hf x).trans (le_csSup hbdd ⟨f, hf, rfl⟩)

theorem perronFamily_upperEnvelope_le {F : Set (X → ℝ)} {M : ℝ} (h : IsPerronFamily F M)
    (x : X) : upperEnvelope F x ≤ M :=
  upperEnvelope_le (perronFamily_nonempty h) (fun _f hf x => perronFamily_bound h hf x) x

theorem perronFamily_mem_le_upperEnvelope {F : Set (X → ℝ)} {M : ℝ} (h : IsPerronFamily F M)
    {f : X → ℝ} (hf : f ∈ F) (x : X) : f x ≤ upperEnvelope F x := by
  rw [upperEnvelope]
  exact le_csSup ⟨M, by rintro y ⟨g, hg, rfl⟩; exact perronFamily_bound h hg x⟩
    ⟨f, hf, rfl⟩

end Basic

/-! ## An increasing sequence in `F` realizing the envelope at a point -/

section Sequence

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] {F : Set (X → ℝ)} {M : ℝ}

/-- Given a nonempty Perron family, there is a pointwise increasing sequence in it whose values at
a fixed point converge to (and have supremum) the value of the upper envelope there. -/
theorem perronFamily_exists_incr_seq (h : IsPerronFamily F M) (z : X) :
    ∃ s : ℕ → X → ℝ, (∀ n, s n ∈ F) ∧ (∀ n (x : X), s n x ≤ s (n + 1) x) ∧
      (⨆ n, s n z) = upperEnvelope F z := by
  have hSne : (F.image (fun f : X → ℝ => f z)).Nonempty := (perronFamily_nonempty h).image _
  have hSbdd : BddAbove (F.image (fun f : X → ℝ => f z)) :=
    ⟨M, by rintro y ⟨f, hf, rfl⟩; exact perronFamily_bound h hf z⟩
  obtain ⟨u, humono, hutend, humem⟩ := exists_seq_tendsto_sSup hSne hSbdd
  have humem' : ∀ n : ℕ, ∃ f ∈ F, f z = u n := fun n => by
    have := humem n
    rw [Set.mem_image] at this
    exact this
  choose f hfF hfz using humem'
  have hBddU : BddAbove (Set.range u) :=
    ⟨M, by rintro y ⟨n, rfl⟩; rw [← hfz n]; exact perronFamily_bound h (hfF n) z⟩
  have husup : (⨆ n, u n) = sSup (F.image (fun f : X → ℝ => f z)) := by
    refine le_antisymm (ciSup_le fun n => le_csSup hSbdd (humem n)) ?_
    have h2 : Tendsto u atTop (nhds (⨆ n, u n)) := tendsto_atTop_ciSup humono hBddU
    exact le_of_eq (tendsto_nhds_unique hutend h2)
  let g : ℕ → X → ℝ := fun n =>
    Nat.rec (f 0) (fun k (gk : X → ℝ) => max gk (f (k + 1))) n
  have hg0 : g 0 = f 0 := rfl
  have hgsucc : ∀ n : ℕ, g (n + 1) = max (g n) (f (n + 1)) := fun n => rfl
  have hgF : ∀ n, g n ∈ F := by
    intro n
    induction n with
    | zero => rw [hg0]; exact hfF 0
    | succ n ih => rw [hgsucc]; exact perronFamily_sup_mem h ih (hfF (n + 1))
  have hgmono : ∀ n (x : X), g n x ≤ g (n + 1) x := by
    intro n x
    rw [hgsucc]
    exact le_max_left _ _
  have hgle : ∀ n (x : X), g n x ≤ upperEnvelope F x := by
    intro n x
    induction n with
    | zero => rw [hg0]; exact perronFamily_mem_le_upperEnvelope h (hfF 0) x
    | succ n ih =>
      rw [hgsucc]
      exact max_le ih (perronFamily_mem_le_upperEnvelope h (hfF (n + 1)) x)
  have hgelim : ∀ n, u n ≤ g n z := by
    intro n
    induction n with
    | zero => rw [hg0, hfz 0]
    | succ n ih =>
      have : (max (g n) (f (n + 1))) z = max (g n z) (f (n + 1) z) := rfl
      rw [hgsucc, this, hfz (n + 1)]
      exact le_max_right _ _
  refine ⟨g, hgF, hgmono, ?_⟩
  have hBddG : BddAbove (Set.range (fun n => g n z)) :=
    ⟨upperEnvelope F z, by rintro y ⟨n, rfl⟩; exact hgle n z⟩
  refine le_antisymm (ciSup_le fun n => hgle n z) ?_
  calc upperEnvelope F z = sSup (F.image (fun f : X → ℝ => f z)) := rfl
    _ = ⨆ n, u n := husup.symm
    _ ≤ ⨆ n, g n z := ciSup_le fun n => (hgelim n).trans (le_ciSup hBddG n)

end Sequence

/-! ## The harmonic replacement in a chart disc -/

section ReplacementAlg

variable {X : Type*} [TopologicalSpace X]

/-- The glued function is additive in the pair of inner and outer functions. -/
theorem gluedBall_sub (u u' F F' : ℂ → ℝ) (a : ℂ) (ρ : ℝ) :
    gluedBall u F a ρ - gluedBall u' F' a ρ = gluedBall (u - u') (F - F') a ρ := by
  funext z
  rw [Pi.sub_apply, gluedBall_apply, gluedBall_apply, gluedBall_apply]
  by_cases h : z ∈ Metric.ball a ρ
  · rw [if_pos h, if_pos h, if_pos h]; rfl
  · rw [if_neg h, if_neg h, if_neg h]; rfl

/-- The harmonic replacement is additive in the pair `(u, f)`. -/
theorem replaceOnDisc_sub {c : OpenPartialHomeomorph X ℂ} {a : ℂ} {ρ : ℝ}
    (u u' : ℂ → ℝ) (f f' : X → ℝ) :
    replaceOnDisc c a ρ u f - replaceOnDisc c a ρ u' f' = replaceOnDisc c a ρ (u - u') (f - f') := by
  funext x
  rw [Pi.sub_apply, replaceOnDisc, replaceOnDisc, replaceOnDisc]
  by_cases h : x ∈ chartBall c a ρ
  · rw [if_pos h, if_pos h, if_pos h]; rfl
  · rw [if_neg h, if_neg h, if_neg h]; rfl

end ReplacementAlg

section Engine

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- The pullback of the replacement by the chart is harmonic inside the disc. -/
theorem harmonicAt_replaceOnDisc_pullback {c : OpenPartialHomeomorph X ℂ} {a : ℂ} {ρ : ℝ}
    {u : ℂ → ℝ} {f : X → ℝ} (hsub : Metric.ball a ρ ⊆ c.target)
    (hu : ∀ z : ℂ, ‖z - a‖ < ρ → InnerProductSpace.HarmonicAt u z)
    {z : ℂ} (hz : z ∈ Metric.ball a ρ) :
    InnerProductSpace.HarmonicAt (fun w => replaceOnDisc c a ρ u f (c.symm w)) z := by
  have hz' : ‖z - a‖ < ρ := by simpa [Metric.mem_ball, dist_eq_norm] using hz
  refine (InnerProductSpace.harmonicAt_congr_nhds ?_).mpr (hu z hz')
  filter_upwards [Metric.isOpen_ball.mem_nhds hz] with w hw
  exact replaceOnDisc_pullback_of_mem hsub hw

/-- **Comparison of two Dirichlet solutions.**  If `u` is harmonic on the disc with glued
boundary data `F`, `v` likewise with `G`, and `F ≤ G` on the boundary circle, then `u ≤ v` on the
whole disc. -/
theorem harmonic_le_of_gluedBall_le {a : ℂ} {ρ : ℝ} (hρ : 0 < ρ) {u v F G : ℂ → ℝ}
    (hu : ∀ z : ℂ, ‖z - a‖ < ρ → InnerProductSpace.HarmonicAt u z)
    (hv : ∀ z : ℂ, ‖z - a‖ < ρ → InnerProductSpace.HarmonicAt v z)
    (hGu : ContinuousOn (gluedBall u F a ρ) (Metric.closedBall a ρ))
    (hGv : ContinuousOn (gluedBall v G a ρ) (Metric.closedBall a ρ))
    (hle : ∀ z ∈ Metric.sphere a ρ, F z ≤ G z) :
    ∀ z : ℂ, ‖z - a‖ < ρ → u z ≤ v z := by
  have hFb : ∀ z : ℂ, z ∈ Metric.sphere a ρ → (fun z : ℂ => F z - G z) z ≤ 0 := by
    intro z hz
    exact sub_nonpos.mpr (hle z hz)
  have hu' : ∀ z : ℂ, ‖z - a‖ < ρ → InnerProductSpace.HarmonicAt (fun z : ℂ => u z - v z) z :=
    fun z hz => InnerProductSpace.HarmonicAt.sub (hu z hz) (hv z hz)
  have huc : ContinuousOn (fun z : ℂ =>
      if ‖z - a‖ < ρ then (fun z : ℂ => u z - v z) z else (fun z : ℂ => F z - G z) z)
      (Metric.closedBall a ρ) := by
    have heq : (fun z : ℂ =>
        if ‖z - a‖ < ρ then (fun z : ℂ => u z - v z) z else (fun z : ℂ => F z - G z) z)
        = gluedBall u F a ρ - gluedBall v G a ρ := by
      funext z
      rw [Pi.sub_apply, gluedBall_apply, gluedBall_apply]
      simp only [Metric.mem_ball, dist_eq_norm]
      by_cases h : ‖z - a‖ < ρ
      · rw [if_pos h, if_pos h, if_pos h]
      · rw [if_neg h, if_neg h, if_neg h]
    rw [heq]
    exact hGu.sub hGv
  have h := Commons.Analysis.Complex.Harmonic.harmonic_le_of_boundary_le (c := a) (R := ρ)
    (M := 0) hρ hFb hu' huc
  intro z hz
  exact sub_nonpos.mp (h z hz)

/-- **The Dirichlet solution dominates the subharmonic boundary data.**  If `f` is subharmonic on
`X` (measured in a preferred chart `chartAt ℂ z₀`) and `u` is the harmonic extension of the
boundary values `f ∘ (chartAt ℂ z₀).symm` on `sphere a ρ`, then the harmonic replacement
`replaceOnDisc (chartAt ℂ z₀) a ρ u f` dominates `f` pointwise. -/
theorem le_replaceOnDisc {f : X → ℝ} (hf : SubharmonicOnX f univ) {z₀ : X} {a : ℂ} {ρ : ℝ}
    (hρ : 0 < ρ) (hsub : Metric.closedBall a ρ ⊆ (chartAt ℂ z₀).target) {u : ℂ → ℝ}
    (hu : ∀ z : ℂ, ‖z - a‖ < ρ → InnerProductSpace.HarmonicAt u z)
    (hG : ContinuousOn (gluedBall u (fun w => f ((chartAt ℂ z₀).symm w)) a ρ)
      (Metric.closedBall a ρ)) :
    ∀ y : X, f y ≤ replaceOnDisc (chartAt ℂ z₀) a ρ u f y := by
  set c : OpenPartialHomeomorph X ℂ := chartAt ℂ z₀ with hc
  have hsub' : Metric.closedBall a ρ ⊆ c.target := by rwa [hc]
  have hball : Metric.ball a ρ ⊆ c.target := fun z hz => hsub' (Metric.ball_subset_closedBall hz)
  have hG' : ContinuousOn (gluedBall u (fun w => f (c.symm w)) a ρ) (Metric.closedBall a ρ) := by
    rwa [hc] at hG
  have hfcont : Continuous f := continuousOn_univ.mp hf.1
  set v : ℂ → ℝ := fun w => f (c.symm w) with hv
  set U : ℂ → ℝ := gluedBall u v a ρ with hU
  have hU_cont : ContinuousOn U (Metric.closedBall a ρ) := by rw [hU, hv]; exact hG'
  have hv_cont : ContinuousOn v (Metric.closedBall a ρ) := by
    rw [hv]
    exact hfcont.continuousOn.comp (c.continuousOn_symm.mono hsub') (fun z _ => mem_univ _)
  -- the local mean value inequality for `v - U`
  have hloc : ∀ p ∈ Metric.ball a ρ, ∃ ε : ℝ, 0 < ε ∧ Metric.ball p ε ⊆ Metric.ball a ρ ∧
      ∀ r : ℝ, 0 < r → Metric.closedBall p r ⊆ Metric.ball p ε →
        (v - U) p ≤ Real.circleAverage (v - U) p r := by
    intro p hp
    have hptarget : p ∈ c.target := hball hp
    have hsubh : SubharmonicAtChart f c (c.symm p) :=
      SubharmonicOnX.subharmonicAtChart hf (mem_univ _) (c.map_target hptarget)
    rw [SubharmonicAtChart] at hsubh
    obtain ⟨-, ρ', hρ', ht', hcont', hmvp'⟩ := hsubh
    have hcp : c (c.symm p) = p := c.right_inv hptarget
    rw [hcp] at ht' hcont' hmvp'
    have hdist : 0 < ρ - dist p a := sub_pos.mpr (by simpa [Metric.mem_ball] using hp)
    refine ⟨min ρ' (ρ - dist p a), lt_min hρ' hdist, ?_, ?_⟩
    · exact (Metric.ball_subset_ball (min_le_right _ _)).trans (ball_subset_ball_of_mem hp)
    · intro r hr hpr
      have hr' : 0 < r := hr
      have hpr' : Metric.closedBall p r ⊆ Metric.ball p ρ' :=
        hpr.trans (Metric.ball_subset_ball (min_le_left _ _))
      have hprball : Metric.closedBall p r ⊆ Metric.ball a ρ :=
        hpr.trans (Metric.ball_subset_ball (min_le_right _ _) |>.trans (ball_subset_ball_of_mem hp))
      have hvle : v p ≤ Real.circleAverage v p r := hmvp' p (Metric.mem_ball_self hρ') r hr
        (by simpa using hpr')
      have hUharm : InnerProductSpace.HarmonicOnNhd U (Metric.closedBall p |r|) := by
        rw [abs_of_pos hr]
        intro q hq
        have hqball : q ∈ Metric.ball a ρ := hprball hq
        have hq' : ‖q - a‖ < ρ := by simpa [Metric.mem_ball, dist_eq_norm] using hqball
        refine (InnerProductSpace.harmonicAt_congr_nhds ?_).mpr (hu q hq')
        filter_upwards [Metric.isOpen_ball.mem_nhds hqball] with w hw
        rw [hU]; exact gluedBall_of_mem hw
      have havgU : Real.circleAverage U p r = U p :=
        InnerProductSpace.HarmonicOnNhd.circleAverage_eq hUharm
      have hvI : CircleIntegrable v p r :=
        (hv_cont.mono (fun z hz =>
          Metric.ball_subset_closedBall (hprball (Metric.sphere_subset_closedBall hz)))).circleIntegrable
          (le_of_lt hr)
      have hUI : CircleIntegrable U p r :=
        (hU_cont.mono (fun z hz =>
          Metric.ball_subset_closedBall (hprball (Metric.sphere_subset_closedBall hz)))).circleIntegrable (le_of_lt hr)
      have : Real.circleAverage (v - U) p r = Real.circleAverage v p r - Real.circleAverage U p r :=
        Real.circleAverage_sub hvI hUI
      rw [Pi.sub_apply, this, havgU]
      linarith
  have hbd : ∀ z ∈ closure (Metric.ball a ρ), z ∉ Metric.ball a ρ → (v - U) z ≤ 0 := by
    rw [closure_ball a (ne_of_gt hρ)]
    intro z hz hznot
    have hzU : U z = v z := by rw [hU]; exact gluedBall_of_not_mem hznot
    rw [Pi.sub_apply, hzU, sub_self]
  have hcont' : ContinuousOn (v - U) (closure (Metric.ball a ρ)) := by
    rw [closure_ball a (ne_of_gt hρ)]
    exact hv_cont.sub hU_cont
  have hle0 : ∀ z ∈ Metric.ball a ρ, v z - U z ≤ 0 :=
    Commons.Analysis.Complex.Harmonic.max_principle_localSubMeanValue Metric.isOpen_ball
      Metric.isPreconnected_ball Metric.isBounded_ball hcont' hloc hbd
  intro y
  by_cases hy : y ∈ chartBall c a ρ
  · have hysrc : y ∈ c.source := hy.1
    have hyball : c y ∈ Metric.ball a ρ := hy.2
    rw [hc, replaceOnDisc_of_mem_chartBall hy]
    have h1 : f y = v (c y) := by rw [hv]; simp only; rw [c.left_inv hysrc]
    rw [h1]
    have h2 : v (c y) ≤ U (c y) := by linarith [hle0 (c y) hyball]
    have h3 : U (c y) = u (c y) := by rw [hU]; exact gluedBall_of_mem hyball
    rw [h3] at h2
    exact h2
  · rw [hc]
    rw [replaceOnDisc_of_not_mem_chartBall hy]

end Engine

/-! ## Notation for the replacement in the chart at a point -/

section Notation

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- The harmonic replacement of `f` in the chart disc at `z₀`. -/
abbrev chartRep (z₀ : X) (a : ℂ) (ρ : ℝ) (u : ℂ → ℝ) (f : X → ℝ) : X → ℝ :=
  replaceOnDisc (chartAt ℂ z₀) a ρ u f

/-- The pullback of `chartRep` by the chart at `z₀`. -/
abbrev chartRepPull (z₀ : X) (a : ℂ) (ρ : ℝ) (u : ℂ → ℝ) (f : X → ℝ) : ℂ → ℝ :=
  fun w => replaceOnDisc (chartAt ℂ z₀) a ρ u f ((chartAt ℂ z₀).symm w)

end Notation

/-- The Dirichlet problem on a disc, with the glued function written using `Metric.ball`
(the form in which `gluedBall` is stated). -/
theorem dirichlet_ball_glued {c : ℂ} {R : ℝ} (hR : 0 < R) {F : ℂ → ℝ}
    (hF : ContinuousOn F (Metric.sphere c R)) :
    ∃ u : ℂ → ℝ, (∀ z : ℂ, ‖z - c‖ < R → InnerProductSpace.HarmonicAt u z) ∧
      ContinuousOn (fun z : ℂ => if z ∈ Metric.ball c R then u z else F z)
        (Metric.closedBall c R) := by
  obtain ⟨u, h1, h2⟩ :=
    Commons.Analysis.Complex.Dirichlet.dirichlet_ball (c := c) (R := R) hR hF
  exact ⟨u, h1, h2.congr (fun z _ => by simp only [Metric.mem_ball, dist_eq_norm])⟩

/-! ## Perron's theorem -/

section Perron

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **Perron's theorem** (Hubbard, Proposition 1.2.3): the upper envelope of a nonempty Perron
family bounded by `M` is harmonic on `X`. -/
theorem IsPerronFamily.upperEnvelope_harmonic {F : Set (X → ℝ)} {M : ℝ}
    (hP : IsPerronFamily F M) : HarmonicOnX (upperEnvelope F) univ := by
  intro z₀ _
  let a : ℂ := (chartAt ℂ z₀) z₀
  have hsrc : z₀ ∈ (chartAt ℂ z₀).source := mem_chart_source ℂ z₀
  have hsymm_a : (chartAt ℂ z₀).symm a = z₀ := (chartAt ℂ z₀).left_inv hsrc
  have hmemtgt : a ∈ (chartAt ℂ z₀).target := (chartAt ℂ z₀).map_source hsrc
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp ((chartAt ℂ z₀).open_target.mem_nhds hmemtgt)
  obtain ⟨ρ, hρ, hsub⟩ : ∃ ρ : ℝ, 0 < ρ ∧ Metric.closedBall a ρ ⊆ (chartAt ℂ z₀).target :=
    ⟨ε / 2, half_pos hε, (Metric.closedBall_subset_ball (by linarith)).trans hεsub⟩
  have hball_target : Metric.ball a ρ ⊆ (chartAt ℂ z₀).target :=
    fun z hz => hsub (Metric.ball_subset_closedBall hz)
  -- the increasing sequence realizing the envelope at `z₀`
  obtain ⟨s, hsF, hsmono, hssup⟩ := perronFamily_exists_incr_seq hP z₀
  have hcont_s : ∀ n, ContinuousOn (fun w => s n ((chartAt ℂ z₀).symm w)) (Metric.sphere a ρ) := by
    intro n
    have hsc : Continuous (s n) := continuousOn_univ.mp (perronFamily_subharmonic hP (hsF n)).1
    refine hsc.continuousOn.comp ((chartAt ℂ z₀).continuousOn_symm.mono ?_) (fun z _ => mem_univ _)
    exact fun z hz => hsub (Metric.sphere_subset_closedBall hz)
  choose u hu_harm hu_cont using fun n =>
    dirichlet_ball_glued (c := a) (R := ρ) hρ (F := fun w => s n ((chartAt ℂ z₀).symm w))
      (hcont_s n)
  have hrepF : ∀ n, chartRep z₀ a ρ (u n) (s n) ∈ F := fun n =>
    perronFamily_replace_mem hP (hsF n) (chartAt ℂ z₀) a ρ hρ hsub (u n) (hu_harm n) (hu_cont n)
  have hrep_ge : ∀ n (y : X), s n y ≤ chartRep z₀ a ρ (u n) (s n) y := fun n =>
    le_replaceOnDisc (perronFamily_subharmonic hP (hsF n)) hρ hsub (hu_harm n) (hu_cont n)
  have hrep_harm : ∀ n, InnerProductSpace.HarmonicOnNhd
      (chartRepPull z₀ a ρ (u n) (s n)) (Metric.ball a ρ) := fun n w hw =>
    harmonicAt_replaceOnDisc_pullback hball_target (hu_harm n) hw
  have hu_mono : ∀ n z, ‖z - a‖ < ρ → u n z ≤ u (n + 1) z := fun n =>
    harmonic_le_of_gluedBall_le hρ (hu_harm n) (hu_harm (n + 1)) (hu_cont n) (hu_cont (n + 1))
      (fun z _ => hsmono n ((chartAt ℂ z₀).symm z))
  have hrep_mono : ∀ n w, w ∈ Metric.ball a ρ →
      chartRepPull z₀ a ρ (u n) (s n) w ≤ chartRepPull z₀ a ρ (u (n + 1)) (s (n + 1)) w := by
    intro n w hw
    change replaceOnDisc (chartAt ℂ z₀) a ρ (u n) (s n) ((chartAt ℂ z₀).symm w) ≤
      replaceOnDisc (chartAt ℂ z₀) a ρ (u (n + 1)) (s (n + 1)) ((chartAt ℂ z₀).symm w)
    rw [replaceOnDisc_pullback_of_mem hball_target hw,
      replaceOnDisc_pullback_of_mem hball_target hw]
    exact hu_mono n w (by simpa [Metric.mem_ball, dist_eq_norm] using hw)
  have hV_bdd : ∀ n w, chartRepPull z₀ a ρ (u n) (s n) w ≤
      upperEnvelope F ((chartAt ℂ z₀).symm w) :=
    fun n w => perronFamily_mem_le_upperEnvelope hP (hrepF n) _
  have hrep_sup : (⨆ n, chartRep z₀ a ρ (u n) (s n) z₀) = upperEnvelope F z₀ := by
    have hBdd : BddAbove (Set.range (fun n => chartRep z₀ a ρ (u n) (s n) z₀)) := by
      refine ⟨upperEnvelope F z₀, ?_⟩
      rintro y ⟨n, rfl⟩
      exact perronFamily_mem_le_upperEnvelope hP (hrepF n) z₀
    refine le_antisymm (ciSup_le fun n =>
      perronFamily_mem_le_upperEnvelope hP (hrepF n) z₀) ?_
    calc upperEnvelope F z₀ = ⨆ n, s n z₀ := hssup.symm
      _ ≤ ⨆ n, chartRep z₀ a ρ (u n) (s n) z₀ :=
          ciSup_le fun n => (hrep_ge n z₀).trans (le_ciSup hBdd n)
  let H : ℂ → ℝ := fun w => ⨆ n, chartRepPull z₀ a ρ (u n) (s n) w
  have hH_harm : InnerProductSpace.HarmonicOnNhd H (Metric.ball a ρ) := by
    refine Commons.Analysis.Complex.Harmonic.harmonicOnNhd_of_monotone_pointwise_limit_ball
      hrep_harm hrep_mono ?_
    intro w hw
    refine tendsto_atTop_ciSup (monotone_nat_of_le_succ fun n => hrep_mono n w hw) ?_
    refine ⟨upperEnvelope F ((chartAt ℂ z₀).symm w), ?_⟩
    rintro y ⟨n, rfl⟩
    exact hV_bdd n w
  have hH_le : ∀ w ∈ Metric.ball a ρ, H w ≤ upperEnvelope F ((chartAt ℂ z₀).symm w) :=
    fun w _ => ciSup_le fun n => hV_bdd n w
  have hH_a : H a = upperEnvelope F z₀ := by
    have hfun : (fun n => replaceOnDisc (chartAt ℂ z₀) a ρ (u n) (s n)
          ((chartAt ℂ z₀).symm a))
        = (fun n => replaceOnDisc (chartAt ℂ z₀) a ρ (u n) (s n) z₀) := by
      funext n
      rw [hsymm_a]
    change (⨆ n, replaceOnDisc (chartAt ℂ z₀) a ρ (u n) (s n) ((chartAt ℂ z₀).symm a)) = _
    rw [hfun]
    exact hrep_sup
  -- the second sequence at a point of the disc
  have hH_ge : ∀ w ∈ Metric.ball a ρ, upperEnvelope F ((chartAt ℂ z₀).symm w) ≤ H w := by
    intro w hw
    set z₁ : X := (chartAt ℂ z₀).symm w with hz₁
    obtain ⟨g, hgF, hgmono, hgsup⟩ := perronFamily_exists_incr_seq hP z₁
    have hcont_g : ∀ n, ContinuousOn (fun v => g n ((chartAt ℂ z₀).symm v))
        (Metric.sphere a ρ) := by
      intro n
      have hsc : Continuous (g n) := continuousOn_univ.mp (perronFamily_subharmonic hP (hgF n)).1
      refine hsc.continuousOn.comp ((chartAt ℂ z₀).continuousOn_symm.mono ?_) (fun z _ => mem_univ _)
      exact fun z hz => hsub (Metric.sphere_subset_closedBall hz)
    choose u' hu'_harm hu'_cont using fun n =>
      dirichlet_ball_glued (c := a) (R := ρ) hρ (F := fun v => g n ((chartAt ℂ z₀).symm v))
        (hcont_g n)
    have hnmono : ∀ n (x : X), max (s n) (g n) x ≤ max (s (n + 1)) (g (n + 1)) x :=
      fun n x => max_le_max (hsmono n x) (hgmono n x)
    have hhnF : ∀ n, max (s n) (g n) ∈ F := fun n => perronFamily_sup_mem hP (hsF n) (hgF n)
    have hcont_hn : ∀ n, ContinuousOn (fun v => max (s n) (g n) ((chartAt ℂ z₀).symm v))
        (Metric.sphere a ρ) := by
      intro n
      have hsc : Continuous (max (s n) (g n)) :=
        continuousOn_univ.mp (perronFamily_subharmonic hP (hhnF n)).1
      refine hsc.continuousOn.comp ((chartAt ℂ z₀).continuousOn_symm.mono ?_) (fun z _ => mem_univ _)
      exact fun z hz => hsub (Metric.sphere_subset_closedBall hz)
    choose u'' hu''_harm hu''_cont using fun n =>
      dirichlet_ball_glued (c := a) (R := ρ) hρ
        (F := fun v => max (s n) (g n) ((chartAt ℂ z₀).symm v)) (hcont_hn n)
    have hhF : ∀ n, chartRep z₀ a ρ (u'' n) (max (s n) (g n)) ∈ F := fun n =>
      perronFamily_replace_mem hP (hhnF n) (chartAt ℂ z₀) a ρ hρ hsub (u'' n) (hu''_harm n)
        (hu''_cont n)
    have hh_ge : ∀ n (y : X), max (s n) (g n) y ≤
        chartRep z₀ a ρ (u'' n) (max (s n) (g n)) y := fun n =>
      le_replaceOnDisc (perronFamily_subharmonic hP (hhnF n)) hρ hsub (hu''_harm n) (hu''_cont n)
    have hh_harm : ∀ n, InnerProductSpace.HarmonicOnNhd
        (chartRepPull z₀ a ρ (u'' n) (max (s n) (g n))) (Metric.ball a ρ) := fun n v hv =>
      harmonicAt_replaceOnDisc_pullback hball_target (hu''_harm n) hv
    have hu''_mono : ∀ n z, ‖z - a‖ < ρ → u'' n z ≤ u'' (n + 1) z := fun n =>
      harmonic_le_of_gluedBall_le hρ (hu''_harm n) (hu''_harm (n + 1)) (hu''_cont n)
        (hu''_cont (n + 1)) (fun z _ => hnmono n _)
    have hh_mono : ∀ n v, v ∈ Metric.ball a ρ →
        chartRepPull z₀ a ρ (u'' n) (max (s n) (g n)) v ≤
        chartRepPull z₀ a ρ (u'' (n + 1)) (max (s (n + 1)) (g (n + 1))) v := by
      intro n v hv
      change replaceOnDisc (chartAt ℂ z₀) a ρ (u'' n) (max (s n) (g n)) ((chartAt ℂ z₀).symm v) ≤
        replaceOnDisc (chartAt ℂ z₀) a ρ (u'' (n + 1)) (max (s (n + 1)) (g (n + 1)))
          ((chartAt ℂ z₀).symm v)
      rw [replaceOnDisc_pullback_of_mem hball_target hv,
        replaceOnDisc_pullback_of_mem hball_target hv]
      exact hu''_mono n v (by simpa [Metric.mem_ball, dist_eq_norm] using hv)
    let Hh : ℂ → ℝ := fun v => ⨆ n, chartRepPull z₀ a ρ (u'' n) (max (s n) (g n)) v
    have hHh_harm : InnerProductSpace.HarmonicOnNhd Hh (Metric.ball a ρ) := by
      refine Commons.Analysis.Complex.Harmonic.harmonicOnNhd_of_monotone_pointwise_limit_ball
        hh_harm hh_mono ?_
      intro v hv
      refine tendsto_atTop_ciSup (monotone_nat_of_le_succ fun n => hh_mono n v hv) ?_
      refine ⟨upperEnvelope F ((chartAt ℂ z₀).symm v), ?_⟩
      rintro y ⟨n, rfl⟩
      exact perronFamily_mem_le_upperEnvelope hP (hhF n) ((chartAt ℂ z₀).symm v)
    have hu_le_u'' : ∀ n z, ‖z - a‖ < ρ → u n z ≤ u'' n z := fun n =>
      harmonic_le_of_gluedBall_le hρ (hu_harm n) (hu''_harm n) (hu_cont n) (hu''_cont n)
        (fun z _ => le_max_left _ _)
    have hHh_ge_H : ∀ v ∈ Metric.ball a ρ, H v ≤ Hh v := by
      intro v hv
      have hBdd : BddAbove (Set.range (fun n => chartRepPull z₀ a ρ (u'' n)
          (max (s n) (g n)) v)) := by
        refine ⟨upperEnvelope F ((chartAt ℂ z₀).symm v), ?_⟩
        rintro y ⟨n, rfl⟩
        exact perronFamily_mem_le_upperEnvelope hP (hhF n) ((chartAt ℂ z₀).symm v)
      refine ciSup_le fun n => ?_
      have h1 : replaceOnDisc (chartAt ℂ z₀) a ρ (u n) (s n) ((chartAt ℂ z₀).symm v) = u n v :=
        replaceOnDisc_pullback_of_mem hball_target hv
      have h2 : replaceOnDisc (chartAt ℂ z₀) a ρ (u'' n) (max (s n) (g n))
          ((chartAt ℂ z₀).symm v) = u'' n v :=
        replaceOnDisc_pullback_of_mem hball_target hv
      have h3 : u n v ≤ u'' n v :=
        hu_le_u'' n v (by simpa [Metric.mem_ball, dist_eq_norm] using hv)
      have h4 : u'' n v ≤ (⨆ k, chartRepPull z₀ a ρ (u'' k) (max (s k) (g k)) v) := by
        rw [← h2]
        exact le_ciSup hBdd n
      calc chartRepPull z₀ a ρ (u n) (s n) v = u n v := h1
        _ ≤ u'' n v := h3
        _ ≤ ⨆ k, chartRepPull z₀ a ρ (u'' k) (max (s k) (g k)) v := h4
    have hHh_a : Hh a = upperEnvelope F z₀ := by
      have hfun : (fun n => replaceOnDisc (chartAt ℂ z₀) a ρ (u'' n) (max (s n) (g n))
            ((chartAt ℂ z₀).symm a))
          = (fun n => replaceOnDisc (chartAt ℂ z₀) a ρ (u'' n) (max (s n) (g n)) z₀) := by
        funext n
        rw [hsymm_a]
      change (⨆ n, replaceOnDisc (chartAt ℂ z₀) a ρ (u'' n) (max (s n) (g n))
        ((chartAt ℂ z₀).symm a)) = _
      rw [hfun]
      have hBdd : BddAbove (Set.range (fun n =>
          chartRep z₀ a ρ (u'' n) (max (s n) (g n)) z₀)) := by
        refine ⟨upperEnvelope F z₀, ?_⟩
        rintro y ⟨n, rfl⟩
        exact perronFamily_mem_le_upperEnvelope hP (hhF n) z₀
      refine le_antisymm (ciSup_le fun n =>
        perronFamily_mem_le_upperEnvelope hP (hhF n) z₀) ?_
      calc upperEnvelope F z₀ = ⨆ n, s n z₀ := hssup.symm
        _ ≤ ⨆ n, chartRep z₀ a ρ (u'' n) (max (s n) (g n)) z₀ :=
            ciSup_le fun n => (le_max_left (s n z₀) (g n z₀)).trans
              ((hh_ge n z₀).trans (le_ciSup hBdd n))
    have hdiff_zero : ∀ v ∈ Metric.ball a ρ, Hh v = H v := by
      have hharm : InnerProductSpace.HarmonicOnNhd (fun v => Hh v - H v) (Metric.ball a ρ) :=
        hHh_harm.sub hH_harm
      have hnonneg : ∀ v ∈ Metric.ball a ρ, 0 ≤ Hh v - H v :=
        fun v hv => sub_nonneg.mpr (hHh_ge_H v hv)
      have ha0 : Hh a - H a = 0 := by rw [hHh_a, hH_a, sub_self]
      have hmin : ∀ v ∈ Metric.ball a ρ, -(Hh v - H v) ≤ -(Hh a - H a) := by
        intro v hv
        rw [ha0]
        linarith [hnonneg v hv]
      have hconst := Commons.Analysis.Complex.Harmonic.harmonic_eqOn_of_isMaxOn_open
        (U := Metric.ball a ρ) Metric.isOpen_ball Metric.isPreconnected_ball
        (u := fun v => -(Hh v - H v)) (fun v hv => (hharm v hv).neg)
        (Metric.mem_ball_self hρ) hmin
      intro v hv
      have hh := hconst v hv
      rw [ha0] at hh
      linarith
    calc upperEnvelope F ((chartAt ℂ z₀).symm w) = upperEnvelope F z₁ := by rw [hz₁]
      _ = ⨆ n, g n z₁ := hgsup.symm
      _ ≤ ⨆ n, chartRepPull z₀ a ρ (u'' n) (max (s n) (g n)) w := by
            refine ciSup_le fun n => ?_
            rw [hz₁]
            have hBdd : BddAbove (Set.range (fun k => chartRepPull z₀ a ρ (u'' k)
                (max (s k) (g k)) w)) := by
              refine ⟨upperEnvelope F ((chartAt ℂ z₀).symm w), ?_⟩
              rintro y ⟨k, rfl⟩
              exact perronFamily_mem_le_upperEnvelope hP (hhF k) ((chartAt ℂ z₀).symm w)
            exact ((le_max_right (s n ((chartAt ℂ z₀).symm w))
              (g n ((chartAt ℂ z₀).symm w))).trans
              (hh_ge n ((chartAt ℂ z₀).symm w))).trans (le_ciSup hBdd n)
      _ = Hh w := rfl
      _ = H w := hdiff_zero w hw
  have hcongr : (upperEnvelope F ∘ (chartAt ℂ z₀).symm) =ᶠ[𝓝 a] H := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hρ)] with w hw
    exact le_antisymm (hH_ge w hw) (hH_le w hw)
  exact (InnerProductSpace.harmonicAt_congr_nhds hcongr).mpr (hH_harm a (Metric.mem_ball_self hρ))

end Perron

end Submission
