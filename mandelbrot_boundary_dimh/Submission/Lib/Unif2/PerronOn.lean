import Submission.Lib.Unif2.UnifDeps
import Submission.Lib.Unif2.RiemannSurface
import Submission.Lib.Unif2.Perron
import Submission.Lib.Unif2.Commons.Analysis.Complex.Harmonic.harmonicOnNhd_of_monotone_pointwise_limit_ball
import Submission.Lib.Unif2.Commons.Analysis.Complex.Harmonic.harmonic_eqOn_of_isMaxOn_open
import Submission.Lib.Unif2.Commons.Analysis.Complex.Harmonic.max_principle_localSubMeanValue

/-!
# Perron's theorem with restricted harmonic replacement

Hubbard's Proposition 1.2.3 (Perron's theorem) produces a harmonic function as the upper envelope
of a family `F` of subharmonic functions which is closed under harmonic replacement in *every*
chart disc.  Several important constructions (the harmonic measure of a boundary component, the
Green function with a pole) only have replacement closure for discs contained in a fixed open set
`U` — the constraints defining the family need not be preserved by a replacement in a disc that
crosses the boundary where the constraint changes.

This module proves the natural generalisation:

* `Submission.IsPerronOn F W U` — a family `F` of subharmonic functions, bounded above on `U` by a
  function `W`, closed under maxima, and closed under harmonic replacement in *sufficiently small*
  chart discs centred at every point of `U`;
* `Submission.IsPerronOn.upperEnvelope_harmonic` — for `U` open, the upper envelope
  `F̄ = sup F` is harmonic on `U`.

The proof is that of `Submission.IsPerronFamily.upperEnvelope_harmonic`, with the radius of the
chart disc chosen small enough to stay inside `U`.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

noncomputable section

open Filter Set
open Classical

namespace Submission

/-- **Perron family with restricted replacement.**  `F` is a nonempty family of subharmonic
functions on `X`, bounded above on `U` by `W`, closed under (pointwise) maxima, and closed under
harmonic replacement in small chart discs centred at the points of `U`. -/
def IsPerronOn {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] (F : Set (X → ℝ)) (W : X → ℝ)
    (U : Set X) : Prop :=
  F.Nonempty ∧
  (∀ f ∈ F, SubharmonicOnX f U) ∧
  (∀ f ∈ F, ∀ x ∈ U, f x ≤ W x) ∧
  (∀ f ∈ F, ∀ g ∈ F, max f g ∈ F) ∧
  (∀ z ∈ U, ∃ ε : ℝ, 0 < ε ∧ ∀ f ∈ F,
    ∀ (ρ : ℝ), 0 < ρ → ρ ≤ ε →
      Metric.closedBall ((chartAt ℂ z) z) ρ ⊆ (chartAt ℂ z).target →
      ∀ u : ℂ → ℝ, (∀ w : ℂ, ‖w - (chartAt ℂ z) z‖ < ρ →
          InnerProductSpace.HarmonicAt u w) →
      ContinuousOn (gluedBall u (fun w => f ((chartAt ℂ z).symm w)) ((chartAt ℂ z) z) ρ)
        (Metric.closedBall ((chartAt ℂ z) z) ρ) →
      replaceOnDisc (chartAt ℂ z) ((chartAt ℂ z) z) ρ u f ∈ F)

section Basic

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

theorem IsPerronOn.nonempty {F : Set (X → ℝ)} {W : X → ℝ} {U : Set X}
    (h : IsPerronOn F W U) : F.Nonempty := h.1

theorem IsPerronOn.subharmonic {F : Set (X → ℝ)} {W : X → ℝ} {U : Set X}
    (h : IsPerronOn F W U) {f : X → ℝ} (hf : f ∈ F) : SubharmonicOnX f U := h.2.1 f hf

theorem IsPerronOn.bound {F : Set (X → ℝ)} {W : X → ℝ} {U : Set X}
    (h : IsPerronOn F W U) {f : X → ℝ} (hf : f ∈ F) {x : X} (hx : x ∈ U) : f x ≤ W x :=
  h.2.2.1 f hf x hx

theorem IsPerronOn.sup_mem {F : Set (X → ℝ)} {W : X → ℝ} {U : Set X}
    (h : IsPerronOn F W U) {f g : X → ℝ} (hf : f ∈ F) (hg : g ∈ F) : max f g ∈ F :=
  h.2.2.2.1 f hf g hg

/-- The replacement axiom of `IsPerronOn`: at every point of `U` replacement is possible in all
sufficiently small chart discs. -/
theorem IsPerronOn.replace {F : Set (X → ℝ)} {W : X → ℝ} {U : Set X}
    (h : IsPerronOn F W U) {z : X} (hz : z ∈ U) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ f ∈ F,
      ∀ (ρ : ℝ), 0 < ρ → ρ ≤ ε →
        Metric.closedBall ((chartAt ℂ z) z) ρ ⊆ (chartAt ℂ z).target →
        ∀ u : ℂ → ℝ, (∀ w : ℂ, ‖w - (chartAt ℂ z) z‖ < ρ →
            InnerProductSpace.HarmonicAt u w) →
        ContinuousOn (gluedBall u (fun w => f ((chartAt ℂ z).symm w)) ((chartAt ℂ z) z) ρ)
          (Metric.closedBall ((chartAt ℂ z) z) ρ) →
        replaceOnDisc (chartAt ℂ z) ((chartAt ℂ z) z) ρ u f ∈ F :=
  h.2.2.2.2 z hz

theorem IsPerronOn.upperEnvelope_le {F : Set (X → ℝ)} {W : X → ℝ} {U : Set X}
    (h : IsPerronOn F W U) {x : X} (hx : x ∈ U) : upperEnvelope F x ≤ W x := by
  rw [upperEnvelope]
  exact csSup_le (h.nonempty.image _) (by rintro y ⟨f, hf, rfl⟩; exact h.bound hf hx)

theorem IsPerronOn.mem_le_upperEnvelope {F : Set (X → ℝ)} {W : X → ℝ} {U : Set X}
    (h : IsPerronOn F W U) {f : X → ℝ} (hf : f ∈ F) {x : X} (hx : x ∈ U) :
    f x ≤ upperEnvelope F x := by
  rw [upperEnvelope]
  refine le_csSup ⟨W x, ?_⟩ ⟨f, hf, rfl⟩
  rintro y ⟨g, hg, rfl⟩
  exact h.bound hg hx

end Basic

/-! ## An increasing sequence in `F` realizing the envelope at a point -/

section Sequence

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  {F : Set (X → ℝ)} {W : X → ℝ} {U : Set X}

/-- Given a Perron family with restricted replacement, there is a pointwise increasing sequence in
it whose values at a fixed point of `U` converge to the value of the upper envelope there. -/
theorem IsPerronOn.exists_incr_seq (h : IsPerronOn F W U) {z : X} (hz : z ∈ U) :
    ∃ s : ℕ → X → ℝ, (∀ n, s n ∈ F) ∧ (∀ n (x : X), s n x ≤ s (n + 1) x) ∧
      (⨆ n, s n z) = upperEnvelope F z := by
  have hSne : (F.image (fun f : X → ℝ => f z)).Nonempty := (h.nonempty).image _
  have hSbdd : BddAbove (F.image (fun f : X → ℝ => f z)) :=
    ⟨W z, by rintro y ⟨f, hf, rfl⟩; exact h.bound hf hz⟩
  obtain ⟨u, humono, hutend, humem⟩ := exists_seq_tendsto_sSup hSne hSbdd
  have humem' : ∀ n : ℕ, ∃ f ∈ F, f z = u n := fun n => by
    have := humem n
    rw [Set.mem_image] at this
    exact this
  choose f hfF hfz using humem'
  have hBddU : BddAbove (Set.range u) :=
    ⟨W z, by rintro y ⟨n, rfl⟩; rw [← hfz n]; exact h.bound (hfF n) hz⟩
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
    | succ n ih => rw [hgsucc]; exact h.sup_mem ih (hfF (n + 1))
  have hgmono : ∀ n (x : X), g n x ≤ g (n + 1) x := by
    intro n x
    rw [hgsucc]
    exact le_max_left _ _
  have hgle : ∀ n (x : X), x ∈ U → g n x ≤ upperEnvelope F x := by
    intro n x hx
    induction n with
    | zero => rw [hg0]; exact h.mem_le_upperEnvelope (hfF 0) hx
    | succ n ih =>
      rw [hgsucc]
      exact max_le ih (h.mem_le_upperEnvelope (hfF (n + 1)) hx)
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
    ⟨upperEnvelope F z, by rintro y ⟨n, rfl⟩; exact hgle n z hz⟩
  refine le_antisymm (ciSup_le fun n => hgle n z hz) ?_
  calc upperEnvelope F z = sSup (F.image (fun f : X → ℝ => f z)) := rfl
    _ = ⨆ n, u n := husup.symm
    _ ≤ ⨆ n, g n z := ciSup_le fun n => (hgelim n).trans (le_ciSup hBddG n)

end Sequence

/-! ## Perron's theorem with restricted replacement -/

section Perron

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **The Dirichlet solution dominates the subharmonic boundary data** (set-level version, for
subharmonicity measured only on an open set `U`).  If the chart disc at `z₀` of radius `ρ` is
contained in `U`, and `u` is the harmonic extension of the boundary values
`f ∘ (chartAt ℂ z₀).symm` on the sphere, then the harmonic replacement
`replaceOnDisc (chartAt ℂ z₀) a ρ u f` dominates `f` on `U`. -/
theorem le_replaceOnDiscOn {U : Set X} (_hU : IsOpen U) {f : X → ℝ} (hf : SubharmonicOnX f U)
    {z₀ : X} {a : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : Metric.closedBall a ρ ⊆ (chartAt ℂ z₀).target)
    (hΔU : (chartAt ℂ z₀).symm '' Metric.closedBall a ρ ⊆ U) {u : ℂ → ℝ}
    (hu : ∀ z : ℂ, ‖z - a‖ < ρ → InnerProductSpace.HarmonicAt u z)
    (hG : ContinuousOn (gluedBall u (fun w => f ((chartAt ℂ z₀).symm w)) a ρ)
      (Metric.closedBall a ρ)) :
    ∀ y ∈ U, f y ≤ replaceOnDisc (chartAt ℂ z₀) a ρ u f y := by
  set c : OpenPartialHomeomorph X ℂ := chartAt ℂ z₀ with hc
  have hsub' : Metric.closedBall a ρ ⊆ c.target := by rwa [hc]
  have hball : Metric.ball a ρ ⊆ c.target := fun z hz => hsub' (Metric.ball_subset_closedBall hz)
  have hK' : c.symm '' Metric.closedBall a ρ ⊆ U := by rw [hc]; exact hΔU
  have hfU : ContinuousOn f U := hf.1
  have hG' : ContinuousOn (gluedBall u (fun w => f (c.symm w)) a ρ) (Metric.closedBall a ρ) := by
    rwa [hc] at hG
  set v : ℂ → ℝ := fun w => f (c.symm w) with hv
  set UU : ℂ → ℝ := gluedBall u v a ρ with hUU
  have hUU_cont : ContinuousOn UU (Metric.closedBall a ρ) := by rw [hUU, hv]; exact hG'
  have hv_cont : ContinuousOn v (Metric.closedBall a ρ) := by
    rw [hv]
    exact hfU.comp (c.continuousOn_symm.mono hsub')
      (fun z hz => hK' ⟨z, hz, rfl⟩)
  have hloc : ∀ p ∈ Metric.ball a ρ, ∃ ε : ℝ, 0 < ε ∧ Metric.ball p ε ⊆ Metric.ball a ρ ∧
      ∀ r : ℝ, 0 < r → Metric.closedBall p r ⊆ Metric.ball p ε →
        (v - UU) p ≤ Real.circleAverage (v - UU) p r := by
    intro p hp
    have hptarget : p ∈ c.target := hball hp
    have hpU : c.symm p ∈ U := hK' ⟨p, Metric.ball_subset_closedBall hp, rfl⟩
    have hsubh : SubharmonicAtChart f c (c.symm p) :=
      SubharmonicOnX.subharmonicAtChart hf hpU (c.map_target hptarget)
    rw [SubharmonicAtChart] at hsubh
    obtain ⟨-, ρ', hρ', ht', hcont', hmvp'⟩ := hsubh
    have hcp : c (c.symm p) = p := c.right_inv hptarget
    rw [hcp] at ht' hcont' hmvp'
    have hdist : 0 < ρ - dist p a := sub_pos.mpr (by simpa [Metric.mem_ball] using hp)
    refine ⟨min ρ' (ρ - dist p a), lt_min hρ' hdist, ?_, ?_⟩
    · exact (Metric.ball_subset_ball (min_le_right _ _)).trans (ball_subset_ball_of_mem hp)
    · intro r hr hpr
      have hpr' : Metric.closedBall p r ⊆ Metric.ball p ρ' :=
        hpr.trans (Metric.ball_subset_ball (min_le_left _ _))
      have hprball : Metric.closedBall p r ⊆ Metric.ball a ρ :=
        hpr.trans (Metric.ball_subset_ball (min_le_right _ _) |>.trans (ball_subset_ball_of_mem hp))
      have hvle : v p ≤ Real.circleAverage v p r := hmvp' p (Metric.mem_ball_self hρ') r hr
        (by simpa using hpr')
      have hUharm : InnerProductSpace.HarmonicOnNhd UU (Metric.closedBall p |r|) := by
        rw [abs_of_pos hr]
        intro q hq
        have hqball : q ∈ Metric.ball a ρ := hprball hq
        have hq' : ‖q - a‖ < ρ := by simpa [Metric.mem_ball, dist_eq_norm] using hqball
        refine (InnerProductSpace.harmonicAt_congr_nhds ?_).mpr (hu q hq')
        filter_upwards [Metric.isOpen_ball.mem_nhds hqball] with w hw
        rw [hUU]; exact gluedBall_of_mem hw
      have havgU : Real.circleAverage UU p r = UU p :=
        InnerProductSpace.HarmonicOnNhd.circleAverage_eq hUharm
      have hvI : CircleIntegrable v p r :=
        (hv_cont.mono (fun z hz =>
          Metric.ball_subset_closedBall (hprball (Metric.sphere_subset_closedBall hz)))).circleIntegrable
          (le_of_lt hr)
      have hUI : CircleIntegrable UU p r :=
        (hUU_cont.mono (fun z hz =>
          Metric.ball_subset_closedBall (hprball (Metric.sphere_subset_closedBall hz)))).circleIntegrable
          (le_of_lt hr)
      have : Real.circleAverage (v - UU) p r = Real.circleAverage v p r - Real.circleAverage UU p r :=
        Real.circleAverage_sub hvI hUI
      rw [Pi.sub_apply, this, havgU]
      linarith
  have hbd : ∀ z ∈ closure (Metric.ball a ρ), z ∉ Metric.ball a ρ → (v - UU) z ≤ 0 := by
    rw [closure_ball a (ne_of_gt hρ)]
    intro z hz hznot
    have hzU : UU z = v z := by rw [hUU]; exact gluedBall_of_not_mem hznot
    rw [Pi.sub_apply, hzU, sub_self]
  have hcont' : ContinuousOn (v - UU) (closure (Metric.ball a ρ)) := by
    rw [closure_ball a (ne_of_gt hρ)]
    exact hv_cont.sub hUU_cont
  have hle0 : ∀ z ∈ Metric.ball a ρ, v z - UU z ≤ 0 :=
    Commons.Analysis.Complex.Harmonic.max_principle_localSubMeanValue Metric.isOpen_ball
      Metric.isPreconnected_ball Metric.isBounded_ball hcont' hloc hbd
  intro y hyU
  by_cases hy : y ∈ chartBall c a ρ
  · have hysrc : y ∈ c.source := hy.1
    have hyball : c y ∈ Metric.ball a ρ := hy.2
    rw [hc, replaceOnDisc_of_mem_chartBall hy]
    have h1 : f y = v (c y) := by rw [hv]; simp only; rw [c.left_inv hysrc]
    rw [h1]
    have h2 : v (c y) ≤ UU (c y) := by linarith [hle0 (c y) hyball]
    have h3 : UU (c y) = u (c y) := by rw [hUU]; exact gluedBall_of_mem hyball
    rw [h3] at h2
    exact h2
  · rw [hc]
    rw [replaceOnDisc_of_not_mem_chartBall hy]

/-- **Perron's theorem with restricted harmonic replacement**: the upper envelope of a Perron
family with replacement closure in small discs around every point of an open set `U` is harmonic
on `U`. -/
theorem IsPerronOn.upperEnvelope_harmonic {F : Set (X → ℝ)} {W : X → ℝ} {U : Set X}
    (hU : IsOpen U) (hP : IsPerronOn F W U) : HarmonicOnX (upperEnvelope F) U := by
  intro z₀ hz₀
  let a : ℂ := (chartAt ℂ z₀) z₀
  have hsrc : z₀ ∈ (chartAt ℂ z₀).source := mem_chart_source ℂ z₀
  have hsymm_a : (chartAt ℂ z₀).symm a = z₀ := (chartAt ℂ z₀).left_inv hsrc
  have hmemtgt : a ∈ (chartAt ℂ z₀).target := (chartAt ℂ z₀).map_source hsrc
  -- the radius supplied by the replacement axiom
  obtain ⟨ε₀, hε₀, hax⟩ := hP.replace hz₀
  -- a radius whose chart ball lies both in the chart target and in `U`
  obtain ⟨ε₁, hε₁, hε₁sub⟩ := Metric.mem_nhds_iff.mp ((chartAt ℂ z₀).open_target.mem_nhds hmemtgt)
  obtain ⟨ε₂, hε₂, hε₂U⟩ := Metric.mem_nhds_iff.mp
    (((chartAt ℂ z₀).continuousAt_symm hmemtgt).preimage_mem_nhds
      (hU.mem_nhds (by rw [hsymm_a]; exact hz₀)))
  set δ : ℝ := min (ε₁ / 2) (ε₂ / 2) with hδdef
  have hδ : 0 < δ := lt_min (half_pos hε₁) (half_pos hε₂)
  have hδsub : Metric.closedBall a δ ⊆ (chartAt ℂ z₀).target :=
    (Metric.closedBall_subset_ball (by rw [hδdef]; linarith [min_le_left (ε₁ / 2) (ε₂ / 2)])).trans
      hε₁sub
  have hδU : (chartAt ℂ z₀).symm '' Metric.closedBall a δ ⊆ U := by
    rintro x ⟨w, hw, rfl⟩
    exact hε₂U (Metric.closedBall_subset_ball (by
      rw [hδdef]; linarith [min_le_right (ε₁ / 2) (ε₂ / 2)]) hw)
  set ρ : ℝ := min (δ / 2) (ε₀ / 2) with hρdef
  have hρ : 0 < ρ := lt_min (half_pos hδ) (half_pos hε₀)
  have hρδ : ρ < δ := by
    calc ρ ≤ δ / 2 := min_le_left _ _
      _ < δ := by linarith
  have hρε₀ : ρ ≤ ε₀ := by
    calc ρ ≤ ε₀ / 2 := min_le_right _ _
      _ ≤ ε₀ := by linarith
  have hsub : Metric.closedBall a ρ ⊆ (chartAt ℂ z₀).target :=
    (Metric.closedBall_subset_closedBall (le_of_lt hρδ)).trans hδsub
  have hρU : (chartAt ℂ z₀).symm '' Metric.closedBall a ρ ⊆ U :=
    (Set.image_mono (Metric.closedBall_subset_closedBall (le_of_lt hρδ))).trans hδU
  have hball_target : Metric.ball a ρ ⊆ (chartAt ℂ z₀).target :=
    fun z hz => hsub (Metric.ball_subset_closedBall hz)
  -- the increasing sequence realizing the envelope at `z₀`
  obtain ⟨s, hsF, hsmono, hssup⟩ := hP.exists_incr_seq hz₀
  have hcont_s : ∀ n, ContinuousOn (fun w => s n ((chartAt ℂ z₀).symm w)) (Metric.sphere a ρ) := by
    intro n
    refine (hP.subharmonic (hsF n)).1.comp
      ((chartAt ℂ z₀).continuousOn_symm.mono (fun z hz =>
        hsub (Metric.sphere_subset_closedBall hz)))
      (fun z hz => hρU ⟨z, Metric.sphere_subset_closedBall hz, rfl⟩)
  choose u hu_harm hu_cont using fun n =>
    dirichlet_ball_glued (c := a) (R := ρ) hρ (F := fun w => s n ((chartAt ℂ z₀).symm w))
      (hcont_s n)
  have hrepF : ∀ n, chartRep z₀ a ρ (u n) (s n) ∈ F := fun n =>
    hax (s n) (hsF n) ρ hρ hρε₀ hsub (u n) (hu_harm n) (hu_cont n)
  have hrep_ge : ∀ n (y : X), y ∈ U → s n y ≤ chartRep z₀ a ρ (u n) (s n) y := fun n =>
    le_replaceOnDiscOn hU (hP.subharmonic (hsF n)) hρ hsub hρU (hu_harm n) (hu_cont n)
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
  have hV_bdd : ∀ n w, w ∈ Metric.ball a ρ → chartRepPull z₀ a ρ (u n) (s n) w ≤
      upperEnvelope F ((chartAt ℂ z₀).symm w) :=
    fun n w hw => hP.mem_le_upperEnvelope (hrepF n) (hρU ⟨w, Metric.ball_subset_closedBall hw, rfl⟩)
  have hrep_sup : (⨆ n, chartRep z₀ a ρ (u n) (s n) z₀) = upperEnvelope F z₀ := by
    have hBdd : BddAbove (Set.range (fun n => chartRep z₀ a ρ (u n) (s n) z₀)) := by
      refine ⟨upperEnvelope F z₀, ?_⟩
      rintro y ⟨n, rfl⟩
      exact hP.mem_le_upperEnvelope (hrepF n) hz₀
    refine le_antisymm (ciSup_le fun n => hP.mem_le_upperEnvelope (hrepF n) hz₀) ?_
    calc upperEnvelope F z₀ = ⨆ n, s n z₀ := hssup.symm
      _ ≤ ⨆ n, chartRep z₀ a ρ (u n) (s n) z₀ :=
          ciSup_le fun n => (hrep_ge n z₀ hz₀).trans (le_ciSup hBdd n)
  let H : ℂ → ℝ := fun w => ⨆ n, chartRepPull z₀ a ρ (u n) (s n) w
  have hH_harm : InnerProductSpace.HarmonicOnNhd H (Metric.ball a ρ) := by
    refine Commons.Analysis.Complex.Harmonic.harmonicOnNhd_of_monotone_pointwise_limit_ball
      hrep_harm hrep_mono ?_
    intro w hw
    refine tendsto_atTop_ciSup (monotone_nat_of_le_succ fun n => hrep_mono n w hw) ?_
    refine ⟨upperEnvelope F ((chartAt ℂ z₀).symm w), ?_⟩
    rintro y ⟨n, rfl⟩
    exact hV_bdd n w hw
  have hH_le : ∀ w ∈ Metric.ball a ρ, H w ≤ upperEnvelope F ((chartAt ℂ z₀).symm w) :=
    fun w hw => ciSup_le fun n => hV_bdd n w hw
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
    have hz₁U : z₁ ∈ U := hρU ⟨w, Metric.ball_subset_closedBall hw, rfl⟩
    obtain ⟨g, hgF, hgmono, hgsup⟩ := hP.exists_incr_seq hz₁U
    have hcont_g : ∀ n, ContinuousOn (fun v => g n ((chartAt ℂ z₀).symm v))
        (Metric.sphere a ρ) := by
      intro n
      refine (hP.subharmonic (hgF n)).1.comp
        ((chartAt ℂ z₀).continuousOn_symm.mono (fun z hz =>
          hsub (Metric.sphere_subset_closedBall hz)))
        (fun z hz => hρU ⟨z, Metric.sphere_subset_closedBall hz, rfl⟩)
    choose u' hu'_harm hu'_cont using fun n =>
      dirichlet_ball_glued (c := a) (R := ρ) hρ (F := fun v => g n ((chartAt ℂ z₀).symm v))
        (hcont_g n)
    have hnmono : ∀ n (x : X), max (s n) (g n) x ≤ max (s (n + 1)) (g (n + 1)) x :=
      fun n x => max_le_max (hsmono n x) (hgmono n x)
    have hhnF : ∀ n, max (s n) (g n) ∈ F := fun n => hP.sup_mem (hsF n) (hgF n)
    have hcont_hn : ∀ n, ContinuousOn (fun v => max (s n) (g n) ((chartAt ℂ z₀).symm v))
        (Metric.sphere a ρ) := by
      intro n
      refine (hP.subharmonic (hhnF n)).1.comp
        ((chartAt ℂ z₀).continuousOn_symm.mono (fun z hz =>
          hsub (Metric.sphere_subset_closedBall hz)))
        (fun z hz => hρU ⟨z, Metric.sphere_subset_closedBall hz, rfl⟩)
    choose u'' hu''_harm hu''_cont using fun n =>
      dirichlet_ball_glued (c := a) (R := ρ) hρ
        (F := fun v => max (s n) (g n) ((chartAt ℂ z₀).symm v)) (hcont_hn n)
    have hhF : ∀ n, chartRep z₀ a ρ (u'' n) (max (s n) (g n)) ∈ F := fun n =>
      hax (max (s n) (g n)) (hhnF n) ρ hρ hρε₀ hsub (u'' n) (hu''_harm n) (hu''_cont n)
    have hh_ge : ∀ n (y : X), y ∈ U → max (s n) (g n) y ≤
        chartRep z₀ a ρ (u'' n) (max (s n) (g n)) y := fun n =>
      le_replaceOnDiscOn hU (hP.subharmonic (hhnF n)) hρ hsub hρU (hu''_harm n) (hu''_cont n)
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
      exact hP.mem_le_upperEnvelope (hhF n) (hρU ⟨v, Metric.ball_subset_closedBall hv, rfl⟩)
    have hu_le_u'' : ∀ n z, ‖z - a‖ < ρ → u n z ≤ u'' n z := fun n =>
      harmonic_le_of_gluedBall_le hρ (hu_harm n) (hu''_harm n) (hu_cont n) (hu''_cont n)
        (fun z _ => le_max_left _ _)
    have hHh_ge_H : ∀ v ∈ Metric.ball a ρ, H v ≤ Hh v := by
      intro v hv
      have hBdd : BddAbove (Set.range (fun n => chartRepPull z₀ a ρ (u'' n)
          (max (s n) (g n)) v)) := by
        refine ⟨upperEnvelope F ((chartAt ℂ z₀).symm v), ?_⟩
        rintro y ⟨n, rfl⟩
        exact hP.mem_le_upperEnvelope (hhF n) (hρU ⟨v, Metric.ball_subset_closedBall hv, rfl⟩)
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
        exact hP.mem_le_upperEnvelope (hhF n) hz₀
      refine le_antisymm (ciSup_le fun n => hP.mem_le_upperEnvelope (hhF n) hz₀) ?_
      calc upperEnvelope F z₀ = ⨆ n, s n z₀ := hssup.symm
        _ ≤ ⨆ n, chartRep z₀ a ρ (u'' n) (max (s n) (g n)) z₀ :=
            ciSup_le fun n => (le_max_left (s n z₀) (g n z₀)).trans
              ((hh_ge n z₀ hz₀).trans (le_ciSup hBdd n))
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
              exact hP.mem_le_upperEnvelope (hhF k) (hρU ⟨w, Metric.ball_subset_closedBall hw, rfl⟩)
            exact ((le_max_right (s n ((chartAt ℂ z₀).symm w))
              (g n ((chartAt ℂ z₀).symm w))).trans
              (hh_ge n ((chartAt ℂ z₀).symm w)
                (hρU ⟨w, Metric.ball_subset_closedBall hw, rfl⟩))).trans (le_ciSup hBdd n)
      _ = Hh w := rfl
      _ = H w := hdiff_zero w hw
  have hcongr : (upperEnvelope F ∘ (chartAt ℂ z₀).symm) =ᶠ[𝓝 a] H := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hρ)] with w hw
    exact le_antisymm (hH_ge w hw) (hH_le w hw)
  exact (InnerProductSpace.harmonicAt_congr_nhds hcongr).mpr (hH_harm a (Metric.mem_ball_self hρ))

end Perron

end Submission
