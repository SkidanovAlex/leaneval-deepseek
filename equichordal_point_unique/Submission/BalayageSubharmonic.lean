import Submission.UnifDeps
import Submission.Balayage
import Submission.GreenFunction
import Submission.TwoConstants
import Submission.SuperharmonicX
import Submission.GreenFunctionX
import Submission.Commons.Analysis.Complex.Harmonic.max_principle_localSubMeanValue
import Submission.Commons.Analysis.Complex.Harmonic.dirichlet_circle_boundary

/-!
# The balayage is subharmonic, the hitting probability is superharmonic

The balayage `balayage c a ρ` (the upper envelope of the family `hittingFamily c a ρ`) is the
pointwise supremum of a family of subharmonic functions which is closed under maxima; on the
closed chart disc it is the constant `-1` and off the closed chart disc it is harmonic.  Its
negation, the hitting probability, is therefore *superharmonic* on all of `X`: continuous, with
values in `[0,1]`, equal to `1` on the closed chart disc, and satisfying the reverse circle
mean-value inequality everywhere.

The main point is the circle mean-value inequality at the inner sphere `‖c· - a‖ = ρ`, where the
naive supremum argument is not directly available (the members of the family satisfy the
inequality only on their own chart balls): it is proved by comparing every member with the
Dirichlet solution on a small disc, i.e. by the maximum principle with a *local* sub-mean-value
hypothesis (`Commons.Analysis.Complex.Harmonic.max_principle_localSubMeanValue`).

The results are stated for the preferred chart at a point `z₀` (the case needed for the Green
function construction), where the boundary regularity of the hitting probability at the inner
sphere is available as `hittingProbability_tendsto_one_at_sphere`.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

noncomputable section

open Filter Set
open Classical

namespace Submission

variable {X : Type*} [TopologicalSpace X] [T2Space X] [PreconnectedSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

section Members

variable {c : OpenPartialHomeomorph X ℂ} {a : ℂ} {ρ : ℝ}

/-- Every member of the hitting family is dominated by its upper envelope, the balayage. -/
theorem hittingFamily_mem_le_balayage {v : X → ℝ} (hv : v ∈ hittingFamily c a ρ) (x : X) :
    v x ≤ balayage c a ρ x := by
  rw [balayage, upperEnvelope]
  exact le_csSup ⟨0, by rintro y ⟨w, hw, rfl⟩; exact hw.2.2 x⟩ ⟨v, hv, rfl⟩

end Members

/-! ## Continuity -/

section Continuity

/-- **Continuity of a function with the data of the hitting probability.**  If `h` is `1` on the
closed chart disc, harmonic off it, bounded above by `1`, and tends to `1` at every point of the
inner sphere when approached from the annulus, then `h` is continuous. -/
theorem continuousAt_of_chart_data {h : X → ℝ} {c : OpenPartialHomeomorph X ℂ} {a : ℂ}
    {ρ ρ₂ : ℝ} (hρ : 0 < ρ) (hρρ₂ : ρ < ρ₂)
    (hsub₂ : Metric.closedBall a ρ₂ ⊆ c.target)
    (hone : ∀ x ∈ chartClosedBall c a ρ, h x = 1)
    (hharm : HarmonicOnX h ((chartClosedBall c a ρ)ᶜ))
    (hlim : ∀ ξ ∈ chartSphere c a ρ, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ x in 𝓝[chartBall c a ρ₂ \ chartClosedBall c a ρ] ξ, 1 - ε ≤ h x)
    (hub : ∀ x, h x ≤ 1) (x : X) : ContinuousAt h x := by
  by_cases hx : x ∈ chartClosedBall c a ρ
  · have hunion : 𝓝 x = 𝓝[chartClosedBall c a ρ] x ⊔ 𝓝[(chartClosedBall c a ρ)ᶜ] x := by
      rw [← nhdsWithin_univ (a := x), ← Set.union_compl_self (chartClosedBall c a ρ),
        nhdsWithin_union]
    rw [ContinuousAt, hone x hx, hunion]
    refine Filter.Tendsto.sup ?_ ?_
    · show Tendsto h (𝓝[chartClosedBall c a ρ] x) (𝓝 1)
      have hev : h =ᶠ[𝓝[chartClosedBall c a ρ] x] fun _ : X => (1 : ℝ) := by
        filter_upwards [self_mem_nhdsWithin] with y hy
        exact hone y hy
      exact tendsto_const_nhds.congr' hev.symm
    · by_cases hsph : x ∈ chartSphere c a ρ
      · -- a point of the inner sphere: the annulus and the complement of the closed
        -- disc define the same filter, since the chart ball of radius `ρ₂` is a
        -- neighbourhood of `x`
        have hxball₂ : x ∈ chartBall c a ρ₂ := by
          obtain ⟨hsrc, hsph'⟩ := mem_chartSphere.mp hsph
          refine ⟨hsrc, ?_⟩
          rw [Metric.mem_sphere, dist_eq_norm] at hsph'
          show c x ∈ Metric.ball a ρ₂
          rw [Metric.mem_ball, dist_eq_norm]
          rw [hsph']
          exact hρρ₂
        have hEq : 𝓝[chartBall c a ρ₂ \ chartClosedBall c a ρ] x
            = 𝓝[(chartClosedBall c a ρ)ᶜ] x := by
          rw [Set.diff_eq, nhdsWithin_inter,
            nhdsWithin_eq_nhds.mpr ((chartBall_isOpen c a ρ₂).mem_nhds hxball₂),
            inf_eq_right.mpr (nhdsWithin_le_nhds (a := x))]
        refine tendsto_order.2 ⟨fun b hb => ?_, fun b hb => ?_⟩
        · have hε : 0 < (1 - b) / 2 := by linarith
          have hE : ∀ᶠ y in 𝓝[(chartClosedBall c a ρ)ᶜ] x, 1 - (1 - b) / 2 ≤ h y :=
            hEq ▸ hlim x hsph ((1 - b) / 2) hε
          filter_upwards [hE] with y hy
          linarith
        · exact Eventually.of_forall fun y => lt_of_le_of_lt (hub y) hb
      · -- `x` is in the open chart ball: the complement is not a neighbourhood of `x`
        have hxball : x ∈ chartBall c a ρ := by
          have hpre : c x ∈ Metric.closedBall a ρ := hx.2
          rw [← Metric.ball_union_sphere] at hpre
          rcases hpre with hb | hs
          · exact ⟨hx.1, hb⟩
          · exact absurd (mem_chartSphere.mpr ⟨hx.1, hs⟩) hsph
        have hdisj : Disjoint (chartBall c a ρ) ((chartClosedBall c a ρ)ᶜ) :=
          Set.disjoint_left.mpr (fun y hy hyc =>
            hyc (chartBall_subset_chartClosedBall c a ρ hy))
        have hbot : 𝓝[(chartClosedBall c a ρ)ᶜ] x = ⊥ := by
          have hinf : 𝓝 x ⊓ 𝓟 ((chartClosedBall c a ρ)ᶜ) = ⊥ := by
            rw [Filter.inf_eq_bot_iff]
            exact ⟨chartBall c a ρ, (chartBall_isOpen c a ρ).mem_nhds hxball,
              (chartClosedBall c a ρ)ᶜ, Filter.mem_principal_self _,
              Set.disjoint_iff_inter_eq_empty.mp hdisj⟩
          show 𝓝 x ⊓ 𝓟 ((chartClosedBall c a ρ)ᶜ) = ⊥
          exact hinf
        rw [hbot]
        exact tendsto_bot
  · exact (hharm x hx).continuousAt

/-- **Continuity of the hitting probability.** -/
theorem continuous_hittingProbability {z₀ : X} {ρ ρ₂ : ℝ} (hρ : 0 < ρ) (hρρ₂ : ρ < ρ₂)
    (hsub₂ : Metric.closedBall (chartAt ℂ z₀ z₀) ρ₂ ⊆ (chartAt ℂ z₀).target) :
    Continuous (hittingProbability (chartAt ℂ z₀) (chartAt ℂ z₀ z₀) ρ) := by
  have hsub : Metric.closedBall (chartAt ℂ z₀ z₀) ρ ⊆ (chartAt ℂ z₀).target :=
    (Metric.closedBall_subset_closedBall hρρ₂.le).trans hsub₂
  refine continuous_iff_continuousAt.mpr fun x => ?_
  exact continuousAt_of_chart_data (c := chartAt ℂ z₀) (a := chartAt ℂ z₀ z₀)
    (ρ := ρ) (ρ₂ := ρ₂) hρ hρρ₂ hsub₂
    (fun x hx => hittingProbability_eq_one_of_mem_chartClosedBall hρ hsub hx)
    (harmonicOnX_hittingProbability hρ hsub)
    (fun ξ hξ ε hε => hittingProbability_tendsto_one_at_sphere hρ hρρ₂ hsub₂ ξ hξ ε hε)
    (fun x => hittingProbability_le_one (chartAt ℂ z₀) (chartAt ℂ z₀ z₀) ρ x) x

end Continuity

/-! ## The Dirichlet solution on a disc, with its mean value at the centre -/

/-- **The Dirichlet solution on a disc.**  For continuous boundary data `F` on the sphere
`Metric.sphere p r` there is a function `H`, harmonic on `Metric.ball p r`, continuous on the
closed ball, agreeing with `F` on the sphere and having the mean value `Real.circleAverage F p r`
at the centre. -/
theorem exists_dirichlet_on_ball {p : ℂ} {r : ℝ} (hr : 0 < r) {F : ℂ → ℝ}
    (hF : ContinuousOn F (Metric.sphere p r)) :
    ∃ H : ℂ → ℝ, (∀ z ∈ Metric.ball p r, InnerProductSpace.HarmonicAt H z) ∧
      ContinuousOn H (Metric.closedBall p r) ∧
      (∀ ζ ∈ Metric.sphere p r, H ζ = F ζ) ∧ H p = Real.circleAverage F p r := by
  let g : ℂ → ℝ := fun w => F (p + w)
  have hg : ContinuousOn g (Metric.sphere (0 : ℂ) r) := by
    refine hF.comp (by fun_prop) ?_
    intro w hw
    rw [Metric.mem_sphere, dist_eq_norm] at hw ⊢
    simpa using hw
  obtain ⟨P, hPcoc, hPg⟩ :=
    Commons.Analysis.Complex.Harmonic.dirichlet_circle_boundary (g := g) (r := r) hr hg
  have hharm : ∀ z ∈ Metric.ball p r, InnerProductSpace.HarmonicAt (fun y : ℂ => P (y - p)) z := by
    intro z hz
    have hz' : z - p ∈ Metric.ball (0 : ℂ) r := by
      simpa [Metric.mem_ball, dist_eq_norm] using hz
    have hP : InnerProductSpace.HarmonicAt P (z - p) := hPcoc.harmonicOnNhd (z - p) hz'
    have hf : AnalyticAt ℂ (fun y : ℂ => y - p) z := analyticAt_id.sub analyticAt_const
    exact Commons.Analysis.InnerProductSpace.harmonicAt_comp_analytic hf hP
  have hcont : ContinuousOn (fun y : ℂ => P (y - p)) (Metric.closedBall p r) := by
    have hPcont : ContinuousOn P (Metric.closedBall (0 : ℂ) r) :=
      InnerProductSpace.HarmonicContOnCl.continuousOn_ball hPcoc
    refine hPcont.comp (by fun_prop) ?_
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm] at hz ⊢
    simpa using hz
  have hsph : ∀ ζ ∈ Metric.sphere p r, P (ζ - p) = F ζ := by
    intro ζ hζ
    have hζ' : ‖ζ - p‖ = r := by
      rw [Metric.mem_sphere, dist_eq_norm] at hζ
      exact hζ
    rw [hPg (ζ - p) hζ']
    show F (p + (ζ - p)) = F ζ
    rw [add_sub_cancel]
  refine ⟨fun y : ℂ => P (y - p), hharm, hcont, hsph, ?_⟩
  have hcoc : InnerProductSpace.HarmonicContOnCl (fun y : ℂ => P (y - p)) (Metric.ball p r) :=
    InnerProductSpace.HarmonicContOnCl.mk_ball hharm hcont
  have hmvp : Real.circleAverage (fun y : ℂ => P (y - p)) p r = P (p - p) :=
    InnerProductSpace.HarmonicContOnCl.circleAverage_eq (R := r)
      (by simpa [abs_of_pos hr] using hcoc)
  rw [sub_self] at hmvp
  have hcongr : Real.circleAverage (fun y : ℂ => P (y - p)) p r = Real.circleAverage F p r :=
    Real.circleAverage_congr_sphere (f₁ := fun y : ℂ => P (y - p)) (f₂ := F)
      (fun z hz => hsph z (by
        rw [Metric.mem_sphere, dist_eq_norm] at hz ⊢
        rwa [abs_of_pos hr] at hz))
  have h0 : (fun y : ℂ => P (y - p)) p = P 0 := by simp
  rw [h0, ← hcongr]
  exact hmvp.symm

/-! ## The circle mean-value inequality for the balayage -/

section Subharmonic

variable {c : OpenPartialHomeomorph X ℂ} {a : ℂ} {ρ : ℝ}

/-- **The balayage satisfies the circle mean-value inequality in the preferred chart at `x`.**

The proof compares every member `v` of the hitting family with the Dirichlet solution `H` on a
disc `D` inside the chart ball: since `v` agrees with `balayage` outside the chart disc and is
dominated by it, the maximum principle with a *local* sub-mean-value hypothesis (valid for
`v - H` because `v` is subharmonic and `H` is harmonic) gives `v ≤ H` on `D`, whence
`v (x) ≤ ⨍ H = ⨍ balayage`.  Taking the supremum over the members gives the mean-value inequality
for the balayage. -/
theorem subharmonicAtChart_balayage (hcont : Continuous (balayage c a ρ)) (x : X) :
    SubharmonicAtChart (balayage c a ρ) (chartAt ℂ x) x := by
  obtain ⟨ρ₁, hρ₁, hρ₁tgt⟩ := Metric.mem_nhds_iff.mp
    ((chartAt ℂ x).open_target.mem_nhds ((chartAt ℂ x).map_source (mem_chart_source ℂ x)))
  have hxsrc : x ∈ (chartAt ℂ x).source := mem_chart_source ℂ x
  have hx' : (chartAt ℂ x).symm ((chartAt ℂ x) x) = x := (chartAt ℂ x).left_inv hxsrc
  refine ⟨hxsrc, ρ₁, hρ₁, hρ₁tgt, ?_, ?_⟩
  · -- continuity of the pullback
    refine hcont.continuousOn.comp
      (((chartAt ℂ x).continuousOn_symm).mono (fun z hz => hρ₁tgt hz)) (fun z hz => mem_univ _)
  · intro p hp r hr hpr
    -- the pullback of the balayage
    have hbalf : (balayage c a ρ ∘ (chartAt ℂ x).symm) = fun w : ℂ => balayage c a ρ
        ((chartAt ℂ x).symm w) := rfl
    have hsphere_sub : Metric.sphere p r ⊆ Metric.ball ((chartAt ℂ x) x) ρ₁ :=
      (Metric.sphere_subset_closedBall).trans hpr
    -- the boundary data
    have hgcont : ContinuousOn (fun w : ℂ => balayage c a ρ ((chartAt ℂ x).symm w))
        (Metric.sphere p r) := by
      refine hcont.continuousOn.comp
        (((chartAt ℂ x).continuousOn_symm).mono (fun z hz => hρ₁tgt (hsphere_sub hz)))
        (fun z hz => mem_univ _)
    -- the Dirichlet solution
    obtain ⟨H, hHharm, hHcont, hHsph, hHavg⟩ :=
      exists_dirichlet_on_ball (p := p) (r := r) hr
        (F := fun w : ℂ => balayage c a ρ ((chartAt ℂ x).symm w)) hgcont
    -- the local subharmonicity of a member, measured in the chart at `x`
    have hmem_sub : ∀ v ∈ hittingFamily c a ρ, ∀ q ∈ Metric.ball ((chartAt ℂ x) x) ρ₁,
        SubharmonicAtChart v (chartAt ℂ x) ((chartAt ℂ x).symm q) := by
      intro v hv q hq
      have hqsrc : (chartAt ℂ x).symm q ∈ (chartAt ℂ x).source :=
        (chartAt ℂ x).map_target (hρ₁tgt hq)
      exact (SubharmonicAtChart_iff_chartAt (u := v) (a := (chartAt ℂ x).symm q) (b := x)
        hqsrc).mp (hv.1.2 _ (mem_univ _))
    -- the member inequality
    have hkey : ∀ v ∈ hittingFamily c a ρ, v ((chartAt ℂ x).symm p) ≤
        Real.circleAverage (fun w : ℂ => balayage c a ρ ((chartAt ℂ x).symm w)) p r := by
      intro v hv
      have hvcont : Continuous v := by
        have h := hv.1.1
        rwa [continuousOn_univ] at h
      have hv'cont : ContinuousOn (fun q : ℂ => v ((chartAt ℂ x).symm q))
          (Metric.closedBall p r) :=
        hvcont.continuousOn.comp
          (((chartAt ℂ x).continuousOn_symm).mono (fun z hz => hρ₁tgt (hpr hz)))
          (fun z hz => mem_univ _)
      have hwcont : ContinuousOn (fun q : ℂ => v ((chartAt ℂ x).symm q) - H q)
          (closure (Metric.ball p r)) := by
        rw [closure_ball p hr.ne']
        exact hv'cont.sub hHcont
      have hloc : ∀ q ∈ Metric.ball p r, ∃ ε : ℝ, 0 < ε ∧ Metric.ball q ε ⊆ Metric.ball p r ∧
          ∀ r' : ℝ, 0 < r' → Metric.closedBall q r' ⊆ Metric.ball q ε →
            (v ((chartAt ℂ x).symm q) - H q) ≤
              Real.circleAverage (fun z : ℂ => v ((chartAt ℂ x).symm z) - H z) q r' := by
        intro q hq
        have hqd : dist q p < r := by
          have h := Metric.mem_ball.mp hq
          rwa [dist_comm] at h
        have hq₁ : q ∈ Metric.ball ((chartAt ℂ x) x) ρ₁ := hpr (Metric.ball_subset_closedBall hq)
        have hqtgt : q ∈ (chartAt ℂ x).target := hρ₁tgt hq₁
        have hqeq : (chartAt ℂ x) ((chartAt ℂ x).symm q) = q := (chartAt ℂ x).right_inv hqtgt
        obtain ⟨-, ρv, hρv, htgtv, hcontv, hmvpv⟩ := hmem_sub v hv q hq₁
        rw [hqeq] at hmvpv
        set ε : ℝ := min ρv ((r - dist q p) / 2) with hεdef
        have hε : 0 < ε := lt_min hρv (by linarith)
        have hεr : ε ≤ (r - dist q p) / 2 := min_le_right _ _
        have hερv : ε ≤ ρv := min_le_left _ _
        have hεsub : Metric.ball q ε ⊆ Metric.ball p r := by
          intro z hz
          rw [Metric.mem_ball] at hz ⊢
          calc dist z p ≤ dist z q + dist q p := dist_triangle _ _ _
            _ < ε + dist q p := by linarith
            _ ≤ (r - dist q p) / 2 + dist q p := by linarith
            _ < r := by linarith
        refine ⟨ε, hε, hεsub, ?_⟩
        intro r' hr' hr'sub
        have hclosed : Metric.closedBall q r' ⊆ Metric.ball p r := hr'sub.trans hεsub
        have hv_mvp : v ((chartAt ℂ x).symm q) ≤
            Real.circleAverage (fun z : ℂ => v ((chartAt ℂ x).symm z)) q r' := by
          have h1 := hmvpv q (Metric.mem_ball_self hρv) r' hr'
            (hr'sub.trans (Metric.ball_subset_ball hερv))
          simpa [Function.comp_def] using h1
        have hHmvp : Real.circleAverage H q r' = H q := by
          have hcoc : InnerProductSpace.HarmonicContOnCl H (Metric.ball q |r'|) := by
            rw [abs_of_pos hr']
            exact InnerProductSpace.HarmonicContOnCl.mk_ball
              (fun z hz => hHharm z (hclosed (Metric.ball_subset_closedBall hz)))
              (hHcont.mono (hclosed.trans Metric.ball_subset_closedBall))
          exact InnerProductSpace.HarmonicContOnCl.circleAverage_eq (R := r') hcoc
        have hInt1 : CircleIntegrable (fun z : ℂ => v ((chartAt ℂ x).symm z)) q r' :=
          ((hv'cont.mono (hclosed.trans Metric.ball_subset_closedBall)).mono
            Metric.sphere_subset_closedBall).circleIntegrable (le_of_lt hr')
        have hInt2 : CircleIntegrable H q r' :=
          ((hHcont.mono (hclosed.trans Metric.ball_subset_closedBall)).mono
            Metric.sphere_subset_closedBall).circleIntegrable (le_of_lt hr')
        show v ((chartAt ℂ x).symm q) - H q ≤
          Real.circleAverage (fun z : ℂ => v ((chartAt ℂ x).symm z) - H z) q r'
        rw [show Real.circleAverage (fun z : ℂ => v ((chartAt ℂ x).symm z) - H z) q r'
            = Real.circleAverage (fun z : ℂ => v ((chartAt ℂ x).symm z)) q r'
              - Real.circleAverage H q r' from Real.circleAverage_sub hInt1 hInt2, hHmvp]
        linarith
      have hbd : ∀ z ∈ closure (Metric.ball p r), z ∉ Metric.ball p r →
          (v ((chartAt ℂ x).symm z) - H z) ≤ 0 := by
        intro z hzcl hznot
        rw [closure_ball p hr.ne'] at hzcl
        have hzsph : z ∈ Metric.sphere p r := by
          refine Metric.mem_sphere.mpr ?_
          rw [Metric.mem_closedBall, dist_eq_norm] at hzcl
          rw [Metric.mem_ball, dist_eq_norm] at hznot
          rw [dist_eq_norm]
          exact le_antisymm hzcl (le_of_not_gt hznot)
        have h1 := hittingFamily_mem_le_balayage hv ((chartAt ℂ x).symm z)
        have h2 := hHsph z hzsph
        rw [h2]
        linarith
      have hmp := Commons.Analysis.Complex.Harmonic.max_principle_localSubMeanValue
        Metric.isOpen_ball Metric.isPreconnected_ball Metric.isBounded_ball hwcont hloc hbd
      have hp' : p ∈ Metric.ball p r := Metric.mem_ball_self hr
      have hfin := hmp p hp'
      rw [hHavg] at hfin
      linarith
    -- the supremum over the members
    rw [hbalf]
    show balayage c a ρ ((chartAt ℂ x).symm p) ≤
      Real.circleAverage (fun w : ℂ => balayage c a ρ ((chartAt ℂ x).symm w)) p r
    rw [balayage, upperEnvelope]
    refine csSup_le ((hittingFamily_nonempty c a ρ).image _) ?_
    rintro y ⟨v, hv, rfl⟩
    exact hkey v hv

end Subharmonic


/-! ## Scaling by a nonnegative constant -/

section Scaling

variable {c' : OpenPartialHomeomorph X ℂ} {x : X} {u : X → ℝ}

/-- Multiplication by a nonnegative constant preserves the circle mean-value inequality in a
chart. -/
theorem SubharmonicAtChart.const_mul {k : ℝ} (hk : 0 ≤ k) (h : SubharmonicAtChart u c' x) :
    SubharmonicAtChart (fun y => k * u y) c' x := by
  obtain ⟨hsrc, ρ, hρ, hsub, hcont, hmvp⟩ := h
  have hfun : (fun y => k * u y) ∘ c'.symm = fun w => k * (u ∘ c'.symm) w := by
    funext w; rfl
  refine ⟨hsrc, ρ, hρ, hsub, ?_, ?_⟩
  · rw [hfun]
    exact hcont.const_mul k
  · intro p hp r hr hrsub
    have hca : Real.circleAverage (fun w => k * (u ∘ c'.symm) w) p r
        = k * Real.circleAverage (u ∘ c'.symm) p r := by
      simpa using Real.circleAverage_fun_smul (f := u ∘ c'.symm) (a := k) (c := p) (R := r)
    rw [hfun, hca]
    exact mul_le_mul_of_nonneg_left (hmvp p hp r hr hrsub) hk

/-- Multiplication by a nonnegative constant preserves subharmonicity at a point. -/
theorem SubharmonicOnXAt.const_mul {k : ℝ} (hk : 0 ≤ k) (h : SubharmonicOnXAt u x) :
    SubharmonicOnXAt (fun y => k * u y) x :=
  SubharmonicAtChart.const_mul hk h

/-- Multiplication by a nonnegative constant preserves subharmonicity. -/
theorem SubharmonicOnX.const_mul {s : Set X} {k : ℝ} (hk : 0 ≤ k)
    (h : SubharmonicOnX u s) : SubharmonicOnX (fun y => k * u y) s :=
  ⟨h.1.const_mul k, fun y hy => (h.2 y hy).const_mul hk⟩

/-- Multiplication by a nonnegative constant preserves the reverse circle mean-value inequality in
a chart. -/
theorem SuperharmonicAtChart.const_mul {k : ℝ} (hk : 0 ≤ k) (h : SuperharmonicAtChart u c' x) :
    SuperharmonicAtChart (fun y => k * u y) c' x := by
  obtain ⟨hsrc, ρ, hρ, hsub, hcont, hmvp⟩ := h
  have hfun : (fun y => k * u y) ∘ c'.symm = fun w => k * (u ∘ c'.symm) w := by
    funext w; rfl
  have hca : ∀ p r, Real.circleAverage (fun w => k * (u ∘ c'.symm) w) p r
      = k * Real.circleAverage (u ∘ c'.symm) p r := fun p r => by
    simpa using Real.circleAverage_fun_smul (f := u ∘ c'.symm) (a := k) (c := p) (R := r)
  refine ⟨hsrc, ρ, hρ, hsub, ?_, ?_⟩
  · rw [hfun]
    exact hcont.const_mul k
  · intro p hp r hr hrsub
    rw [hfun, hca]
    exact mul_le_mul_of_nonneg_left (hmvp p hp r hr hrsub) hk

/-- Multiplication by a nonnegative constant preserves superharmonicity at a point. -/
theorem SuperharmonicOnXAt.const_mul {k : ℝ} (hk : 0 ≤ k) (h : SuperharmonicOnXAt u x) :
    SuperharmonicOnXAt (fun y => k * u y) x :=
  SuperharmonicAtChart.const_mul hk h

/-- Multiplication by a nonnegative constant preserves superharmonicity. -/
theorem SuperharmonicOnX.const_mul {s : Set X} {k : ℝ} (hk : 0 ≤ k)
    (h : SuperharmonicOnX u s) : SuperharmonicOnX (fun y => k * u y) s :=
  ⟨h.1.const_mul k, fun y hy => (h.2 y hy).const_mul hk⟩

end Scaling

/-! ## The main consequences -/

section Main

/-- The balayage is continuous. -/
theorem continuous_balayage {z₀ : X} {ρ ρ₂ : ℝ} (hρ : 0 < ρ) (hρρ₂ : ρ < ρ₂)
    (hsub₂ : Metric.closedBall (chartAt ℂ z₀ z₀) ρ₂ ⊆ (chartAt ℂ z₀).target) :
    Continuous (balayage (chartAt ℂ z₀) (chartAt ℂ z₀ z₀) ρ) := by
  have h := (continuous_hittingProbability (z₀ := z₀) hρ hρρ₂ hsub₂).neg
  have hfun : balayage (chartAt ℂ z₀) (chartAt ℂ z₀ z₀) ρ
      = fun x => -hittingProbability (chartAt ℂ z₀) (chartAt ℂ z₀ z₀) ρ x := by
    funext x
    simp [hittingProbability]
  rwa [hfun]

/-- **The balayage is subharmonic on all of `X`.** -/
theorem subharmonicOnX_balayage {z₀ : X} {ρ ρ₂ : ℝ} (hρ : 0 < ρ) (hρρ₂ : ρ < ρ₂)
    (hsub₂ : Metric.closedBall (chartAt ℂ z₀ z₀) ρ₂ ⊆ (chartAt ℂ z₀).target) :
    SubharmonicOnX (balayage (chartAt ℂ z₀) (chartAt ℂ z₀ z₀) ρ) univ :=
  ⟨(continuous_balayage hρ hρρ₂ hsub₂).continuousOn,
    fun x _ => subharmonicAtChart_balayage (continuous_balayage hρ hρρ₂ hsub₂) x⟩

/-- **The hitting probability is superharmonic on all of `X`.** -/
theorem superharmonicOnX_hittingProbability {z₀ : X} {ρ ρ₂ : ℝ} (hρ : 0 < ρ)
    (hρρ₂ : ρ < ρ₂)
    (hsub₂ : Metric.closedBall (chartAt ℂ z₀ z₀) ρ₂ ⊆ (chartAt ℂ z₀).target) :
    SuperharmonicOnX (hittingProbability (chartAt ℂ z₀) (chartAt ℂ z₀ z₀) ρ) univ := by
  have h := (subharmonicOnX_balayage (z₀ := z₀) hρ hρρ₂ hsub₂).neg
  have hfun : (fun x => -balayage (chartAt ℂ z₀) (chartAt ℂ z₀ z₀) ρ x)
      = hittingProbability (chartAt ℂ z₀) (chartAt ℂ z₀ z₀) ρ := by
    funext x
    simp [hittingProbability]
  rwa [hfun] at h

/-- **The normalised hitting probability `greenPsi` is superharmonic on all of `X`.** -/
theorem superharmonicOnX_greenPsi (z₀ : X) {ρ ρ₂ : ℝ} (hρ : 0 < ρ) (hρρ₂ : ρ < ρ₂)
    (hsub₂ : Metric.closedBall (chartAt ℂ z₀ z₀) ρ₂ ⊆ (chartAt ℂ z₀).target) :
    SuperharmonicOnX (greenPsi z₀ ρ₂ ρ) univ := by
  have hlog : 0 ≤ Real.log (ρ₂ / ρ) := Real.log_nonneg (by rw [le_div_iff₀ hρ]; linarith)
  have hbase := superharmonicOnX_hittingProbability (z₀ := z₀) hρ hρρ₂ hsub₂
  have hscaled := SuperharmonicOnX.const_mul (u := hittingProbability (chartAt ℂ z₀) (chartAt ℂ z₀ z₀) ρ) hlog hbase
  have hfun : (fun y => Real.log (ρ₂ / ρ) * hittingProbability (chartAt ℂ z₀) (chartAt ℂ z₀ z₀) ρ y)
      = greenPsi z₀ ρ₂ ρ := by
    funext y
    rw [greenPsi_apply]
  rwa [hfun] at hscaled

end Main

end Submission
