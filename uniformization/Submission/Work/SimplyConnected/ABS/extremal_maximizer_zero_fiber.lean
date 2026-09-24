import Mathlib
import Submission.Work.SimplyConnected.ABS.ExtremalImports
import Submission.Commons.Analysis.Complex.exists_ball_factorization_of_analyticAt_zero
import Submission.Work.SimplyConnected.ABS.norm_le_exp_neg_of_unitGreen
import Submission.GreenConditional
import Submission.SweepMember
import Submission.ChartLogClamp
import Submission.Work.SimplyConnected.ABS.exists_posHarmonic_logPole_dominating
import Submission.Work.SimplyConnected.ABS.modulusLP_main
import Submission.Work.SimplyConnected.ABS.periods_of_circleCharacter_trivial
import Submission.Work.SimplyConnected.exists_diffeomorph_plane_or_upperHalfPlane_of_isUnitGreenFunction
import Submission.Work.SimplyConnected.ABS.modulus_of_single_zero
import Submission.Work.SimplyConnected.ABS.isPreconnected_compl_closedDiscrete

/-!
# The zero fibre of a dominating single-zero member of the extremal family

-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology
set_option linter.unusedSectionVars false
noncomputable section
open Filter Set Classical

namespace Work.SimplyConnected.ABS

variable {X : Type*} [TopologicalSpace X] [T2Space X]
    [ConnectedSpace X] [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- The local holomorphic extension of the quotient `f/Φ` at `x₀`. -/
theorem analyticAt_quotient_extension {x₀ : X} {f Φ : X → ℂ}
    (hf : AnalyticAt ℂ (f ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀))
    (hf0 : f x₀ = 0)
    (hpos : deriv (f ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀) ≠ 0)
    (hΦc : AnalyticAt ℂ (Φ ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀))
    (hΦsimple : ∃ H : ℂ → ℂ, AnalyticAt ℂ H ((chartAt ℂ x₀) x₀) ∧ H ((chartAt ℂ x₀) x₀) ≠ 0 ∧
      Filter.EventuallyEq (nhds ((chartAt ℂ x₀) x₀)) (Φ ∘ (chartAt ℂ x₀).symm)
        (fun w : ℂ => (w - (chartAt ℂ x₀) x₀) * H w)) :
    ∃ V : ℂ, AnalyticAt ℂ (Function.update (fun w => f ((chartAt ℂ x₀).symm w) / Φ ((chartAt ℂ x₀).symm w))
        ((chartAt ℂ x₀) x₀) V) ((chartAt ℂ x₀) x₀) := by
  classical
  have hnotzero : ¬ ∀ᶠ w in nhds ((chartAt ℂ x₀) x₀),
      (f ∘ (chartAt ℂ x₀).symm) w = 0 := by
    intro h
    have hd : deriv (f ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀) = 0 := by
      have hc0 : (f ∘ (chartAt ℂ x₀).symm) =ᶠ[nhds ((chartAt ℂ x₀) x₀)] fun _ => (0 : ℂ) := h
      rw [hc0.deriv_eq]
      simp
    exact hpos hd
  obtain ⟨k, g, hgana, hgne, hgeq⟩ := hf.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hnotzero
  have hk1 : 1 ≤ k := by
    by_contra h
    rw [not_le] at h
    have hk0 : k = 0 := Nat.lt_one_iff.mp h
    have h0 : (f ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀) = 0 := by
      simp [Function.comp_apply, (chartAt ℂ x₀).left_inv (mem_chart_source ℂ x₀), hf0]
    have h1 := hgeq.self_of_nhds
    rw [h0, hk0, pow_zero, one_smul] at h1
    exact hgne h1.symm
  obtain ⟨H, hHana, hHne, hHeq⟩ := hΦsimple
  set F₁ : ℂ → ℂ := fun w => (w - (chartAt ℂ x₀) x₀) ^ (k - 1) * g w with hF₁
  have hF₁ana : AnalyticAt ℂ F₁ ((chartAt ℂ x₀) x₀) :=
    ((analyticAt_id.sub analyticAt_const).pow _).mul hgana
  have hfeq : (f ∘ (chartAt ℂ x₀).symm) =ᶠ[nhds ((chartAt ℂ x₀) x₀)]
      fun w => (w - (chartAt ℂ x₀) x₀) * F₁ w := by
    filter_upwards [hgeq] with w hw
    rw [hw, hF₁, smul_eq_mul]
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    rw [hj]
    simp only [Nat.succ_eq_add_one]
    rw [show j + 1 - 1 = j from by omega, pow_succ]
    ring
  refine ⟨F₁ ((chartAt ℂ x₀) x₀) / H ((chartAt ℂ x₀) x₀), ?_⟩
  have hHF : AnalyticAt ℂ (fun w => F₁ w / H w) ((chartAt ℂ x₀) x₀) := hF₁ana.div hHana hHne
  refine hHF.congr ?_
  have hHev : ∀ᶠ w in nhds ((chartAt ℂ x₀) x₀), H w ≠ 0 :=
    hHana.continuousAt.eventually_ne hHne
  have hsub : ∀ᶠ w in nhds ((chartAt ℂ x₀) x₀), w - (chartAt ℂ x₀) x₀ ≠ 0 ∨ w = (chartAt ℂ x₀) x₀ := by
    filter_upwards with w
    by_cases h : w = (chartAt ℂ x₀) x₀
    · exact Or.inr h
    · exact Or.inl (sub_ne_zero.mpr h)
  filter_upwards [hHev, hHeq, hfeq, hsub] with w hHw hΦw hfw hsub
  by_cases hw : w = (chartAt ℂ x₀) x₀
  · subst hw
    rw [Function.update_self]
  · have hsub' : w - (chartAt ℂ x₀) x₀ ≠ 0 := sub_ne_zero.mpr hw
    rw [Function.update_apply, if_neg hw]
    rw [show f ((chartAt ℂ x₀).symm w) = (w - (chartAt ℂ x₀) x₀) * F₁ w from
        by simpa only [Function.comp_apply] using hfw,
      show Φ ((chartAt ℂ x₀).symm w) = (w - (chartAt ℂ x₀) x₀) * H w from
        by simpa only [Function.comp_apply] using hΦw]
    field_simp


end Work.SimplyConnected.ABS

namespace Work.SimplyConnected.ABS

variable {X : Type*} [TopologicalSpace X] [T2Space X]
    [ConnectedSpace X] [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **The zero fibre of a function that attains a strictly positive modulus.**  If `f` vanishes at
`x₀` and `‖f x‖ = exp (-(E x))` for every `x ≠ x₀`, then `f` has no other zero: the modulus `exp (-E)`
never vanishes.

This is the form in which the *rigidity* of the extremal maximiser
(`Work.SimplyConnected.ABS.rigidity_of_maximizer_of_modulus`, or the ABS-route theorem
`Work.SimplyConnected.ABS.rigidity_of_maximizer`) yields the zero-fibre statement, without any
domination hypothesis. -/
theorem zero_fiber_of_rigidity {x₀ : X} {E : X → ℝ} {f : X → ℂ} (hf0 : f x₀ = 0)
    (hrig : ∀ x : X, x ≠ x₀ → ‖f x‖ = Real.exp (-(E x))) :
    f ⁻¹' {0} = {x₀} := by
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · intro hx
    by_contra hne
    have h := hrig x hne
    rw [hx, norm_zero] at h
    exact Real.exp_ne_zero (-(E x)) h.symm
  · intro hx
    rw [hx]
    exact hf0

theorem zero_fiber_of_dominating_single_zero {x₀ : X} {f Φ : X → ℂ}
    (hf : f ∈ Submission.extremalFamily x₀)
    (hmax : ∀ g ∈ Submission.extremalFamily x₀,
      ‖deriv (g ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀)‖ ≤
        ‖deriv (f ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀)‖)
    (hpos : 0 < ‖deriv (f ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀)‖)
    (hΦ : Φ ∈ Submission.extremalFamily x₀)
    (hΦ0 : Φ ⁻¹' {0} = {x₀})
    (hΦsimple : ∃ H : ℂ → ℂ, AnalyticAt ℂ H ((chartAt ℂ x₀) x₀) ∧ H ((chartAt ℂ x₀) x₀) ≠ 0 ∧
      Filter.EventuallyEq (nhds ((chartAt ℂ x₀) x₀)) (Φ ∘ (chartAt ℂ x₀).symm)
        (fun w : ℂ => (w - (chartAt ℂ x₀) x₀) * H w))
    (hdom : ∀ g ∈ Submission.extremalFamily x₀, ∀ x : X, ‖g x‖ ≤ ‖Φ x‖) :
    f ⁻¹' {0} = {x₀} := by
  classical
  have hsrc : x₀ ∈ (chartAt ℂ x₀).source := mem_chart_source ℂ x₀
  have hsymm : (chartAt ℂ x₀).symm ((chartAt ℂ x₀) x₀) = x₀ := (chartAt ℂ x₀).left_inv hsrc
  have hfc : AnalyticAt ℂ (f ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀) := hf.1 x₀ (mem_univ x₀)
  have hΦc : AnalyticAt ℂ (Φ ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀) := hΦ.1 x₀ (mem_univ x₀)
  have hpos' : deriv (f ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hpos
    exact lt_irrefl 0 hpos
  obtain ⟨V, hVana⟩ := analyticAt_quotient_extension (x₀ := x₀) (f := f) (Φ := Φ)
    hfc hf.2.2 hpos' hΦc hΦsimple
  let R : X → ℂ := fun x => if x = x₀ then V else f x / Φ x
  have hRval : ∀ x : X, x ≠ x₀ → R x = f x / Φ x := fun x hx => by simp only [R, if_neg hx]
  have hRval₀ : R x₀ = V := by simp only [R, ↓reduceIte]
  have hmemb : ∀ x : X, Φ x = 0 → x = x₀ := fun x hx => by
    have h1 : x ∈ Φ ⁻¹' {0} := hx
    rw [hΦ0] at h1
    simpa using h1
  have hRc : (R ∘ (chartAt ℂ x₀).symm) =ᶠ[nhds ((chartAt ℂ x₀) x₀)]
      Function.update (fun w => f ((chartAt ℂ x₀).symm w) / Φ ((chartAt ℂ x₀).symm w))
        ((chartAt ℂ x₀) x₀) V := by
    have hball : ∀ᶠ w in nhds ((chartAt ℂ x₀) x₀), w ∈ (chartAt ℂ x₀).target :=
      (chartAt ℂ x₀).open_target.mem_nhds ((chartAt ℂ x₀).map_source hsrc)
    filter_upwards [hball] with w hw
    by_cases hwz : w = (chartAt ℂ x₀) x₀
    · rw [hwz]
      simp only [Function.comp_apply, R, hsymm, ↓reduceIte, Function.update_self]
    · have hne : (chartAt ℂ x₀).symm w ≠ x₀ := by
        intro h
        have h2 : (chartAt ℂ x₀) ((chartAt ℂ x₀).symm w) = (chartAt ℂ x₀) x₀ := by rw [h]
        rw [(chartAt ℂ x₀).right_inv hw] at h2
        exact hwz h2
      rw [Function.comp_apply, Function.update_apply, if_neg hwz, hRval _ hne]
  have hRana₀ : AnalyticAt ℂ (R ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀) := hVana.congr hRc.symm
  have hRhol : Submission.HolomorphicOnX R Set.univ := by
    intro x hx
    rw [Submission.HolomorphicOnXAt]
    by_cases hxx : x = x₀
    · rw [hxx]
      exact hRana₀
    · have hxne : x ∈ ({x₀}ᶜ : Set X) := hxx
      have hopen : IsOpen ({x₀}ᶜ : Set X) := isClosed_singleton.isOpen_compl
      have hxsrc : x ∈ (chartAt ℂ x).source := mem_chart_source ℂ x
      have hΦne : (Φ ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) ≠ 0 := by
        have hval : (chartAt ℂ x).symm ((chartAt ℂ x) x) = x := (chartAt ℂ x).left_inv hxsrc
        have hx0 : Φ x ≠ 0 := fun h => hxne (hmemb x h)
        simpa only [Function.comp_apply, hval] using hx0
      have han : AnalyticAt ℂ ((f / Φ) ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) :=
        (hf.1 x (mem_univ x)).div (hΦ.1 x (mem_univ x)) hΦne
      refine han.congr ?_
      have hev1 : ∀ᶠ w in nhds ((chartAt ℂ x) x), (chartAt ℂ x).symm w ≠ x₀ := by
        have hcont : ContinuousAt (chartAt ℂ x).symm ((chartAt ℂ x) x) :=
          (chartAt ℂ x).continuousAt_symm ((chartAt ℂ x).map_source hxsrc)
        have hval : (chartAt ℂ x).symm ((chartAt ℂ x) x) = x := (chartAt ℂ x).left_inv hxsrc
        have hmem : (chartAt ℂ x).symm ((chartAt ℂ x) x) ∈ ({x₀}ᶜ : Set X) := by
          rw [hval]; exact hxne
        exact hcont.eventually (hopen.mem_nhds hmem)
      filter_upwards [hev1] with w hw
      show (f / Φ) ((chartAt ℂ x).symm w) = R ((chartAt ℂ x).symm w)
      rw [hRval _ hw, Pi.div_apply]
  have hRle : ∀ x : X, ‖R x‖ ≤ 1 := by
    intro x
    by_cases hxx : x = x₀
    · rw [hxx, hRval₀]
      have hball : ∀ᶠ w in nhds ((chartAt ℂ x₀) x₀), w ∈ (chartAt ℂ x₀).target :=
        (chartAt ℂ x₀).open_target.mem_nhds ((chartAt ℂ x₀).map_source hsrc)
      have hlim : Filter.Tendsto
          (fun w : ℂ => ‖f ((chartAt ℂ x₀).symm w) / Φ ((chartAt ℂ x₀).symm w)‖)
          (𝓝[≠] ((chartAt ℂ x₀) x₀)) (nhds ‖V‖) := by
        have h1 : Filter.Tendsto (R ∘ (chartAt ℂ x₀).symm) (nhds ((chartAt ℂ x₀) x₀)) (nhds V) := by
          have h2 : (R ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀) = V := by
            rw [Function.comp_apply, hsymm, hRval₀]
          rw [← h2]
          exact hRana₀.continuousAt
        have h3 : Filter.Tendsto (R ∘ (chartAt ℂ x₀).symm) (𝓝[≠] ((chartAt ℂ x₀) x₀)) (nhds V) :=
          h1.mono_left inf_le_left
        refine (h3.norm).congr' ?_
        filter_upwards [Filter.Eventually.filter_mono inf_le_left hball, self_mem_nhdsWithin]
          with w hw hwne
        have hne : (chartAt ℂ x₀).symm w ≠ x₀ := by
          intro hcon
          apply hwne
          have h2 : (chartAt ℂ x₀) ((chartAt ℂ x₀).symm w) = (chartAt ℂ x₀) x₀ := by rw [hcon]
          rwa [(chartAt ℂ x₀).right_inv hw] at h2
        rw [Function.comp_apply, hRval _ hne]
      have hbound : ∀ᶠ w in 𝓝[≠] ((chartAt ℂ x₀) x₀),
          ‖f ((chartAt ℂ x₀).symm w) / Φ ((chartAt ℂ x₀).symm w)‖ ≤ 1 := by
        filter_upwards [Filter.Eventually.filter_mono inf_le_left hball, self_mem_nhdsWithin]
          with w hw hwne
        have hne : (chartAt ℂ x₀).symm w ≠ x₀ := by
          intro h
          have h2 : (chartAt ℂ x₀) ((chartAt ℂ x₀).symm w) = (chartAt ℂ x₀) x₀ := by rw [h]
          rw [(chartAt ℂ x₀).right_inv hw] at h2
          exact hwne h2
        have hΦne : Φ ((chartAt ℂ x₀).symm w) ≠ 0 := fun h => hne (hmemb _ h)
        rw [norm_div, div_le_one (norm_pos_iff.mpr hΦne)]
        exact hdom f hf _
      exact le_of_tendsto hlim hbound
    · have hΦne : Φ x ≠ 0 := fun h => hxx (hmemb x h)
      rw [hRval x hxx, norm_div, div_le_one (norm_pos_iff.mpr hΦne)]
      exact hdom f hf x
  have hmul : ∀ x : X, f x = R x * Φ x := by
    intro x
    by_cases hxx : x = x₀
    · rw [hxx]
      rw [hRval₀, hΦ.2.2, mul_zero, hf.2.2]
    · have hΦne : Φ x ≠ 0 := fun h => hxx (hmemb x h)
      rw [hRval x hxx]
      field_simp
  have hderiv : deriv (f ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀) =
      R x₀ * deriv (Φ ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀) := by
    have heqfun : (f ∘ (chartAt ℂ x₀).symm) =ᶠ[nhds ((chartAt ℂ x₀) x₀)]
        fun w => (R ∘ (chartAt ℂ x₀).symm) w * (Φ ∘ (chartAt ℂ x₀).symm) w :=
      Filter.Eventually.of_forall fun w => by
        have := hmul ((chartAt ℂ x₀).symm w)
        simpa only [Function.comp_apply] using this
    have hRz : (R ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀) = R x₀ := by
      simp only [Function.comp_apply, hsymm]
    have hΦz : (Φ ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀) = 0 := by
      simp only [Function.comp_apply, hsymm, hΦ.2.2]
    rw [heqfun.deriv_eq]
    rw [show deriv (fun w => (R ∘ (chartAt ℂ x₀).symm) w * (Φ ∘ (chartAt ℂ x₀).symm) w)
        ((chartAt ℂ x₀) x₀)
        = deriv ((R ∘ (chartAt ℂ x₀).symm) * (Φ ∘ (chartAt ℂ x₀).symm)) ((chartAt ℂ x₀) x₀) from rfl]
    rw [deriv_mul hRana₀.differentiableAt hΦc.differentiableAt, hRz, hΦz, mul_zero, zero_add]
  have hge : 1 ≤ ‖R x₀‖ := by
    have h1 := hmax Φ hΦ
    rw [hderiv, norm_mul] at h1
    have hA : 0 ≤ ‖deriv (Φ ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀)‖ := norm_nonneg _
    have hB : 0 < ‖R x₀‖ * ‖deriv (Φ ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀)‖ := by
      rw [← norm_mul, ← hderiv]
      exact hpos
    have hRnn : 0 ≤ ‖R x₀‖ := norm_nonneg _
    have hApos : 0 < ‖deriv (Φ ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀)‖ := by
      by_contra hcon
      rw [not_lt] at hcon
      have hzero : ‖deriv (Φ ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀)‖ = 0 :=
        le_antisymm hcon hA
      rw [hzero, mul_zero] at hB
      exact lt_irrefl 0 hB
    nlinarith [h1, hApos]
  have hReq : ‖R x₀‖ = 1 := le_antisymm (hRle x₀) hge
  have hconst : ∀ x : X, R x = R x₀ := by
    have hSclosed : IsClosed {x : X | ‖R x‖ = 1} :=
      isClosed_eq hRhol.continuous.norm continuous_const
    have hSopen : IsOpen {x : X | ‖R x‖ = 1} := by
      rw [isOpen_iff_mem_nhds]
      intro y hy
      have hloc : ∀ᶠ x in nhds y, R x = R y := by
        set e : OpenPartialHomeomorph X ℂ := chartAt ℂ y with he
        have hysrc : y ∈ e.source := mem_chart_source ℂ y
        have hana : AnalyticAt ℂ (R ∘ e.symm) (e y) := hRhol y (mem_univ y)
        obtain ⟨ρ, hρ, hρana⟩ := hana.exists_ball_analyticOnNhd
        obtain ⟨ε, hε, hεsub⟩ : ∃ ε > 0, Metric.ball (e y) ε ⊆ e.target :=
          Metric.isOpen_iff.mp e.open_target (e y) (e.map_source hysrc)
        set r : ℝ := min ρ ε with hr
        have hrpos : 0 < r := lt_min hρ hε
        have hrleρ : r ≤ ρ := min_le_left _ _
        have hrleε : r ≤ ε := min_le_right _ _
        have hdiff : DifferentiableOn ℂ (R ∘ e.symm) (Metric.ball (e y) r) :=
          (hρana.mono (Metric.ball_subset_ball hrleρ)).differentiableOn
        have hmax' : IsMaxOn (norm ∘ (R ∘ e.symm)) (Metric.ball (e y) r) (e y) := by
          intro z hz
          have h1 : ‖R (e.symm z)‖ ≤ 1 := hRle _
          have h2 : ‖R y‖ = 1 := hy
          have h3 : e.symm (e y) = y := e.left_inv hysrc
          simp only [Function.comp_apply, h3, h2]
          exact h1
        have hEq := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm
          (f := R ∘ e.symm) (U := Metric.ball (e y) r) (c := e y)
          (convex_ball _ _).isPreconnected Metric.isOpen_ball hdiff
          (Metric.mem_ball_self hrpos) hmax'
        have hpre1 : e.source ∈ nhds y := e.open_source.mem_nhds hysrc
        have hpre2 : e ⁻¹' (Metric.ball (e y) r) ∈ nhds y :=
          (e.continuousAt hysrc).preimage_mem_nhds
            (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hrpos))
        have hpre : e.source ∩ e ⁻¹' (Metric.ball (e y) r) ∈ nhds y :=
          Filter.inter_mem hpre1 hpre2
        filter_upwards [hpre] with x hx
        have hxsrc : x ∈ e.source := hx.1
        have hxball : e x ∈ Metric.ball (e y) r := hx.2
        calc R x = R (e.symm (e x)) := by rw [e.left_inv hxsrc]
          _ = (R ∘ e.symm) (e x) := rfl
          _ = (R ∘ e.symm) (e y) := hEq hxball
          _ = R y := by simp only [Function.comp_apply, e.left_inv hysrc]
      refine Filter.mem_of_superset hloc (fun x hx => ?_)
      simp only [Set.mem_ofPred_eq] at hx ⊢
      rw [hx]
      exact hy
    have hsub : (Set.univ : Set X) ⊆ {x : X | ‖R x‖ = 1} :=
      isPreconnected_univ.subset_isClopen ⟨hSclosed, hSopen⟩ ⟨x₀, mem_univ x₀, hReq⟩
    intro x
    have h1 : ‖R x‖ = ‖R x₀‖ := by rw [hsub (mem_univ x), hsub (mem_univ x₀)]
    exact hRhol.exists_eq_const_of_norm_eq x₀
      (fun y => by rw [hsub (mem_univ y), hsub (mem_univ x₀)]) x
  have hRne : R x₀ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hReq
    exact one_ne_zero hReq.symm
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · intro hx
    have h1 : R x * Φ x = 0 := by rw [← hmul x, hx]
    have h2 : Φ x = 0 := by
      rcases mul_eq_zero.mp h1 with h | h
      · exact absurd (hconst x ▸ h) hRne
      · exact h
    exact hmemb x h2
  · intro hx
    rw [hx]
    exact hf.2.2


end Work.SimplyConnected.ABS

namespace Work.SimplyConnected.ABS

variable {X : Type*} [TopologicalSpace X] [T2Space X]
    [ConnectedSpace X] [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **Assembly, second form — the Perron form of the two inputs.**

This is the form in which the target is actually assembled.  The two inputs are

* `hperp` — Perron's method for the logarithmic pole: for every non-zero member `g` of the
  extremal family there is a positive harmonic `E` on `X \ {x₀}` with a *unit* logarithmic pole at
  `x₀` (`HasLogPoleOn`) which dominates the whole family: `‖h x‖ ≤ exp (-(E x))` for every member
  `h` and every `x ≠ x₀`.  **No decay of `E` at the ideal boundary is required** — in particular no
  Green function in the relative-compactness sense of `Work.Parabolic.IsGreenFunctionAt` and no
  hyperbolicity, only the Perron envelope of the class of subharmonic functions `≤ 0` with a unit
  logarithmic pole at `x₀` (equivalently the sweep of the clamped logarithmic barrier, cut off
  inside the small ball around `x₀` where the other zeros of `g` do not lie).

* `hmod` — the holomorphic modulus of such an `E`: `exp (-(E + iE~))` is single valued because
  every homomorphism `π₁(X,x₀) → ℝ` vanishes.

The proof is `zero_fiber_of_dominating_single_zero` applied to `Φ`: the domination comes from
`hperp` combined with the modulus identity `‖Φ x‖ = exp (-(E x))`. -/
theorem extremal_maximizer_zero_fiber_of_inputs' {x₀ : X}
    [Subsingleton (Additive (FundamentalGroup X x₀) →+ ℝ)]
    (hperp : ∀ {g : X → ℂ}, g ∈ Submission.extremalFamily x₀ → (∃ x : X, g x ≠ 0) →
      ∃ E : X → ℝ,
        (∀ x : X, x ≠ x₀ → 0 < E x) ∧
        Submission.HarmonicOnX E (Set.univ \ {x₀}) ∧
        Work.SimplyConnected.ABS.HasLogPoleOn (Set.univ \ {x₀}) x₀ E ∧
        (∀ h ∈ Submission.extremalFamily x₀, ∀ x : X, x ≠ x₀ → ‖h x‖ ≤ Real.exp (-(E x))))
    (hmod : ∀ {E : X → ℝ},
      (∀ x : X, x ≠ x₀ → 0 < E x) →
      Submission.HarmonicOnX E (Set.univ \ {x₀}) →
      Work.SimplyConnected.ABS.HasLogPoleOn (Set.univ \ {x₀}) x₀ E →
      ∃ Φ : X → ℂ, Submission.HolomorphicOnX Φ Set.univ ∧ Φ x₀ = 0 ∧
        (∀ x : X, x ≠ x₀ → ‖Φ x‖ = Real.exp (-(E x))) ∧
        (∃ H : ℂ → ℂ, AnalyticAt ℂ H ((chartAt ℂ x₀) x₀) ∧ H ((chartAt ℂ x₀) x₀) ≠ 0 ∧
          Filter.EventuallyEq (nhds ((chartAt ℂ x₀) x₀)) (Φ ∘ (chartAt ℂ x₀).symm)
            (fun w : ℂ => (w - (chartAt ℂ x₀) x₀) * H w)))
    {f : X → ℂ}
    (hf : f ∈ Submission.extremalFamily x₀)
    (hmax : ∀ g ∈ Submission.extremalFamily x₀,
      ‖deriv (g ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀)‖ ≤
        ‖deriv (f ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀)‖)
    (hpos : 0 < ‖deriv (f ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀)‖) :
    f ⁻¹' {0} = {x₀} := by
  classical
  -- the extremal value is positive, so `f` is not identically zero
  have hne : ∃ x : X, f x ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have hzero : f = fun _ => (0 : ℂ) := funext fun x => hcon x
    have hd : deriv (f ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀) = 0 := by
      have h1 : (f ∘ (chartAt ℂ x₀).symm) = fun _ => (0 : ℂ) := by
        funext w; simp [hzero]
      rw [h1, deriv_const]
    rw [hd, norm_zero] at hpos
    exact lt_irrefl 0 hpos
  -- Perron's method: `E`
  obtain ⟨E, hEpos, hEharm, hpole, hdom⟩ := hperp hf hne
  -- the holomorphic modulus of `E`
  obtain ⟨Φ, hΦhol, hΦzero, hΦmod, hΦsimple⟩ := hmod hEpos hEharm hpole
  -- `Φ` lies in the extremal family: `E > 0` off the pole gives `‖Φ‖ ≤ 1`
  have hΦmem : Φ ∈ Submission.extremalFamily x₀ := by
    refine ⟨hΦhol, ?_, hΦzero⟩
    intro x
    by_cases hx : x = x₀
    · rw [hx, hΦzero, norm_zero]; norm_num
    · rw [hΦmod x hx]
      exact le_of_lt (Real.exp_lt_one_iff.mpr (by linarith [hEpos x hx]))
  -- the zero fibre of `Φ` is `{x₀}`
  have hΦfib : Φ ⁻¹' {0} = {x₀} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hx
      by_contra hne'
      have h1 : ‖Φ x‖ = Real.exp (-(E x)) := hΦmod x hne'
      rw [hx, norm_zero] at h1
      have h2 : 0 < Real.exp (-(E x)) := Real.exp_pos _
      linarith [h1.symm ▸ h2]
    · intro hx
      rw [hx]; exact hΦzero
  -- the domination by `Φ` is the domination by `exp (-E)` read through the modulus
  have hdom' : ∀ g ∈ Submission.extremalFamily x₀, ∀ x : X, ‖g x‖ ≤ ‖Φ x‖ := by
    intro g hg x
    by_cases hx : x = x₀
    · rw [hx, hg.2.2, hΦzero, norm_zero]
    · have h1 : ‖g x‖ ≤ Real.exp (-(E x)) := hdom g hg x hx
      rwa [hΦmod x hx]
  exact zero_fiber_of_dominating_single_zero hf hmax hpos hΦmem hΦfib hΦsimple hdom'


end Work.SimplyConnected.ABS
namespace Work.SimplyConnected.ABS


/-- **A simple zero from a non-vanishing derivative.**  If `F` is analytic at `a`, vanishes there,
and has non-zero derivative, then `F` factors as `(w - a) * H w` near `a` with `H` analytic and
`H a ≠ 0` — i.e. the zero is *simple*.  (The order of vanishing is `1`: the `k`-th power
factorization of `AnalyticAt.exists_eventuallyEq_pow_smul_nonzero_iff` gives `k ≥ 1`, and `k ≥ 2`
would force `deriv F a = 0`.) -/
theorem exists_simpleZero_factorization {a : ℂ} {F : ℂ → ℂ} (hana : AnalyticAt ℂ F a)
    (h0 : F a = 0) (hd : deriv F a ≠ 0) :
    ∃ H : ℂ → ℂ, AnalyticAt ℂ H a ∧ H a ≠ 0 ∧ (∀ᶠ w in 𝓝 a, F w = (w - a) * H w) := by
  have hnotzero : ¬ ∀ᶠ w in 𝓝 a, F w = 0 := by
    intro h
    have heq : Filter.EventuallyEq (𝓝 a) F (fun _ : ℂ => 0) := h
    have hd0 : deriv F a = 0 := by
      rw [heq.deriv_eq]
      simp
    exact hd hd0
  obtain ⟨k, g, hgana, hgne, hgeq⟩ := hana.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hnotzero
  have hge : Filter.EventuallyEq (𝓝 a) F (fun w : ℂ => (w - a) ^ k * g w) := by
    filter_upwards [hgeq] with w hw
    simpa [smul_eq_mul] using hw
  have hk1 : 1 ≤ k := by
    have hval : F a = (a - a) ^ k * g a := hge.self_of_nhds
    by_contra h
    have hk0 : k = 0 := Nat.lt_one_iff.mp (not_le.mp h)
    rw [hk0, pow_zero, one_mul] at hval
    exact hgne (hval.symm.trans h0)
  have hk : k = 1 := by
    by_contra hk
    have hk2 : 2 ≤ k := by
      have h1 : 1 < k := Nat.lt_of_le_of_ne hk1 (fun h => hk h.symm)
      omega
    have hder : deriv F a = deriv (fun w : ℂ => (w - a) ^ k * g w) a := hge.deriv_eq
    have hz : deriv (fun w : ℂ => (w - a) ^ k * g w) a = 0 := by
      have hfac : (fun w : ℂ => (w - a) ^ k * g w)
          = fun w : ℂ => (w - a) ^ 2 * ((w - a) ^ (k - 2) * g w) := by
        funext w
        have hpow : (w - a) ^ k = (w - a) ^ 2 * (w - a) ^ (k - 2) := by
          rw [← pow_add]
          congr 1
          omega
        rw [hpow]
        ring
      rw [hfac]
      have hd1 : DifferentiableAt ℂ (fun w : ℂ => (w - a) ^ 2) a :=
        (differentiableAt_id.sub (differentiableAt_const a)).pow 2
      have hd2 : DifferentiableAt ℂ (fun w : ℂ => (w - a) ^ (k - 2) * g w) a :=
        ((differentiableAt_id.sub (differentiableAt_const a)).pow _).mul hgana.differentiableAt
      change deriv ((fun w : ℂ => (w - a) ^ 2) * (fun w : ℂ => (w - a) ^ (k - 2) * g w)) a = 0
      rw [deriv_mul hd1 hd2]
      have h1 : deriv (fun w : ℂ => (w - a) ^ 2) a = 0 := by
        have hda : DifferentiableAt ℂ (fun w : ℂ => w - a) a :=
          differentiableAt_id.sub (differentiableAt_const a)
        have hp := deriv_pow hda 2
        change deriv ((fun w : ℂ => w - a) ^ 2) a = 0
        rw [hp]
        simp
      have h2 : (a - a) ^ 2 = 0 := by ring
      rw [h1, zero_mul, h2, zero_mul, add_zero]
    rw [hz] at hder
    exact hd hder
  refine ⟨g, hgana, hgne, ?_⟩
  filter_upwards [hge] with w hw
  rw [hw, hk, pow_one]

/-- **The target, from the loop hypothesis.**  If every loop of `X ∖ {x₀}` is null-homotopic in `X`
(`Work.Modulus.AllLoopsOfPuncturedTrivialInX x₀`, which is immediate from `SimplyConnectedSpace X`,
hence from Hubbard 1.1.2), then the requested zero-fibre statement follows from

* the Perron/balayage envelope of the clamped logarithmic barrier
  (`exists_posHarmonic_logPole_dominating'`, proved in this directory) and
* its decay-free holomorphic modulus (`Work.ModulusLP.exists_modulus_of_logPole_of_loopsTrivial`,
  the port of `Work.Modulus` to the hypotheses actually used there).

This isolates the *entire* remaining gap of the target to a purely topological statement about `X`. -/
theorem extremal_maximizer_zero_fiber_of_loopsTrivial {X : Type*} [TopologicalSpace X]
    [T2Space X] [ConnectedSpace X] [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] {x₀ : X}
    [Subsingleton (Additive (FundamentalGroup X x₀) →+ ℝ)] {f : X → ℂ}
    (hf : f ∈ Submission.extremalFamily x₀)
    (hmax : ∀ g ∈ Submission.extremalFamily x₀,
      ‖deriv (g ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀)‖ ≤
        ‖deriv (f ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀)‖)
    (hpos : 0 < ‖deriv (f ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀)‖)
    (hloop : Work.Modulus.AllLoopsOfPuncturedTrivialInX (X := X) x₀) :
    f ⁻¹' {0} = {x₀} := by
  classical
  have hsrc : x₀ ∈ (chartAt ℂ x₀).source := mem_chart_source ℂ x₀
  have hne : ∃ x : X, f x ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have hzero : f = fun _ => (0 : ℂ) := funext fun x => hcon x
    have hd : deriv (f ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀) = 0 := by
      have h1 : (f ∘ (chartAt ℂ x₀).symm) = fun _ => (0 : ℂ) := by
        funext w; simp [hzero]
      rw [h1, deriv_const]
    rw [hd, norm_zero] at hpos
    exact lt_irrefl 0 hpos
  -- the zero of `f` at `x₀` is simple
  have hderivne : deriv (f ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hpos
    exact lt_irrefl 0 hpos
  have hf0c : (f ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀) = 0 := by
    simp only [Function.comp_apply, (chartAt ℂ x₀).left_inv hsrc]
    exact hf.2.2
  obtain ⟨H, hHana, hHne, hHeq⟩ :=
    exists_simpleZero_factorization (a := (chartAt ℂ x₀) x₀) (hf.1 x₀ (mem_univ x₀)) hf0c hderivne
  -- Perron's method: the envelope
  obtain ⟨E, hEpos, hEharm, hpole, hdom⟩ :=
    exists_posHarmonic_logPole_dominating' (x₀ := x₀) hf hne ⟨H, hHana, hHne, hHeq⟩
  -- the decay-free holomorphic modulus of the envelope
  obtain ⟨Φ, hΦhol, hΦ0, hΦmod, hΦsimple⟩ :=
    Work.ModulusLP.exists_modulus_of_logPole_of_loopsTrivial (z₀ := x₀) hEharm hpole hloop
  have hΦmem : Φ ∈ Submission.extremalFamily x₀ := by
    refine ⟨hΦhol, ?_, hΦ0⟩
    intro x
    by_cases hx : x = x₀
    · rw [hx, hΦ0, norm_zero]; norm_num
    · rw [hΦmod x hx]
      exact le_of_lt (Real.exp_lt_one_iff.mpr (by linarith [hEpos x hx]))
  have hΦfib : Φ ⁻¹' {0} = {x₀} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hx
      by_contra hne'
      have h1 : ‖Φ x‖ = Real.exp (-(E x)) := hΦmod x hne'
      rw [hx, norm_zero] at h1
      have h2 : 0 < Real.exp (-(E x)) := Real.exp_pos _
      linarith [h1.symm ▸ h2]
    · intro hx
      rw [hx]; exact hΦ0
  have hdom' : ∀ g ∈ Submission.extremalFamily x₀, ∀ x : X, ‖g x‖ ≤ ‖Φ x‖ := by
    intro g hg x
    by_cases hx : x = x₀
    · rw [hx, hg.2.2, hΦ0, norm_zero]
    · have h1 : ‖g x‖ ≤ Real.exp (-(E x)) := hdom g hg x hx
      rwa [hΦmod x hx]
  exact zero_fiber_of_dominating_single_zero hf hmax hpos hΦmem hΦfib hΦsimple hdom'

/-- **The target, from a holomorphic function with a single simple zero.**

If there is a holomorphic `g : X → ℂ` whose zero set is exactly `{x₀}` (written below as
`{x | g x = 0} = {x₀}`), with a *simple* zero there (`Submission.HasLogPoleAt x₀ g`), then every
maximiser of the extremal problem has zero fibre `{x₀}`.  This is a second, logically independent
sufficient input for the target (the first being `Work.Modulus.AllLoopsOfPuncturedTrivialInX`, i.e.
the spine): it is the form of the input supplied by the ABS embedding theorem
(`Work.SimplyConnected.ABS.exists_injective_holomorphic_of_isSimplyConnected_noncompact`, whose `g`
is injective, hence has the single zero `x₀`).

The proof: Perron method gives the envelope `E` of the logarithmic pole; a holomorphic `g` with a
single simple zero at `x₀` makes `E + log ‖g‖` harmonic on `X`
(`exists_modulus_of_singleSimpleZero`), so `E` has a holomorphic modulus `Φ`; `Φ` dominates the
extremal family (domination by `E`) and has zero fibre `{x₀}`, so
`zero_fiber_of_dominating_single_zero` identifies the zero fibre of every maximiser. -/
theorem extremal_maximizer_zero_fiber_of_singleZeroFunction {X : Type*} [TopologicalSpace X]
    [T2Space X] [ConnectedSpace X] [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] {x₀ : X} {f g : X → ℂ}
    (hg : Submission.HolomorphicOnX g Set.univ) (hg0 : {x : X | g x = 0} = {x₀})
    (hgs : Submission.HasLogPoleAt x₀ g)
    (hf : f ∈ Submission.extremalFamily x₀)
    (hmax : ∀ g ∈ Submission.extremalFamily x₀,
      ‖deriv (g ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀)‖ ≤
        ‖deriv (f ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀)‖)
    (hpos : 0 < ‖deriv (f ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀)‖)
    [Subsingleton (Additive (FundamentalGroup X x₀) →+ ℝ)] :
    {x : X | f x = 0} = {x₀} := by
  classical
  have hsrc : x₀ ∈ (chartAt ℂ x₀).source := mem_chart_source ℂ x₀
  have hne : ∃ x : X, f x ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have hzero : f = fun _ => (0 : ℂ) := funext fun x => hcon x
    have hd : deriv (f ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀) = 0 := by
      have h1 : (f ∘ (chartAt ℂ x₀).symm) = fun _ => (0 : ℂ) := by
        funext w; simp [hzero]
      rw [h1, deriv_const]
    rw [hd, norm_zero] at hpos
    exact lt_irrefl 0 hpos
  have hderivne : deriv (f ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hpos
    exact lt_irrefl 0 hpos
  have hf0c : (f ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀) = 0 := by
    simp only [Function.comp_apply, (chartAt ℂ x₀).left_inv hsrc]
    exact hf.2.2
  obtain ⟨H, hHana, hHne, hHeq⟩ :=
    exists_simpleZero_factorization (a := (chartAt ℂ x₀) x₀) (hf.1 x₀ (mem_univ x₀)) hf0c hderivne
  obtain ⟨E, hEpos, hEharm, hpole, hdom⟩ :=
    exists_posHarmonic_logPole_dominating' (x₀ := x₀) hf hne ⟨H, hHana, hHne, hHeq⟩
  have hgne : ∀ x : X, x ≠ x₀ → g x ≠ 0 := by
    intro x hx hgx
    have hmem : x ∈ {y : X | g y = 0} := hgx
    rw [hg0] at hmem
    exact hx hmem
  obtain ⟨Φ, hΦhol, hΦ0, hΦmod, hΦsimple⟩ :=
    exists_modulus_of_singleSimpleZero (x₀ := x₀) hEharm hpole hg hgne hgs
  have hΦmem : Φ ∈ Submission.extremalFamily x₀ := by
    refine ⟨hΦhol, ?_, hΦ0⟩
    intro x
    by_cases hx : x = x₀
    · rw [hx, hΦ0, norm_zero]; norm_num
    · rw [hΦmod x hx]
      exact le_of_lt (Real.exp_lt_one_iff.mpr (by linarith [hEpos x hx]))
  have hΦfib : Set.preimage Φ ({0} : Set ℂ) = {x₀} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hx
      by_contra hne2
      have h1 : ‖Φ x‖ = Real.exp (-(E x)) := hΦmod x hne2
      rw [hx, norm_zero] at h1
      have h2 : 0 < Real.exp (-(E x)) := Real.exp_pos _
      linarith [h1.symm ▸ h2]
    · intro hx
      rw [hx]; exact hΦ0
  have hdom2 : ∀ h ∈ Submission.extremalFamily x₀, ∀ x : X, ‖h x‖ ≤ ‖Φ x‖ := by
    intro h hh x
    by_cases hx : x = x₀
    · rw [hx, hh.2.2, hΦ0, norm_zero]
    · have h1 : ‖h x‖ ≤ Real.exp (-(E x)) := hdom h hh x hx
      rwa [hΦmod x hx]
  exact zero_fiber_of_dominating_single_zero hf hmax hpos hΦmem hΦfib hΦsimple hdom2

/- NOTE (this session).  Two *independent* sufficient inputs for the target are now proved in this
file:

* `extremal_maximizer_zero_fiber_of_loopsTrivial` -- the loop hypothesis
  `Work.Modulus.AllLoopsOfPuncturedTrivialInX x₀` (equivalently the spine / Hubbard 1.1.2);

* `extremal_maximizer_zero_fiber_of_singleZeroFunction` -- the existence of a holomorphic
  `g : X → ℂ` whose zero set is exactly `{x₀}` and whose zero there is *simple*
  (`Submission.HasLogPoleAt x₀ g`).  This is the shape supplied by the ABS embedding theorem
  (`Work.SimplyConnected.ABS.exists_injective_holomorphic_of_isSimplyConnected_noncompact`), and it
  uses the new modulus construction `exists_modulus_of_singleSimpleZero`
  (`Submission/Work/SimplyConnected/ABS/modulus_of_single_zero.lean`), which needs *no* harmonicity
  hypothesis on `E + log ‖g‖`: the unit pole of `E` cancels the simple zero of `g`, so `E + log ‖g‖`
  extends harmonically across the pole (that file proves it). -/

/-- **The target, from the attainment of the envelope at the pole (function form).**

Let `E` be harmonic off `x₀` and let `V` be a harmonic function on all of `X` which

* is `≤ 0` off `x₀` (this is the domination of the extremal family, applied to `f`),
* vanishes at `x₀` (this is the *attainment* statement: `E + log ‖f‖` has limit `0` there),
* and agrees with `E + log ‖f‖` where `f ≠ 0`.

Then the maximiser `f` has zero fibre `{x₀}`.  The proof uses only the modulus `exp (-E)`: the
strong maximum principle forces `V ≡ 0`, hence `‖f‖ = exp (-E)` off the zero set `Z`, and `Z` is
closed discrete, so `Zᶜ` is preconnected
(`Work.SimplyConnected.ABS.isPreconnected_compl_closedDiscrete`); a further zero would then force
`0 = exp (-(E x₁))`. -/
theorem extremal_maximizer_zero_fiber_of_attainment {X : Type*} [TopologicalSpace X] [T2Space X]
    [ConnectedSpace X] [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] {x₀ : X} {E : X → ℝ} {f : X → ℂ} {V : X → ℝ}
    (hVharm : Submission.HarmonicOnX V Set.univ)
    (hEharm : Submission.HarmonicOnX E (Set.univ \ {x₀}))
    (hVneg : ∀ x : X, x ≠ x₀ → V x ≤ 0)
    (hV0 : V x₀ = 0)
    (hVf : ∀ x : X, x ≠ x₀ → f x ≠ 0 → V x = E x + Real.log ‖f x‖)
    (hf : f ∈ Submission.extremalFamily x₀) (hne : ∃ x : X, f x ≠ 0) :
    f ⁻¹' {0} = {x₀} := by
  classical
  -- ## the zero set `Z` is closed and discrete
  have hZc : IsClosed {x : X | f x = 0} := isClosed_eq hf.1.continuous continuous_const
  have hZd : ∀ x ∈ {y : X | f y = 0}, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      U ∩ {y : X | f y = 0} = {x} := by
    intro x hxZ
    have hx0 : f x = 0 := hxZ
    obtain ⟨ε₀, hε₀pos, hε₀⟩ := exists_isolated_zero_chart (X := X) hf.1 hx0 hne
    obtain ⟨ε₁, hε₁pos, hε₁sub⟩ : ∃ ε : ℝ, 0 < ε ∧
        Metric.ball ((chartAt ℂ x) x) ε ⊆ (chartAt ℂ x).target :=
      Metric.mem_nhds_iff.mp ((chartAt ℂ x).open_target.mem_nhds
        ((chartAt ℂ x).map_source (mem_chart_source ℂ x)))
    set ε : ℝ := min ε₀ ε₁ / 2 with hεdef
    have hεpos : 0 < ε := by rw [hεdef]; have h := lt_min hε₀pos hε₁pos; positivity
    have hεle₀ : ε ≤ ε₀ := by rw [hεdef]; linarith [min_le_left ε₀ ε₁, lt_min hε₀pos hε₁pos]
    have hεle₁ : ε ≤ ε₁ := by rw [hεdef]; linarith [min_le_right ε₀ ε₁, lt_min hε₀pos hε₁pos]
    have hballtgt : Metric.ball ((chartAt ℂ x) x) ε ⊆ (chartAt ℂ x).target :=
      (Metric.ball_subset_ball hεle₁).trans hε₁sub
    refine ⟨(chartAt ℂ x).symm '' Metric.ball ((chartAt ℂ x) x) ε, ?_, ?_, ?_⟩
    · exact (chartAt ℂ x).isOpen_image_symm_of_subset_target Metric.isOpen_ball hballtgt
    · exact ⟨(chartAt ℂ x) x, Metric.mem_ball_self hεpos,
        (chartAt ℂ x).left_inv (mem_chart_source ℂ x)⟩
    · refine Subset.antisymm ?_ ?_
      · rintro z ⟨hzU, hzZ⟩
        obtain ⟨w, hw, rfl⟩ := hzU
        have hwtgt : w ∈ (chartAt ℂ x).target := hballtgt hw
        have hcz : (chartAt ℂ x) ((chartAt ℂ x).symm w) = w :=
          (chartAt ℂ x).right_inv hwtgt
        have hzsrc : (chartAt ℂ x).symm w ∈ (chartAt ℂ x).source :=
          (chartAt ℂ x).map_target hwtgt
        have hdist : ‖(chartAt ℂ x) ((chartAt ℂ x).symm w) - (chartAt ℂ x) x‖ < ε := by
          rw [hcz]
          simpa [Metric.mem_ball, dist_eq_norm] using hw
        exact hε₀ _ hzsrc (lt_of_lt_of_le hdist hεle₀) hzZ
      · intro z hz
        rw [mem_singleton_iff] at hz
        rw [hz]
        exact ⟨⟨(chartAt ℂ x) x, Metric.mem_ball_self hεpos,
          (chartAt ℂ x).left_inv (mem_chart_source ℂ x)⟩, hx0⟩
  -- ## `Zᶜ` is preconnected
  have hpcZ : IsPreconnected ({y : X | f y = 0}ᶜ) :=
    Work.SimplyConnected.ABS.isPreconnected_compl_closedDiscrete hZc hZd
  -- ## the maximum principle forces `V ≡ 0`
  have hVcont : Continuous V := by
    rw [continuous_iff_continuousAt]
    intro x
    exact (hVharm x (Set.mem_univ x)).continuousAt
  have hSclosed : IsClosed {x : X | V x = 0} := isClosed_eq hVcont continuous_const
  have hSopen : IsOpen {x : X | V x = 0} := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    have hle : ∀ y ∈ (Set.univ : Set X), V y ≤ V x := by
      intro y _
      rw [hx]
      by_cases hy : y = x₀
      · rw [hy, hV0]
      · exact hVneg y hy
    obtain ⟨W, hW, hWeq⟩ := Submission.SubharmonicOnXAt.eqOn_of_le
      ((hVharm x (Set.mem_univ x)).subharmonic) univ_mem hle
    exact Filter.mem_of_superset hW fun y hy => by
      simp only [Set.mem_ofPred_eq]
      rw [hWeq y hy, hx]
  have hVzero : ∀ x : X, V x = 0 :=
    fun x => ((connectedSpace_iff_univ.mp inferInstance).isPreconnected.subset_isClopen
      ⟨hSclosed, hSopen⟩ ⟨x₀, Set.mem_univ x₀, hV0⟩) (Set.mem_univ x)
  -- ## no other zero of `f`
  have hkey : ∀ x ∈ {y : X | f y = 0}, x ≠ x₀ → False := by
    intro x hxZ hxne
    obtain ⟨U, hUo, hxU, hUZ⟩ := hZd x hxZ
    obtain ⟨Vp, -, -, -, -, hxcl⟩ := exists_punctured_chart_nbhd hZd hxZ
    have hxcl2 : x ∈ closure ({x}ᶜ : Set X) :=
      closure_mono (fun y hy => hy.2) hxcl
    haveI : NeBot (𝓝[≠] x) := mem_closure_iff_nhdsWithin_neBot.mp hxcl2
    have hev : ∀ᶠ y in 𝓝[≠] x, ‖f y‖ = Real.exp (-(E y)) := by
      have hUev : ∀ᶠ y in 𝓝[≠] x, y ∈ U :=
        Filter.Eventually.filter_mono nhdsWithin_le_nhds
          (show ∀ᶠ y in 𝓝 x, y ∈ U from hUo.mem_nhds hxU)
      have hnev : ∀ᶠ y in 𝓝[≠] x, y ∈ ({x}ᶜ : Set X) := self_mem_nhdsWithin
      filter_upwards [hUev, hnev] with y hyU hyne
      have hfy : f y ≠ 0 := by
        intro h0
        have hmem : y ∈ U ∩ {z : X | f z = 0} := ⟨hyU, h0⟩
        rw [hUZ] at hmem
        exact hyne (by simpa using hmem)
      have hyx0 : y ≠ x₀ := by
        intro h
        have hx0U : x₀ ∈ U ∩ {z : X | f z = 0} := by
          rw [h] at hyU
          exact ⟨hyU, hf.2.2⟩
        rw [hUZ] at hx0U
        exact hxne (by simpa using hx0U.symm)
      have h1 : V y = E y + Real.log ‖f y‖ := hVf y hyx0 hfy
      have h2 : V y = 0 := hVzero y
      have h3 : Real.log ‖f y‖ = -(E y) := by linarith [h1, h2]
      calc ‖f y‖ = Real.exp (Real.log ‖f y‖) := (Real.exp_log (norm_pos_iff.mpr hfy)).symm
        _ = Real.exp (-(E y)) := by rw [h3]
    have hA : Filter.Tendsto (fun y : X => ‖f y‖) (𝓝[≠] x) (𝓝 0) := by
      have hfx : f x = 0 := hxZ
      have h1 : Filter.Tendsto f (𝓝[≠] x) (𝓝 (f x)) :=
        hf.1.continuous.continuousAt.continuousWithinAt
      rw [hfx] at h1
      simpa using h1.norm
    have hB : Filter.Tendsto (fun y : X => Real.exp (-(E y))) (𝓝[≠] x)
        (𝓝 (Real.exp (-(E x)))) :=
      (Real.continuous_exp.continuousAt.comp (continuousAt_neg.comp
        (hEharm x ⟨Set.mem_univ x, hxne⟩).continuousAt)).continuousWithinAt
    have hB0 : Filter.Tendsto (fun y : X => Real.exp (-(E y))) (𝓝[≠] x) (𝓝 0) := hA.congr' hev
    have hEq : (0 : ℝ) = Real.exp (-(E x)) := tendsto_nhds_unique hB0 hB
    exact absurd hEq.symm (Real.exp_ne_zero _)
  -- ## conclusion
  ext x
  constructor
  · intro hx
    by_contra hxne
    exact hkey x hx hxne
  · intro hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact hf.2.2

/-- Local constancy of the modulus at a point of maximal modulus (`IsMaxOn` is only used in the
    `∀ w, ‖f w‖ ≤ ‖f y‖` form to keep the call sites simple). -/
theorem norm_eventually_eq_of_isMaxOn_norm {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    {f : X → ℂ} (hf : Submission.HolomorphicOnX f Set.univ)
    {y : X} (hy : ∀ w : X, ‖f w‖ ≤ ‖f y‖) :
    ∀ᶠ z in 𝓝 y, ‖f z‖ = ‖f y‖ := by
  set e : OpenPartialHomeomorph X ℂ := chartAt ℂ y with he
  have hsrc : y ∈ e.source := mem_chart_source ℂ y
  have han : AnalyticAt ℂ (f ∘ e.symm) (e y) := hf y (Set.mem_univ y)
  obtain ⟨ρ, hρ, hρana⟩ := han.exists_ball_analyticOnNhd
  obtain ⟨ε, hε, hεsub⟩ : ∃ ε > 0, Metric.ball (e y) ε ⊆ e.target := by
    obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp e.open_target (e y) (e.map_source hsrc)
    exact ⟨ε, hε, hεsub⟩
  set r : ℝ := min ρ ε with hr
  have hrpos : 0 < r := lt_min hρ hε
  have hrleρ : r ≤ ρ := min_le_left _ _
  have hrleε : r ≤ ε := min_le_right _ _
  have hdiff : DifferentiableOn ℂ (f ∘ e.symm) (Metric.ball (e y) r) :=
    (hρana.mono (Metric.ball_subset_ball hrleρ)).differentiableOn
  have hmax : IsMaxOn (norm ∘ (f ∘ e.symm)) (Metric.ball (e y) r) (e y) := by
    intro z hz
    have h3 : e.symm (e y) = y := e.left_inv hsrc
    have h1 : ‖f (e.symm z)‖ ≤ ‖f y‖ := hy (e.symm z)
    simp only [Function.comp_apply, h3]
    exact h1
  have hEq := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm
    (f := f ∘ e.symm) (U := Metric.ball (e y) r) (c := e y)
    (convex_ball _ _).isPreconnected Metric.isOpen_ball hdiff
    (Metric.mem_ball_self hrpos) hmax
  have hpre1 : e.source ∈ 𝓝 y := e.open_source.mem_nhds hsrc
  have hpre2 : e ⁻¹' (Metric.ball (e y) r) ∈ 𝓝 y :=
    (e.continuousAt hsrc).preimage_mem_nhds
      (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hrpos))
  have hpre : e.source ∩ e ⁻¹' (Metric.ball (e y) r) ∈ 𝓝 y := Filter.inter_mem hpre1 hpre2
  filter_upwards [hpre] with z hz
  have hzsrc : z ∈ e.source := hz.1
  have hzball : e z ∈ Metric.ball (e y) r := hz.2
  have hval : (f ∘ e.symm) (e z) = (f ∘ e.symm) (e y) := hEq hzball
  calc ‖f z‖ = ‖f (e.symm (e z))‖ := by rw [e.left_inv hzsrc]
    _ = ‖(f ∘ e.symm) (e z)‖ := rfl
    _ = ‖(f ∘ e.symm) (e y)‖ := by rw [hval]
    _ = ‖f y‖ := by simp only [Function.comp_apply, e.left_inv hsrc]

/-- **The compact case is vacuous.**  On a compact surface every member of the extremal family is
identically zero (its modulus attains a maximum, and the maximum principle makes `f` constant), so
the chart derivative at `x₀` vanishes and a maximiser with positive extremal value cannot exist. -/
theorem deriv_eq_zero_of_compact {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] {x₀ : X} {f : X → ℂ}
    (hf : f ∈ Submission.extremalFamily x₀) [CompactSpace X] :
    deriv (f ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀) = 0 := by
  classical
  have hcont : Continuous f := hf.1.continuous
  obtain ⟨y, -, hy⟩ : ∃ y ∈ (Set.univ : Set X), IsMaxOn (fun x => ‖f x‖) Set.univ y :=
    isCompact_univ.exists_isMaxOn ⟨x₀, Set.mem_univ x₀⟩ hcont.norm.continuousOn
  have hmaxy : ∀ w : X, ‖f w‖ ≤ ‖f y‖ := fun w => hy (Set.mem_univ w)
  have hall : ∀ x : X, ‖f x‖ = ‖f y‖ := by
    have hclosed : IsClosed {x : X | ‖f x‖ = ‖f y‖} := isClosed_eq hcont.norm continuous_const
    have hopen : IsOpen {x : X | ‖f x‖ = ‖f y‖} := by
      rw [isOpen_iff_mem_nhds]
      intro z hz
      have hzeq : ‖f z‖ = ‖f y‖ := hz
      have hzmax : ∀ w : X, ‖f w‖ ≤ ‖f z‖ := by
        intro w
        rw [hzeq]
        exact hmaxy w
      refine Filter.mem_of_superset
        (norm_eventually_eq_of_isMaxOn_norm (f := f) hf.1 hzmax) ?_
      intro w hw
      have hw' : ‖f w‖ = ‖f z‖ := hw
      show ‖f w‖ = ‖f y‖
      rw [hw', hzeq]
    intro x
    exact isPreconnected_univ.subset_isClopen ⟨hclosed, hopen⟩
      ⟨y, Set.mem_univ y, rfl⟩ (Set.mem_univ x)
  have hconst : ∀ z : X, f z = f x₀ :=
    hf.1.exists_eq_const_of_norm_eq x₀ (fun z => by rw [hall z, hall x₀])
  have hzero : f = fun _ => (0 : ℂ) := funext fun z => by rw [hconst z, hf.2.2]
  have h1 : (f ∘ (chartAt ℂ x₀).symm) = fun _ => (0 : ℂ) := by
    funext w; simp [hzero]
  rw [h1, deriv_const]


variable {X : Type*} [TopologicalSpace X] [T2Space X]
    [ConnectedSpace X] [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **The target, from the vanishing of the circle-valued characters of `π₁(X,·)`.**

`hcirc` is the statement that every additive character `π₁(X,y) →+ ℝ ⧸ 2πℤ` vanishes; this is
strictly weaker than simple connectivity of `X` and is equivalent, under the challenge hypothesis
`H¹(X,ℝ) = 0` plus torsion-freeness of `H₁(X;ℤ) = π₁(X)^{ab}`, to the challenge hypothesis itself
(`Work.SimplyConnected.subsingleton_hom_addCircle_of_torsionFree`).

The proof is the proof of `extremal_maximizer_zero_fiber_of_loopsTrivial` with the topological
input replaced by `Work.SimplyConnected.ABS.periodsAreMultiplesOfTwoPi_of_circleCharacter_trivial`:
Perron's method produces the envelope `E` of the logarithmic pole of the maximiser, the period port
makes `exp (-(E + iE*))` single-valued, and the resulting holomorphic modulus `Φ` dominates the
extremal family with a single simple zero `x₀`. -/
theorem extremal_maximizer_zero_fiber_of_circleCharacter_trivial {x₀ : X}
    [Subsingleton (Additive (FundamentalGroup X x₀) →+ ℝ)]
    (hcirc : ∀ y : X, Subsingleton (Additive (FundamentalGroup X y) →+
      (ℝ ⧸ AddSubgroup.zmultiples (2 * Real.pi))))
    {f : X → ℂ}
    (hf : f ∈ Submission.extremalFamily x₀)
    (hmax : ∀ g ∈ Submission.extremalFamily x₀,
      ‖deriv (g ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀)‖ ≤
        ‖deriv (f ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀)‖)
    (hpos : 0 < ‖deriv (f ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀)‖) :
    f ⁻¹' {0} = {x₀} := by
  classical
  have hsrc : x₀ ∈ (chartAt ℂ x₀).source := mem_chart_source ℂ x₀
  have hne : ∃ x : X, f x ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have hzero : f = fun _ => (0 : ℂ) := funext fun x => hcon x
    have hd : deriv (f ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀) = 0 := by
      have h1 : (f ∘ (chartAt ℂ x₀).symm) = fun _ => (0 : ℂ) := by
        funext w; simp [hzero]
      rw [h1, deriv_const]
    rw [hd, norm_zero] at hpos
    exact lt_irrefl 0 hpos
  have hderivne : deriv (f ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hpos
    exact lt_irrefl 0 hpos
  have hf0c : (f ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀) = 0 := by
    simp only [Function.comp_apply, (chartAt ℂ x₀).left_inv hsrc]
    exact hf.2.2
  obtain ⟨H, hHana, hHne, hHeq⟩ :=
    exists_simpleZero_factorization (a := (chartAt ℂ x₀) x₀) (hf.1 x₀ (mem_univ x₀)) hf0c hderivne
  -- Perron's method: the envelope of the logarithmic pole
  obtain ⟨E, hEpos, hEharm, hpole, hdom⟩ :=
    exists_posHarmonic_logPole_dominating' (x₀ := x₀) hf hne ⟨H, hHana, hHne, hHeq⟩
  -- the circle-valued characters vanish, so the conjugate periods are multiples of `2π`, so the
  -- modulus `exp (-(E + iE*))` is single-valued
  obtain ⟨Φ, hΦhol, hΦne, hΦmod⟩ :=
    Work.ModulusLP.hasTrivialModulusMonodromy_of_periods hEharm hpole
      (periodsAreMultiplesOfTwoPi_of_circleCharacter_trivial hEharm hpole hcirc)
  have hΦpole : Submission.HasLogPoleAt x₀ Φ :=
    Work.ModulusLP.poleOrderModulus_of_unitGreen hEharm hpole hΦhol hΦne hΦmod
  have hΦ0 : Φ x₀ = 0 := Submission.phi_zero_of_logPole hΦhol hΦpole
  have hΦmem : Φ ∈ Submission.extremalFamily x₀ := by
    refine ⟨hΦhol, ?_, hΦ0⟩
    intro x
    by_cases hx : x = x₀
    · rw [hx, hΦ0, norm_zero]; norm_num
    · rw [hΦmod x hx]
      exact le_of_lt (Real.exp_lt_one_iff.mpr (by linarith [hEpos x hx]))
  have hΦfib : Φ ⁻¹' {0} = {x₀} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hx
      by_contra hne'
      have h1 : ‖Φ x‖ = Real.exp (-(E x)) := hΦmod x hne'
      rw [hx, norm_zero] at h1
      have h2 : 0 < Real.exp (-(E x)) := Real.exp_pos _
      linarith [h1.symm ▸ h2]
    · intro hx
      rw [hx]; exact hΦ0
  have hdom' : ∀ g ∈ Submission.extremalFamily x₀, ∀ x : X, ‖g x‖ ≤ ‖Φ x‖ := by
    intro g hg x
    by_cases hx : x = x₀
    · rw [hx, hg.2.2, hΦ0, norm_zero]
    · have h1 : ‖g x‖ ≤ Real.exp (-(E x)) := hdom g hg x hx
      rwa [hΦmod x hx]
  exact zero_fiber_of_dominating_single_zero hf hmax hpos hΦmem hΦfib hΦpole hdom'

/-- **The target, from the torsion-freeness of `H₁(X;ℤ) = π₁(X)^{ab}`.**

This is the *sharp* named topological input of the target: by
`Work.SimplyConnected.subsingleton_hom_addCircle_of_torsionFree`, torsion-freeness of the
abelianization together with the challenge hypothesis `Subsingleton (π₁(X,y) →+ ℝ)` (transported to
any base point) gives the vanishing of *all* circle-valued characters of `π₁(X,·)`, which
`extremal_maximizer_zero_fiber_of_circleCharacter_trivial` consumes.

The remaining mathematical content is therefore exactly: *the abelianization `H₁(X;ℤ) = π₁(X)^{ab}`
of the fundamental group of a connected non-compact Riemann surface is torsion-free*
(`Work.Mori.torsionFree_abelianization_riemannSurface` — the "abelian half" of
Johansson/Stallings; the full freeness of `π₁` is *not* needed). -/
theorem extremal_maximizer_zero_fiber_of_torsionFree {x₀ : X}
    [Subsingleton (Additive (FundamentalGroup X x₀) →+ ℝ)]
    (htf : ∀ y : X, IsMulTorsionFree (Abelianization (FundamentalGroup X y)))
    {f : X → ℂ}
    (hf : f ∈ Submission.extremalFamily x₀)
    (hmax : ∀ g ∈ Submission.extremalFamily x₀,
      ‖deriv (g ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀)‖ ≤
        ‖deriv (f ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀)‖)
    (hpos : 0 < ‖deriv (f ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀)‖) :
    f ⁻¹' {0} = {x₀} := by
  haveI : PathConnectedSpace X :=
    Work.SimplyConnected.pathConnectedSpace_of_chartedSpace_complex
  refine extremal_maximizer_zero_fiber_of_circleCharacter_trivial (x₀ := x₀) (fun y => ?_)
    hf hmax hpos
  exact Work.SimplyConnected.subsingleton_hom_addCircle_of_torsionFree y
    (Work.SimplyConnected.subsingleton_hom_toReal_of_path
      (PathConnectedSpace.somePath x₀ y) inferInstance) (htf y)

/-- Base-point transport of torsion-freeness of the abelianization along a path. -/
theorem torsionFree_abelianization_of_path {x y : X}
    (h : IsMulTorsionFree (Abelianization (FundamentalGroup X x))) :
    IsMulTorsionFree (Abelianization (FundamentalGroup X y)) := by
  haveI : PathConnectedSpace X :=
    Work.SimplyConnected.pathConnectedSpace_of_chartedSpace_complex
  exact Work.Mori.isMulTorsionFree_of_mulEquiv
    (FundamentalGroup.fundamentalGroupMulEquivOfPath
      (PathConnectedSpace.somePath x y)).abelianizationCongr h

/-- **The single-base-point form of the sharp input.**  Torsion-freeness at one base point gives it
at every base point, since the abelianization is transported along
`FundamentalGroup.fundamentalGroupMulEquivOfPath`. -/
theorem torsionFree_abelianization_of_single {x₀ : X}
    (h : IsMulTorsionFree (Abelianization (FundamentalGroup X x₀))) :
    ∀ y : X, IsMulTorsionFree (Abelianization (FundamentalGroup X y)) := by
  haveI : PathConnectedSpace X :=
    Work.SimplyConnected.pathConnectedSpace_of_chartedSpace_complex
  intro y
  exact torsionFree_abelianization_of_path (x := x₀) (y := y) h

/-- **The target from the torsion-freeness of `H₁` at a single base point.**

This is the minimal form of the remaining topological input: everything else in the chain is proved.
The statement `IsMulTorsionFree (Abelianization (FundamentalGroup X x₀))` is
`Work.Mori.torsionFree_abelianization_riemannSurface` (the abelian half of Johansson/Stallings),
which is being built spine-free via `Work.Mori.exists_torsionFreeExhaustion_of_disc_tiling` from the
piece level statement `piece_level_torsionFree_of_disc_tiling`. -/
theorem extremal_maximizer_zero_fiber_of_torsionFree_single {x₀ : X}
    [Subsingleton (Additive (FundamentalGroup X x₀) →+ ℝ)]
    (htf : IsMulTorsionFree (Abelianization (FundamentalGroup X x₀)))
    {f : X → ℂ}
    (hf : f ∈ Submission.extremalFamily x₀)
    (hmax : ∀ g ∈ Submission.extremalFamily x₀,
      ‖deriv (g ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀)‖ ≤
        ‖deriv (f ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀)‖)
    (hpos : 0 < ‖deriv (f ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀)‖) :
    f ⁻¹' {0} = {x₀} :=
  extremal_maximizer_zero_fiber_of_torsionFree (x₀ := x₀)
    (torsionFree_abelianization_of_single (x₀ := x₀) htf) hf hmax hpos

/-- **The target.**

Everything analytic is now proved in this directory:

* `exists_posHarmonic_logPole_dominating'` — the Perron/balayage envelope `E` with its unit
  logarithmic pole and the sharp domination of the extremal family (no decay, no Green function);
* `Work.ModulusLP.exists_modulus_of_logPole_of_loopsTrivial` — the holomorphic modulus of `E`,
  i.e. the decay-free port of the whole `Work.Modulus` chapter, available as soon as every loop of
  `X ∖ {x₀}` is null-homotopic in `X`;
* `extremal_maximizer_zero_fiber_of_loopsTrivial` — the target itself with that single extra
  hypothesis (proved above).

Hence the only missing input is `Work.Modulus.AllLoopsOfPuncturedTrivialInX x₀`, which is
*immediate* from `SimplyConnectedSpace X` (every loop of `X ∖ {x₀}` is a loop of `X`).  Deriving
`SimplyConnectedSpace X` from `[Subsingleton (Additive (FundamentalGroup X x₀) →+ ℝ)]` and
non-compactness is exactly Hubbard 1.1.2 — the team's `Work.Spine` chapter
(`Work.Spine.simplyConnectedSpace_of_subsingleton_hom_toReal`), whose geometric content
(`Work/Topology/Surface/spine_reduction_library.lean` reduces it to `HasCutSystemCore`) is still
open.  This is not an analytic gap: the identity "extremal value = conformal radius" encoded by the
modulus fails for multiply connected surfaces (e.g. the annulus, whose conjugate differential has
period `±π`), so the statement is genuinely topological. -/

theorem extremal_maximizer_zero_fiber {X : Type*} [TopologicalSpace X] [T2Space X]
    [ConnectedSpace X] [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] {x₀ : X}
    [Subsingleton (Additive (FundamentalGroup X x₀) →+ ℝ)] {f : X → ℂ}
    (hf : f ∈ Submission.extremalFamily x₀)
    (hmax : ∀ g ∈ Submission.extremalFamily x₀,
      ‖deriv (g ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀)‖ ≤
        ‖deriv (f ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀)‖)
    (hpos : 0 < ‖deriv (f ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀)‖) :
    f ⁻¹' {0} = {x₀} := by
  classical
  by_cases hX : CompactSpace X
  · haveI := hX
    have h0 := deriv_eq_zero_of_compact (x₀ := x₀) hf
    rw [h0, norm_zero] at hpos
    exact absurd hpos (lt_irrefl 0)
  · -- non-compact case: the whole chain is proved; the only input is that `H₁(X;ℤ)` is torsion-free
    refine extremal_maximizer_zero_fiber_of_torsionFree_single (x₀ := x₀) ?_ hf hmax hpos
    -- The abelian half of Johansson/Stallings: `H₁(X;ℤ) = π₁(X,x₀)^{ab}` is torsion-free for a
    -- connected non-compact Riemann surface (`Work.Mori.torsionFree_abelianization_riemannSurface`,
    -- spine-free route: `Work.Mori.exists_torsionFreeExhaustion_of_disc_tiling` +
    -- `piece_level_torsionFree_of_disc_tiling`).
    exact sorry

end Work.SimplyConnected.ABS
