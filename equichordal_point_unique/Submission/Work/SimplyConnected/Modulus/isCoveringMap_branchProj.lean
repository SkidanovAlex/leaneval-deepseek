import Mathlib
import Submission.Work.SimplyConnected.ModulusDefs
import Submission.Work.SimplyConnected.Modulus.exists_isModulusBranch_at_pole
import Submission.Work.SimplyConnected.Modulus.exists_isModulusBranch_of_ne
import Submission.Work.SimplyConnected.Modulus.exists_ratio_eq_of_isModulusBranch

open LeanEval.Geometry
open scoped Manifold ContDiff Topology
open Filter Set
open Classical

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Work.SC

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [SecondCountableTopology X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

variable {z₀ x : X} {E : X → ℝ}

/-! ## Chart balls centred at a point -/

/-- The chart ball at `x` of radius `ρ`. -/
abbrev ballAt (x : X) (ρ : ℝ) : Set X := Submission.chartBall (chartAt ℂ x) ((chartAt ℂ x) x) ρ

theorem mem_ballAt {x y : X} {ρ : ℝ} :
    y ∈ ballAt x ρ ↔ y ∈ (chartAt ℂ x).source ∧ (chartAt ℂ x) y ∈ Metric.ball ((chartAt ℂ x) x) ρ :=
  Submission.mem_chartBall

theorem isOpen_ballAt (x : X) (ρ : ℝ) : IsOpen (ballAt x ρ) :=
  Submission.chartBall_isOpen _ _ _

theorem ballAt_mono {x : X} {ρ ρ' : ℝ} (h : ρ ≤ ρ') : ballAt x ρ ⊆ ballAt x ρ' :=
  fun _ hy => ⟨hy.1, Metric.ball_subset_ball h hy.2⟩

theorem ballAt_eq_image {x : X} {ρ : ℝ}
    (ht : Metric.ball ((chartAt ℂ x) x) ρ ⊆ (chartAt ℂ x).target) :
    ballAt x ρ = (chartAt ℂ x).symm '' Metric.ball ((chartAt ℂ x) x) ρ := by
  ext y
  constructor
  · rintro ⟨hysrc, hyball⟩
    exact ⟨(chartAt ℂ x) y, hyball, (chartAt ℂ x).left_inv hysrc⟩
  · rintro ⟨w, hw, rfl⟩
    refine ⟨(chartAt ℂ x).map_target (ht hw), ?_⟩
    show (chartAt ℂ x) ((chartAt ℂ x).symm w) ∈ Metric.ball ((chartAt ℂ x) x) ρ
    rw [(chartAt ℂ x).right_inv (ht hw)]
    exact hw

theorem isPreconnected_ballAt {x : X} {ρ : ℝ}
    (ht : Metric.ball ((chartAt ℂ x) x) ρ ⊆ (chartAt ℂ x).target) :
    IsPreconnected (ballAt x ρ) := by
  rw [ballAt_eq_image ht]
  exact Metric.isPreconnected_ball.image _
    ((chartAt ℂ x).continuousOn_symm.mono ht)

theorem mem_ballAt_self {x : X} {ρ : ℝ} (hρ : 0 < ρ) : x ∈ ballAt x ρ :=
  ⟨mem_chart_source ℂ x, Metric.mem_ball_self hρ⟩

theorem exists_ballAt_subset_target (x : X) :
    ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball ((chartAt ℂ x) x) ρ ⊆ (chartAt ℂ x).target := by
  have hxsrc : x ∈ (chartAt ℂ x).source := mem_chart_source ℂ x
  obtain ⟨ρ, hρ, hsub⟩ := Metric.mem_nhds_iff.mp
    ((chartAt ℂ x).open_target.mem_nhds ((chartAt ℂ x).map_source hxsrc))
  exact ⟨ρ, hρ, hsub⟩

theorem exists_ballAt_subset_nhds {x : X} {V : Set X} (hV : V ∈ 𝓝 x) :
    ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball ((chartAt ℂ x) x) ρ ⊆ (chartAt ℂ x).target ∧
      ballAt x ρ ⊆ V := by
  have hxsrc : x ∈ (chartAt ℂ x).source := mem_chart_source ℂ x
  have h1 : (chartAt ℂ x) '' (V ∩ (chartAt ℂ x).source) ∈ 𝓝 ((chartAt ℂ x) x) :=
    (chartAt ℂ x).image_mem_nhds hxsrc
      (Filter.inter_mem hV ((chartAt ℂ x).open_source.mem_nhds hxsrc))
  have h2 : (chartAt ℂ x).target ∈ 𝓝 ((chartAt ℂ x) x) :=
    (chartAt ℂ x).open_target.mem_nhds ((chartAt ℂ x).map_source hxsrc)
  obtain ⟨ρ, hρ, hsub⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem h1 h2)
  refine ⟨ρ, hρ, hsub.trans Set.inter_subset_right, ?_⟩
  rintro y ⟨hysrc, hyball⟩
  have hmem : (chartAt ℂ x) y ∈ (chartAt ℂ x) '' (V ∩ (chartAt ℂ x).source) :=
    (hsub hyball).1
  obtain ⟨z, hz, hzy⟩ := hmem
  have hzy' : z = y := (chartAt ℂ x).injOn hz.2 hysrc hzy
  rw [hzy'] at hz
  exact hz.1

theorem norm_ofReal_eq (r : ℝ) : ‖(r : ℂ)‖ = |r| := by
  rw [Complex.norm_def, Complex.normSq_ofReal]
  by_cases h : 0 ≤ r
  · rw [Real.sqrt_mul_self h, abs_of_nonneg h]
  · rw [abs_of_neg (not_le.mp h)]
    have hr : r * r = (-r) * (-r) := by ring
    rw [hr, Real.sqrt_mul_self (by linarith)]

theorem exists_ballAt_avoid {x : X} {ρ : ℝ} (hρ : 0 < ρ) (hx : x ≠ z₀) :
    ∃ ρ' : ℝ, 0 < ρ' ∧ ρ' ≤ ρ ∧ z₀ ∉ ballAt x ρ' := by
  by_cases hz : z₀ ∈ ballAt x ρ
  · have hsrc : z₀ ∈ (chartAt ℂ x).source := (mem_ballAt.mp hz).1
    have hne : (chartAt ℂ x) z₀ ≠ (chartAt ℂ x) x := by
      intro h
      exact hx ((chartAt ℂ x).injOn hsrc (mem_chart_source ℂ x) h).symm
    have hpos : 0 < ‖(chartAt ℂ x) x - (chartAt ℂ x) z₀‖ := by
      rw [norm_pos_iff]; exact sub_ne_zero.mpr (Ne.symm hne)
    refine ⟨min ρ (‖(chartAt ℂ x) x - (chartAt ℂ x) z₀‖ / 2), by positivity,
      min_le_left _ _, ?_⟩
    intro hmem
    rw [mem_ballAt, Metric.mem_ball, dist_eq_norm] at hmem
    have h1 : ‖(chartAt ℂ x) z₀ - (chartAt ℂ x) x‖
        = ‖(chartAt ℂ x) x - (chartAt ℂ x) z₀‖ := by rw [← norm_neg, neg_sub]
    rw [h1] at hmem
    have h4 := min_le_right ρ (‖(chartAt ℂ x) x - (chartAt ℂ x) z₀‖ / 2)
    have h5 : 0 ≤ ‖(chartAt ℂ x) x - (chartAt ℂ x) z₀‖ := norm_nonneg _
    linarith [hmem.2]
  · exact ⟨ρ, hρ, le_rfl, hz⟩

theorem exists_ne_of_mem_ballAt {x : X} {ρ : ℝ} (hρ : 0 < ρ) (h : z₀ ∈ ballAt x ρ) :
    ∃ y ∈ ballAt x ρ, y ≠ z₀ := by
  obtain ⟨ε, hε, htgt⟩ := exists_ballAt_subset_target x
  have hε' : 0 < min ρ ε := lt_min hρ hε
  have hleρ : min ρ ε ≤ ρ := min_le_left _ _
  have hleε : min ρ ε ≤ ε := min_le_right _ _
  have hball : Metric.ball ((chartAt ℂ x) x) (min ρ ε) ⊆ (chartAt ℂ x).target :=
    (Metric.ball_subset_ball hleε).trans htgt
  have hmem : ∀ t : ℝ, |t| < min ρ ε →
      ((chartAt ℂ x) x + (t : ℂ)) ∈ Metric.ball ((chartAt ℂ x) x) (min ρ ε) := by
    intro t ht
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_ofReal_eq]
    exact ht
  have h1 := hmem (min ρ ε / 2) (by rw [abs_of_pos (by positivity)]; linarith)
  have h2 := hmem (-(min ρ ε / 2)) (by rw [abs_neg, abs_of_pos (by positivity)]; linarith)
  have hne : ((chartAt ℂ x) x + ((min ρ ε / 2 : ℝ) : ℂ))
      ≠ ((chartAt ℂ x) x + ((-(min ρ ε / 2) : ℝ) : ℂ)) := by
    intro heq
    have h3 : ((min ρ ε / 2 : ℝ) : ℂ) = ((-(min ρ ε / 2) : ℝ) : ℂ) := add_left_cancel heq
    have h4 : min ρ ε / 2 = -(min ρ ε / 2) := by
      have := congrArg Complex.re h3
      simpa using this
    linarith
  have hex : ∃ w ∈ Metric.ball ((chartAt ℂ x) x) (min ρ ε), w ≠ (chartAt ℂ x) z₀ := by
    by_cases hc : ((chartAt ℂ x) x + ((min ρ ε / 2 : ℝ) : ℂ)) = (chartAt ℂ x) z₀
    · exact ⟨_, h2, fun hh => hne (hc.trans hh.symm)⟩
    · exact ⟨_, h1, hc⟩
  obtain ⟨w, hw, hwne⟩ := hex
  refine ⟨(chartAt ℂ x).symm w, ⟨(chartAt ℂ x).map_target (hball hw), ?_⟩, ?_⟩
  · show (chartAt ℂ x) ((chartAt ℂ x).symm w) ∈ Metric.ball ((chartAt ℂ x) x) ρ
    rw [(chartAt ℂ x).right_inv (hball hw)]
    exact (Metric.ball_subset_ball hleρ) hw
  · intro hy
    exact hwne (by rw [← hy, (chartAt ℂ x).right_inv (hball hw)])

theorem exists_ballAt_subset_avoid {y : X} {V : Set X} (hV : V ∈ 𝓝 y) (hyz : y ≠ z₀) :
    ∃ δ : ℝ, 0 < δ ∧ Metric.ball ((chartAt ℂ y) y) δ ⊆ (chartAt ℂ y).target ∧
      ballAt y δ ⊆ V ∧ z₀ ∉ ballAt y δ := by
  obtain ⟨δ₀, hδ₀, htgt, hsub⟩ := exists_ballAt_subset_nhds (x := y) hV
  by_cases hz : z₀ ∈ (chartAt ℂ y).source
  · have hne : (chartAt ℂ y) z₀ ≠ (chartAt ℂ y) y := by
      intro hh
      exact hyz ((chartAt ℂ y).injOn hz (mem_chart_source ℂ y) hh).symm
    have hpos : 0 < ‖(chartAt ℂ y) y - (chartAt ℂ y) z₀‖ := by
      rw [norm_pos_iff]; exact sub_ne_zero.mpr (Ne.symm hne)
    refine ⟨min δ₀ (‖(chartAt ℂ y) y - (chartAt ℂ y) z₀‖ / 2), by positivity,
      (Metric.ball_subset_ball (min_le_left _ _)).trans htgt,
      (ballAt_mono (min_le_left _ _)).trans hsub, ?_⟩
    intro hmem
    rw [mem_ballAt, Metric.mem_ball, dist_eq_norm] at hmem
    have h1 : ‖(chartAt ℂ y) z₀ - (chartAt ℂ y) y‖
        = ‖(chartAt ℂ y) y - (chartAt ℂ y) z₀‖ := by rw [← norm_neg, neg_sub]
    rw [h1] at hmem
    have h4 := min_le_right δ₀ (‖(chartAt ℂ y) y - (chartAt ℂ y) z₀‖ / 2)
    have h5 : 0 ≤ ‖(chartAt ℂ y) y - (chartAt ℂ y) z₀‖ := norm_nonneg _
    linarith [hmem.2]
  · exact ⟨δ₀, hδ₀, htgt, hsub, fun hmem => hz (mem_ballAt.mp hmem).1⟩

/-! ## The derivative in the preferred chart -/

theorem chartDeriv_congr {Φ Ψ : X → ℂ} {x : X} (h : Φ =ᶠ[𝓝 x] Ψ) :
    chartDeriv Φ x = chartDeriv Ψ x := by
  unfold chartDeriv
  refine Filter.EventuallyEq.deriv_eq ?_
  exact h.comp_tendsto ((chartAt ℂ x).tendsto_symm (mem_chart_source ℂ x))

theorem chartDeriv_congr_on {Φ Ψ : X → ℂ} {x : X} {W : Set X} (hW : W ∈ 𝓝 x)
    (h : ∀ y ∈ W, Φ y = Ψ y) : chartDeriv Φ x = chartDeriv Ψ x :=
  chartDeriv_congr (Filter.eventually_of_mem hW h)

theorem chartDeriv_const_mul (c : ℂ) {Φ : X → ℂ} {x : X} (h : Submission.HolomorphicOnXAt Φ x) :
    chartDeriv (fun y => c * Φ y) x = c * chartDeriv Φ x := by
  unfold chartDeriv
  have hfun : (fun y : X => c * Φ y) ∘ (chartAt ℂ x).symm
      = fun w : ℂ => c * (Φ ∘ (chartAt ℂ x).symm) w := rfl
  rw [hfun, deriv_const_mul c h.differentiableAt]

theorem isModulusBranch_const_mul {z₀ : X} {E : X → ℝ} {U : Set X} {Φ : X → ℂ} {c : ℂ}
    (hc : ‖c‖ = 1) (h : IsModulusBranch z₀ E U Φ) :
    IsModulusBranch z₀ E U (fun y => c * Φ y) := by
  have hcne : c ≠ 0 := by
    rw [← norm_ne_zero_iff, hc]; norm_num
  refine ⟨h.1, ?_, ?_, ?_⟩
  · have hfun : (fun y : X => c * Φ y) = Φ * (fun _ : X => c) := by
      funext y; exact mul_comm c (Φ y)
    rw [hfun]
    exact h.2.1.mul (Submission.holomorphicOnX_const c)
  · intro y hy hyz
    exact mul_ne_zero hcne (h.ne_zero y hy hyz)
  · intro y hy hyz
    rw [norm_mul, hc, one_mul, h.norm_eq y hy hyz]

/-! ## The identity theorem on a chart ball -/

theorem eqOn_ballAt_of_eventuallyEq {x : X} {ρ : ℝ}
    (ht : Metric.ball ((chartAt ℂ x) x) ρ ⊆ (chartAt ℂ x).target) {Φ Ψ : X → ℂ}
    (hΦ : Submission.HolomorphicOnX Φ (ballAt x ρ))
    (hΨ : Submission.HolomorphicOnX Ψ (ballAt x ρ))
    {y₀ : X} (hy₀ : y₀ ∈ ballAt x ρ) (h : Φ =ᶠ[𝓝 y₀] Ψ) :
    ∀ y ∈ ballAt x ρ, Φ y = Ψ y := by
  have hana : ∀ {Θ : X → ℂ}, Submission.HolomorphicOnX Θ (ballAt x ρ) →
      AnalyticOnNhd ℂ (Θ ∘ (chartAt ℂ x).symm) (Metric.ball ((chartAt ℂ x) x) ρ) := by
    intro Θ hΘ w hw
    have hwT : w ∈ (chartAt ℂ x).target := ht hw
    have hmem : (chartAt ℂ x).symm w ∈ ballAt x ρ := by
      refine ⟨(chartAt ℂ x).map_target hwT, ?_⟩
      show (chartAt ℂ x) ((chartAt ℂ x).symm w) ∈ Metric.ball ((chartAt ℂ x) x) ρ
      rw [(chartAt ℂ x).right_inv hwT]
      exact hw
    have h1 : Submission.HolomorphicOnXAt Θ ((chartAt ℂ x).symm w) := hΘ _ hmem
    rw [Submission.HolomorphicOnXAt_iff_chart (f := Θ) (x := (chartAt ℂ x).symm w) (y := x)
      ((chartAt ℂ x).map_target hwT)] at h1
    rwa [(chartAt ℂ x).right_inv hwT] at h1
  have hysrc : y₀ ∈ (chartAt ℂ x).source := (mem_ballAt.mp hy₀).1
  have hy' : (chartAt ℂ x) y₀ ∈ Metric.ball ((chartAt ℂ x) x) ρ := (mem_ballAt.mp hy₀).2
  have htend : Tendsto (chartAt ℂ x).symm (𝓝 ((chartAt ℂ x) y₀)) (𝓝 y₀) := by
    have h1 : ContinuousAt (chartAt ℂ x).symm ((chartAt ℂ x) y₀) :=
      (chartAt ℂ x).continuousAt_symm ((chartAt ℂ x).map_source hysrc)
    have h2 : (chartAt ℂ x).symm ((chartAt ℂ x) y₀) = y₀ := (chartAt ℂ x).left_inv hysrc
    simpa [h2] using h1.tendsto
  have hev : (Φ ∘ (chartAt ℂ x).symm) =ᶠ[𝓝 ((chartAt ℂ x) y₀)] (Ψ ∘ (chartAt ℂ x).symm) :=
    htend.eventually h
  have heq := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (hana hΦ) (hana hΨ)
    Metric.isPreconnected_ball hy' hev
  intro y hy
  have hys : y ∈ (chartAt ℂ x).source := (mem_ballAt.mp hy).1
  calc Φ y = (Φ ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) y) := by
        rw [Function.comp_apply, (chartAt ℂ x).left_inv hys]
    _ = (Ψ ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) y) := heq (mem_ballAt.mp hy).2
    _ = Ψ y := by rw [Function.comp_apply, (chartAt ℂ x).left_inv hys]

/-! ## Local models of the modulus bundle -/

/-- A local model of the modulus bundle at `x`: a chart ball around `x` carrying a branch `Φ` of the
modulus, and the requirement that `Φ` has a nonvanishing derivative at the pole when the pole lies
in the ball. -/
structure LocalModel (z₀ : X) (E : X → ℝ) (x : X) where
  ρ : ℝ
  hρ : 0 < ρ
  Φ : X → ℂ
  htarget : Metric.ball ((chartAt ℂ x) x) ρ ⊆ (chartAt ℂ x).target
  hbranch : IsModulusBranch z₀ E (ballAt x ρ) Φ
  hder₀ : z₀ ∈ ballAt x ρ → chartDeriv Φ z₀ ≠ 0

namespace LocalModel

variable {z₀ : X} {E : X → ℝ} {x : X}

theorem mem_ball (M : LocalModel z₀ E x) : x ∈ ballAt x M.ρ :=
  mem_ballAt_self M.hρ

/-- Off the pole the branch does not vanish; at the pole its derivative does not vanish. -/
theorem hsep (M : LocalModel z₀ E x) :
    ∀ y ∈ ballAt x M.ρ, M.Φ y ≠ 0 ∨ chartDeriv M.Φ y ≠ 0 := by
  intro y hy
  by_cases hyz : y = z₀
  · right
    rw [hyz]
    exact M.hder₀ (hyz ▸ hy)
  · left
    exact M.hbranch.ne_zero y hy hyz

theorem hol (M : LocalModel z₀ E x) : ∀ y ∈ ballAt x M.ρ, Submission.HolomorphicOnXAt M.Φ y :=
  M.hbranch.holomorphic

/-- **Two branches on overlapping domains differ by a constant of modulus one, locally.** -/
theorem exists_local_ratio (M : LocalModel z₀ E x) {V : Set X} {Ψ : X → ℂ}
    (hΨ : IsModulusBranch z₀ E V Ψ) {y : X}
    (hyB : y ∈ ballAt x M.ρ) (hyV : y ∈ V) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ∃ W : Set X, IsOpen W ∧ y ∈ W ∧ W ⊆ ballAt x M.ρ ∩ V ∧
      ∀ z ∈ W, Ψ z = c * M.Φ z := by
  by_cases hyz : y = z₀
  · subst y
    obtain ⟨δ, hδ, htgtδ, hsubδ⟩ :=
      exists_ballAt_subset_nhds (x := z₀) (V := ballAt x M.ρ ∩ V)
        (Filter.inter_mem ((isOpen_ballAt x M.ρ).mem_nhds hyB) (hΨ.1.mem_nhds hyV))
    have hsub1 : ballAt z₀ δ ⊆ ballAt x M.ρ :=
      fun z hz => ((Set.mem_of_mem_inter_left (hsubδ hz)))
    have hsub2 : ballAt z₀ δ ⊆ V :=
      fun z hz => ((Set.mem_of_mem_inter_right (hsubδ hz)))
    have hy : z₀ ∈ ballAt z₀ δ := mem_ballAt_self hδ
    obtain ⟨y', hy', hy'z⟩ := exists_ne_of_mem_ballAt hδ hy
    obtain ⟨δ', hδ', htgtδ', hsubδ', havoid⟩ :=
      exists_ballAt_subset_avoid (y := y') (V := ballAt z₀ δ)
        ((isOpen_ballAt z₀ δ).mem_nhds hy') hy'z
    have hy'self : y' ∈ ballAt y' δ' := mem_ballAt_self hδ'
    have hΦ' : IsModulusBranch z₀ E (ballAt y' δ') M.Φ :=
      M.hbranch.mono (isOpen_ballAt y' δ') (hsubδ'.trans hsub1)
    have hΨ' : IsModulusBranch z₀ E (ballAt y' δ') Ψ :=
      hΨ.mono (isOpen_ballAt y' δ') (hsubδ'.trans hsub2)
    have hpre : IsPreconnected ((ballAt y' δ' ∩ ballAt y' δ') \ {z₀}) := by
      have hP : (ballAt y' δ' ∩ ballAt y' δ') \ {z₀} = ballAt y' δ' := by
        ext z
        simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_singleton_iff]
        constructor
        · rintro ⟨⟨hz, -⟩, -⟩; exact hz
        · intro hz; exact ⟨⟨hz, hz⟩, fun h => havoid (h ▸ hz)⟩
      rw [hP]
      exact isPreconnected_ballAt htgtδ'
    obtain ⟨c, hc, heq⟩ :=
      Work.SimplyConnected.Modulus.exists_ratio_eq_of_isModulusBranch hΦ' hΨ' hpre
        ⟨y', ⟨⟨hy'self, hy'self⟩, hy'z⟩⟩
    have heq' : ∀ z ∈ ballAt y' δ', Ψ z = c * M.Φ z :=
      fun z hz => heq z ⟨⟨hz, hz⟩, fun h => havoid (h ▸ hz)⟩
    have hcΦ : Submission.HolomorphicOnX (fun z => c * M.Φ z) (ballAt z₀ δ) :=
      (isModulusBranch_const_mul hc (M.hbranch.mono (isOpen_ballAt z₀ δ) hsub1)).holomorphic
    have hΨδ : Submission.HolomorphicOnX Ψ (ballAt z₀ δ) :=
      (hΨ.mono (isOpen_ballAt z₀ δ) hsub2).holomorphic
    have hev : Ψ =ᶠ[𝓝 y'] (fun z => c * M.Φ z) :=
      Filter.eventually_of_mem ((isOpen_ballAt y' δ').mem_nhds hy'self) heq'
    have hfinal := eqOn_ballAt_of_eventuallyEq htgtδ hΨδ hcΦ hy' hev
    exact ⟨c, hc, ballAt z₀ δ, isOpen_ballAt _ _, hy, hsubδ, hfinal⟩
  · obtain ⟨δ, hδ, htgtδ, hsubδ, havoid⟩ :=
      exists_ballAt_subset_avoid (y := y) (V := ballAt x M.ρ ∩ V)
        (Filter.inter_mem ((isOpen_ballAt x M.ρ).mem_nhds hyB) (hΨ.1.mem_nhds hyV)) hyz
    have hsub1 : ballAt y δ ⊆ ballAt x M.ρ :=
      fun z hz => ((Set.mem_of_mem_inter_left (hsubδ hz)))
    have hsub2 : ballAt y δ ⊆ V :=
      fun z hz => ((Set.mem_of_mem_inter_right (hsubδ hz)))
    have hyself : y ∈ ballAt y δ := mem_ballAt_self hδ
    have hΦ' : IsModulusBranch z₀ E (ballAt y δ) M.Φ :=
      M.hbranch.mono (isOpen_ballAt y δ) hsub1
    have hΨ' : IsModulusBranch z₀ E (ballAt y δ) Ψ :=
      hΨ.mono (isOpen_ballAt y δ) hsub2
    have hpre : IsPreconnected ((ballAt y δ ∩ ballAt y δ) \ {z₀}) := by
      have hP : (ballAt y δ ∩ ballAt y δ) \ {z₀} = ballAt y δ := by
        ext z
        simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_singleton_iff]
        constructor
        · rintro ⟨⟨hz, -⟩, -⟩; exact hz
        · intro hz; exact ⟨⟨hz, hz⟩, fun h => havoid (h ▸ hz)⟩
      rw [hP]
      exact isPreconnected_ballAt htgtδ
    obtain ⟨c, hc, heq⟩ :=
      Work.SimplyConnected.Modulus.exists_ratio_eq_of_isModulusBranch hΦ' hΨ' hpre
        ⟨y, ⟨⟨hyself, hyself⟩, hyz⟩⟩
    exact ⟨c, hc, ballAt y δ, isOpen_ballAt _ _, hyself, hsubδ,
      fun z hz => heq z ⟨⟨hz, hz⟩, fun h => havoid (h ▸ hz)⟩⟩

theorem unit_eq_of_mul_eq (M : LocalModel z₀ E x) {c c' : ℂ} {y : X} (hy : y ∈ ballAt x M.ρ)
    (hval : c' * M.Φ y = c * M.Φ y) (hder : c' * chartDeriv M.Φ y = c * chartDeriv M.Φ y) :
    c' = c := by
  rcases M.hsep y hy with h | h
  · have h0 : (c' - c) * M.Φ y = 0 := by rw [sub_mul, sub_eq_zero]; exact hval
    exact sub_eq_zero.mp ((mul_eq_zero.mp h0).resolve_right h)
  · have h0 : (c' - c) * chartDeriv M.Φ y = 0 := by rw [sub_mul, sub_eq_zero]; exact hder
    exact sub_eq_zero.mp ((mul_eq_zero.mp h0).resolve_right h)

theorem unit_eq_of_mem_graph (M : LocalModel z₀ E x) {p : X × ℂ × ℂ} {c c' : ℂ}
    {y : X} (hy : y ∈ ballAt x M.ρ) (hy1 : p.1 = y)
    (h1 : p ∈ branchGraph (ballAt x M.ρ) (fun z => c * M.Φ z))
    (h2 : p ∈ branchGraph (ballAt x M.ρ) (fun z => c' * M.Φ z)) : c' = c := by
  have hp1 : p.1 ∈ ballAt x M.ρ := hy1 ▸ hy
  have hval : c' * M.Φ y = c * M.Φ y := by
    have h2' : p.2.1 = c' * M.Φ p.1 := h2.2.1
    have h1' : p.2.1 = c * M.Φ p.1 := h1.2.1
    rw [← hy1, ← h2', h1']
  have hder : c' * chartDeriv M.Φ y = c * chartDeriv M.Φ y := by
    have h2' : p.2.2 = c' * chartDeriv M.Φ p.1 := by
      rw [h2.2.2, chartDeriv_const_mul c' (M.hbranch.holomorphic p.1 hp1)]
    have h1' : p.2.2 = c * chartDeriv M.Φ p.1 := by
      rw [h1.2.2, chartDeriv_const_mul c (M.hbranch.holomorphic p.1 hp1)]
    rw [← hy1, ← h2', h1']
  exact M.unit_eq_of_mul_eq hy hval hder

/-- **Every point of the bundle over the chart ball lies on a sheet.** -/
theorem exists_unit_mem_graph (M : LocalModel z₀ E x) {p : X × ℂ × ℂ}
    (hp : p ∈ branchSet z₀ E) (hpB : p.1 ∈ ballAt x M.ρ) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ p ∈ branchGraph (ballAt x M.ρ) (fun z => c * M.Φ z) := by
  obtain ⟨V, Ψ, hΨ, hpV⟩ := hp
  obtain ⟨c, hc, W, hWopen, hpW, hWsub, heq⟩ := M.exists_local_ratio hΨ hpB hpV.1
  refine ⟨c, hc, hpB, ?_, ?_⟩
  · rw [hpV.2.1, heq p.1 hpW]
  · rw [hpV.2.2, chartDeriv_congr (Filter.eventually_of_mem (hWopen.mem_nhds hpW) heq)]

noncomputable def unitAt (M : LocalModel z₀ E x) (p : X × ℂ × ℂ) (hp : p ∈ branchSet z₀ E)
    (hpB : p.1 ∈ ballAt x M.ρ) : ℂ := Classical.choose (M.exists_unit_mem_graph hp hpB)

theorem unitAt_spec (M : LocalModel z₀ E x) (p : X × ℂ × ℂ) (hp : p ∈ branchSet z₀ E)
    (hpB : p.1 ∈ ballAt x M.ρ) :
    ‖M.unitAt p hp hpB‖ = 1 ∧
      p ∈ branchGraph (ballAt x M.ρ) (fun z => M.unitAt p hp hpB * M.Φ z) :=
  Classical.choose_spec (M.exists_unit_mem_graph hp hpB)

/-- The unit of the sheet through a point: off the pole it is the ratio of the value to `Φ`, at the
pole the ratio of the preferred-chart derivative to that of `Φ`. -/
noncomputable def sheetIndex (M : LocalModel z₀ E x) (p : X × ℂ × ℂ) : ℂ :=
  if p.1 = z₀ then p.2.2 / chartDeriv M.Φ z₀ else p.2.1 / M.Φ p.1

theorem sheetIndex_eq_of_mem_graph (M : LocalModel z₀ E x) {c : ℂ} {p : X × ℂ × ℂ}
    (hp : p ∈ branchGraph (ballAt x M.ρ) (fun z => c * M.Φ z)) (hpB : p.1 ∈ ballAt x M.ρ) :
    M.sheetIndex p = c := by
  unfold LocalModel.sheetIndex
  by_cases hz : p.1 = z₀
  · rw [if_pos hz]
    have hd : chartDeriv M.Φ z₀ ≠ 0 := M.hder₀ (hz ▸ hpB)
    have hΦz : Submission.HolomorphicOnXAt M.Φ p.1 := M.hbranch.holomorphic p.1 hpB
    have hp22 : p.2.2 = c * chartDeriv M.Φ z₀ := by
      rw [hp.2.2, chartDeriv_const_mul c hΦz, hz]
    rw [hp22]
    field_simp
  · rw [if_neg hz]
    have hne : M.Φ p.1 ≠ 0 := M.hbranch.ne_zero p.1 hpB hz
    rw [hp.2.1]
    field_simp

theorem unit_spec_eq (M : LocalModel z₀ E x) (p : X × ℂ × ℂ) (hp : p ∈ branchSet z₀ E)
    (hpB : p.1 ∈ ballAt x M.ρ) : M.sheetIndex p = M.unitAt p hp hpB :=
  M.sheetIndex_eq_of_mem_graph (M.unitAt_spec p hp hpB).2 hpB

theorem sheetIndex_unit (M : LocalModel z₀ E x) {p : X × ℂ × ℂ} (hp : p ∈ branchSet z₀ E)
    (hpB : p.1 ∈ ballAt x M.ρ) : ‖M.sheetIndex p‖ = 1 := by
  rw [M.unit_spec_eq p hp hpB]
  exact (M.unitAt_spec p hp hpB).1

theorem sheetIndex_mem_graph (M : LocalModel z₀ E x) {p : X × ℂ × ℂ} (hp : p ∈ branchSet z₀ E)
    (hpB : p.1 ∈ ballAt x M.ρ) :
    p ∈ branchGraph (ballAt x M.ρ) (fun z => M.sheetIndex p * M.Φ z) := by
  rw [M.unit_spec_eq p hp hpB]
  exact (M.unitAt_spec p hp hpB).2

/-! ## Sheets -/

/-- The point of the sheet with unit `c` over `y`. -/
def sheetPt (M : LocalModel z₀ E x) (c : ℂ) (y : X) : X × ℂ × ℂ :=
  (y, c * M.Φ y, chartDeriv (fun z => c * M.Φ z) y)

theorem sheetPt_mem_graph (M : LocalModel z₀ E x) {c : ℂ} {y : X}
    (hy : y ∈ ballAt x M.ρ) :
    sheetPt M c y ∈ branchGraph (ballAt x M.ρ) (fun z => c * M.Φ z) :=
  ⟨hy, rfl, rfl⟩

theorem sheetPt_mem_branchSet (M : LocalModel z₀ E x) {c : ℂ} (hc : ‖c‖ = 1) {y : X}
    (hy : y ∈ ballAt x M.ρ) : sheetPt M c y ∈ branchSet z₀ E :=
  ⟨ballAt x M.ρ, fun z => c * M.Φ z, isModulusBranch_const_mul hc M.hbranch,
    sheetPt_mem_graph M hy⟩

theorem eq_sheetPt_of_mem_graph (M : LocalModel z₀ E x) {c : ℂ} {p : X × ℂ × ℂ}
    (hp : p ∈ branchGraph (ballAt x M.ρ) (fun z => c * M.Φ z)) : p = sheetPt M c p.1 := by
  obtain ⟨-, h1, h2⟩ := hp
  refine Prod.ext rfl (Prod.ext ?_ ?_)
  · simpa [LocalModel.sheetPt] using h1
  · simpa [LocalModel.sheetPt] using h2

theorem sheetPt_eq_sheetPt_iff (M : LocalModel z₀ E x) {c c' : ℂ} {y : X}
    (hy : y ∈ ballAt x M.ρ) : sheetPt M c y = sheetPt M c' y ↔ c = c' := by
  constructor
  · intro h
    have h1 : c * M.Φ y = c' * M.Φ y := by
      have := congrArg (fun p : X × ℂ × ℂ => p.2.1) h
      simpa [LocalModel.sheetPt] using this
    have h2 : c * chartDeriv M.Φ y = c' * chartDeriv M.Φ y := by
      have h3 : chartDeriv (fun z => c * M.Φ z) y = chartDeriv (fun z => c' * M.Φ z) y := by
        have := congrArg (fun p : X × ℂ × ℂ => p.2.2) h
        simpa [LocalModel.sheetPt] using this
      rwa [chartDeriv_const_mul c (M.hbranch.holomorphic y hy),
           chartDeriv_const_mul c' (M.hbranch.holomorphic y hy)] at h3
    exact (M.unit_eq_of_mul_eq hy h1.symm h2.symm).symm
  · intro h; rw [h]

end LocalModel

/-! ## Continuity into the bundle topology -/

/-- Continuity into the topology generated by the branch graphs: it suffices to know that the
preimages of the graphs are open. -/
theorem continuous_branchTopology_of_generators {Z : Type*} [TopologicalSpace Z] {z₀ : X}
    {E : X → ℝ} {f : Z → X × ℂ × ℂ}
    (h : ∀ G ∈ branchFamily z₀ E, IsOpen (f ⁻¹' G)) :
    @Continuous Z (X × ℂ × ℂ) _ (branchTopology z₀ E) f := by
  letI : TopologicalSpace (X × ℂ × ℂ) := branchTopology z₀ E
  refine Continuous.mk ?_
  intro S hS
  change TopologicalSpace.GenerateOpen (branchFamily z₀ E) S at hS
  induction hS with
  | basic s hs => exact h s hs
  | univ => simpa using isOpen_univ
  | inter s t _ _ ihs iht => rw [Set.preimage_inter]; exact ihs.inter iht
  | sUnion S _ ih =>
      rw [Set.preimage_sUnion]
      exact isOpen_iUnion fun s => isOpen_iUnion fun hs => ih s hs

theorem isOpen_preimage_graph_of_sheetPt (M : LocalModel z₀ E x) {c : ℂ}
    {V : Set X} {Ψ : X → ℂ} (hV : IsModulusBranch z₀ E V Ψ) :
    IsOpen {y : X | y ∈ ballAt x M.ρ ∧
      LocalModel.sheetPt M c y ∈ branchGraph V Ψ} := by
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨hyB, hyV, hval, hder⟩
  simp only [LocalModel.sheetPt] at hyV hval hder
  obtain ⟨c₀, hc₀, W, hWopen, hyW, hWsub, heq⟩ := M.exists_local_ratio hV hyB hyV
  have hΦy : Submission.HolomorphicOnXAt M.Φ y := M.hbranch.holomorphic y hyB
  have hc₀eq : c₀ = c := by
    refine M.unit_eq_of_mul_eq hyB ?_ ?_
    · exact (heq y hyW).symm.trans hval.symm
    · rw [← chartDeriv_const_mul c₀ hΦy, ← chartDeriv_const_mul c hΦy]
      rw [← chartDeriv_congr (Filter.eventually_of_mem (hWopen.mem_nhds hyW) heq), hder]
  have heqc : ∀ z ∈ W, Ψ z = c * M.Φ z := by
    intro z hz
    rw [heq z hz, hc₀eq]
  refine Filter.mem_of_superset (hWopen.mem_nhds hyW) ?_
  intro z hz
  exact ⟨(hWsub hz).1, (hWsub hz).2, (heqc z hz).symm,
    (chartDeriv_congr (Filter.eventually_of_mem (hWopen.mem_nhds hz) heqc)).symm⟩

theorem continuous_sheetPt (M : LocalModel z₀ E x) {c : ℂ} (hc : ‖c‖ = 1) :
    @Continuous (↥(ballAt x M.ρ)) (X × ℂ × ℂ) _ (branchTopology z₀ E)
      (fun y => LocalModel.sheetPt M c y.1) := by
  refine continuous_branchTopology_of_generators ?_
  intro G hG
  obtain ⟨V, Ψ, hΨ, rfl⟩ := hG
  have h1 : IsOpen (Subtype.val ⁻¹' {y : X | y ∈ ballAt x M.ρ ∧
      LocalModel.sheetPt M c y ∈ branchGraph V Ψ}) :=
    IsOpen.preimage (f := (Subtype.val : ↥(ballAt x M.ρ) → X)) continuous_subtype_val
      (isOpen_preimage_graph_of_sheetPt M hΨ)
  have hset : Subtype.val ⁻¹' {y : X | y ∈ ballAt x M.ρ ∧
      LocalModel.sheetPt M c y ∈ branchGraph V Ψ}
      = (fun y : ↥(ballAt x M.ρ) => LocalModel.sheetPt M c y.1) ⁻¹' branchGraph V Ψ := by
    ext y
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    constructor
    · rintro ⟨-, h⟩; exact h
    · intro h; exact ⟨y.2, h⟩
  rwa [hset] at h1

/-! ## The bundle with its modulus topology -/

theorem isOpen_modulusBundle_of_isOpen {z₀ : X} {E : X → ℝ} {S : Set (X × ℂ × ℂ)}
    (hS : IsOpen[branchTopology z₀ E] S) :
    IsOpen[modulusBundleTopology z₀ E] (Subtype.val ⁻¹' S) := by
  letI : TopologicalSpace (X × ℂ × ℂ) := branchTopology z₀ E
  letI : TopologicalSpace ↥(branchSet z₀ E) := modulusBundleTopology z₀ E
  exact IsOpen.preimage (f := (Subtype.val : ↥(branchSet z₀ E) → X × ℂ × ℂ))
    (continuous_induced_dom (t := branchTopology z₀ E)) hS

theorem isOpen_modulusBundle_preimage {z₀ : X} {E : X → ℝ} {U : Set X} {Φ : X → ℂ}
    (h : IsModulusBranch z₀ E U Φ) :
    IsOpen[modulusBundleTopology z₀ E] (Subtype.val ⁻¹' branchGraph U Φ) :=
  isOpen_modulusBundle_of_isOpen (TopologicalSpace.isOpen_generateFrom_of_mem ⟨U, Φ, h, rfl⟩)

theorem continuous_branchProj :
    @Continuous (↥(branchSet z₀ E)) X (modulusBundleTopology z₀ E) _ (branchProj z₀ E) := by
  letI : TopologicalSpace (X × ℂ × ℂ) := branchTopology z₀ E
  letI : TopologicalSpace ↥(branchSet z₀ E) := modulusBundleTopology z₀ E
  rw [continuous_def]
  intro W hW
  have hS : IsOpen[branchTopology z₀ E]
      (⋃₀ {G : Set (X × ℂ × ℂ) | G ∈ branchFamily z₀ E ∧ G ⊆ Prod.fst ⁻¹' W}) :=
    isOpen_sUnion fun G hG => TopologicalSpace.isOpen_generateFrom_of_mem hG.1
  have hset : (Subtype.val : ↥(branchSet z₀ E) → X × ℂ × ℂ) ⁻¹'
        (⋃₀ {G : Set (X × ℂ × ℂ) | G ∈ branchFamily z₀ E ∧ G ⊆ Prod.fst ⁻¹' W})
      = branchProj z₀ E ⁻¹' W := by
    ext p
    constructor
    · rintro ⟨G, ⟨hG, hGsub⟩, hpG⟩
      exact hGsub hpG
    · intro hp
      obtain ⟨U, Φ, hbr, hpG⟩ := p.2
      exact ⟨branchGraph (U ∩ W) Φ,
        ⟨⟨U ∩ W, Φ, hbr.mono (hbr.1.inter hW) Set.inter_subset_left, rfl⟩,
          fun q hq => hq.1.2⟩,
        ⟨⟨hpG.1, hp⟩, hpG.2.1, hpG.2.2⟩⟩
  rw [← hset]
  exact isOpen_modulusBundle_of_isOpen hS


/-! ## Existence of local models -/

theorem exists_localModel {z₀ : X} {E : X → ℝ} (hE : Submission.HasGreenFunctionE z₀ E)
    (x : X) : Nonempty (LocalModel z₀ E x) := by
  by_cases hx : x = z₀
  · subst x
    obtain ⟨U, Φ, hbr, hU, hpole⟩ :=
      Work.SimplyConnected.Modulus.exists_isModulusBranch_at_pole (X := X) (z₀ := z₀) (E := E) hE
    obtain ⟨ρ, hρ, htgt, hsub⟩ := exists_ballAt_subset_nhds (x := z₀) (V := U) hU
    exact ⟨⟨ρ, hρ, Φ, htgt, hbr.mono (isOpen_ballAt z₀ ρ) hsub,
      fun _ => Submission.phi_deriv_ne_zero_of_logPole hpole⟩⟩
  · obtain ⟨U, Φ, hbr, hU, hΦx⟩ :=
      Work.SimplyConnected.Modulus.exists_isModulusBranch_of_ne (X := X) (z₀ := z₀) (x := x) (E := E)
        hE hx
    obtain ⟨ρ₀, hρ₀, htgt₀, hsub₀⟩ := exists_ballAt_subset_nhds (x := x) (V := U) hU
    obtain ⟨ρ, hρ, hρle, havoid⟩ := exists_ballAt_avoid (x := x) (ρ := ρ₀) hρ₀ hx
    exact ⟨⟨ρ, hρ, Φ, (Metric.ball_subset_ball hρle).trans htgt₀,
      hbr.mono (isOpen_ballAt x ρ) ((ballAt_mono hρle).trans hsub₀),
      fun h => (havoid h).elim⟩⟩

/-! ## Additional sheet lemmas -/

namespace LocalModel

variable {z₀ : X} {E : X → ℝ} {x : X}

theorem sheetIndex_sheetPt (M : LocalModel z₀ E x) {c : ℂ} {y : X}
    (hy : y ∈ ballAt x M.ρ) : M.sheetIndex (sheetPt M c y) = c :=
  M.sheetIndex_eq_of_mem_graph (sheetPt_mem_graph M hy) hy

theorem eq_sheetPt_sheetIndex (M : LocalModel z₀ E x) {p : X × ℂ × ℂ}
    (hp : p ∈ branchSet z₀ E) (hpB : p.1 ∈ ballAt x M.ρ) :
    sheetPt M (M.sheetIndex p) p.1 = p :=
  (eq_sheetPt_of_mem_graph M (M.sheetIndex_mem_graph hp hpB)).symm

theorem sheetPt_index_eq_self (M : LocalModel z₀ E x) {i : X × ℂ × ℂ}
    (hi : i ∈ branchSet z₀ E) (hi1 : i.1 = x) :
    sheetPt M (M.sheetIndex i) x = i := by
  have h := M.eq_sheetPt_sheetIndex hi (hi1 ▸ mem_ball M)
  rwa [hi1] at h

theorem continuous_sheetPtB (M : LocalModel z₀ E x) {c : ℂ} (hc : ‖c‖ = 1) :
    @Continuous (↥(ballAt x M.ρ)) (↥(branchSet z₀ E)) _ (modulusBundleTopology z₀ E)
      (fun y => ⟨sheetPt M c y.1, M.sheetPt_mem_branchSet hc y.2⟩) := by
  letI : TopologicalSpace (X × ℂ × ℂ) := branchTopology z₀ E
  letI : TopologicalSpace ↥(branchSet z₀ E) := modulusBundleTopology z₀ E
  exact Continuous.subtype_mk (continuous_sheetPt M hc)
    (fun y => M.sheetPt_mem_branchSet hc y.2)

end LocalModel

end Work.SC

namespace Work.SimplyConnected.Modulus

theorem isCoveringMap_branchProj {X : Type*} [TopologicalSpace X] [T2Space X]
    [ConnectedSpace X] [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] {z₀ : X} {E : X → ℝ}
    (hE : Submission.HasGreenFunctionE z₀ E) :
    @IsCoveringMap (Work.SC.ModulusBundle z₀ E) X (Work.SC.modulusBundleTopology z₀ E) _
      (Work.SC.branchProj z₀ E) := by
  letI : TopologicalSpace (Work.SC.ModulusBundle z₀ E) := Work.SC.modulusBundleTopology z₀ E
  intro x
  obtain ⟨M⟩ := Work.SC.exists_localModel (z₀ := z₀) (E := E) hE x
  have hxM : x ∈ Work.SC.ballAt x M.ρ := M.mem_ball
  have hfib : ∀ (c : ℂ) (hc : ‖c‖ = 1), (Work.SC.branchProj z₀ E)
      ⟨Work.SC.LocalModel.sheetPt M c x, M.sheetPt_mem_branchSet hc hxM⟩ = x := by
    intro c hc
    simp [Work.SC.branchProj, Work.SC.LocalModel.sheetPt]
  -- the point of the fibre over `x` on the sheet with unit `c`
  let fibPt : (c : ℂ) → ‖c‖ = 1 → ↥((Work.SC.branchProj z₀ E) ⁻¹' ({x} : Set X)) :=
    fun c hc => ⟨⟨Work.SC.LocalModel.sheetPt M c x, M.sheetPt_mem_branchSet hc hxM⟩, hfib c hc⟩
  -- the trivialisation and its inverse
  let H : ↥((Work.SC.branchProj z₀ E) ⁻¹' Work.SC.ballAt x M.ρ) →
      ↥(Work.SC.ballAt x M.ρ) × ↥((Work.SC.branchProj z₀ E) ⁻¹' ({x} : Set X)) :=
    fun p => (⟨p.1.1.1, p.2⟩, fibPt (M.sheetIndex p.1.1) (M.sheetIndex_unit p.1.2 p.2))
  let Hinv : ↥(Work.SC.ballAt x M.ρ) × ↥((Work.SC.branchProj z₀ E) ⁻¹' ({x} : Set X)) →
      ↥((Work.SC.branchProj z₀ E) ⁻¹' Work.SC.ballAt x M.ρ) := fun q =>
    ⟨⟨Work.SC.LocalModel.sheetPt M (M.sheetIndex q.2.1.1) q.1.1,
        M.sheetPt_mem_branchSet (M.sheetIndex_unit q.2.1.2 (by
          have h : q.2.1.1.1 = x := q.2.2
          rw [h]; exact hxM)) q.1.2⟩,
      q.1.2⟩
  -- discreteness of the fibre
  have hdisc : DiscreteTopology ↥((Work.SC.branchProj z₀ E) ⁻¹' ({x} : Set X)) := by
    rw [discreteTopology_iff_isOpen_singleton]
    rintro ⟨p, hp⟩
    have hp' : p.1.1 = x := hp
    have hpB : p.1.1 ∈ Work.SC.ballAt x M.ρ := by rw [hp']; exact hxM
    have hc1 : ‖M.sheetIndex p.1‖ = 1 := M.sheetIndex_unit p.2 hpB
    have hmem : p.1 ∈ Work.SC.branchGraph (Work.SC.ballAt x M.ρ)
        (fun z => M.sheetIndex p.1 * M.Φ z) := M.sheetIndex_mem_graph p.2 hpB
    refine ⟨(fun p' : ↥(Work.SC.branchSet z₀ E) => (p' : X × ℂ × ℂ)) ⁻¹'
        Work.SC.branchGraph (Work.SC.ballAt x M.ρ) (fun z => M.sheetIndex p.1 * M.Φ z),
      Work.SC.isOpen_modulusBundle_preimage (Work.SC.isModulusBranch_const_mul hc1 M.hbranch), ?_⟩
    ext q
    constructor
    · intro hq
      rw [Set.mem_singleton_iff]
      have hq1 : q.1.1.1 = x := q.2
      have hqmem : q.1.1 ∈ Work.SC.branchGraph (Work.SC.ballAt x M.ρ)
          (fun z => M.sheetIndex p.1 * M.Φ z) := hq
      have h1' := Work.SC.LocalModel.eq_sheetPt_of_mem_graph M hqmem
      have h1 : q.1.1 = Work.SC.LocalModel.sheetPt M (M.sheetIndex p.1) x := by
        rw [show q.1.1.1 = x from hq1] at h1'
        exact h1'
      have h2' := Work.SC.LocalModel.eq_sheetPt_of_mem_graph M hmem
      have h2 : p.1 = Work.SC.LocalModel.sheetPt M (M.sheetIndex p.1) x := by
        rw [show p.1.1 = x from hp'] at h2'
        exact h2'
      refine Subtype.ext (Subtype.ext ?_)
      exact h1.trans h2.symm
    · intro hq
      rw [Set.mem_singleton_iff] at hq
      subst hq
      exact hmem
  -- openness of the preimage of the trivialising neighbourhood
  have hopenF : IsOpen ((Work.SC.branchProj z₀ E) ⁻¹' Work.SC.ballAt x M.ρ) :=
    Work.SC.continuous_branchProj.isOpen_preimage (Work.SC.ballAt x M.ρ)
      (Work.SC.isOpen_ballAt x M.ρ)
  -- value-level descriptions of the two maps
  have H_fst_val (p : ↥((Work.SC.branchProj z₀ E) ⁻¹' Work.SC.ballAt x M.ρ)) :
      (H p).1.1 = p.1.1.1 := rfl
  have H_snd_val (p : ↥((Work.SC.branchProj z₀ E) ⁻¹' Work.SC.ballAt x M.ρ)) :
      (H p).2.1.1 = Work.SC.LocalModel.sheetPt M (M.sheetIndex p.1.1) x := rfl
  have H_snd_val' (p : ↥((Work.SC.branchProj z₀ E) ⁻¹' Work.SC.ballAt x M.ρ)) :
      (H p).2 = fibPt (M.sheetIndex p.1.1) (M.sheetIndex_unit p.1.2 p.2) := rfl
  have Hinv_val (b : ↥(Work.SC.ballAt x M.ρ))
      (i : ↥((Work.SC.branchProj z₀ E) ⁻¹' ({x} : Set X))) :
      (Hinv (b, i)).1.1 = Work.SC.LocalModel.sheetPt M (M.sheetIndex i.1.1) b.1 := rfl
  have fibPt_val (c : ℂ) (hc : ‖c‖ = 1) :
      (fibPt c hc).1.1 = Work.SC.LocalModel.sheetPt M c x := rfl
  -- the two inverse identities
  have hleft : Function.LeftInverse Hinv H := by
    intro p
    have h1 : M.sheetIndex (Work.SC.LocalModel.sheetPt M (M.sheetIndex p.1.1) x)
        = M.sheetIndex p.1.1 := M.sheetIndex_sheetPt hxM
    have h2 : Work.SC.LocalModel.sheetPt M (M.sheetIndex p.1.1) p.1.1.1 = p.1.1 :=
      M.eq_sheetPt_sheetIndex p.1.2 p.2
    have hval : (Hinv (H p)).1.1 = p.1.1 := by
      rw [show (Hinv (H p)).1.1 = Work.SC.LocalModel.sheetPt M
        (M.sheetIndex (H p).2.1.1) (H p).1.1 from rfl]
      rw [H_snd_val p, H_fst_val p, h1, h2]
    exact Subtype.ext (Subtype.ext hval)
  have hright : Function.RightInverse Hinv H := by
    intro q
    have hq2 : q.2.1.1.1 = x := q.2.2
    have h1 : M.sheetIndex (Work.SC.LocalModel.sheetPt M (M.sheetIndex q.2.1.1) q.1.1)
        = M.sheetIndex q.2.1.1 := M.sheetIndex_sheetPt q.1.2
    have h3 : Work.SC.LocalModel.sheetPt M (M.sheetIndex q.2.1.1) x = q.2.1.1 :=
      M.sheetPt_index_eq_self q.2.1.2 hq2
    have hidx : M.sheetIndex (Hinv q).1.1 = M.sheetIndex q.2.1.1 := by
      rw [show (Hinv q).1.1 = Work.SC.LocalModel.sheetPt M (M.sheetIndex q.2.1.1) q.1.1 from rfl]
      exact h1
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext (Subtype.ext ?_))
    · change (H (Hinv q)).1.1 = q.1.1
      rw [H_fst_val (Hinv q)]
      rw [show (Hinv q).1.1 = Work.SC.LocalModel.sheetPt M (M.sheetIndex q.2.1.1) q.1.1 from rfl]
      rfl
    · rw [show (H (Hinv q)).2 = fibPt (M.sheetIndex (Hinv q).1.1)
          (M.sheetIndex_unit (Hinv q).1.2 (Hinv q).2) from rfl]
      rw [fibPt_val (M.sheetIndex (Hinv q).1.1) (M.sheetIndex_unit (Hinv q).1.2 (Hinv q).2)]
      rw [hidx]
      exact h3
  -- continuity of the trivialisation
  have hcontH : Continuous H := by
    rw [continuous_iff_continuousAt]
    intro p
    have hc1 : ‖M.sheetIndex p.1.1‖ = 1 := M.sheetIndex_unit p.1.2 p.2
    have hmem : p.1.1 ∈ Work.SC.branchGraph (Work.SC.ballAt x M.ρ)
        (fun z => M.sheetIndex p.1.1 * M.Φ z) := M.sheetIndex_mem_graph p.1.2 p.2
    have hS : IsOpen ((fun p' : ↥(Work.SC.branchSet z₀ E) => (p' : X × ℂ × ℂ)) ⁻¹'
        Work.SC.branchGraph (Work.SC.ballAt x M.ρ) (fun z => M.sheetIndex p.1.1 * M.Φ z)) :=
      Work.SC.isOpen_modulusBundle_preimage (Work.SC.isModulusBranch_const_mul hc1 M.hbranch)
    have hopen : IsOpen ((fun q : ↥((Work.SC.branchProj z₀ E) ⁻¹' Work.SC.ballAt x M.ρ) =>
        (q.1 : ↥(Work.SC.branchSet z₀ E))) ⁻¹'
        ((fun p' : ↥(Work.SC.branchSet z₀ E) => (p' : X × ℂ × ℂ)) ⁻¹'
          Work.SC.branchGraph (Work.SC.ballAt x M.ρ)
            (fun z => M.sheetIndex p.1.1 * M.Φ z))) :=
      IsOpen.preimage (f := (Subtype.val :
        ↥((Work.SC.branchProj z₀ E) ⁻¹' Work.SC.ballAt x M.ρ) → ↥(Work.SC.branchSet z₀ E)))
        continuous_subtype_val hS
    have hmemS : p ∈ ((fun q : ↥((Work.SC.branchProj z₀ E) ⁻¹' Work.SC.ballAt x M.ρ) =>
        (q.1 : ↥(Work.SC.branchSet z₀ E))) ⁻¹'
        ((fun p' : ↥(Work.SC.branchSet z₀ E) => (p' : X × ℂ × ℂ)) ⁻¹'
          Work.SC.branchGraph (Work.SC.ballAt x M.ρ)
            (fun z => M.sheetIndex p.1.1 * M.Φ z))) := hmem
    have hg : Continuous (fun q : ↥((Work.SC.branchProj z₀ E) ⁻¹' Work.SC.ballAt x M.ρ) =>
        ((⟨q.1.1.1, q.2⟩ : ↥(Work.SC.ballAt x M.ρ)),
          fibPt (M.sheetIndex p.1.1) (M.sheetIndex_unit p.1.2 p.2))) := by
      refine Continuous.prodMk ?_ continuous_const
      exact Continuous.subtype_mk
        (Work.SC.continuous_branchProj.comp continuous_subtype_val) (fun q => q.2)
    refine ContinuousOn.continuousAt
      (ContinuousOn.congr (Continuous.continuousOn hg) ?_) (hopen.mem_nhds hmemS)
    intro q hq
    have hqidx : M.sheetIndex q.1.1 = M.sheetIndex p.1.1 :=
      M.sheetIndex_eq_of_mem_graph hq q.2
    refine Prod.ext (Subtype.ext (H_fst_val q)) (Subtype.ext (Subtype.ext ?_))
    rw [H_snd_val q, fibPt_val (M.sheetIndex p.1.1) (M.sheetIndex_unit p.1.2 p.2), hqidx]
  -- continuity of the inverse
  have hcontHinv : Continuous Hinv := by
    rw [continuous_iff_continuousAt]
    rintro ⟨b, i⟩
    have hi1 : i.1.1.1 = x := i.2
    have hci : ‖M.sheetIndex i.1.1‖ = 1 :=
      M.sheetIndex_unit i.1.2 (by rw [hi1]; exact hxM)
    have hopen : IsOpen ((Set.univ : Set ↥(Work.SC.ballAt x M.ρ)) ×ˢ
        ({i} : Set ↥((Work.SC.branchProj z₀ E) ⁻¹' ({x} : Set X)))) :=
      isOpen_univ.prod (isOpen_discrete ({i} : Set ↥((Work.SC.branchProj z₀ E) ⁻¹' ({x} : Set X))))
    have hmemS : (b, i) ∈ (Set.univ : Set ↥(Work.SC.ballAt x M.ρ)) ×ˢ
        ({i} : Set ↥((Work.SC.branchProj z₀ E) ⁻¹' ({x} : Set X))) := ⟨trivial, rfl⟩
    have hg : Continuous (fun q : ↥(Work.SC.ballAt x M.ρ) ×
        ↥((Work.SC.branchProj z₀ E) ⁻¹' ({x} : Set X)) =>
        (⟨⟨Work.SC.LocalModel.sheetPt M (M.sheetIndex i.1.1) q.1.1,
            M.sheetPt_mem_branchSet hci q.1.2⟩, q.1.2⟩ :
          ↥((Work.SC.branchProj z₀ E) ⁻¹' Work.SC.ballAt x M.ρ))) := by
      refine Continuous.subtype_mk ?_ (fun q => q.1.2)
      have hbase : Continuous (fun q : ↥(Work.SC.ballAt x M.ρ) ×
          ↥((Work.SC.branchProj z₀ E) ⁻¹' ({x} : Set X)) => q.1) :=
        continuous_fst
      exact (Work.SC.LocalModel.continuous_sheetPtB M hci).comp hbase
    refine ContinuousOn.continuousAt
      (ContinuousOn.congr (Continuous.continuousOn hg) ?_) (hopen.mem_nhds hmemS)
    intro q hq
    have hq2 : q.2 = i := hq.2
    have hidx : M.sheetIndex q.2.1.1 = M.sheetIndex i.1.1 := by
      congr 1
      rw [hq2]
    refine Subtype.ext (Subtype.ext ?_)
    rw [show (Hinv q).1.1 = Work.SC.LocalModel.sheetPt M (M.sheetIndex q.2.1.1) q.1.1 from rfl,
      hidx]
  refine ⟨hdisc, Work.SC.ballAt x M.ρ, hxM, Work.SC.isOpen_ballAt x M.ρ, hopenF, ?_, ?_⟩
  · exact { toEquiv := ⟨H, Hinv, hleft, hright⟩
            continuous_toFun := hcontH
            continuous_invFun := hcontHinv }
  · intro p
    rfl

end Work.SimplyConnected.Modulus
