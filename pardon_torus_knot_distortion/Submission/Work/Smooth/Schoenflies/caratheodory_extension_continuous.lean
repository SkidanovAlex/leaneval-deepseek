import Mathlib
import Submission.Work.Smooth.SphereJordan.Caratheodory.CapArgument
import Submission.Work.Smooth.SphereJordan.Caratheodory.CapEstimate
import Submission.Work.Smooth.SphereJordan.Caratheodory.CapEndpoints
import Submission.Work.Smooth.SphereJordan.Caratheodory.TopologyAux
import Submission.Work.Smooth.SphereJordan.Caratheodory.InverseAnalytic
import Submission.Work.Smooth.SphereJordan.jsepExists
import Submission.Work.Smooth.Schoenflies.jsep_V_eq_of_isDomain

/-!
# Caratheodory's extension theorem (continuity part)

A biholomorphism `g` of the unit disc onto a bounded simply connected domain `Ω` whose frontier is
the trace of a simple closed curve extends continuously to the closed disc, with boundary values on
`frontier Ω`.

The proof is the Garnett--Marshall length--area / cap argument, built on the workspace's
`Work.Smooth.SphereJordan.Caratheodory` chapter.
-/

open Set Metric Filter
open scoped Topology
open Work.Smooth.SphereJordan (JSep)
open Work.Smooth.SphereJordan.Caratheodory

namespace Work.Smooth.Schoenflies

noncomputable section

/-! ## Toolbox -/

/-- **Finite energy of a biholomorphism onto a bounded domain.** -/
theorem energy_lt_top {Ω : Set ℂ} (hΩb : Bornology.IsBounded Ω) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (Metric.ball (0 : ℂ) 1))
    (hinj : Set.InjOn g (Metric.ball (0 : ℂ) 1)) (himg : g '' Metric.ball (0 : ℂ) 1 = Ω) :
    ∫⁻ z in Metric.ball (0 : ℂ) 1, ENNReal.ofReal (‖deriv g z‖ ^ 2) < ⊤ := by
  rw [lintegral_normSq_deriv_eq_volume isOpen_ball hinj
    (fun z hz => hg.differentiableAt (isOpen_ball.mem_nhds hz)), himg]
  exact hΩb.measure_lt_top

/-- **Radii with small cap length.**  There is a sequence of radii `r n ∈ (0, 1/2)`, decreasing to
`0`, along which the length of the image of the cap arc at the boundary point `1` is at most
`1/(n+1)`. -/
theorem exists_radii_capLen_small {Ω : Set ℂ} (hΩb : Bornology.IsBounded Ω) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) 1))
    (hinj : Set.InjOn f (Metric.ball (0 : ℂ) 1)) (himg : f '' Metric.ball (0 : ℂ) 1 = Ω) :
    ∃ r : ℕ → ℝ, (∀ n, 0 < r n) ∧ Antitone r ∧ (∀ n, r n < 1 / 2) ∧
      (∀ n, (capLen f (r n)).toReal ≤ 1 / ((n : ℝ) + 1)) ∧
      Tendsto r atTop (𝓝 0) := by
  have hE : ∫⁻ z in Metric.ball (0 : ℂ) 1, ENNReal.ofReal (‖deriv f z‖ ^ 2) < ⊤ :=
    energy_lt_top hΩb hf hinj himg
  have hstep : ∀ (k : ℕ) (s : ℝ), 0 < s →
      ∃ t : ℝ, 0 < t ∧ t < min s (min (1 / 2) (1 / ((k : ℝ) + 2))) ∧
        (capLen f t).toReal ≤ 1 / ((k : ℝ) + 2) := by
    intro k s hs
    have hε : (0 : ℝ) < 1 / ((k : ℝ) + 2) := by positivity
    have hδ : 0 < min s (min (1 / 2) (1 / ((k : ℝ) + 2))) :=
      lt_min hs (lt_min (by norm_num) hε)
    obtain ⟨t, ht, htc⟩ := exists_capLen_le f hE (1 / ((k : ℝ) + 2)) hε _ hδ
    exact ⟨t, ht.1, ht.2,
      calc (capLen f t).toReal ≤ (ENNReal.ofReal (1 / ((k : ℝ) + 2))).toReal :=
            ENNReal.toReal_mono ENNReal.ofReal_ne_top htc
        _ = 1 / ((k : ℝ) + 2) := ENNReal.toReal_ofReal (by positivity)⟩
  let next : ℕ → ℝ → ℝ := fun k s => if h : 0 < s then Classical.choose (hstep k s h) else 1
  let r : ℕ → ℝ := fun n => Nat.rec (next 0 1) (fun k s => next (k + 1) s) n
  have hr_zero : r 0 = next 0 1 := rfl
  have hr_succ : ∀ k, r (k + 1) = next (k + 1) (r k) := fun k => rfl
  have hpos : ∀ n, 0 < r n := by
    intro n
    induction n with
    | zero =>
      rw [hr_zero]
      simp only [next, dif_pos (by norm_num : (0 : ℝ) < 1)]
      exact (Classical.choose_spec (hstep 0 1 (by norm_num))).1
    | succ k ih =>
      rw [hr_succ]
      simp only [next, dif_pos ih]
      exact (Classical.choose_spec (hstep (k + 1) (r k) ih)).1
  have hle : ∀ k, r (k + 1) ≤ r k := by
    intro k
    rw [hr_succ]
    simp only [next, dif_pos (hpos k)]
    exact le_trans (le_of_lt (Classical.choose_spec (hstep (k + 1) (r k) (hpos k))).2.1)
      (min_le_left _ _)
  have hlt2 : ∀ n, r n < 1 / 2 := by
    intro n
    induction n with
    | zero =>
      rw [hr_zero]
      simp only [next, dif_pos (by norm_num : (0 : ℝ) < 1)]
      exact lt_of_lt_of_le (Classical.choose_spec (hstep 0 1 (by norm_num))).2.1
        (le_trans (min_le_right _ _) (min_le_left _ _))
    | succ k ih =>
      rw [hr_succ]
      simp only [next, dif_pos (hpos k)]
      exact lt_of_lt_of_le (Classical.choose_spec (hstep (k + 1) (r k) (hpos k))).2.1
        (le_trans (min_le_right _ _) (min_le_left _ _))
  have htoReal : ∀ n, (capLen f (r n)).toReal ≤ 1 / ((n : ℝ) + 1) := by
    intro n
    cases n with
    | zero =>
      rw [hr_zero]
      simp only [next, dif_pos (by norm_num : (0 : ℝ) < 1)]
      refine (Classical.choose_spec (hstep 0 1 (by norm_num))).2.2.trans ?_
      norm_num
    | succ k =>
      rw [hr_succ]
      simp only [next, dif_pos (hpos k)]
      refine (Classical.choose_spec (hstep (k + 1) (r k) (hpos k))).2.2.trans ?_
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      push_cast
      linarith
  have hbound : ∀ n, r n ≤ 1 / ((n : ℝ) + 2) := by
    intro n
    cases n with
    | zero =>
      rw [hr_zero]
      simp only [next, dif_pos (by norm_num : (0 : ℝ) < 1)]
      exact le_trans (le_of_lt (Classical.choose_spec (hstep 0 1 (by norm_num))).2.1)
        (le_trans (min_le_right _ _) (min_le_right _ _))
    | succ k =>
      rw [hr_succ]
      simp only [next, dif_pos (hpos k)]
      exact le_trans (le_of_lt (Classical.choose_spec (hstep (k + 1) (r k) (hpos k))).2.1)
        (le_trans (min_le_right _ _) (min_le_right _ _))
  have htend : Tendsto r atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) (fun n => ?_) (fun n => ?_)
    · exact le_of_lt (hpos n)
    · refine (hbound n).trans ?_
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      push_cast
      linarith
  exact ⟨r, hpos, antitone_nat_of_succ_le hle, hlt2, htoReal, htend⟩

/-- **The homeomorphism `𝔻 ≃ₜ Ω` induced by a biholomorphism.** -/
theorem homeo_of_biholomorph {Ω : Set ℂ} {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (Metric.ball (0 : ℂ) 1))
    (hinj : Set.InjOn g (Metric.ball (0 : ℂ) 1)) (himg : g '' Metric.ball (0 : ℂ) 1 = Ω) :
    ∃ φ : Metric.ball (0 : ℂ) 1 ≃ₜ ↥Ω, ∀ z : Metric.ball (0 : ℂ) 1, (φ z : ℂ) = g z := by
  have hbij : Set.BijOn g (Metric.ball (0 : ℂ) 1) Ω :=
    ⟨fun w hw => by rw [← himg]; exact ⟨w, hw, rfl⟩, hinj,
      by intro b hb; rw [← himg] at hb; exact hb⟩
  obtain ⟨f, hfbij, hfa, hfg, hgf⟩ :=
    exists_analytic_inverse Metric.isOpen_ball
      (convex_ball (0 : ℂ) 1).isPreconnected
      ⟨0, by simp, 1 / 2, by norm_num [Metric.mem_ball, dist_zero_right], by norm_num⟩
      hbij (hg.analyticOnNhd Metric.isOpen_ball)
  have hfwd : Continuous fun z : Metric.ball (0 : ℂ) 1 => (⟨g z, hbij.mapsTo z.2⟩ : ↥Ω) :=
    (hg.continuousOn.domRestrict).subtype_mk (fun z => hbij.mapsTo z.2)
  have hinv : Continuous fun w : ↥Ω => (⟨f w, hfbij.mapsTo w.2⟩ : Metric.ball (0 : ℂ) 1) :=
    (hfa.continuousOn.domRestrict).subtype_mk (fun w => hfbij.mapsTo w.2)
  exact ⟨Homeomorph.mk
    { toFun := fun z => ⟨g z, hbij.mapsTo z.2⟩
      invFun := fun w => ⟨f w, hfbij.mapsTo w.2⟩
      left_inv := fun z => Subtype.ext (hfg z z.2)
      right_inv := fun w => Subtype.ext (hgf w w.2) } hfwd hinv, fun z => rfl⟩

/-- A holomorphic injection on the disc is an open map. -/
theorem open_image_of_injOn {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g (Metric.ball (0 : ℂ) 1))
    (hinj : Set.InjOn g (Metric.ball (0 : ℂ) 1)) {U : Set ℂ} (hU : IsOpen U)
    (hUsub : U ⊆ Metric.ball (0 : ℂ) 1) :
    IsOpen (g '' U) := by
  rcases (hg.analyticOnNhd Metric.isOpen_ball).is_constant_or_isOpen
      (convex_ball (0 : ℂ) 1).isPreconnected with hconst | hopen
  · exfalso
    obtain ⟨w, hw⟩ := hconst
    have h0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by simp
    have h1 : (1 / 2 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
      norm_num [Metric.mem_ball, dist_zero_right]
    have h01 : g 0 = g (1 / 2) := (hw 0 h0).trans (hw (1 / 2) h1).symm
    exact absurd (hinj h0 h1 h01) (by norm_num)
  · exact hopen U hUsub hU

/-- **Two nearby points of the disc with far images, in the limit.**  If `g` is continuous on the
disc and fails the quantitative uniform-continuity bound `ε`, there is a boundary point `ζ` of the
disc and two sequences in the disc converging to `ζ` whose images stay `ε` apart. -/
theorem exists_far_pair {g : ℂ → ℂ}
    (hg : ContinuousOn g (Metric.ball (0 : ℂ) 1)) {ε : ℝ} (hε : 0 < ε)
    (h : ∀ δ > 0, ∃ z ∈ Metric.ball (0 : ℂ) 1, ∃ w ∈ Metric.ball (0 : ℂ) 1,
      ‖z - w‖ < δ ∧ ε ≤ ‖g z - g w‖) :
    ∃ ζ : ℂ, ‖ζ‖ = 1 ∧ ∃ z w : ℕ → ℂ,
      (∀ n, z n ∈ Metric.ball (0 : ℂ) 1) ∧ (∀ n, w n ∈ Metric.ball (0 : ℂ) 1) ∧
      Tendsto z atTop (𝓝 ζ) ∧ Tendsto w atTop (𝓝 ζ) ∧
      ∀ n, ε ≤ ‖g (z n) - g (w n)‖ := by
  have hscale : ∀ n : ℕ, ∃ p : ℂ × ℂ, p.1 ∈ Metric.ball (0 : ℂ) 1 ∧
      p.2 ∈ Metric.ball (0 : ℂ) 1 ∧ ‖p.1 - p.2‖ < 1 / ((n : ℝ) + 1) ∧
      ε ≤ ‖g p.1 - g p.2‖ := by
    intro n
    obtain ⟨z, hz, w, hw, hd, hge⟩ := h (1 / ((n : ℝ) + 1)) (by positivity)
    exact ⟨(z, w), hz, hw, hd, hge⟩
  choose P hP1 hP2 hPd hPge using hscale
  obtain ⟨ζ, hζball, φ, hφ, hζt⟩ :=
    IsCompact.tendsto_subseq (isCompact_closedBall (0 : ℂ) 1)
      (fun n => Metric.ball_subset_closedBall (hP1 n))
  have hζnorm : ‖ζ‖ ≤ 1 := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hζball
  have hdist : Tendsto (fun n => ‖(P (φ n)).1 - (P (φ n)).2‖) atTop (𝓝 0) := by
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => le_of_lt (hPd (φ n))) ?_
    exact (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hφ.tendsto_atTop
  have hWt : Tendsto (fun n => (P (φ n)).2) atTop (𝓝 ζ) := by
    have h2 : Tendsto (fun n => (P (φ n)).1 - (P (φ n)).2) atTop (𝓝 0) :=
      (tendsto_iff_norm_sub_tendsto_zero).mpr (by simpa using hdist)
    simpa using hζt.sub h2
  have hζsphere : ‖ζ‖ = 1 := by
    rcases lt_or_eq_of_le hζnorm with hlt | heq
    · exfalso
      have hζmem : ζ ∈ Metric.ball (0 : ℂ) 1 := by
        rwa [Metric.mem_ball, dist_zero_right]
      have hct : ContinuousAt g ζ := hg.continuousAt (isOpen_ball.mem_nhds hζmem)
      have h1 : Tendsto (fun n => g ((P (φ n)).1)) atTop (𝓝 (g ζ)) :=
        hct.tendsto.comp hζt
      have h2 : Tendsto (fun n => g ((P (φ n)).2)) atTop (𝓝 (g ζ)) :=
        hct.tendsto.comp hWt
      have h3 : Tendsto (fun n => ‖g ((P (φ n)).1) - g ((P (φ n)).2)‖) atTop (𝓝 0) := by
        simpa using (h1.sub h2).norm
      have hev : ∀ᶠ n : ℕ in atTop, ‖g ((P (φ n)).1) - g ((P (φ n)).2)‖ < ε :=
        h3.eventually (isOpen_Iio.mem_nhds hε)
      obtain ⟨n, hn⟩ := hev.exists
      exact absurd (hPge (φ n)) (not_le.mpr hn)
    · exact heq
  exact ⟨ζ, hζsphere, fun n => (P (φ n)).1, fun n => (P (φ n)).2, fun n => hP1 (φ n),
    fun n => hP2 (φ n), hζt, hWt, fun n => hPge (φ n)⟩

theorem capExtend_continuousOn {f : ℂ → ℂ} {s : ℝ} {a b : ℂ}
    (hf : ContinuousOn f (Metric.ball (0 : ℂ) 1))
    (ha : Tendsto (fun τ => f (capPt s τ))
      (𝓝[>] (-(capAlpha s))) (𝓝 a))
    (hb : Tendsto (fun τ => f (capPt s τ))
      (𝓝[<] (capAlpha s)) (𝓝 b))
    (hs : 0 < s) (hs2 : s < 2) :
    Continuous (capExtend f s a b) := by
  rw [continuous_iff_continuousAt]
  intro τ
  rcases lt_trichotomy τ (-(capAlpha s)) with h | h | h
  · -- `τ < -α`: locally equal to the constant `a`
    refine (continuousAt_const (y := a)).congr ?_
    filter_upwards [IsOpen.mem_nhds isOpen_Iio h] with τ' hτ'
    have h1 : τ' < -(capAlpha s) := hτ'
    simp only [capExtend, if_pos h1.le]
  · -- `τ = -α`: glue the constant `a` with the one-sided limit `ha`
    subst h
    show Tendsto (capExtend f s a b) (𝓝 (-(capAlpha s)))
      (𝓝 (capExtend f s a b (-(capAlpha s))))
    rw [show capExtend f s a b (-(capAlpha s)) = a from by
      simp only [capExtend, if_pos le_rfl]]
    rw [← nhdsWithin_univ, ← Set.Iic_union_Ioi (a := -(capAlpha s)), nhdsWithin_union]
    refine tendsto_sup.mpr ⟨?_, ?_⟩
    · refine (tendsto_const_nhds (x := a)).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with τ' hτ'
      have h1 : τ' ≤ -(capAlpha s) := hτ'
      simp only [capExtend, if_pos h1]
    · refine ha.congr' ?_
      have hlt : ∀ᶠ τ' in 𝓝[Set.Ioi (-(capAlpha s))] (-(capAlpha s)),
          τ' < capAlpha s :=
        (nhdsWithin_le_nhds :
          𝓝[Set.Ioi (-(capAlpha s))] (-(capAlpha s)) ≤
            𝓝 (-(capAlpha s)))
          (IsOpen.mem_nhds isOpen_Iio (by
            have hα : 0 < capAlpha s := capAlpha_pos hs2
            show -(capAlpha s) < capAlpha s
            linarith))
      filter_upwards [self_mem_nhdsWithin, hlt] with τ' h1 h2
      have h1' : -(capAlpha s) < τ' := h1
      have h2' : τ' < capAlpha s := h2
      simp only [capExtend, if_neg (not_le.mpr h1'), if_neg (not_le.mpr h2')]
  · -- `-α < τ`
    rcases lt_or_ge τ (capAlpha s) with h' | h'
    · -- `-α < τ < α`: continuity of `f` at the interior point `capPt s τ`
      have hmem : capPt s τ ∈ Metric.ball (0 : ℂ) 1 :=
        capPt_mem_ball_of_mem_Ioo hs hs2 ⟨h, h'⟩
      have hcont : ContinuousAt (fun τ' => f (capPt s τ')) τ :=
        (hf.continuousAt (Metric.isOpen_ball.mem_nhds hmem)).comp
          ((continuous_capPt s).continuousAt)
      refine hcont.congr ?_
      filter_upwards [IsOpen.mem_nhds isOpen_Ioi h, IsOpen.mem_nhds isOpen_Iio h'] with τ' hτ' hτ''
      have h1 : -(capAlpha s) < τ' := hτ'
      have h2 : τ' < capAlpha s := hτ''
      simp only [Function.comp_apply, capExtend, if_neg (not_le.mpr h1),
        if_neg (not_le.mpr h2)]
    · rcases lt_or_eq_of_le h' with h'' | h''
      · -- `τ > α`: locally equal to the constant `b`
        refine (continuousAt_const (y := b)).congr ?_
        filter_upwards [IsOpen.mem_nhds isOpen_Ioi h''] with τ' hτ'
        have h2 : capAlpha s < τ' := hτ'
        have h1 : -(capAlpha s) < τ' :=
          lt_of_lt_of_le
            (by have := capAlpha_pos hs2; linarith) h2.le
        simp only [capExtend, if_neg (not_le.mpr h1), if_pos h2.le]
      · -- `τ = α`: glue the one-sided limit `hb` with the constant `b`
        subst h''
        show Tendsto (capExtend f s a b) (𝓝 (capAlpha s))
          (𝓝 (capExtend f s a b (capAlpha s)))
        rw [show capExtend f s a b (capAlpha s) = b from by
          simp only [capExtend, if_neg (not_le.mpr h), if_pos le_rfl]]
        rw [← nhdsWithin_univ, ← Set.Iio_union_Ici (a := capAlpha s), nhdsWithin_union]
        refine tendsto_sup.mpr ⟨?_, ?_⟩
        · refine hb.congr' ?_
          have hlt : ∀ᶠ τ' in 𝓝[Set.Iio (capAlpha s)] (capAlpha s),
              -(capAlpha s) < τ' :=
            (nhdsWithin_le_nhds :
              𝓝[Set.Iio (capAlpha s)] (capAlpha s) ≤
                𝓝 (capAlpha s))
              (IsOpen.mem_nhds isOpen_Ioi (by
                have hα : 0 < capAlpha s := capAlpha_pos hs2
                show -(capAlpha s) < capAlpha s
                linarith))
          filter_upwards [self_mem_nhdsWithin, hlt] with τ' h1 h2
          have h1' : τ' < capAlpha s := h1
          have h2' : -(capAlpha s) < τ' := h2
          simp only [capExtend, if_neg (not_le.mpr h2'), if_neg (not_le.mpr h1')]
        · refine (tendsto_const_nhds (x := b)).congr' ?_
          filter_upwards [self_mem_nhdsWithin] with τ' hτ'
          have h2 : capAlpha s ≤ τ' := hτ'
          have h1 : -(capAlpha s) < τ' :=
            lt_of_lt_of_le (by have := capAlpha_pos hs2; linarith) h2
          simp only [capExtend, if_neg (not_le.mpr h1), if_pos h2]


theorem cap_planeCurve_self {Ω : Set ℂ} {γ : ℝ → ℂ} {f : ℂ → ℂ} {s : ℝ} {a : ℂ}
    (hΩo : IsOpen Ω) (hγc : Continuous γ) (hγp : Function.Periodic γ (2 * Real.pi))
    (hγi : Set.InjOn γ (Set.Ico 0 (2 * Real.pi)))
    (hs : 0 < s) (hs2 : s < 2) (hcont : Continuous (capExtend f s a a))
    (hinj : Set.InjOn f (Metric.ball (0 : ℂ) 1)) (himg : f '' Metric.ball (0 : ℂ) 1 = Ω)
    (hfr : frontier Ω = Set.range γ) (ha : a ∈ frontier Ω) :
    ∃ K : Work.Smooth.Jordan.PlaneCurve, K.IsSimple ∧
      Set.range K.γ = f '' (capPt s '' Set.Ioo (-(capAlpha s)) (capAlpha s)) ∪ {a} := by
  have hα : 0 < capAlpha s := capAlpha_pos hs2
  have hane : a ∉ Ω := (hΩo.frontier_eq ▸ ha).2
  have hE : ∀ t : Set.Icc (0 : ℝ) 1,
      capExtend f s a a (-(capAlpha s) + (t : ℝ) * (2 * capAlpha s))
        = (if (t : ℝ) = 0 ∨ (t : ℝ) = 1 then a
            else f (capPt s (-(capAlpha s) + (t : ℝ) * (2 * capAlpha s)))) := by
    intro t
    rcases eq_or_ne (t : ℝ) 0 with h0 | h0
    · rw [if_pos (Or.inl h0), show -(capAlpha s) + (t : ℝ) * (2 * capAlpha s) = -(capAlpha s) by
        rw [h0]; ring]
      simp [capExtend]
    · rcases eq_or_ne (t : ℝ) 1 with h1 | h1
      · rw [if_pos (Or.inr h1), show -(capAlpha s) + (t : ℝ) * (2 * capAlpha s) = capAlpha s by
          rw [h1]; ring]
        simp [capExtend]
      · rw [if_neg (by tauto)]
        have htI := Set.mem_Icc.mp t.2
        have h0' : 0 < (t : ℝ) := lt_of_le_of_ne htI.1 (Ne.symm h0)
        have h1' : (t : ℝ) < 1 := lt_of_le_of_ne htI.2 h1
        have hlt : -(capAlpha s) < -(capAlpha s) + (t : ℝ) * (2 * capAlpha s) := by nlinarith [h0', hα]
        have hgt : -(capAlpha s) + (t : ℝ) * (2 * capAlpha s) < capAlpha s := by nlinarith [h1', hα]
        simp only [capExtend, if_neg (not_le.mpr hlt), if_neg (not_le.mpr hgt)]
  let P : C(Set.Icc (0 : ℝ) 1, ℂ) :=
    ⟨fun t => capExtend f s a a (-(capAlpha s) + (t : ℝ) * (2 * capAlpha s)), by
      refine hcont.comp ?_
      exact continuous_const.add (continuous_subtype_val.mul continuous_const)⟩
  have hPval : ∀ t : Set.Icc (0 : ℝ) 1,
      (P t : ℂ) = capExtend f s a a (-(capAlpha s) + (t : ℝ) * (2 * capAlpha s)) := fun t => rfl
  have hP0 : P ⟨0, by norm_num⟩ = a := by
    rw [hPval]
    rw [hE]
    rw [if_pos (Or.inl rfl)]
  have hP1 : P ⟨1, by norm_num⟩ = a := by
    rw [hPval]
    rw [hE]
    rw [if_pos (Or.inr rfl)]
  have hnot : ∀ t : Set.Icc (0 : ℝ) 1, (t : ℝ) ≠ 0 → (t : ℝ) ≠ 1 →
      ¬ ((t : ℝ) = 0 ∨ (t : ℝ) = 1) := by tauto
  have hinjP : Set.InjOn (⇑P) {t : Set.Icc (0 : ℝ) 1 | (t : ℝ) < 1} := by
    intro t ht t' ht' heq
    have htI := Set.mem_Icc.mp t.2
    have ht'I := Set.mem_Icc.mp t'.2
    simp only [hPval] at heq
    rw [hE t, hE t'] at heq
    by_cases h0 : (t : ℝ) = 0
    · rw [if_pos (Or.inl h0)] at heq
      by_cases h0' : (t' : ℝ) = 0
      · exact Subtype.ext (by rw [h0, h0'])
      · exfalso
        have h0'' : 0 < (t' : ℝ) := lt_of_le_of_ne ht'I.1 (Ne.symm h0')
        have h1' : (t' : ℝ) < 1 := ht'
        rw [if_neg (hnot t' h0' (ne_of_lt h1'))] at heq
        have hmem : capPt s (-(capAlpha s) + (t' : ℝ) * (2 * capAlpha s)) ∈ Metric.ball (0 : ℂ) 1 :=
          capPt_mem_ball_of_mem_Ioo hs hs2 ⟨by nlinarith [h0'', hα], by nlinarith [h1', hα]⟩
        have : a ∈ Ω := by rw [heq]; rw [← himg]; exact ⟨_, hmem, rfl⟩
        exact hane this
    · by_cases h0' : (t' : ℝ) = 0
      · exfalso
        have h0'' : 0 < (t : ℝ) := lt_of_le_of_ne htI.1 (Ne.symm h0)
        have h1 : (t : ℝ) < 1 := ht
        rw [if_neg (hnot t h0 (ne_of_lt h1)), if_pos (Or.inl h0')] at heq
        have hmem : capPt s (-(capAlpha s) + (t : ℝ) * (2 * capAlpha s)) ∈ Metric.ball (0 : ℂ) 1 :=
          capPt_mem_ball_of_mem_Ioo hs hs2 ⟨by nlinarith [h0'', hα], by nlinarith [h1, hα]⟩
        have : a ∈ Ω := by rw [← heq]; rw [← himg]; exact ⟨_, hmem, rfl⟩
        exact hane this
      · have h0'' : 0 < (t : ℝ) := lt_of_le_of_ne htI.1 (Ne.symm h0)
        have h0''' : 0 < (t' : ℝ) := lt_of_le_of_ne ht'I.1 (Ne.symm h0')
        have h1 : (t : ℝ) < 1 := ht
        have h1' : (t' : ℝ) < 1 := ht'
        rw [if_neg (hnot t h0 (ne_of_lt h1)), if_neg (hnot t' h0' (ne_of_lt h1'))] at heq
        have hmem : capPt s (-(capAlpha s) + (t : ℝ) * (2 * capAlpha s)) ∈ Metric.ball (0 : ℂ) 1 :=
          capPt_mem_ball_of_mem_Ioo hs hs2 ⟨by nlinarith [h0'', hα], by nlinarith [h1, hα]⟩
        have hmem' : capPt s (-(capAlpha s) + (t' : ℝ) * (2 * capAlpha s)) ∈ Metric.ball (0 : ℂ) 1 :=
          capPt_mem_ball_of_mem_Ioo hs hs2 ⟨by nlinarith [h0''', hα], by nlinarith [h1', hα]⟩
        have hcp : capPt s (-(capAlpha s) + (t : ℝ) * (2 * capAlpha s)) =
            capPt s (-(capAlpha s) + (t' : ℝ) * (2 * capAlpha s)) := hinj hmem hmem' heq
        have harc : capArcPath s ⟨(t : ℝ), htI⟩ = capArcPath s ⟨(t' : ℝ), ht'I⟩ := by
          rw [capArcPath_apply, capArcPath_apply]
          exact hcp
        have hsub := capArcPath_injective hs hs2 harc
        exact Subtype.ext (congrArg Subtype.val hsub)
  have hrange : Set.range (⇑P) =
      f '' (capPt s '' Set.Ioo (-(capAlpha s)) (capAlpha s)) ∪ {a} := by
    ext z
    constructor
    · rintro ⟨t, rfl⟩
      rw [hPval, hE t]
      by_cases h : (t : ℝ) = 0 ∨ (t : ℝ) = 1
      · rw [if_pos h]; exact Or.inr rfl
      · rw [if_neg h]
        have htI := Set.mem_Icc.mp t.2
        have h0 : (t : ℝ) ≠ 0 := fun hc => h (Or.inl hc)
        have h1 : (t : ℝ) ≠ 1 := fun hc => h (Or.inr hc)
        have h0' : 0 < (t : ℝ) := lt_of_le_of_ne htI.1 (Ne.symm h0)
        have h1' : (t : ℝ) < 1 := lt_of_le_of_ne htI.2 h1
        refine Or.inl ⟨capPt s (-(capAlpha s) + (t : ℝ) * (2 * capAlpha s)),
          ⟨-(capAlpha s) + (t : ℝ) * (2 * capAlpha s),
            ⟨by nlinarith [h0', hα], by nlinarith [h1', hα]⟩, rfl⟩, rfl⟩
    · rintro (⟨w, ⟨u, hu, rfl⟩, rfl⟩ | rfl)
      · refine ⟨⟨(u + capAlpha s) / (2 * capAlpha s), Set.mem_Icc.mpr ⟨?_, ?_⟩⟩, ?_⟩
        · apply div_nonneg <;> linarith [hu.1]
        · rw [div_le_one (by linarith)]; linarith [hu.2]
        · show capExtend f s a a
            (-(capAlpha s) + (((u + capAlpha s) / (2 * capAlpha s) : ℝ)) * (2 * capAlpha s))
            = f (capPt s u)
          rw [show -(capAlpha s) + (((u + capAlpha s) / (2 * capAlpha s) : ℝ)) * (2 * capAlpha s) = u by
            rw [div_mul_cancel₀ _ (by positivity : (2 * capAlpha s) ≠ 0)]; ring]
          simp only [capExtend, if_neg (not_le.mpr hu.1), if_neg (not_le.mpr hu.2)]
      · exact ⟨⟨0, by norm_num⟩, hP0⟩
  refine ⟨Work.Smooth.SphereJordan.loopCurve P (hP0.trans hP1.symm),
    Work.Smooth.SphereJordan.loopCurve_isSimple P (hP0.trans hP1.symm) hinjP, ?_⟩
  rw [Work.Smooth.SphereJordan.range_loopCurve, hrange]


set_option maxHeartbeats 2000000 in
/-- **The cap arc closed up into a Jordan curve.**  Given the two one-sided limits `a`, `b` of the
image of the cap arc at radius `s`, with `a = γ x`, `b = γ y` and `x ≤ y`, the arc together with the
image `γ '' Icc x y` closes up into a simple closed curve (in the degenerate case `a = b` the arc is
closed up at `a` alone). -/
theorem cap_planeCurve {Ω : Set ℂ} {γ : ℝ → ℂ} {f : ℂ → ℂ} {s : ℝ} {a b : ℂ} {x y : ℝ}
    (hΩo : IsOpen Ω) (hγc : Continuous γ) (hγp : Function.Periodic γ (2 * Real.pi))
    (hγi : Set.InjOn γ (Set.Ico 0 (2 * Real.pi)))
    (hf : ContinuousOn f (Metric.ball (0 : ℂ) 1)) (hinj : Set.InjOn f (Metric.ball (0 : ℂ) 1))
    (himg : f '' Metric.ball (0 : ℂ) 1 = Ω) (hfr : frontier Ω = Set.range γ)
    (hs : 0 < s) (hs2 : s < 2)
    (ha : Tendsto (fun τ => f (capPt s τ)) (𝓝[>] (-(capAlpha s))) (𝓝 a))
    (hb : Tendsto (fun τ => f (capPt s τ)) (𝓝[<] (capAlpha s)) (𝓝 b))
    (hafr : a ∈ frontier Ω) (hbfr : b ∈ frontier Ω)
    (hxy : x ≤ y) (hxy_eq : a = b → x = y)
    (h : (γ x = a ∧ γ y = b) ∨ (γ x = b ∧ γ y = a))
    (hlen : a ≠ b → y - x < 2 * Real.pi) :
    ∃ (K : Work.Smooth.Jordan.PlaneCurve) (T : JSep K), K.IsSimple ∧
      Set.range K.γ = (f '' (capPt s '' Set.Ioo (-(capAlpha s)) (capAlpha s)) ∪ {a, b})
        ∪ γ '' Set.Icc x y := by
  have hcont : Continuous (capExtend f s a b) := capExtend_continuousOn hf ha hb hs hs2
  by_cases hab : a = b
  · subst hab
    have hxy' : x = y := hxy_eq rfl
    subst hxy'
    obtain ⟨K, hK, hKr⟩ :=
      cap_planeCurve_self hΩo hγc hγp hγi hs hs2 hcont hinj himg hfr hbfr
    obtain ⟨T⟩ := Work.Smooth.SphereJordan.exists_jsep K hK
    refine ⟨K, T, hK, ?_⟩
    have hγx : γ x = a := by
      rcases h with hh | hh
      · exact hh.1
      · exact hh.2
    have h2 : γ '' Set.Icc x x = ({a} : Set ℂ) := by
      rw [Set.Icc_self, Set.image_singleton, hγx]
    rw [hKr, h2]
    ext z
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  · have hxy' : x < y := by
      rcases lt_or_eq_of_le hxy with hlt | heq
      · exact hlt
      · exfalso
        rcases h with hh | hh
        · have h2 : γ x = b := by rw [heq]; exact hh.2
          exact hab (hh.1.symm.trans h2)
        · have h2 : γ x = a := by rw [heq]; exact hh.2
          exact hab (h2.symm.trans hh.1)
    obtain ⟨K, T, hK, hKr⟩ :=
      exists_capJSep hΩo hγc hγp hγi hs hs2 hcont hinj himg hfr hafr hbfr hab hxy'
        (hlen hab) h
    exact ⟨K, T, hK, hKr⟩

set_option maxHeartbeats 4000000 in
/-- **The bounded side of the cap Jordan curve lies in `Ω` and is small.** -/
theorem cap_V_subset_and_diam {Ω : Set ℂ} {γ : ℝ → ℂ} {f : ℂ → ℂ} {s : ℝ} {a b : ℂ} {x y : ℝ}
    {K : Work.Smooth.Jordan.PlaneCurve} (hγc : Continuous γ)
    (hγp : Function.Periodic γ (2 * Real.pi))
    (S : JSep ⟨γ, hγc, hγp⟩) (T : JSep K) (hSV : S.V = Ω)
    (hΩo : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hf : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) 1))
    (hinj : Set.InjOn f (Metric.ball (0 : ℂ) 1)) (himg : f '' Metric.ball (0 : ℂ) 1 = Ω)
    (hfr : frontier Ω = Set.range γ) (hs : 0 < s) (hs2 : s < 2)
    (hafr : a ∈ frontier Ω) (hbfr : b ∈ frontier Ω)
    (hsubfr : γ '' Set.Icc x y ⊆ frontier Ω)
    (ha : Tendsto (fun τ => f (capPt s τ)) (𝓝[>] (-(capAlpha s))) (𝓝 a))
    (hb : Tendsto (fun τ => f (capPt s τ)) (𝓝[<] (capAlpha s)) (𝓝 b))
    (hfin : capLen f s < ⊤) (haC : a ∈ γ '' Set.Icc x y)
    (hKrange : Set.range K.γ = (f '' (capPt s '' Set.Ioo (-(capAlpha s)) (capAlpha s)) ∪ {a, b})
      ∪ γ '' Set.Icc x y) :
    T.V ⊆ Ω ∧ Metric.diam T.V ≤ 2 * ((capLen f s).toReal + Metric.diam (γ '' Set.Icc x y)) := by
  have htrace : K.trace ⊆ Ω ∪ Set.range γ := by
    rw [show K.trace = Set.range K.γ from rfl, hKrange]
    rintro z ((hz | hz) | hz)
    · obtain ⟨w, ⟨τ, hτ, rfl⟩, rfl⟩ := hz
      exact Or.inl (by rw [← himg]; exact ⟨capPt s τ, capPt_mem_ball_of_mem_Ioo hs hs2 hτ, rfl⟩)
    · rcases hz with h | h
      · refine Or.inr ?_
        rw [← hfr, h]
        exact hafr
      · refine Or.inr ?_
        rw [← hfr, h]
        exact hbfr
    · obtain ⟨t, _, rfl⟩ := hz
      exact Or.inr ⟨t, rfl⟩
  have hdisj : Disjoint K.trace S.U := by
    rw [Set.disjoint_left]
    intro z hzK hzU
    rcases htrace hzK with h | h
    · exact (Set.disjoint_left.mp S.disjoint_UV hzU) (by rw [hSV]; exact h)
    · have hfrU : z ∈ frontier S.U := by rw [S.frontier_U]; exact h
      exact ((S.isOpen_U.frontier_eq ▸ hfrU).2) hzU
  have hTVΩ : T.V ⊆ Ω := by
    have h' := JSep.V_subset_of_disjoint_trace S T hdisj
    rwa [hSV] at h'
  refine ⟨hTVΩ, ?_⟩
  have hA : Metric.diam (f '' (capPt s '' Set.Ioo (-(capAlpha s)) (capAlpha s)))
      ≤ (capLen f s).toReal :=
    diam_image_capArc_le (hf.analyticOnNhd Metric.isOpen_ball) hs hs2 hfin
  have hnear : ∀ {c : ℂ}, Tendsto (fun τ => f (capPt s τ)) (𝓝[>] (-(capAlpha s))) (𝓝 c) →
      c ∈ closure (f '' (capPt s '' Set.Ioo (-(capAlpha s)) (capAlpha s))) := by
    intro c hc
    refine mem_closure_of_tendsto hc ?_
    have h1 : ∀ᶠ τ in 𝓝[>] (-(capAlpha s)), -(capAlpha s) < τ := self_mem_nhdsWithin
    have h2 : ∀ᶠ τ in 𝓝[>] (-(capAlpha s)), τ < capAlpha s :=
      (nhdsWithin_le_nhds :
        𝓝[Set.Ioi (-(capAlpha s))] (-(capAlpha s)) ≤ 𝓝 (-(capAlpha s)))
        (IsOpen.mem_nhds isOpen_Iio (by
          have hα : 0 < capAlpha s := capAlpha_pos hs2
          show -(capAlpha s) < capAlpha s
          linarith))
    filter_upwards [h1, h2] with τ hτ1 hτ2
    exact ⟨capPt s τ, ⟨τ, ⟨hτ1, hτ2⟩, rfl⟩, rfl⟩
  have hnear' : ∀ {c : ℂ}, Tendsto (fun τ => f (capPt s τ)) (𝓝[<] (capAlpha s)) (𝓝 c) →
      c ∈ closure (f '' (capPt s '' Set.Ioo (-(capAlpha s)) (capAlpha s))) := by
    intro c hc
    refine mem_closure_of_tendsto hc ?_
    have h1 : ∀ᶠ τ in 𝓝[<] (capAlpha s), -(capAlpha s) < τ :=
      (nhdsWithin_le_nhds :
        𝓝[Set.Iio (capAlpha s)] (capAlpha s) ≤ 𝓝 (capAlpha s))
        (IsOpen.mem_nhds isOpen_Ioi (by
          have hα : 0 < capAlpha s := capAlpha_pos hs2
          show -(capAlpha s) < capAlpha s
          linarith))
    have h2 : ∀ᶠ τ in 𝓝[<] (capAlpha s), τ < capAlpha s := self_mem_nhdsWithin
    filter_upwards [h1, h2] with τ hτ1 hτ2
    exact ⟨capPt s τ, ⟨τ, ⟨hτ1, hτ2⟩, rfl⟩, rfl⟩
  have hbddA : Bornology.IsBounded (f '' (capPt s '' Set.Ioo (-(capAlpha s)) (capAlpha s))) := by
    refine Bornology.IsBounded.subset hΩb ?_
    rw [← himg]
    exact Set.image_mono (Set.image_subset_iff.mpr
      (fun τ hτ => capPt_mem_ball_of_mem_Ioo hs hs2 hτ))
  have hbddC : Bornology.IsBounded (γ '' Set.Icc x y) := (isCompact_Icc.image hγc).isBounded
  have hε : Metric.diam T.V ≤ (4 * ((capLen f s).toReal + Metric.diam (γ '' Set.Icc x y))) / 2 :=
    diam_capJSep_V_le (γ := ⟨γ, hγc, hγp⟩) (x := x) (y := y)
      (ε := 4 * ((capLen f s).toReal + Metric.diam (γ '' Set.Icc x y)))
      T hKrange (hnear ha) (hnear' hb) haC hbddA hbddC hA
      (by
        have h4 : (4 * ((capLen f s).toReal + Metric.diam (γ '' Set.Icc x y))) / 4
            = (capLen f s).toReal + Metric.diam (γ '' Set.Icc x y) := by ring
        rw [h4]
        exact le_add_of_nonneg_left ENNReal.toReal_nonneg)
      (by
        have h4 : (4 * ((capLen f s).toReal + Metric.diam (γ '' Set.Icc x y))) / 4
            = (capLen f s).toReal + Metric.diam (γ '' Set.Icc x y) := by ring
        rw [h4]
        exact le_add_of_nonneg_right Metric.diam_nonneg)
  calc Metric.diam T.V ≤ (4 * ((capLen f s).toReal + Metric.diam (γ '' Set.Icc x y))) / 2 := hε
    _ = 2 * ((capLen f s).toReal + Metric.diam (γ '' Set.Icc x y)) := by ring

set_option maxHeartbeats 2000000 in
/-- **Which side of the cap Jordan curve is the lens?**  The bounded side `T.V` of the cap curve is
one of the two pieces into which the cap arc cuts `Ω`: the image of the lens or the image of the
outer lens. -/
theorem cap_lens_dichotomy {Ω : Set ℂ} {f : ℂ → ℂ} {γ : ℝ → ℂ} {s : ℝ} {a b : ℂ} {x y : ℝ}
    {K : Work.Smooth.Jordan.PlaneCurve} (T : JSep K)
    (hΩo : IsOpen Ω) (hf : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) 1))
    (hinj : Set.InjOn f (Metric.ball (0 : ℂ) 1))
    (himg : f '' Metric.ball (0 : ℂ) 1 = Ω) (hTV : T.V ⊆ Ω)
    (hs : 0 < s) (hs2 : s < 2) (hafr : a ∈ frontier Ω) (hbfr : b ∈ frontier Ω)
    (hsubfr : γ '' Set.Icc x y ⊆ frontier Ω)
    (hKrange : Set.range K.γ = (f '' (capPt s '' Set.Ioo (-(capAlpha s)) (capAlpha s)) ∪ {a, b})
      ∪ γ '' Set.Icc x y) :
    T.V = f '' lens s ∨ T.V = f '' outerLens s := by
  have hcapArc : capPt s '' Set.Ioo (-(capAlpha s)) (capAlpha s) ⊆ Metric.ball (0 : ℂ) 1 :=
    fun z hz => by
      obtain ⟨τ, hτ, rfl⟩ := hz
      exact capPt_mem_ball_of_mem_Ioo hs hs2 hτ
  have hdisjLA : Disjoint (lens s) (capPt s '' Set.Ioo (-(capAlpha s)) (capAlpha s)) := by
    rw [Set.disjoint_left]
    intro z hz hz'
    exact (Set.disjoint_left.mp (lens_disjoint_arc hs)) hz (capPt_image_subset_range (s := s) hs2 hz')
  have hdisjOA : Disjoint (outerLens s) (capPt s '' Set.Ioo (-(capAlpha s)) (capAlpha s)) := by
    rw [Set.disjoint_left]
    intro z hz hz'
    obtain ⟨t, ht⟩ := capPt_image_subset_range (s := s) hs2 hz'
    rw [← ht, capArcPath_apply] at hz
    have h2 : s < ‖capPt s (-(capAlpha s) + (t : ℝ) * (2 * capAlpha s)) - 1‖ := hz.2
    rw [norm_capPt_sub_one, abs_of_pos hs] at h2
    exact absurd h2 (lt_irrefl s)
  -- trichotomy of the disc at the cap arc
  have htrich : ∀ u : ℂ, u ∈ Metric.ball (0 : ℂ) 1 →
      u ∈ lens s ∨ u ∈ capPt s '' Set.Ioo (-(capAlpha s)) (capAlpha s) ∨ u ∈ outerLens s := by
    intro u hu
    have hu' : ‖u‖ < 1 := by rwa [Metric.mem_ball, dist_zero_right] at hu
    rcases lt_trichotomy ‖u - 1‖ s with h | h | h
    · exact Or.inl (mem_lens_iff.mpr ⟨hu', h⟩)
    · refine Or.inr (Or.inl ?_)
      rw [← sphere_inter_ball hs hs2]
      exact ⟨h, hu⟩
    · exact Or.inr (Or.inr ⟨hu, h⟩)
  set A : Set ℂ := f '' (capPt s '' Set.Ioo (-(capAlpha s)) (capAlpha s)) with hA
  have hAΩ : A ⊆ Ω := by
    rintro z ⟨w, hw, rfl⟩
    rw [← himg]; exact ⟨w, hcapArc hw, rfl⟩
  have htraceΩ : K.trace ∩ Ω = A := by
    ext z
    constructor
    · rintro ⟨hzK, hzΩ⟩
      rw [show K.trace = Set.range K.γ from rfl, hKrange] at hzK
      rcases hzK with (hz | hz) | hz
      · exact hz
      · rcases hz with h | h
        · exact absurd (h ▸ hzΩ) ((hΩo.frontier_eq ▸ hafr).2)
        · exact absurd (h ▸ hzΩ) ((hΩo.frontier_eq ▸ hbfr).2)
      · exact absurd hzΩ ((hΩo.frontier_eq ▸ hsubfr hz).2)
    · intro hz
      exact ⟨by rw [show K.trace = Set.range K.γ from rfl, hKrange]; exact Or.inl (Or.inl hz),
        hAΩ hz⟩
  have hAtrace : A ⊆ K.trace := by
    intro z hz
    have h : z ∈ K.trace ∩ Ω := by rw [htraceΩ]; exact hz
    exact h.1
  have htraceA : K.trace ∩ Ω ⊆ A := fun z hz => by rwa [htraceΩ] at hz
  have hdecomp : Ω \ K.trace = f '' lens s ∪ f '' outerLens s := by
    have h1 : Ω \ K.trace = Ω \ A := by
      ext z; constructor
      · rintro ⟨hz1, hz2⟩
        exact ⟨hz1, fun hzA => hz2 (hAtrace hzA)⟩
      · rintro ⟨hz1, hz2⟩
        exact ⟨hz1, fun hzK => hz2 (htraceA ⟨hzK, hz1⟩)⟩
    rw [h1]
    refine Set.Subset.antisymm ?_ ?_
    · rintro z ⟨hzΩ, hzA⟩
      obtain ⟨u, hu, rfl⟩ := (show z ∈ f '' Metric.ball (0 : ℂ) 1 by rwa [himg])
      rcases htrich u hu with h | h | h
      · exact Or.inl ⟨u, h, rfl⟩
      · exact absurd ⟨u, h, rfl⟩ hzA
      · exact Or.inr ⟨u, h, rfl⟩
    · rintro z (hz | hz)
      · obtain ⟨u, hu, rfl⟩ := hz
        refine ⟨by rw [← himg]; exact ⟨u, lens_subset_ball s hu, rfl⟩, fun hzA => ?_⟩
        obtain ⟨w, hw, hwu⟩ := hzA
        have huw : u = w := hinj (lens_subset_ball s hu) (hcapArc hw) hwu.symm
        exact (Set.disjoint_left.mp hdisjLA hu) (huw ▸ hw)
      · obtain ⟨u, hu, rfl⟩ := hz
        refine ⟨by rw [← himg]; exact ⟨u, hu.1, rfl⟩, fun hzA => ?_⟩
        obtain ⟨w, hw, hwu⟩ := hzA
        have huw : u = w := hinj hu.1 (hcapArc hw) hwu.symm
        exact (Set.disjoint_left.mp hdisjOA hu) (huw ▸ hw)
  have hopenL : IsOpen (f '' lens s) :=
    open_image_of_injOn hf hinj (lens_isOpen s) (lens_subset_ball s)
  have hopenO : IsOpen (f '' outerLens s) :=
    open_image_of_injOn hf hinj (outerLens_isOpen s) (fun z hz => hz.1)
  have hpreO : IsPreconnected (outerLens s) := by
    obtain ⟨P, Q, _, _, _, _, hPpre, hQpre, hunion, hdisjPQ, hcase⟩ := lens_eq_component hs hs2
    have hcompl := lens_union_outerLens hs hs2
    have key : ∀ x : ℂ, x ∈ lens s ∪ outerLens s ↔ x ∈ P ∪ Q := fun x => by rw [hcompl, hunion]
    have houter : outerLens s = P ∨ outerLens s = Q := by
      rcases hcase with hcase | hcase
      · -- `lens = P`, so `outerLens = Q`
        right
        refine Set.Subset.antisymm ?_ ?_
        · intro z hz
          rcases (key z).mp (Or.inr hz) with h | h
          · exfalso
            exact (Set.disjoint_left.mp (disjoint_lens_outerLens (s := s)) (hcase.symm ▸ h)) hz
          · exact h
        · intro z hz
          rcases (key z).mpr (Or.inr hz) with h | h
          · exfalso
            exact (Set.disjoint_left.mp hdisjPQ (hcase ▸ h)) hz
          · exact h
      · -- `lens = Q`, so `outerLens = P`
        left
        refine Set.Subset.antisymm ?_ ?_
        · intro z hz
          rcases (key z).mp (Or.inr hz) with h | h
          · exact h
          · exfalso
            exact (Set.disjoint_left.mp (disjoint_lens_outerLens (s := s)) (hcase.symm ▸ h)) hz
        · intro z hz
          rcases (key z).mpr (Or.inl hz) with h | h
          · exfalso
            exact (Set.disjoint_left.mp hdisjPQ hz) (hcase ▸ h)
          · exact h
    rcases houter with h | h
    · rw [h]; exact hPpre
    · rw [h]; exact hQpre
  have hdisjLO : Disjoint (f '' lens s) (f '' outerLens s) := by
    rw [Set.disjoint_left]
    rintro z ⟨u, hu, rfl⟩ ⟨v, hv, huv⟩
    have huv' : u = v := hinj (lens_subset_ball s hu) hv.1 huv.symm
    exact (Set.disjoint_left.mp (disjoint_lens_outerLens (s := s)) hu) (huv' ▸ hv)
  have hTVsub : T.V ⊆ f '' lens s ∪ f '' outerLens s := by
    rw [← hdecomp]
    intro z hz
    exact ⟨hTV hz, fun hzK => (T.trace_subset_compl hzK).2 hz⟩
  have hcomplL : f '' lens s ⊆ K.traceᶜ := by
    rintro z ⟨u, hu, rfl⟩ hzK
    have hzA : f u ∈ A :=
      htraceA ⟨hzK, by rw [← himg]; exact ⟨u, lens_subset_ball s hu, rfl⟩⟩
    obtain ⟨w, hw, hwu⟩ := hzA
    have huw : u = w := hinj (lens_subset_ball s hu) (hcapArc hw) hwu.symm
    exact (Set.disjoint_left.mp hdisjLA hu) (huw ▸ hw)
  have hcomplO : f '' outerLens s ⊆ K.traceᶜ := by
    rintro z ⟨u, hu, rfl⟩ hzK
    have hzA : f u ∈ A := htraceA ⟨hzK, by rw [← himg]; exact ⟨u, hu.1, rfl⟩⟩
    obtain ⟨w, hw, hwu⟩ := hzA
    have huw : u = w := hinj hu.1 (hcapArc hw) hwu.symm
    exact (Set.disjoint_left.mp hdisjOA hu) (huw ▸ hw)
  rcases T.preconn_V.subset_or_subset hopenL hopenO hdisjLO hTVsub with h | h
  · left
    refine Set.Subset.antisymm h ?_
    have hpreL : IsPreconnected (f '' lens s) :=
      (lens_convex s).isPreconnected.image f ((hf.mono (lens_subset_ball s)).continuousOn)
    have hsub : f '' lens s ⊆ T.U ∪ T.V := by
      intro z hz
      rw [T.union_eq]
      exact hcomplL hz
    rcases hpreL.subset_or_subset T.isOpen_U T.isOpen_V T.disjoint_UV hsub with h2 | h2
    · obtain ⟨x, hx⟩ := T.nonempty_V
      exact absurd (h2 (h hx)) (fun hcon => (Set.disjoint_left.mp T.disjoint_UV) hcon hx)
    · exact h2
  · right
    refine Set.Subset.antisymm h ?_
    have hpreO' : IsPreconnected (f '' outerLens s) :=
      hpreO.image f ((hf.mono (fun z hz => hz.1)).continuousOn)
    have hsub : f '' outerLens s ⊆ T.U ∪ T.V := by
      intro z hz
      rw [T.union_eq]
      exact hcomplO hz
    rcases hpreO'.subset_or_subset T.isOpen_U T.isOpen_V T.disjoint_UV hsub with h2 | h2
    · obtain ⟨x, hx⟩ := T.nonempty_V
      exact absurd (h2 (h hx)) (fun hcon => (Set.disjoint_left.mp T.disjoint_UV) hcon hx)
    · exact h2

/-- **Radii with small cap length, capped by a prescribed sequence.**  For any positive sequence
`δ`, there is a sequence of radii `r n ∈ (0, 1/2)`, decreasing to `0`, with the length of the image
of the cap arc at the boundary point `1` at most `1/(n+1)` and with real value below `δ n`. -/
theorem exists_radii_capLen_short {Ω : Set ℂ} (hΩb : Bornology.IsBounded Ω) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) 1))
    (hinj : Set.InjOn f (Metric.ball (0 : ℂ) 1)) (himg : f '' Metric.ball (0 : ℂ) 1 = Ω)
    {δ : ℕ → ℝ} (hδ : ∀ n, 0 < δ n) :
    ∃ r : ℕ → ℝ, (∀ n, 0 < r n) ∧ Antitone r ∧ (∀ n, r n < 1 / 2) ∧
      (∀ n, capLen f (r n) ≤ ENNReal.ofReal (1 / ((n : ℝ) + 1))) ∧
      (∀ n, (capLen f (r n)).toReal < δ n) ∧ Tendsto r atTop (𝓝 0) := by
  have hE : ∫⁻ z in Metric.ball (0 : ℂ) 1, ENNReal.ofReal (‖deriv f z‖ ^ 2) < ⊤ :=
    energy_lt_top hΩb hf hinj himg
  have hstep : ∀ (k : ℕ) (s : ℝ), 0 < s →
      ∃ t : ℝ, 0 < t ∧ t < min s (min (1 / 2) (min (δ k / 2) (1 / ((k : ℝ) + 2)))) ∧
        capLen f t ≤ ENNReal.ofReal (min (δ k / 2) (1 / ((k : ℝ) + 2))) := by
    intro k s hs
    have hε : (0 : ℝ) < min (δ k / 2) (1 / ((k : ℝ) + 2)) :=
      lt_min (by linarith [hδ k]) (by positivity)
    have hδ' : 0 < min s (min (1 / 2) (min (δ k / 2) (1 / ((k : ℝ) + 2)))) :=
      lt_min hs (lt_min (by norm_num) hε)
    obtain ⟨t, ht, htc⟩ := exists_capLen_le f hE _ hε _ hδ'
    exact ⟨t, ht.1, ht.2, htc⟩
  let next : ℕ → ℝ → ℝ := fun k s => if h : 0 < s then Classical.choose (hstep k s h) else 1
  let r : ℕ → ℝ := fun n => Nat.rec (next 0 1) (fun k s => next (k + 1) s) n
  have hr_zero : r 0 = next 0 1 := rfl
  have hr_succ : ∀ k, r (k + 1) = next (k + 1) (r k) := fun k => rfl
  have hpos : ∀ n, 0 < r n := by
    intro n
    induction n with
    | zero =>
      rw [hr_zero]
      simp only [next, dif_pos (by norm_num : (0 : ℝ) < 1)]
      exact (Classical.choose_spec (hstep 0 1 (by norm_num))).1
    | succ k ih =>
      rw [hr_succ]
      simp only [next, dif_pos ih]
      exact (Classical.choose_spec (hstep (k + 1) (r k) ih)).1
  have hcap_le : ∀ n, capLen f (r n) ≤
      ENNReal.ofReal (min (δ n / 2) (1 / ((n : ℝ) + 2))) := by
    intro n
    cases n with
    | zero =>
      rw [hr_zero]
      simp only [next, dif_pos (by norm_num : (0 : ℝ) < 1)]
      exact (Classical.choose_spec (hstep 0 1 (by norm_num))).2.2
    | succ k =>
      rw [hr_succ]
      simp only [next, dif_pos (hpos k)]
      exact (Classical.choose_spec (hstep (k + 1) (r k) (hpos k))).2.2
  have hsmall : ∀ n, min (δ n / 2) (1 / ((n : ℝ) + 2)) ≤
      min (δ n / 2) (1 / ((n : ℝ) + 1)) := by
    intro n
    refine min_le_min le_rfl ?_
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    push_cast
    linarith
  have hle : ∀ n, capLen f (r n) ≤ ENNReal.ofReal (1 / ((n : ℝ) + 1)) := by
    intro n
    refine (hcap_le n).trans (ENNReal.ofReal_le_ofReal ?_)
    have h2 : (1 : ℝ) / ((n : ℝ) + 2) ≤ 1 / ((n : ℝ) + 1) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      push_cast
      linarith
    linarith [min_le_right (δ n / 2) (1 / ((n : ℝ) + 2)), h2]
  have hltδ : ∀ n, (capLen f (r n)).toReal < δ n := by
    intro n
    have h1 : (capLen f (r n)).toReal ≤
        (ENNReal.ofReal (min (δ n / 2) (1 / ((n : ℝ) + 2)))).toReal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top (hcap_le n)
    rw [ENNReal.toReal_ofReal (le_of_lt (lt_min (by linarith [hδ n]) (by positivity)))] at h1
    linarith [min_le_left (δ n / 2) (1 / ((n : ℝ) + 2)), hδ n]
  have hle' : ∀ k, r (k + 1) ≤ r k := by
    intro k
    rw [hr_succ]
    simp only [next, dif_pos (hpos k)]
    exact le_trans (le_of_lt (Classical.choose_spec (hstep (k + 1) (r k) (hpos k))).2.1)
      (min_le_left _ _)
  have hlt2 : ∀ n, r n < 1 / 2 := by
    intro n
    induction n with
    | zero =>
      rw [hr_zero]
      simp only [next, dif_pos (by norm_num : (0 : ℝ) < 1)]
      exact lt_of_lt_of_le (Classical.choose_spec (hstep 0 1 (by norm_num))).2.1
        (le_trans (min_le_right _ _) (min_le_left _ _))
    | succ k ih =>
      rw [hr_succ]
      simp only [next, dif_pos (hpos k)]
      exact lt_of_lt_of_le (Classical.choose_spec (hstep (k + 1) (r k) (hpos k))).2.1
        (le_trans (min_le_right _ _) (min_le_left _ _))
  have hbound : ∀ n, r n ≤ 1 / ((n : ℝ) + 2) := by
    intro n
    cases n with
    | zero =>
      rw [hr_zero]
      simp only [next, dif_pos (by norm_num : (0 : ℝ) < 1)]
      exact le_trans (le_of_lt (Classical.choose_spec (hstep 0 1 (by norm_num))).2.1)
        (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
    | succ k =>
      rw [hr_succ]
      simp only [next, dif_pos (hpos k)]
      exact le_trans (le_of_lt (Classical.choose_spec (hstep (k + 1) (r k) (hpos k))).2.1)
        (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  have htend : Tendsto r atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) (fun n => ?_) (fun n => ?_)
    · exact le_of_lt (hpos n)
    · refine (hbound n).trans ?_
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      push_cast
      linarith
  exact ⟨r, hpos, antitone_nat_of_succ_le hle', hlt2, hle, hltδ, htend⟩


set_option maxHeartbeats 8000000 in
/-- **There is no limit gap at the boundary point `1`.**  If two sequences in the disc converge to
`1` while their images stay `ε` apart, we get a contradiction: the cap argument forces the image of
the lens at a suitable small radius to have small diameter, while the two points eventually lie in
that lens. -/
theorem key_no_far_tendsto {Ω : Set ℂ} (hΩo : IsOpen Ω) (hΩne : Ω.Nonempty)
    (hΩb : Bornology.IsBounded Ω) (hΩpre : IsPreconnected Ω)
    {γ : ℝ → ℂ} (hγc : Continuous γ) (hγp : Function.Periodic γ (2 * Real.pi))
    (hγi : Set.InjOn γ (Set.Ico 0 (2 * Real.pi))) (hfr : frontier Ω = Set.range γ)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) 1))
    (hinj : Set.InjOn f (Metric.ball (0 : ℂ) 1)) (himg : f '' Metric.ball (0 : ℂ) 1 = Ω)
    {z w : ℕ → ℂ} (hz : ∀ n, z n ∈ Metric.ball (0 : ℂ) 1)
    (hw : ∀ n, w n ∈ Metric.ball (0 : ℂ) 1)
    (hzt : Tendsto z atTop (𝓝 1)) (hwt : Tendsto w atTop (𝓝 1))
    {ε : ℝ} (hε : 0 < ε) (hfar : ∀ n, ε ≤ ‖f (z n) - f (w n)‖) : False := by
  classical
  -- ## the separation datum of the boundary curve
  obtain ⟨S⟩ := Work.Smooth.SphereJordan.exists_jsep ⟨γ, hγc, hγp⟩ hγi
  have hSV : S.V = Ω := jsep_V_eq_of_isDomain S hΩo hΩne hΩb hΩpre hfr
  -- ## the inverse of `f`, as a function on `Ω`
  obtain ⟨φ, hφ⟩ := homeo_of_biholomorph hf hinj himg
  set G : ℂ → ℂ := fun u => if h : u ∈ Ω then ((φ.symm ⟨u, h⟩ : Metric.ball (0 : ℂ) 1) : ℂ) else 0
    with hGdef
  have hGapply : ∀ u (hu : u ∈ Ω), G u = ((φ.symm ⟨u, hu⟩ : Metric.ball (0 : ℂ) 1) : ℂ) := by
    intro u hu
    rw [hGdef]
    simp only [dif_pos hu]
  have hGf : ∀ u ∈ Metric.ball (0 : ℂ) 1, G (f u) = u := by
    intro u hu
    have hmemΩ : f u ∈ Ω := by rw [← himg]; exact ⟨u, hu, rfl⟩
    rw [hGapply (f u) hmemΩ]
    have h1 : (⟨f u, hmemΩ⟩ : ↥Ω) = φ ⟨u, hu⟩ := by
      apply Subtype.ext
      rw [hφ]
    calc ((φ.symm ⟨f u, hmemΩ⟩ : Metric.ball (0 : ℂ) 1) : ℂ)
        = ((φ.symm (φ ⟨u, hu⟩) : Metric.ball (0 : ℂ) 1) : ℂ) := by rw [h1]
      _ = ((⟨u, hu⟩ : Metric.ball (0 : ℂ) 1) : ℂ) := by rw [φ.symm_apply_apply]
      _ = u := rfl
  have hGmem : Set.MapsTo G Ω (Metric.ball (0 : ℂ) 1) := by
    intro u hu
    rw [hGapply u hu]
    exact (φ.symm ⟨u, hu⟩).2
  have hGcont : ContinuousOn G Ω := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hfun : Ω.domRestrict G = fun u : ↥Ω => ((φ.symm u : Metric.ball (0 : ℂ) 1) : ℂ) := by
      funext u
      exact hGapply u u.2
    rw [hfun]
    exact continuous_subtype_val.comp φ.symm.continuous
  -- ## nearby points of `γ` bound a short arc of parameter length `< 2π`
  have hlen_short : ∀ {u v : ℝ}, u < v → Set.InjOn γ (Set.Icc u v) → γ u ≠ γ v →
      v - u < 2 * Real.pi := by
    intro u v huv hinjarc huvne
    by_contra hcon
    have hcon' : 2 * Real.pi ≤ v - u := not_lt.mp hcon
    have hmem : u + 2 * Real.pi ∈ Set.Icc u v :=
      ⟨by linarith [Real.two_pi_pos], by linarith⟩
    have h1 := hinjarc ⟨le_refl u, by linarith [Real.two_pi_pos]⟩ hmem (hγp u).symm
    linarith [Real.two_pi_pos]
  -- ## the cap-length radii
  have hεn : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  set δ : ℕ → ℝ := fun n => Classical.choose (exists_short_arc hγc hγp hγi (hεn n)) with hδdef
  have hδpos : ∀ n, 0 < δ n := fun n =>
    (Classical.choose_spec (exists_short_arc hγc hγp hγi (hεn n))).1
  have hδprop : ∀ n, ∀ (u : ℂ), u ∈ Set.range γ → ∀ (v : ℂ), v ∈ Set.range γ → u ≠ v →
      ‖u - v‖ < δ n →
      ∃ x y, x < y ∧ Set.InjOn γ (Set.Icc x y) ∧
        Metric.diam (γ '' Set.Icc x y) ≤ 1 / ((n : ℝ) + 1) ∧
        ((γ x = u ∧ γ y = v) ∨ (γ x = v ∧ γ y = u)) := fun n =>
    (Classical.choose_spec (exists_short_arc hγc hγp hγi (hεn n))).2
  obtain ⟨r, hrpos, hranti, hrlt, hrle, hrltδ, hrtend⟩ :=
    exists_radii_capLen_short (δ := δ) hΩb hf hinj himg hδpos
  have hcapfin : ∀ n : ℕ, capLen f (r n) < ⊤ := fun n =>
    lt_of_le_of_lt (hrle n) ENNReal.ofReal_lt_top
  have htoReal : ∀ n : ℕ, (capLen f (r n)).toReal ≤ 1 / ((n : ℝ) + 1) := fun n =>
    (ENNReal.toReal_mono ENNReal.ofReal_ne_top (hrle n)).trans_eq
      (ENNReal.toReal_ofReal (by positivity))
  have hσ : ∀ n : ℕ, r n < 2 := fun n => by linarith [hrlt n]
  -- ## the cap data at each radius
  have hdata : ∀ n : ℕ, ∃ (K : Work.Smooth.Jordan.PlaneCurve) (T : JSep K), T.V ⊆ Ω ∧
      Metric.diam T.V ≤ 4 / ((n : ℝ) + 1) ∧
      (T.V = f '' lens (r n) ∨ T.V = f '' outerLens (r n)) := by
    intro n
    obtain ⟨a, b, hafr, hbfr, ha, hb, hab⟩ :=
      capLimits_mem_frontier hΩo hfr (hf.analyticOnNhd Metric.isOpen_ball) hGcont hGf hGmem himg
        (hrpos n) (hσ n) (hcapfin n)
    have key4 : ∀ {c d : ℝ}, c ≤ 1 / ((n : ℝ) + 1) → d ≤ 1 / ((n : ℝ) + 1) →
        2 * (c + d) ≤ 4 / ((n : ℝ) + 1) := by
      intro c d hc hd
      have h1 : c + d ≤ 2 * (1 / ((n : ℝ) + 1)) := by linarith
      have h2 : 2 * (c + d) ≤ 2 * (2 * (1 / ((n : ℝ) + 1))) := mul_le_mul_of_nonneg_left h1 (by norm_num)
      have h3 : 2 * (2 * (1 / ((n : ℝ) + 1))) = 4 / ((n : ℝ) + 1) := by ring
      linarith
    by_cases hne : a = b
    · -- degenerate: the arc is closed up at `a` alone
      obtain ⟨t, ht⟩ := show a ∈ Set.range γ from by rw [← hfr]; exact hafr
      have hcont : Continuous (capExtend f (r n) a a) :=
        capExtend_continuousOn hf.continuousOn ha (hne.symm ▸ hb) (hrpos n) (hσ n)
      obtain ⟨K, T, hK, hKr⟩ := cap_planeCurve hΩo hγc hγp hγi hf.continuousOn hinj himg hfr
        (hrpos n) (hσ n) ha hb hafr hbfr (x := t) (y := t) le_rfl (fun _ => rfl)
        (Or.inl ⟨ht, ht.trans hne⟩) (fun _ => by linarith [Real.two_pi_pos])
      have hsubfr : γ '' Set.Icc t t ⊆ frontier Ω := fun u hu => by
        obtain ⟨s, _, rfl⟩ := hu
        rw [hfr]; exact ⟨s, rfl⟩
      have haC : a ∈ γ '' Set.Icc t t := ⟨t, ⟨le_rfl, le_rfl⟩, ht⟩
      have hduv : Metric.diam (γ '' Set.Icc t t) ≤ 1 / ((n : ℝ) + 1) := by
        have hset : γ '' Set.Icc t t = ({a} : Set ℂ) := by
          rw [Set.Icc_self, Set.image_singleton, ht]
        rw [hset, Metric.diam_singleton]
        positivity
      have hTV := cap_V_subset_and_diam (γ := γ) (a := a) (b := b) (x := t) (y := t) (K := K)
        hγc hγp S T hSV hΩo hΩb hf hinj himg hfr (hrpos n) (hσ n) hafr hbfr hsubfr ha hb
        (hcapfin n) haC hKr
      exact ⟨K, T, hTV.1, by linarith [hTV.2, key4 (htoReal n) hduv],
        cap_lens_dichotomy T hΩo hf hinj himg hTV.1 (hrpos n) (hσ n) hafr hbfr hsubfr hKr⟩
    · -- non-degenerate: close the arc up with a short sub-arc of `γ`
      obtain ⟨x, y, hxy, hinjarc, hdiamarc, hcase⟩ :=
        hδprop n a (by rw [← hfr]; exact hafr) b (by rw [← hfr]; exact hbfr) hne
          (lt_of_le_of_lt hab (hrltδ n))
      have harcne : γ x ≠ γ y := by
        rcases hcase with h | h
        · rw [h.1, h.2]; exact hne
        · rw [h.1, h.2]; exact fun hc => hne hc.symm
      have hlenarc : y - x < 2 * Real.pi := hlen_short hxy hinjarc harcne
      have hsubfr : γ '' Set.Icc x y ⊆ frontier Ω := fun s hs => by
        obtain ⟨τ, _, rfl⟩ := hs
        rw [hfr]; exact ⟨τ, rfl⟩
      have haC : a ∈ γ '' Set.Icc x y := by
        rcases hcase with h | h
        · exact ⟨x, ⟨le_refl x, hxy.le⟩, h.1⟩
        · exact ⟨y, ⟨hxy.le, le_refl y⟩, h.2⟩
      obtain ⟨K, T, hK, hKr⟩ := cap_planeCurve hΩo hγc hγp hγi hf.continuousOn hinj himg hfr
        (hrpos n) (hσ n) ha hb hafr hbfr (x := x) (y := y) hxy.le (fun hc => absurd hc hne)
        hcase (fun _ => hlenarc)
      have hTV := cap_V_subset_and_diam (γ := γ) (a := a) (b := b) (x := x) (y := y) (K := K)
        hγc hγp S T hSV hΩo hΩb hf hinj himg hfr (hrpos n) (hσ n) hafr hbfr hsubfr ha hb
        (hcapfin n) haC hKr
      exact ⟨K, T, hTV.1, by linarith [hTV.2, key4 (htoReal n) hdiamarc],
        cap_lens_dichotomy T hΩo hf hinj himg hTV.1 (hrpos n) (hσ n) hafr hbfr hsubfr hKr⟩
  choose K T hTV hTdiam hTdich using hdata
  -- ## the outer lens has a fixed positive diameter
  have houterbdd : Bornology.IsBounded (f '' outerLens (r 0)) := by
    refine Bornology.IsBounded.subset hΩb ?_
    rw [← himg]
    exact Set.image_mono (fun u hu => hu.1)
  have hc : 0 < Metric.diam (f '' outerLens (r 0)) :=
    diam_image_outerLens_pos hinj (hrpos 0) (hσ 0) houterbdd
  have houter_mono : ∀ k, Metric.diam (f '' outerLens (r 0)) ≤
      Metric.diam (f '' outerLens (r k)) := by
    intro k
    refine diam_image_outerLens_le (hranti (Nat.zero_le k)) ?_
    refine Bornology.IsBounded.subset hΩb ?_
    rw [← himg]
    exact Set.image_mono (fun u hu => hu.1)
  -- ## a subsequence of the two sequences entering the lens
  have hsubseq : ∃ n : ℕ → ℕ, StrictMono n ∧ ∀ k, ‖z (n k) - 1‖ < r k ∧ ‖w (n k) - 1‖ < r k := by
    have hz0 : Tendsto (fun j : ℕ => ‖z j - 1‖) atTop (𝓝 0) := by
      have h1 : Tendsto (fun j : ℕ => z j - 1) atTop (𝓝 ((1 : ℂ) - 1)) :=
        hzt.sub tendsto_const_nhds
      simpa using h1.norm
    have hw0 : Tendsto (fun j : ℕ => ‖w j - 1‖) atTop (𝓝 0) := by
      have h1 : Tendsto (fun j : ℕ => w j - 1) atTop (𝓝 ((1 : ℂ) - 1)) :=
        hwt.sub tendsto_const_nhds
      simpa using h1.norm
    have hstep : ∀ (k m : ℕ), ∃ j : ℕ, m < j ∧ ‖z j - 1‖ < r k ∧ ‖w j - 1‖ < r k := by
      intro k m
      have h1 : ∀ᶠ j in atTop, ‖z j - 1‖ < r k := hz0.eventually (isOpen_Iio.mem_nhds (hrpos k))
      have h2 : ∀ᶠ j in atTop, ‖w j - 1‖ < r k := hw0.eventually (isOpen_Iio.mem_nhds (hrpos k))
      have h3 : ∀ᶠ j in atTop, m < j := eventually_gt_atTop m
      obtain ⟨j, hj1, hj2, hj3⟩ := (h1.and (h2.and h3)).exists
      exact ⟨j, hj3, hj1, hj2⟩
    let n : ℕ → ℕ := fun k => Nat.rec (Classical.choose (hstep 0 0))
      (fun k j => Classical.choose (hstep (k + 1) j)) k
    have hn0 : n 0 = Classical.choose (hstep 0 0) := rfl
    have hnsucc : ∀ k, n (k + 1) = Classical.choose (hstep (k + 1) (n k)) := fun k => rfl
    have hnmono : StrictMono n := by
      apply strictMono_nat_of_lt_succ
      intro k
      rw [hnsucc]
      exact (Classical.choose_spec (hstep (k + 1) (n k))).1
    have hnz : ∀ k, ‖z (n k) - 1‖ < r k := by
      intro k
      cases k with
      | zero => rw [hn0]; exact (Classical.choose_spec (hstep 0 0)).2.1
      | succ k => rw [hnsucc]; exact (Classical.choose_spec (hstep (k + 1) (n k))).2.1
    have hnw : ∀ k, ‖w (n k) - 1‖ < r k := by
      intro k
      cases k with
      | zero => rw [hn0]; exact (Classical.choose_spec (hstep 0 0)).2.2
      | succ k => rw [hnsucc]; exact (Classical.choose_spec (hstep (k + 1) (n k))).2.2
    exact ⟨n, hnmono, fun k => ⟨hnz k, hnw k⟩⟩
  obtain ⟨n, _hnmono, hzw⟩ := hsubseq
  have hnz : ∀ k, ‖z (n k) - 1‖ < r k := fun k => (hzw k).1
  have hnw : ∀ k, ‖w (n k) - 1‖ < r k := fun k => (hzw k).2
  -- ## for large indices the bounded side is the lens
  have htend4 : Tendsto (fun k : ℕ => 4 / ((k : ℝ) + 1)) atTop (𝓝 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (4 : ℝ)
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp (htend4.eventually (isOpen_Iio.mem_nhds
    (show (0 : ℝ) < min ε (Metric.diam (f '' outerLens (r 0))) by positivity)))
  have hside : ∀ k ≥ N₁, (T k).V = f '' lens (r k) := by
    intro k hk
    rcases hTdich k with h | h
    · exact h
    · exfalso
      have h1 : Metric.diam (f '' outerLens (r 0)) ≤ Metric.diam (f '' outerLens (r k)) :=
        houter_mono k
      have h2 : Metric.diam (f '' outerLens (r k)) = Metric.diam (T k).V := by rw [h]
      have h3 : Metric.diam (T k).V ≤ 4 / ((k : ℝ) + 1) := hTdiam k
      have h4 : 4 / ((k : ℝ) + 1) < min ε (Metric.diam (f '' outerLens (r 0))) := hN₁ k hk
      have h5 : min ε (Metric.diam (f '' outerLens (r 0))) ≤ Metric.diam (f '' outerLens (r 0)) :=
        min_le_right _ _
      linarith
  -- ## the contradiction
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp (htend4.eventually (isOpen_Iio.mem_nhds hε))
  obtain ⟨k₀, hk₀₁, hk₀₂⟩ : ∃ k₀, N₁ ≤ k₀ ∧ N₂ ≤ k₀ := ⟨max N₁ N₂, le_max_left _ _, le_max_right _ _⟩
  have hsmall : 4 / ((k₀ : ℝ) + 1) < ε := hN₂ k₀ hk₀₂
  have hzball : ‖z (n k₀)‖ < 1 := by
    have h := hz (n k₀)
    rwa [Metric.mem_ball, dist_zero_right] at h
  have hwball : ‖w (n k₀)‖ < 1 := by
    have h := hw (n k₀)
    rwa [Metric.mem_ball, dist_zero_right] at h
  have hmemz : z (n k₀) ∈ lens (r k₀) := mem_lens_iff.mpr ⟨hzball, hnz k₀⟩
  have hmemw : w (n k₀) ∈ lens (r k₀) := mem_lens_iff.mpr ⟨hwball, hnw k₀⟩
  have hbddL : Bornology.IsBounded (f '' lens (r k₀)) := by
    refine Bornology.IsBounded.subset hΩb ?_
    rw [← himg]
    exact Set.image_mono (fun u hu => lens_subset_ball (r k₀) hu)
  have hdist : ‖f (z (n k₀)) - f (w (n k₀))‖ ≤ Metric.diam (f '' lens (r k₀)) := by
    rw [← dist_eq_norm]
    exact Metric.dist_le_diam_of_mem hbddL ⟨_, hmemz, rfl⟩ ⟨_, hmemw, rfl⟩
  have hdiam : Metric.diam (f '' lens (r k₀)) = Metric.diam (T k₀).V := by
    rw [← hside k₀ hk₀₁]
  have h3 : Metric.diam (T k₀).V ≤ 4 / ((k₀ : ℝ) + 1) := hTdiam k₀
  linarith [hfar (n k₀), hdist, h3, hdiam.ge, hdiam.le]


set_option maxHeartbeats 2000000 in
/-- **A biholomorphism of the disc onto a Jordan domain is uniformly continuous.** -/
theorem uniformContinuousOn_of_biholomorph {Ω : Set ℂ} (hΩo : IsOpen Ω) (hΩne : Ω.Nonempty)
    (hΩb : Bornology.IsBounded Ω) (hΩpre : IsPreconnected Ω)
    {γ : ℝ → ℂ} (hγc : Continuous γ) (hγp : Function.Periodic γ (2 * Real.pi))
    (hγi : Set.InjOn γ (Set.Ico 0 (2 * Real.pi))) (hfr : frontier Ω = Set.range γ)
    {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g (Metric.ball (0 : ℂ) 1))
    (hinj : Set.InjOn g (Metric.ball (0 : ℂ) 1)) (himg : g '' Metric.ball (0 : ℂ) 1 = Ω) :
    UniformContinuousOn g (Metric.ball (0 : ℂ) 1) := by
  rw [Metric.uniformContinuousOn_iff]
  by_contra hcon
  push_neg at hcon
  obtain ⟨ε, hε, hbad⟩ := hcon
  have hbad' : ∀ δ > 0, ∃ z ∈ Metric.ball (0 : ℂ) 1, ∃ w ∈ Metric.ball (0 : ℂ) 1,
      ‖z - w‖ < δ ∧ ε ≤ ‖g z - g w‖ := by
    intro δ hδ
    obtain ⟨z, hz, w, hw, hd, hg'⟩ := hbad δ hδ
    exact ⟨z, hz, w, hw, by rwa [dist_eq_norm] at hd, by rwa [dist_eq_norm] at hg'⟩
  obtain ⟨ζ, hζ, z, w, hz, hw, hzt, hwt, hfar⟩ :=
    exists_far_pair hg.continuousOn hε hbad'
  have hζne : ζ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hζ
    norm_num at hζ
  have hball : ∀ v : ℂ, ‖ζ * v‖ = ‖v‖ := fun v => by rw [norm_mul, hζ, one_mul]
  have hrot : ∀ v : ℂ, ζ * v ∈ Metric.ball (0 : ℂ) 1 ↔ v ∈ Metric.ball (0 : ℂ) 1 := by
    intro v
    rw [Metric.mem_ball, Metric.mem_ball, dist_zero_right, dist_zero_right, hball v]
  have hdiff : DifferentiableOn ℂ (fun v : ℂ => ζ * v) (Metric.ball (0 : ℂ) 1) := by fun_prop
  have hf' : DifferentiableOn ℂ (fun v : ℂ => g (ζ * v)) (Metric.ball (0 : ℂ) 1) :=
    hg.comp hdiff (fun v hv => (hrot v).mpr hv)
  have hinj' : Set.InjOn (fun v : ℂ => g (ζ * v)) (Metric.ball (0 : ℂ) 1) := by
    intro v₁ h₁ v₂ h₂ heq
    exact mul_left_cancel₀ hζne (hinj ((hrot v₁).mpr h₁) ((hrot v₂).mpr h₂) heq)
  have himg' : (fun v : ℂ => g (ζ * v)) '' Metric.ball (0 : ℂ) 1 = Ω := by
    have h2 : (fun v : ℂ => ζ * v) '' Metric.ball (0 : ℂ) 1 = Metric.ball (0 : ℂ) 1 := by
      refine Set.Subset.antisymm (fun u hu => ?_) (fun u hu => ?_)
      · obtain ⟨v, hv, rfl⟩ := hu
        exact (hrot v).mpr hv
      · refine ⟨ζ⁻¹ * u, ?_, ?_⟩
        · have h : ζ * (ζ⁻¹ * u) ∈ Metric.ball (0 : ℂ) 1 := by
            rw [← mul_assoc, mul_inv_cancel₀ hζne, one_mul]
            exact hu
          exact (hrot (ζ⁻¹ * u)).mp h
        · show ζ * (ζ⁻¹ * u) = u
          rw [← mul_assoc, mul_inv_cancel₀ hζne, one_mul]
    rw [show (fun v : ℂ => g (ζ * v)) = g ∘ (fun v : ℂ => ζ * v) from rfl, Set.image_comp, h2,
      himg]
  have hz' : ∀ k, ζ⁻¹ * z k ∈ Metric.ball (0 : ℂ) 1 := fun k => by
    refine (hrot (ζ⁻¹ * z k)).mp ?_
    rw [← mul_assoc, mul_inv_cancel₀ hζne, one_mul]
    exact hz k
  have hw' : ∀ k, ζ⁻¹ * w k ∈ Metric.ball (0 : ℂ) 1 := fun k => by
    refine (hrot (ζ⁻¹ * w k)).mp ?_
    rw [← mul_assoc, mul_inv_cancel₀ hζne, one_mul]
    exact hw k
  have hzt' : Tendsto (fun k => ζ⁻¹ * z k) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => ζ⁻¹) atTop (𝓝 ζ⁻¹)).mul hzt
    simpa [inv_mul_cancel₀ hζne] using h
  have hwt' : Tendsto (fun k => ζ⁻¹ * w k) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => ζ⁻¹) atTop (𝓝 ζ⁻¹)).mul hwt
    simpa [inv_mul_cancel₀ hζne] using h
  have hfar' : ∀ k, ε ≤ ‖(fun v : ℂ => g (ζ * v)) (ζ⁻¹ * z k)
      - (fun v : ℂ => g (ζ * v)) (ζ⁻¹ * w k)‖ := by
    intro k
    have h1 : ζ * (ζ⁻¹ * z k) = z k := by rw [← mul_assoc, mul_inv_cancel₀ hζne, one_mul]
    have h2 : ζ * (ζ⁻¹ * w k) = w k := by rw [← mul_assoc, mul_inv_cancel₀ hζne, one_mul]
    show ε ≤ ‖g (ζ * (ζ⁻¹ * z k)) - g (ζ * (ζ⁻¹ * w k))‖
    rw [h1, h2]
    exact hfar k
  exact key_no_far_tendsto hΩo hΩne hΩb hΩpre hγc hγp hγi hfr hf' hinj' himg'
    hz' hw' hzt' hwt' hε hfar'

set_option maxHeartbeats 3000000 in
/-- **Continuous extension of a uniformly continuous disc map onto `Ω`.**  A function which is
uniformly continuous on the open unit disc with image `Ω` extends continuously to the closed disc;
its boundary values lie in `frontier Ω`. -/
theorem extension_of_uniformContinuousOn {Ω : Set ℂ} {g : ℂ → ℂ}
    (huc : UniformContinuousOn g (Metric.ball (0 : ℂ) 1)) (hΩo : IsOpen Ω)
    (himg : g '' Metric.ball (0 : ℂ) 1 = Ω)
    (φ : Metric.ball (0 : ℂ) 1 ≃ₜ ↥Ω) (hφ : ∀ z, (φ z : ℂ) = g z) :
    ∃ G : ℂ → ℂ, ContinuousOn G (Metric.closedBall (0 : ℂ) 1) ∧
      (∀ z ∈ Metric.ball (0 : ℂ) 1, G z = g z) ∧
      ∀ ζ : ℂ, ‖ζ‖ = 1 → G ζ ∈ frontier Ω := by
  classical
  -- ## the open disc is dense in the closed disc
  have hdense : Dense {z : ↥(Metric.closedBall (0 : ℂ) 1) | (z : ℂ) ∈ Metric.ball (0 : ℂ) 1} := by
    rw [Subtype.dense_iff]
    rintro z hz
    have hz' : ‖z‖ ≤ 1 := by rwa [Metric.mem_closedBall, dist_zero_right] at hz
    rcases lt_or_eq_of_le hz' with h | h
    · refine subset_closure ⟨⟨z, hz⟩, ?_, rfl⟩
      show ((⟨z, hz⟩ : ↥(Metric.closedBall (0 : ℂ) 1)) : ℂ) ∈ Metric.ball (0 : ℂ) 1
      rw [Metric.mem_ball, dist_zero_right]
      exact h
    · rw [Metric.mem_closure_iff]
      intro ε hε
      set δ : ℝ := min (ε / 2) (1 / 2) with hδdef
      have hδpos : 0 < δ := lt_min (by linarith) (by norm_num)
      have hδlt : δ < 1 := (min_le_right _ _).trans_lt (by norm_num)
      have hδle : δ < ε := (min_le_left _ _).trans_lt (by linarith)
      set w : ℂ := ((1 - δ : ℝ) : ℂ) * z with hwdef
      have hwball : w ∈ Metric.ball (0 : ℂ) 1 := by
        rw [hwdef, Metric.mem_ball, dist_zero_right, norm_mul, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos (by linarith), h, mul_one]
        linarith
      have hwclosed : w ∈ Metric.closedBall (0 : ℂ) 1 := by
        rw [hwdef, Metric.mem_closedBall, dist_zero_right, norm_mul, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos (by linarith), h, mul_one]
        linarith
      refine ⟨w, ⟨⟨w, hwclosed⟩, hwball, rfl⟩, ?_⟩
      rw [dist_eq_norm]
      have h1 : z - ((1 - δ : ℝ) : ℂ) * z = ((δ : ℝ) : ℂ) * z := by push_cast; ring
      rw [hwdef, h1, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδpos, h, mul_one]
      exact hδle
  -- ## the uniformly continuous function on the dense subset
  let fsub : {z : ↥(Metric.closedBall (0 : ℂ) 1) | (z : ℂ) ∈ Metric.ball (0 : ℂ) 1} → ℂ :=
    fun z => g (z : ℂ)
  have hfsub : UniformContinuous fsub := by
    rw [Metric.uniformContinuous_iff]
    intro ε hε
    obtain ⟨δ, hδ, hδprop⟩ := Metric.uniformContinuousOn_iff.mp huc ε hε
    refine ⟨δ, hδ, fun x y hxy => ?_⟩
    have hxy' : dist (x : ℂ) (y : ℂ) < δ := by
      rwa [Subtype.dist_eq] at hxy
    exact hδprop (x : ℂ) x.2 (y : ℂ) y.2 hxy'
  let G' : ↥(Metric.closedBall (0 : ℂ) 1) → ℂ := hdense.extend fsub
  have hG'uc : UniformContinuous G' := hdense.uniformContinuous_extend hfsub
  have hG'ind : ∀ z : {z : ↥(Metric.closedBall (0 : ℂ) 1) | (z : ℂ) ∈ Metric.ball (0 : ℂ) 1},
      G' ↑z = fsub z := fun z => hdense.extend_of_ind hfsub z
  refine ⟨fun u => if h : u ∈ Metric.closedBall (0 : ℂ) 1 then G' ⟨u, h⟩ else 0, ?_, ?_, ?_⟩
  · -- continuity on the closed disc
    rw [continuousOn_iff_continuous_domRestrict]
    have hfun : (Metric.closedBall (0 : ℂ) 1).domRestrict
        (fun u => if h : u ∈ Metric.closedBall (0 : ℂ) 1 then G' ⟨u, h⟩ else 0) = G' := by
      funext u
      exact dif_pos u.2
    rw [hfun]
    exact hG'uc.continuous
  · -- agrees with `g` on the open disc
    intro u hu
    have hcl : u ∈ Metric.closedBall (0 : ℂ) 1 := Metric.ball_subset_closedBall hu
    show (if h : u ∈ Metric.closedBall (0 : ℂ) 1 then G' ⟨u, h⟩ else 0) = g u
    rw [dif_pos hcl]
    exact hG'ind ⟨⟨u, hcl⟩, hu⟩
  · -- boundary values
    intro ζ hζ
    have hζclosed : ζ ∈ Metric.closedBall (0 : ℂ) 1 := by
      rw [Metric.mem_closedBall, dist_zero_right, hζ]
    show (if h : ζ ∈ Metric.closedBall (0 : ℂ) 1 then G' ⟨ζ, h⟩ else 0) ∈ frontier Ω
    rw [dif_pos hζclosed]
    set zn : ℕ → ℂ := fun n => (((1 - 1 / ((n : ℝ) + 1) : ℝ)) : ℂ) * ζ with hzndef
    have hzn_ball : ∀ n, zn n ∈ Metric.ball (0 : ℂ) 1 := by
      intro n
      have h1 : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      have h2 : (0 : ℝ) ≤ 1 - 1 / ((n : ℝ) + 1) := by
        have h3 : 1 / ((n : ℝ) + 1) ≤ 1 := by
          have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
          have h4 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith
          have h5 : (0 : ℝ) ≤ (n : ℝ) + 1 := by linarith
          calc 1 / ((n : ℝ) + 1) ≤ ((n : ℝ) + 1) / ((n : ℝ) + 1) :=
                div_le_div_of_nonneg_right h4 h5
            _ = 1 := by field_simp
        linarith
      refine Metric.mem_ball.mpr ?_
      rw [dist_zero_right, hzndef, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg h2, hζ, mul_one]
      linarith
    have hzn_tend : Tendsto zn atTop (𝓝 ζ) := by
      rw [tendsto_iff_dist_tendsto_zero]
      have h1 : ∀ n, dist (zn n) ζ = 1 / ((n : ℝ) + 1) := by
        intro n
        have h2 : (((1 - 1 / ((n : ℝ) + 1) : ℝ)) : ℂ) * ζ - ζ
            = ((-(1 / ((n : ℝ) + 1)) : ℝ) : ℂ) * ζ := by push_cast; ring
        rw [dist_eq_norm, hzndef, h2, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_neg (by simp only [neg_lt_zero]; positivity), hζ, mul_one, neg_neg]
      simp only [h1]
      exact tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    -- the values converge
    have hgt : Tendsto (fun n => g (zn n)) atTop (𝓝 (G' ⟨ζ, hζclosed⟩)) := by
      have h1 : Tendsto
          (fun n => (⟨zn n, Metric.ball_subset_closedBall (hzn_ball n)⟩ :
            ↥(Metric.closedBall (0 : ℂ) 1))) atTop (𝓝 (⟨ζ, hζclosed⟩ :
              ↥(Metric.closedBall (0 : ℂ) 1))) := tendsto_subtype_rng.mpr hzn_tend
      have h2 : Tendsto (fun n => G' ⟨zn n, Metric.ball_subset_closedBall (hzn_ball n)⟩)
          atTop (𝓝 (G' ⟨ζ, hζclosed⟩)) := (hG'uc.continuous.tendsto _).comp h1
      have h3 : (fun n => G' ⟨zn n, Metric.ball_subset_closedBall (hzn_ball n)⟩)
          = fun n => g (zn n) := by
        funext n
        exact hG'ind ⟨⟨zn n, Metric.ball_subset_closedBall (hzn_ball n)⟩, hzn_ball n⟩
      rw [h3] at h2
      exact h2
    have hmem : G' ⟨ζ, hζclosed⟩ ∈ closure Ω := by
      refine isClosed_closure.mem_of_tendsto hgt (Eventually.of_forall fun n => ?_)
      exact subset_closure (by rw [← himg]; exact ⟨zn n, hzn_ball n, rfl⟩)
    -- ## the value is not in `Ω`
    have hnotmem : G' ⟨ζ, hζclosed⟩ ∉ Ω := by
      intro hmemΩ
      set Ginv : ℂ → ℂ :=
        fun u => if h : u ∈ Ω then ((φ.symm ⟨u, h⟩ : Metric.ball (0 : ℂ) 1) : ℂ) else 0
        with hGinvdef
      have hGinvapply : ∀ u (hu : u ∈ Ω),
          Ginv u = ((φ.symm ⟨u, hu⟩ : Metric.ball (0 : ℂ) 1) : ℂ) := by
        intro u hu
        rw [hGinvdef]
        simp only [dif_pos hu]
      have hGinvf : ∀ u ∈ Metric.ball (0 : ℂ) 1, Ginv (g u) = u := by
        intro u hu
        have hmemΩ : g u ∈ Ω := by rw [← himg]; exact ⟨u, hu, rfl⟩
        rw [hGinvapply (g u) hmemΩ]
        have h1 : (⟨g u, hmemΩ⟩ : ↥Ω) = φ ⟨u, hu⟩ := by
          apply Subtype.ext
          rw [hφ]
        calc ((φ.symm ⟨g u, hmemΩ⟩ : Metric.ball (0 : ℂ) 1) : ℂ)
            = ((φ.symm (φ ⟨u, hu⟩) : Metric.ball (0 : ℂ) 1) : ℂ) := by rw [h1]
          _ = ((⟨u, hu⟩ : Metric.ball (0 : ℂ) 1) : ℂ) := by rw [φ.symm_apply_apply]
          _ = u := rfl
      have hGinvcont : ContinuousOn Ginv Ω := by
        rw [continuousOn_iff_continuous_domRestrict]
        have hfun : Ω.domRestrict Ginv
            = fun u : ↥Ω => ((φ.symm u : Metric.ball (0 : ℂ) 1) : ℂ) := by
          funext u
          exact hGinvapply u u.2
        rw [hfun]
        exact continuous_subtype_val.comp φ.symm.continuous
      have h1 : Tendsto (fun n => Ginv (g (zn n))) atTop (𝓝 (Ginv (G' ⟨ζ, hζclosed⟩))) :=
        (hGinvcont.continuousAt (hΩo.mem_nhds hmemΩ)).tendsto.comp hgt
      have h2 : (fun n => Ginv (g (zn n))) = zn := funext fun n => hGinvf (zn n) (hzn_ball n)
      rw [h2] at h1
      have h3 : ζ = Ginv (G' ⟨ζ, hζclosed⟩) := tendsto_nhds_unique hzn_tend h1
      have h4 : Ginv (G' ⟨ζ, hζclosed⟩)
          = ((φ.symm ⟨G' ⟨ζ, hζclosed⟩, hmemΩ⟩ : Metric.ball (0 : ℂ) 1) : ℂ) :=
        hGinvapply _ hmemΩ
      have h5 : ‖Ginv (G' ⟨ζ, hζclosed⟩)‖ < 1 := by
        rw [h4]
        have h6 := Metric.mem_ball.mp (φ.symm ⟨G' ⟨ζ, hζclosed⟩, hmemΩ⟩).2
        rwa [dist_zero_right] at h6
      rw [← h3, hζ] at h5
      exact absurd h5 (by norm_num)
    rw [closure_eq_self_union_frontier] at hmem
    rcases hmem with h | h
    · exact absurd h hnotmem
    · exact h

/-! ## Carathéodory's extension theorem -/

/-- **Carathéodory's extension theorem (continuity part).**  A biholomorphism `g` of the unit disc
onto a bounded simply connected domain `Ω` whose frontier is the trace of a simple closed curve
extends continuously to the closed disc, with boundary values on `frontier Ω`. -/
theorem caratheodory_extension_continuous {Ω : Set ℂ} (hΩo : IsOpen Ω) (hΩne : Ω.Nonempty)
    (hΩb : Bornology.IsBounded Ω) (hΩsc : SimplyConnectedSpace ↥Ω)
    {γ : ℝ → ℂ} (hγc : Continuous γ) (hγp : Function.Periodic γ (2 * Real.pi))
    (hγi : Set.InjOn γ (Set.Ico 0 (2 * Real.pi))) (hfr : frontier Ω = Set.range γ)
    {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g (Metric.ball (0 : ℂ) 1))
    (hinj : Set.InjOn g (Metric.ball (0 : ℂ) 1)) (himg : g '' Metric.ball (0 : ℂ) 1 = Ω) :
    ∃ G : ℂ → ℂ, ContinuousOn G (Metric.closedBall (0 : ℂ) 1) ∧
      (∀ z ∈ Metric.ball (0 : ℂ) 1, G z = g z) ∧
      ∀ ζ : ℂ, ‖ζ‖ = 1 → G ζ ∈ frontier Ω := by
  have hΩpre : IsPreconnected Ω := by
    rw [isPreconnected_iff_preconnectedSpace]
    infer_instance
  have huc : UniformContinuousOn g (Metric.ball (0 : ℂ) 1) :=
    uniformContinuousOn_of_biholomorph hΩo hΩne hΩb hΩpre hγc hγp hγi hfr hg hinj himg
  obtain ⟨φ, hφ⟩ := homeo_of_biholomorph hg hinj himg
  exact extension_of_uniformContinuousOn huc hΩo himg φ hφ


end

end Work.Smooth.Schoenflies
