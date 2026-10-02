import Mathlib
import Submission.Work.Bottcher.Defs
import Submission.Work.Bottcher.Contraction.LiftCoreDefs
import Submission.Work.Bottcher.Contraction.isPreconnected_escapeSet
import Submission.Work.Bottcher.Contraction.bottcher_comm_Tantibar_of_analytic
import Submission.Work.Bottcher.Series.summable_bottcherTerm
import Submission.Work.Bottcher.Inverse.green_eq_log_of_inverseBottcher
import Submission.Work.Bottcher.Green.greenParam_pos_iff
import Submission.Work.Bottcher.Green.green_nonneg
import Submission.Work.Bottcher.Green.green_comm
import Submission.Work.Bottcher.Core.analyticAt_bottcher
import Submission.Work.Escape.continuous_green
import Submission.Work.Escape.Mandelbar
import Submission.Work.Escape.differentiableOn_of_continuousOn_exp_eq
import Submission.Work.Top.isPreconnected_gt_potential
import Submission.Work.Bottcher.Contraction2.isConnected_filledJulia_of_mem_mandelbar
import Submission.Work.Bottcher.Contraction2.exists_analyticOnNhd_exp_eq_of_liftChange_eq_zero
import Submission.Work.Bottcher.Contraction2.liftChange_normFactor_eq_zero

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter Function Set
open scoped Topology

namespace Work.Bottcher.Contraction2

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-! ## Elementary facts about the Green function and the escape set -/

/-- The Green function of the tricorn is continuous. -/
theorem continuous_green (c : ℂ) : Continuous (Work.Bottcher.green c) :=
  Work.Escape.continuous_green_Tantibar c

/-- The escape set `{G_c > 0}` is open. -/
theorem isOpen_escapeSet (c : ℂ) : IsOpen (Work.Bottcher.EscapeSet c) :=
  isOpen_lt continuous_const (continuous_green c)

/-- The escape radius of the tricorn is positive. -/
theorem escapeRadius_pos' (c : ℂ) : 0 < Work.Bottcher.escapeRadius c := by
  rw [Work.Bottcher.escapeRadius]; positivity

/-- At a mandelbar parameter the Green function vanishes at the critical point `0`. -/
theorem green_self_eq_zero (c : ℂ) (hc : c ∈ Mandelbar) : Work.Bottcher.green c 0 = 0 := by
  have hle : Work.Bottcher.greenParam c ≤ 0 := by
    by_contra h
    exact ((Work.Bottcher.Green.greenParam_pos_iff c).mp (lt_of_not_ge h)) hc
  rw [← Work.Bottcher.greenParam_def c]
  exact le_antisymm hle (Work.Bottcher.Green.green_nonneg c 0)

/-- The escape set is nonempty. -/
theorem escapeSet_nonempty (c : ℂ) : (Work.Bottcher.EscapeSet c).Nonempty := by
  refine ⟨((Work.Bottcher.escapeRadius c + 1 : ℝ) : ℂ), ?_⟩
  rw [Work.Bottcher.mem_EscapeSet]
  refine Work.Bottcher.Contraction.green_pos_of_escapeRadius_le c ?_
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [escapeRadius_pos' c])]
  linarith [escapeRadius_pos' c]

/-! ## Analyticity and non-vanishing of `normFactor` -/

/-- `normFactor c` is differentiable off `0`. -/
theorem differentiableOn_normFactor (c : ℂ) :
    DifferentiableOn ℂ (Work.Bottcher.normFactor c) {z : ℂ | z ≠ 0} :=
  fun z hz =>
    (Work.Bottcher.Core.hasDerivAt_normFactor c z hz).differentiableAt.differentiableWithinAt

/-- `normFactor c` is continuous off `0`. -/
theorem continuousOn_normFactor (c : ℂ) :
    ContinuousOn (Work.Bottcher.normFactor c) {z : ℂ | z ≠ 0} :=
  (differentiableOn_normFactor c).continuousOn

/-- At a mandelbar parameter, `normFactor c` is analytic on the escape set. -/
theorem analyticOnNhd_normFactor (c : ℂ) (hc : c ∈ Mandelbar) :
    AnalyticOnNhd ℂ (Work.Bottcher.normFactor c) (Work.Bottcher.EscapeSet c) := by
  refine DifferentiableOn.analyticOnNhd ?_ (isOpen_escapeSet c)
  refine (differentiableOn_normFactor c).mono ?_
  intro z hz hz0
  rw [hz0] at hz
  rw [Work.Bottcher.mem_EscapeSet, green_self_eq_zero c hc] at hz
  exact lt_irrefl 0 hz

/-- At a mandelbar parameter, `normFactor c` does not vanish on the escape set. -/
theorem normFactor_ne_zero_of_green_pos (c : ℂ) (hc : c ∈ Mandelbar) {z : ℂ}
    (hz : 0 < Work.Bottcher.green c z) : Work.Bottcher.normFactor c z ≠ 0 := by
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, green_self_eq_zero c hc] at hz
    exact lt_irrefl 0 hz
  rw [Work.Bottcher.normFactor, div_ne_zero_iff]
  refine ⟨?_, pow_ne_zero 4 hz0⟩
  intro hp
  have h1 := Work.Bottcher.Inverse.green_pMap c z
  rw [hp, green_self_eq_zero c hc] at h1
  have h2 : Work.Bottcher.green c z = 0 := by linarith
  linarith

/-! ## Behaviour at infinity -/

theorem tendsto_normFactor_cocompact (c : ℂ) :
    Tendsto (Work.Bottcher.normFactor c) (cocompact ℂ) (nhds (1 : ℂ)) := by
  rw [← Metric.cobounded_eq_cocompact]
  exact Work.Bottcher.Series.tendsto_normFactor_atCobounded c

theorem tendsto_log_normFactor_cocompact (c : ℂ) :
    Tendsto (fun z : ℂ => Complex.log (Work.Bottcher.normFactor c z))
      (cocompact ℂ) (nhds (0 : ℂ)) := by
  rw [← Metric.cobounded_eq_cocompact]
  exact Work.Bottcher.Series.tendsto_log_normFactor_atCobounded c

/-- The open far region is eventually cocompact. -/
theorem eventually_farRegion (c : ℂ) :
    ∀ᶠ z : ℂ in cocompact ℂ, Work.Bottcher.escapeRadius c < ‖z‖ := by
  refine Filter.mem_of_superset
    (isCompact_closedBall (0 : ℂ) (Work.Bottcher.escapeRadius c)).compl_mem_cocompact ?_
  intro z hz
  rw [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right] at hz
  exact not_le.mp hz

/-- The open far region is preconnected. -/
theorem isPreconnected_farRegion (c : ℂ) :
    IsPreconnected {z : ℂ | Work.Bottcher.escapeRadius c < ‖z‖} :=
  (Work.Top.isPathConnected_norm_gt (le_of_lt (escapeRadius_pos' c))).isConnected.isPreconnected


/-- Given any analytic logarithm `L` of `normFactor c` on the escape set, subtract the
constant making it vanish at infinity. -/
theorem exists_normalized_log {c : ℂ} (hc : c ∈ Mandelbar) {L : ℂ → ℂ}
    (hLan : AnalyticOnNhd ℂ L (Work.Bottcher.EscapeSet c))
    (hLexp : ∀ z : ℂ, 0 < Work.Bottcher.green c z →
      Complex.exp (L z) = Work.Bottcher.normFactor c z) :
    ∃ L' : ℂ → ℂ, AnalyticOnNhd ℂ L' (Work.Bottcher.EscapeSet c) ∧
      (∀ z : ℂ, 0 < Work.Bottcher.green c z →
        Complex.exp (L' z) = Work.Bottcher.normFactor c z) ∧
      Tendsto L' (cocompact ℂ) (nhds (0 : ℂ)) := by
  set z₁ : ℂ := ((Work.Bottcher.escapeRadius c + 1 : ℝ) : ℂ) with hz₁def
  have hz₁far : Work.Bottcher.escapeRadius c < ‖z₁‖ := by
    rw [hz₁def, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith [escapeRadius_pos' c])]
    linarith [escapeRadius_pos' c]
  have hz₁mem : 0 < Work.Bottcher.green c z₁ :=
    Work.Bottcher.Contraction.green_pos_of_escapeRadius_le c (le_of_lt hz₁far)
  have hz₁ne : Work.Bottcher.normFactor c z₁ ≠ 0 :=
    normFactor_ne_zero_of_green_pos c hc hz₁mem
  have hexpd : Complex.exp (L z₁ - Complex.log (Work.Bottcher.normFactor c z₁)) = 1 := by
    rw [Complex.exp_sub, hLexp z₁ hz₁mem, Complex.exp_log hz₁ne, div_self hz₁ne]
  refine ⟨fun z => L z - (L z₁ - Complex.log (Work.Bottcher.normFactor c z₁)),
    hLan.sub analyticOnNhd_const, ?_, ?_⟩
  · intro z hz
    rw [Complex.exp_sub, hLexp z hz, div_eq_mul_inv, hexpd, inv_one, mul_one]
  · have hFsub : {z : ℂ | Work.Bottcher.escapeRadius c < ‖z‖} ⊆ Work.Bottcher.EscapeSet c :=
      fun z hz => Work.Bottcher.mem_EscapeSet.mpr
        (Work.Bottcher.Contraction.green_pos_of_escapeRadius_le c (le_of_lt hz))
    have hslit : ∀ z ∈ {z : ℂ | Work.Bottcher.escapeRadius c < ‖z‖},
        Work.Bottcher.normFactor c z ∈ Complex.slitPlane := by
      intro z hz
      have hz' : Work.Bottcher.escapeRadius c < ‖z‖ := hz
      refine Work.Bottcher.Core.normFactor_mem_slitPlane c z ?_
      have hle : (1 + ‖c‖) ≤ Work.Bottcher.escapeRadius c := by
        rw [Work.Bottcher.escapeRadius]; nlinarith [norm_nonneg c]
      linarith
    have hg : ∀ z ∈ {z : ℂ | Work.Bottcher.escapeRadius c < ‖z‖},
        Complex.exp (L z - Complex.log (Work.Bottcher.normFactor c z)) = 1 := by
      intro z hz
      rw [Complex.exp_sub, Complex.exp_log (Complex.slitPlane_ne_zero (hslit z hz)),
        hLexp z (hFsub hz), div_self (normFactor_ne_zero_of_green_pos c hc (hFsub hz))]
    have hcont_g : ContinuousOn (fun z => L z - Complex.log (Work.Bottcher.normFactor c z))
        {z : ℂ | Work.Bottcher.escapeRadius c < ‖z‖} := by
      have hlog : DifferentiableOn ℂ (fun z => Complex.log (Work.Bottcher.normFactor c z))
          {z : ℂ | Work.Bottcher.escapeRadius c < ‖z‖} :=
        ((differentiableOn_normFactor c).mono (fun z hz hz0 => by
          have hz' : Work.Bottcher.escapeRadius c < ‖z‖ := hz
          rw [hz0, norm_zero] at hz'
          exact absurd hz' (not_lt.mpr (le_of_lt (escapeRadius_pos' c))))).clog hslit
      exact ContinuousOn.sub (hLan.continuousOn.mono hFsub) hlog.continuousOn
    have hkey : ∀ z ∈ {z : ℂ | Work.Bottcher.escapeRadius c < ‖z‖},
        L z - Complex.log (Work.Bottcher.normFactor c z)
          = L z₁ - Complex.log (Work.Bottcher.normFactor c z₁) := by
      intro z hz
      refine Complex.isCoveringMap_exp.constOn_of_comp
        (isPreconnected_farRegion c) hcont_g ?_ hz ?_
      · intro a ha a' ha'
        have h1 : Complex.exp (L a - Complex.log (Work.Bottcher.normFactor c a)) = 1 := hg a ha
        have h2 : Complex.exp (L a' - Complex.log (Work.Bottcher.normFactor c a')) = 1 := hg a' ha'
        apply Subtype.ext
        show Complex.exp (L a - Complex.log (Work.Bottcher.normFactor c a))
            = Complex.exp (L a' - Complex.log (Work.Bottcher.normFactor c a'))
        rw [h1, h2]
      · exact hz₁far
    have hev : (fun z => L z - (L z₁ - Complex.log (Work.Bottcher.normFactor c z₁)))
        =ᶠ[cocompact ℂ] (fun z => Complex.log (Work.Bottcher.normFactor c z)) := by
      filter_upwards [eventually_farRegion c] with z hz
      have h := hkey z hz
      rw [← h]; ring
    exact (tendsto_log_normFactor_cocompact c).congr' hev.symm

theorem exists_analytic_log_normFactor_of_mem_mandelbar (c : ℂ)
    (hc : c ∈ LeanEval.ComplexAnalysis.Mandelbar) :
    ∃ L : ℂ → ℂ,
      AnalyticOnNhd ℂ L (Work.Bottcher.EscapeSet c) ∧
        (∀ z : ℂ, 0 < Work.Bottcher.green c z →
          Complex.exp (L z) = Work.Bottcher.pMap c z / z ^ 4) ∧
        Filter.Tendsto L (Filter.cocompact ℂ) (nhds (0 : ℂ)) := by
  have hK : IsConnected {z : ℂ | Work.Bottcher.green c z = 0} :=
    isConnected_filledJulia_of_mem_mandelbar c hc
  have hf : AnalyticOnNhd ℂ (Work.Bottcher.normFactor c) (Work.Bottcher.EscapeSet c) :=
    analyticOnNhd_normFactor c hc
  have hne : ∀ z ∈ Work.Bottcher.EscapeSet c, Work.Bottcher.normFactor c z ≠ 0 :=
    fun z hz => normFactor_ne_zero_of_green_pos c hc hz
  have hmono : ∀ (γ : C(unitInterval, ℂ)) (hγ : ∀ t, γ t ∈ Work.Bottcher.EscapeSet c),
      γ 0 = γ 1 →
      Work.Bottcher.Contraction.liftChange
        ⟨fun t => Work.Bottcher.normFactor c (γ t),
          hf.continuousOn.comp_continuous γ.continuous hγ⟩
        (fun t => hne (γ t) (hγ t)) = 0 := by
    intro γ hγ hloop
    exact liftChange_normFactor_eq_zero c hc hK γ hγ hloop
      (hf.continuousOn.comp_continuous γ.continuous hγ)
      (fun t => hne (γ t) (hγ t))
  obtain ⟨L, hLan, hLexp⟩ :=
    exists_analyticOnNhd_exp_eq_of_liftChange_eq_zero (isOpen_escapeSet c) (escapeSet_nonempty c)
      (Work.Bottcher.Contraction.isPreconnected_escapeSet c) hf hne hmono
  obtain ⟨L', hL'an, hL'exp, hL't⟩ := exists_normalized_log hc hLan hLexp
  refine ⟨L', hL'an, ?_, hL't⟩
  intro z hz
  rw [hL'exp z hz]
  rfl

end Work.Bottcher.Contraction2
