import Mathlib
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.ExtremalImports
import Submission.Lib.Unif2.Work.UnitGreen.Defs
import Submission.Lib.Unif2.MaxPrincipleRegion
import Submission.Lib.Unif2.Commons.Analysis.Complex.exists_ball_factorization_of_analyticAt_zero

/-!
# `‖g‖ ≤ exp (-E)` for `g` in the extremal family and `E` a unit Green function

Let `X` be a connected complex one-manifold, `E` a unit Green function at `x₀` (positive and
harmonic off `x₀`, logarithmic pole of coefficient one, decay at the ideal boundary), and
`g : X → ℂ` a holomorphic function with `‖g‖ ≤ 1` and `g x₀ = 0`.  Then `‖g x‖ ≤ exp (-E x)` for
every `x`.

This is the sharp Schwarz–Pick estimate for the Green function.  The proof is the classical
$\varepsilon$-trick: for `0 < t < 1` the function `log ‖g‖ + t·E` is *bounded above near the pole*
(the pole of `t·E` is *weaker* than the zero of `g` there), so the maximum principle applies to it:
its superlevel set `{t·E + log ‖g‖ > t·s}` is open, relatively compact (as `log ‖g‖ ≤ 0` and the
superlevel sets of `E` are compact) and on its boundary the value is `t·s`; the strong maximum
principle then propagates the value along a clopen set, which is a contradiction.  Letting
`s ↓ 0` and then `t ↑ 1` gives the estimate with `E` itself.

The pole analysis uses the *quantitative* linear vanishing of `g` at its zero `x₀`
(`norm_le_mul_norm_chartAt_of_vanishing`), which together with the logarithmic bound on `E`
forces `log ‖g‖ + t·E → -∞` at the pole.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

noncomputable section

open Filter Set

namespace Work.SimplyConnected.ABS

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [SecondCountableTopology X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **An analytic function on `ℂ` vanishing at `c` is `O(‖z - c‖)` near `c`.** -/
theorem norm_le_mul_norm_sub_of_vanishing {f : ℂ → ℂ} {c : ℂ}
    (hf : AnalyticAt ℂ f c) (hfc : f c = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ z in 𝓝 c, z ≠ c → ‖f z‖ ≤ C * ‖z - c‖ := by
  by_cases h : ∀ᶠ z in 𝓝 c, f z = 0
  · refine ⟨1, one_pos, ?_⟩
    filter_upwards [h] with z hz _
    rw [hz, norm_zero]
    positivity
  · obtain ⟨R, k, ψ, hR0, hR1, hk1, hψan, _hψne, hψeq⟩ :=
      Commons.Analysis.Complex.exists_ball_factorization_of_analyticAt_zero (ρ := 1)
        one_pos hf hfc h
    have hψc : AnalyticAt ℂ ψ c := hψan c (Metric.mem_ball_self hR0)
    have hevψ : ∀ᶠ z in 𝓝 c, ‖ψ z‖ ≤ ‖ψ c‖ + 1 := by
      have htend : Tendsto (fun z : ℂ => ‖ψ z‖) (𝓝 c) (𝓝 ‖ψ c‖) :=
        hψc.continuousAt.tendsto.norm
      filter_upwards [htend.eventually (Iio_mem_nhds (lt_add_one (‖ψ c‖)))] with z hz
      exact le_of_lt hz
    have hball : ∀ᶠ z in 𝓝 c, z ∈ Metric.ball c R :=
      Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hR0)
    refine ⟨‖ψ c‖ + 1, by positivity, ?_⟩
    filter_upwards [hevψ, hball] with z hzψ hzR hzne
    have hr1 : ‖z - c‖ < 1 := lt_of_lt_of_le (by simpa [dist_eq_norm] using hzR) (le_of_lt hR1)
    have hpow : ‖z - c‖ ^ k ≤ ‖z - c‖ := by
      have hk : k - 1 + 1 = k := Nat.sub_add_cancel hk1
      have h1 : ‖z - c‖ ^ (k - 1) ≤ 1 := pow_le_one₀ (norm_nonneg _) (le_of_lt hr1)
      calc ‖z - c‖ ^ k = ‖z - c‖ ^ (k - 1 + 1) := by rw [hk]
        _ = ‖z - c‖ ^ (k - 1) * ‖z - c‖ := pow_succ _ _
        _ ≤ 1 * ‖z - c‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
        _ = ‖z - c‖ := one_mul _
    calc ‖f z‖ = ‖z - c‖ ^ k * ‖ψ z‖ := by
          rw [hψeq z hzR, norm_mul, norm_pow]
      _ ≤ ‖z - c‖ * (‖ψ c‖ + 1) := mul_le_mul hpow hzψ (norm_nonneg _) (norm_nonneg _)
      _ = (‖ψ c‖ + 1) * ‖z - c‖ := by ring

/-- **A holomorphic function on `X` vanishing at `x₀` is `O(‖chart x - chart x₀‖)` near `x₀`.** -/
theorem norm_le_mul_norm_chartAt_of_vanishing {x₀ : X} {g : X → ℂ}
    (hhol : Submission.HolomorphicOnXAt g x₀) (h0 : g x₀ = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x in 𝓝 x₀, x ≠ x₀ →
      ‖g x‖ ≤ C * ‖(chartAt ℂ x₀) x - (chartAt ℂ x₀) x₀‖ := by
  set c := chartAt ℂ x₀ with hc
  set f : ℂ → ℂ := g ∘ c.symm with hfdef
  have hfsrc : x₀ ∈ c.source := mem_chart_source ℂ x₀
  have hsymm : c.symm (c x₀) = x₀ := c.left_inv hfsrc
  have hf_an : AnalyticAt ℂ f (c x₀) := hhol
  have hf0 : f (c x₀) = 0 := by
    simp only [hfdef, Function.comp_apply, hsymm]
    exact h0
  obtain ⟨C, hCpos, hev⟩ := norm_le_mul_norm_sub_of_vanishing hf_an hf0
  refine ⟨C, hCpos, ?_⟩
  have hctend : Tendsto c (𝓝 x₀) (𝓝 (c x₀)) := c.continuousAt hfsrc
  have hsrc : ∀ᶠ x in 𝓝 x₀, x ∈ c.source := c.open_source.mem_nhds hfsrc
  filter_upwards [hctend.eventually hev, hsrc] with x hx hxsrc hxne
  have hcx : c x ≠ c x₀ := fun h => hxne (c.injOn hxsrc hfsrc h)
  have h1 : f (c x) = g x := by
    simp only [hfdef, Function.comp_apply, c.left_inv hxsrc]
  rw [h1] at hx
  exact hx hcx

/-- `log ‖g‖` is harmonic at a point where `g` is holomorphic and non-zero. -/
theorem harmonicOnXAt_log_norm_of_holomorphicOnXAt {f : X → ℂ} {x : X}
    (hf : Submission.HolomorphicOnXAt f x) (hne : f x ≠ 0) :
    Submission.HarmonicOnXAt (fun y => Real.log ‖f y‖) x := by
  rw [Submission.HarmonicOnXAt]
  have hana : AnalyticAt ℂ (f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) := hf
  have hval : (f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) = f x := by
    simp only [Function.comp_apply]
    rw [(chartAt ℂ x).left_inv (mem_chart_source ℂ x)]
  have hne' : (f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) ≠ 0 := by
    rw [hval]; exact hne
  exact hana.harmonicAt_log_norm hne'

theorem norm_le_exp_neg_of_unitGreen {X : Type*} [TopologicalSpace X] [T2Space X]
    [ConnectedSpace X] [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] {x₀ : X} {E : X → ℝ}
    (hE : Work.UnitGreen.IsUnitGreenFunctionAt x₀ E) {g : X → ℂ}
    (hg : g ∈ Submission.extremalFamily x₀) :
    ∀ x : X, ‖g x‖ ≤ Real.exp (-(E x)) := by
  classical
  have hhol : Submission.HolomorphicOnX g Set.univ := hg.1
  have hbd : ∀ x : X, ‖g x‖ ≤ 1 := hg.2.1
  have hg0 : g x₀ = 0 := hg.2.2
  have hcontg : Continuous g := hhol.continuous
  have hEpos : ∀ x : X, x ≠ x₀ → 0 < E x := hE.1.1
  have hEharm : Submission.HarmonicOnX E (Set.univ \ {x₀}) := hE.1.2.1
  have hEcpt : ∀ ε : ℝ, 0 < ε → IsCompact (closure {x : X | ε ≤ E x}) := hE.1.2.2
  obtain ⟨C₂, V₂, hV₂mem, hEbound⟩ := hE.2
  obtain ⟨C₁, hC₁pos, hlin⟩ :=
    norm_le_mul_norm_chartAt_of_vanishing (hhol x₀ (Set.mem_univ x₀)) hg0
  have hchart_src : x₀ ∈ (chartAt ℂ x₀).source := mem_chart_source ℂ x₀
  -- The bound with `E` replaced by `t·E`, `t < 1`.
  have key : ∀ t : ℝ, 0 < t → t < 1 → ∀ y : X, g y ≠ 0 →
      Real.log ‖g y‖ + t * E y ≤ 0 := by
    intro t ht ht1 y hy
    have hbound : ∀ s : ℝ, 0 < s → Real.log ‖g y‖ + t * E y ≤ t * s := by
      intro s hs
      by_contra hcon
      rw [not_le] at hcon
      -- the comparison function and the superlevel region
      set v : X → ℝ := fun z => Real.log ‖g z‖ + t * E z with hv
      have hvapply : ∀ z : X, v z = Real.log ‖g z‖ + t * E z := fun z => rfl
      set Ω : Set X := {z : X | g z ≠ 0 ∧ t * s < v z} with hΩ
      have hyΩ : y ∈ Ω := ⟨hy, by rw [hvapply]; exact hcon⟩
      -- harmonicity of `v` off the pole and off the zeros of `g`
      have hv_harm : ∀ z : X, z ≠ x₀ → g z ≠ 0 → Submission.HarmonicOnXAt v z := by
        intro z hzx hgz
        have h1 : Submission.HarmonicOnXAt (fun w : X => Real.log ‖g w‖) z :=
          harmonicOnXAt_log_norm_of_holomorphicOnXAt (hhol z (Set.mem_univ z)) hgz
        have h2 : Submission.HarmonicOnXAt (fun w : X => t * E w) z :=
          (hEharm z ⟨Set.mem_univ z, hzx⟩).const_smul t
        have h3 : Submission.HarmonicOnXAt (fun w : X => Real.log ‖g w‖ + t * E w) z :=
          h1.add h2
        rw [hv]
        exact h3
      -- `Ω` is open
      have hΩopen : IsOpen Ω := by
        have hU1 : IsOpen {z : X | g z ≠ 0} := by
          rw [show {z : X | g z ≠ 0} = (g ⁻¹' ({0} : Set ℂ))ᶜ by
            ext z; simp]
          exact (isClosed_singleton.preimage hcontg).isOpen_compl
        have hUopen : IsOpen ({z : X | g z ≠ 0} ∩ {z : X | z ≠ x₀}) :=
          hU1.inter isOpen_compl_singleton
        have hcontv : ContinuousOn v ({z : X | g z ≠ 0} ∩ {z : X | z ≠ x₀}) := by
          intro z hz
          exact (hv_harm z hz.2 hz.1).continuousAt.continuousWithinAt
        have hset : Ω =
            ({z : X | g z ≠ 0} ∩ {z : X | z ≠ x₀}) ∩ v ⁻¹' (Set.Ioi (t * s)) := by
          rw [hΩ]
          ext z
          constructor
          · rintro ⟨hgz, hgt⟩
            exact ⟨⟨hgz, fun h => hgz (by rw [h]; exact hg0)⟩, hgt⟩
          · rintro ⟨⟨hgz, _⟩, hgt⟩
            exact ⟨hgz, hgt⟩
        rw [hset]
        exact hcontv.isOpen_inter_preimage hUopen isOpen_Ioi
      -- `Ω` is contained in a superlevel set of `E`
      have hΩsub : Ω ⊆ {z : X | s ≤ E z} := by
        intro z hz
        rw [hΩ] at hz
        obtain ⟨hgz, hgt⟩ := hz
        have hlog : Real.log ‖g z‖ ≤ 0 := Real.log_nonpos (norm_nonneg _) (hbd z)
        have h1 : t * s < t * E z := by
          have h2 : v z ≤ t * E z := by rw [hvapply]; linarith
          linarith
        exact le_of_lt (lt_of_mul_lt_mul_left h1 (le_of_lt ht))
      have hΩcompact : IsCompact (closure Ω) :=
        IsCompact.of_isClosed_subset (hEcpt s hs) isClosed_closure (closure_mono hΩsub)
      -- `log ‖g‖ + t·E` tends to `-∞` at the pole
      have hEev : ∀ᶠ z in 𝓝 x₀, z ≠ x₀ →
          E z ≤ -Real.log ‖(chartAt ℂ x₀) z - (chartAt ℂ x₀) x₀‖ + C₂ := by
        filter_upwards [hV₂mem] with z hz hzne
        have h := (abs_le.mp (hEbound z hz hzne)).2
        linarith
      have hctend : Tendsto (fun z : X => (chartAt ℂ x₀) z) (𝓝 x₀)
          (𝓝 ((chartAt ℂ x₀) x₀)) := (chartAt ℂ x₀).continuousAt hchart_src
      have hrt : Tendsto (fun z : X => ‖(chartAt ℂ x₀) z - (chartAt ℂ x₀) x₀‖)
          (𝓝[≠] x₀) (𝓝[≠] (0 : ℝ)) := by
        rw [tendsto_nhdsWithin_iff]
        refine ⟨?_, ?_⟩
        · have h0 : Tendsto (fun z : X => (chartAt ℂ x₀) z - (chartAt ℂ x₀) x₀)
              (𝓝 x₀) (𝓝 0) := by
            have h1 := hctend.sub (tendsto_const_nhds :
              Tendsto (fun _ : X => (chartAt ℂ x₀) x₀) (𝓝 x₀) (𝓝 ((chartAt ℂ x₀) x₀)))
            simpa using h1
          simpa using h0.norm.mono_left nhdsWithin_le_nhds
        · have hsrcmem : (chartAt ℂ x₀).source ∈ 𝓝[≠] x₀ :=
            nhdsWithin_le_nhds ((chartAt ℂ x₀).open_source.mem_nhds hchart_src)
          filter_upwards [self_mem_nhdsWithin, hsrcmem] with z hzne hzsrc
          exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr
            (fun h => hzne ((chartAt ℂ x₀).injOn hzsrc hchart_src h)))
      have hscaled : Tendsto (fun z : X =>
          (1 - t) * Real.log ‖(chartAt ℂ x₀) z - (chartAt ℂ x₀) x₀‖) (𝓝[≠] x₀) atBot :=
        Tendsto.const_mul_atBot (by linarith : (0 : ℝ) < 1 - t)
          (Real.tendsto_log_nhdsNE_zero.comp hrt)
      have hthresh : ∀ᶠ z in 𝓝 x₀, z ≠ x₀ →
          (1 - t) * Real.log ‖(chartAt ℂ x₀) z - (chartAt ℂ x₀) x₀‖
            < t * s - Real.log C₁ - t * C₂ :=
        eventually_nhdsWithin_iff.mp (hscaled.eventually (eventually_lt_atBot _))
      have hpole : ∀ᶠ z in 𝓝 x₀, g z = 0 ∨ v z ≤ t * s := by
        filter_upwards [hEev, hlin, hthresh, (chartAt ℂ x₀).open_source.mem_nhds hchart_src]
          with z hEz hlinz hthz hzsrc
        by_cases hgz : g z = 0
        · exact Or.inl hgz
        · have hzx : z ≠ x₀ := fun h => hgz (by rw [h]; exact hg0)
          have hrpos : 0 < ‖(chartAt ℂ x₀) z - (chartAt ℂ x₀) x₀‖ :=
            norm_pos_iff.mpr (sub_ne_zero.mpr
              (fun h => hzx ((chartAt ℂ x₀).injOn hzsrc hchart_src h)))
          have h1 : Real.log ‖g z‖
              ≤ Real.log C₁ + Real.log ‖(chartAt ℂ x₀) z - (chartAt ℂ x₀) x₀‖ := by
            rw [← Real.log_mul (ne_of_gt hC₁pos) (ne_of_gt hrpos)]
            exact Real.log_le_log (norm_pos_iff.mpr hgz) (hlinz hzx)
          have h2 : t * E z
              ≤ t * C₂ - t * Real.log ‖(chartAt ℂ x₀) z - (chartAt ℂ x₀) x₀‖ := by
            have h3 : t * E z ≤ t * (-Real.log ‖(chartAt ℂ x₀) z - (chartAt ℂ x₀) x₀‖ + C₂) :=
              mul_le_mul_of_nonneg_left (hEz hzx) (le_of_lt ht)
            have h4 : t * (-Real.log ‖(chartAt ℂ x₀) z - (chartAt ℂ x₀) x₀‖ + C₂)
                = t * C₂ - t * Real.log ‖(chartAt ℂ x₀) z - (chartAt ℂ x₀) x₀‖ := by ring
            rw [h4] at h3
            exact h3
          refine Or.inr ?_
          have h5 : v z ≤ (Real.log C₁ + t * C₂)
              + (1 - t) * Real.log ‖(chartAt ℂ x₀) z - (chartAt ℂ x₀) x₀‖ := by
            rw [hvapply]
            nlinarith [h1, h2]
          have h6 : (Real.log C₁ + t * C₂)
              + (1 - t) * Real.log ‖(chartAt ℂ x₀) z - (chartAt ℂ x₀) x₀‖ < t * s := by
            linarith [hthz hzx]
          linarith [h5, h6]
      -- zeros of `g` away from the pole do not accumulate on `Ω`
      have hzero : ∀ y : X, g y = 0 → y ≠ x₀ →
          ∀ᶠ z in 𝓝 y, g z = 0 ∨ v z ≤ t * s := by
        intro y hy0 hyx
        have hcontEy : ContinuousAt E y := (hEharm y ⟨Set.mem_univ y, hyx⟩).continuousAt
        have hevE : ∀ᶠ z in 𝓝 y, E z ≤ E y + 1 := by
          filter_upwards [hcontEy.eventually (Iio_mem_nhds (lt_add_one (E y)))] with z hz
          exact le_of_lt hz
        have htendg : Tendsto (fun z : X => ‖g z‖) (𝓝 y) (𝓝 0) := by
          have h1 : Tendsto g (𝓝 y) (𝓝 (g y)) :=
            (hhol y (Set.mem_univ y)).continuousAt.tendsto
          rw [hy0] at h1
          simpa using h1.norm
        have hevg : ∀ᶠ z in 𝓝 y, ‖g z‖ < Real.exp (t * s - t * (E y + 1)) :=
          htendg.eventually (Iio_mem_nhds (Real.exp_pos _))
        filter_upwards [hevE, hevg] with z hzE hzg
        by_cases hgz : g z = 0
        · exact Or.inl hgz
        · refine Or.inr ?_
          have hlogz : Real.log ‖g z‖ < t * s - t * (E y + 1) :=
            (Real.log_lt_iff_lt_exp (norm_pos_iff.mpr hgz)).mpr hzg
          have h1 : t * E z ≤ t * (E y + 1) := mul_le_mul_of_nonneg_left hzE (le_of_lt ht)
          have h2 : Real.log ‖g z‖ + t * E z
              < (t * s - t * (E y + 1)) + t * (E y + 1) := add_lt_add_of_lt_of_le hlogz h1
          have h3 : (t * s - t * (E y + 1)) + t * (E y + 1) = t * s := by ring
          calc v z = Real.log ‖g z‖ + t * E z := hvapply z
            _ ≤ t * s := le_of_lt (h3 ▸ h2)
      have hnotmem : ∀ y : X, g y = 0 → y ∉ closure Ω := by
        intro y hy0
        have hev : ∀ᶠ z in 𝓝 y, g z = 0 ∨ v z ≤ t * s := by
          by_cases hyx : y = x₀
          · subst hyx; exact hpole
          · exact hzero y hy0 hyx
        have h1 : ∀ᶠ z in 𝓝 y, z ∉ Ω := by
          filter_upwards [hev] with z hz hzΩ
          rw [hΩ] at hzΩ
          rcases hz with h | h
          · exact hzΩ.1 h
          · exact absurd hzΩ.2 (not_lt.mpr h)
        have h2 : Ωᶜ ∈ 𝓝 y := h1
        intro hycl
        rw [closure_eq_compl_interior_compl] at hycl
        exact hycl (mem_interior_iff_mem_nhds.mpr h2)
      have hclsub : closure Ω ⊆ {z : X | g z ≠ 0} := by
        intro z hz
        by_contra hgz
        exact hnotmem z (not_ne_iff.mp hgz) hz
      have hcontvΩ : ContinuousOn v (closure Ω) := by
        intro z hz
        have hgz : g z ≠ 0 := hclsub hz
        have hzx : z ≠ x₀ := fun h => hgz (by rw [h]; exact hg0)
        exact (hv_harm z hzx hgz).continuousAt.continuousWithinAt
      -- the maximum of `v` on `closure Ω`
      obtain ⟨p, hp_mem, hp_max⟩ := hΩcompact.exists_isMaxOn ⟨y, subset_closure hyΩ⟩ hcontvΩ
      have hyv : t * s < v y := by rw [hvapply]; exact hcon
      have hpv : t * s < v p := lt_of_lt_of_le hyv (hp_max (subset_closure hyΩ))
      have hpΩ : p ∈ Ω := ⟨hclsub hp_mem, hpv⟩
      have hpnx : p ≠ x₀ := fun h => hpΩ.1 (by rw [h]; exact hg0)
      have hΩint : Ω ⊆ interior (closure Ω) := interior_maximal subset_closure hΩopen
      have hcl_nhds : closure Ω ∈ 𝓝 p :=
        Filter.mem_of_superset (isOpen_interior.mem_nhds (hΩint hpΩ)) interior_subset
      -- the level set `{v = v p} ∩ {g ≠ 0}` is clopen and non-empty
      set W : Set X := {z : X | g z ≠ 0 ∧ v z = v p} with hW
      have hWne : W.Nonempty := ⟨p, hpΩ.1, rfl⟩
      have hWopen : IsOpen W := by
        rw [isOpen_iff_mem_nhds]
        intro z hzW
        rw [hW] at hzW
        obtain ⟨hgz, hzv⟩ := hzW
        have hzΩ : z ∈ Ω := ⟨hgz, by rw [hzv]; exact hpv⟩
        have hzx : z ≠ x₀ := fun h => hgz (by rw [h]; exact hg0)
        have hsub_z : Submission.SubharmonicOnXAt v z := (hv_harm z hzx hgz).subharmonic
        have hcl_nhds_z : closure Ω ∈ 𝓝 z :=
          Filter.mem_of_superset (isOpen_interior.mem_nhds (hΩint hzΩ)) interior_subset
        obtain ⟨V', hV'mem, hV'eq⟩ :=
          hsub_z.eqOn_of_le (U := closure Ω) hcl_nhds_z (fun w hw => by rw [hzv]; exact hp_max hw)
        have hgne : ∀ᶠ w in 𝓝 z, g w ≠ 0 :=
          (hhol z (Set.mem_univ z)).continuousAt.eventually_ne hgz
        filter_upwards [hV'mem, hgne] with w hw hgw
        rw [hW]
        exact ⟨hgw, by rw [hV'eq w hw, hzv]⟩
      have hWclosed : IsClosed W := by
        rw [← closure_subset_iff_isClosed]
        intro z hz
        have hzΩcl : z ∈ closure Ω :=
          closure_mono (fun w hw => by rw [hW] at hw; exact ⟨hw.1, by rw [hw.2]; exact hpv⟩) hz
        have hgz : g z ≠ 0 := hclsub hzΩcl
        have hzx : z ≠ x₀ := fun h => hgz (by rw [h]; exact hg0)
        have hcont_z : ContinuousAt v z := (hv_harm z hzx hgz).continuousAt
        haveI hnb : (𝓝[W] z).NeBot := (mem_closure_iff_nhdsWithin_neBot).mp hz
        have h1 : Tendsto v (𝓝[W] z) (𝓝 (v z)) := hcont_z.continuousWithinAt.tendsto
        have h2 : Tendsto v (𝓝[W] z) (𝓝 (v p)) := by
          refine tendsto_const_nhds.congr' ?_
          filter_upwards [self_mem_nhdsWithin] with w hw
          rw [hW] at hw
          exact hw.2.symm
        have hzv : v z = v p := tendsto_nhds_unique h1 h2
        rw [hW]
        exact ⟨hgz, hzv⟩
      have hpW : p ∈ W := by rw [hW]; exact ⟨hpΩ.1, rfl⟩
      have huniv : (Set.univ : Set X) ⊆ W :=
        isPreconnected_univ.subset_isClopen ⟨hWclosed, hWopen⟩
          ⟨p, Set.mem_univ p, hpW⟩
      have hfinal : g x₀ ≠ 0 := by
        have h1 : x₀ ∈ W := huniv (Set.mem_univ x₀)
        rw [hW] at h1
        exact h1.1
      exact hfinal hg0
    -- let `s ↓ 0`
    have hle0 : Real.log ‖g y‖ + t * E y ≤ 0 := by
      refine le_of_forall_pos_le_add ?_
      intro ε hε
      have hpos : 0 < ε / t := div_pos hε ht
      have h1 := hbound (ε / t) hpos
      have h2 : t * (ε / t) = ε := by field_simp
      linarith
    exact hle0
  -- assemble
  intro x
  by_cases hx : g x = 0
  · rw [hx, norm_zero]
    exact (Real.exp_pos _).le
  · have hxn : x ≠ x₀ := fun h => hx (by rw [h]; exact hg0)
    have hEx : 0 < E x := hEpos x hxn
    have hev : ∀ᶠ t in 𝓝[<] (1 : ℝ), Real.log ‖g x‖ ≤ -(t * E x) := by
      have h1 : ∀ᶠ t in 𝓝[<] (1 : ℝ), (1 / 2 : ℝ) < t :=
        nhdsWithin_le_nhds (Ioi_mem_nhds (by norm_num))
      have h2 : ∀ᶠ t in 𝓝[<] (1 : ℝ), t < 1 := self_mem_nhdsWithin
      filter_upwards [h1, h2] with t ht1 ht2
      have h3 := key t (by linarith) ht2 x hx
      linarith
    have htend : Tendsto (fun t : ℝ => -(t * E x)) (𝓝[<] (1 : ℝ)) (𝓝 (-(E x))) := by
      have h1 : Tendsto (fun t : ℝ => t) (𝓝[<] (1 : ℝ)) (𝓝 (1 : ℝ)) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      have h2 : Tendsto (fun t : ℝ => t * E x) (𝓝[<] (1 : ℝ)) (𝓝 (1 * E x)) :=
        h1.mul_const (E x)
      simpa using h2.neg
    have hlog' : Real.log ‖g x‖ ≤ -(E x) := ge_of_tendsto htend hev
    calc ‖g x‖ = Real.exp (Real.log ‖g x‖) := (Real.exp_log (norm_pos_iff.mpr hx)).symm
      _ ≤ Real.exp (-(E x)) := Real.exp_le_exp.mpr hlog'

end Work.SimplyConnected.ABS
