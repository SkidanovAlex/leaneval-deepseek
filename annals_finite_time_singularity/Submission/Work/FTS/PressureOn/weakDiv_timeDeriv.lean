import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Trace
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Work.FTS.PressureOn.Defs
import Submission.Work.FTS.PressureOn.integral_div_eq_zero_of_hasFDerivAt

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `weakDiv_timeDeriv` — the divergence-free condition survives time differentiation

For a velocity field `u` whose spatial slices `u · s` are `C¹` and divergence-free for `s ≥ t` close
to `t`, and which has a one-sided time derivative `∂ₜu(·,t)` at `t` with a Lipschitz-in-time
domination, the pairing of `∂ₜu(·,t)` against the gradient of a compactly supported smooth test
function `φ` vanishes:

`∫ x, ⟪∂ₜu(x,t), ∇φ(x)⟫ = 0`.

The proof has two halves:

* the **integration by parts** half, resting on the divergence theorem in `ℝ³` for a compactly
  supported `C¹` field (`integral_div_eq_zero_of_hasFDerivAt`).  Applied to `φ • v` it gives the
  identity `∫ ⟪∇φ, v⟫ = -∫ (div v) φ`; with `div v = 0` the slice pairing
  `s ↦ ∫ x, ⟪u(x,s), ∇φ(x)⟫` vanishes identically on `[t, t+ε)`
  (`integral_inner_gradient_eq_zero` below);
* the **differentiation under the integral sign** half (`tendsto_integral_slope_self` below), a
  fixed-filter dominated convergence theorem: as `s ↓ t` the integrals of the slopes
  `(s - t)⁻¹ • (u x s - u x t)` converge to the integral of `∂ₜu(·,t)`.

The slopes are the difference quotients of the slice pairing, which is eventually `0`; hence the
limit — the pairing of `∂ₜu(·,t)` against `∇φ` — is `0`.
-/

open MeasureTheory Filter Set Topology
open FiniteTimeSingularity

namespace Work.FTS.PressureOn

set_option maxHeartbeats 4000000

/-- **The divergence of a scalar multiple of a divergence-free field.**  The product rule for the
trace of the Jacobian, `div (φ • v) x = φ x * div v x + (fderiv ℝ φ x) (v x)`, combined with the
identification of `fderiv ℝ φ x (v x)` with `⟪∇φ x, v x⟫`. -/
lemma div_smul_eq_inner_gradient (φ : R3 → ℝ) (v : R3 → R3) (x : R3)
    (hφ : DifferentiableAt ℝ φ x) (hv : DifferentiableAt ℝ v x) (hdiv : div v = 0) :
    div (φ • v) x = inner ℝ (gradient φ x) (v x) := by
  have hsmul := fderiv_smul (𝕜 := ℝ) hφ hv
  have htrace : div (φ • v) x = φ x * div v x + fderiv ℝ φ x (v x) := by
    rw [div, div, hsmul]
    rw [ContinuousLinearMap.toLinearMap_add, ContinuousLinearMap.toLinearMap_smul,
      ContinuousLinearMap.coe_smulRight]
    rw [map_add, map_smul, LinearMap.trace_smulRight, ContinuousLinearMap.coe_coe]
    ring
  rw [htrace, hdiv, Pi.zero_apply, mul_zero, zero_add, ← inner_gradient_left]

/-- An inner product whose **left** factor is compactly supported is compactly supported. -/
lemma hasCompactSupport_inner_left (w : R3 → R3) (hwcs : HasCompactSupport w) (g : R3 → R3) :
    HasCompactSupport (fun x => inner ℝ (w x) (g x)) := by
  refine HasCompactSupport.of_support_subset_isCompact hwcs ?_
  intro x hx
  rw [Function.mem_support] at hx
  exact subset_tsupport _ (by
    rw [Function.mem_support]
    intro h0
    exact hx (by simp [h0]))

/-- An inner product whose **right** factor is compactly supported is compactly supported. -/
lemma hasCompactSupport_inner_right (w : R3 → R3) (hwcs : HasCompactSupport w) (g : R3 → R3) :
    HasCompactSupport (fun x => inner ℝ (g x) (w x)) := by
  refine HasCompactSupport.of_support_subset_isCompact hwcs ?_
  intro x hx
  rw [Function.mem_support] at hx
  exact subset_tsupport _ (by
    rw [Function.mem_support]
    intro h0
    exact hx (by simp [h0]))

/-- **Integration by parts / weak divergence**: for a `C¹` divergence-free field `v` and a compactly
supported smooth test function `φ`, `∫ x, ⟪v x, ∇φ x⟫ = 0`.

Proof: put `G := φ • v`.  Then `G` is `C¹` with compact support, `div G = ⟪∇φ, v⟫`, and the
divergence theorem gives `∫ div G = 0`. -/
lemma integral_inner_gradient_eq_zero {v : R3 → R3} {φ : R3 → ℝ}
    (hv : ContDiff ℝ 1 v) (hdiv : div v = 0)
    (hφ : ∀ n : ℕ, ContDiff ℝ n φ) (hφcs : HasCompactSupport φ) :
    ∫ x, inner ℝ (v x) (gradient φ x) = 0 := by
  have hφ1 : ContDiff ℝ 1 φ := hφ 1
  have hφd : Differentiable ℝ φ := hφ1.differentiable (by norm_num)
  have hvd : Differentiable ℝ v := hv.differentiable (by norm_num)
  have hgradcont : Continuous (fun x => gradient φ x) := by
    have h : Continuous fun x => (InnerProductSpace.toDual ℝ R3).symm (fderiv ℝ φ x) :=
      (InnerProductSpace.toDual ℝ R3).symm.continuous.comp (hφ1.continuous_fderiv (by norm_num))
    simpa [gradient, Function.comp_def] using h
  have hgradcs : HasCompactSupport (fun x => gradient φ x) := by
    have h := (hφcs.fderiv ℝ).comp_left
      (g := fun L : R3 →L[ℝ] ℝ => (InnerProductSpace.toDual ℝ R3).symm L) (by simp)
    simpa [gradient, Function.comp_def] using h
  have hGcs : HasCompactSupport (φ • v) := hφcs.smul_right
  have hGcont : Continuous (φ • v) := hφ1.continuous.smul hv.continuous
  have hGdiff : ∀ x, HasFDerivAt (φ • v) (fderiv ℝ (φ • v) x) x := fun x =>
    (hφd.differentiableAt.smul hvd.differentiableAt).hasFDerivAt
  have hdivG : div (φ • v) = fun x => inner ℝ (gradient φ x) (v x) := by
    funext x
    exact div_smul_eq_inner_gradient φ v x hφd.differentiableAt hvd.differentiableAt hdiv
  have hGint : Integrable (div (φ • v)) := by
    rw [hdivG]
    exact (hgradcont.inner hv.continuous).integrable_of_hasCompactSupport
      (hasCompactSupport_inner_left _ hgradcs v)
  have h0 := integral_div_eq_zero_of_hasFDerivAt (φ • v) hGcs hGcont hGdiff hGint
  have hthis : (∫ x, inner ℝ (gradient φ x) (v x)) = 0 := by simpa [hdivG] using h0
  rw [← hthis]
  refine integral_congr_ae ?_
  filter_upwards with x
  rw [real_inner_comm (v x) (gradient φ x)]

/-- **Differentiation under the integral sign from the right.**  For a field `u` with

* a one-sided time derivative `∂ₜu(·,t)` at `t` (`hderiv`),
* a Lipschitz-in-time domination at `t` (`hlip`),
* slices continuous along `s ↓ t` (`hu`),

and a continuous compactly supported weight `w`, the integrals of the slopes `(s - t)⁻¹ • (u·s - u·t)`
against `w` converge, as `s ↓ t`, to the integral of `∂ₜu(·,t)` against `w`.

The proof is the dominated convergence theorem along the filter `𝓝[>] t`, with dominating function
`C ‖w‖` (the Lipschitz constant times the weight).  The measurability of the `t`-slice — the only
delicate point, since `u · t` is only known to be the pointwise limit of the continuous slices
`u · (t + η/(n+2))` — is obtained from that limit. -/
lemma tendsto_integral_slope_self {u : R3 → ℝ → R3} {t : ℝ} {w : R3 → R3}
    (hwcont : Continuous w) (hwcs : HasCompactSupport w)
    (hu : Filter.Eventually (fun s => Continuous (fun x => u x s)) (nhdsWithin t (Set.Ioi t)))
    (hderiv : ∀ x, HasDerivWithinAt (u x) (timeDeriv u x t) (Set.Ici t) t)
    (hlip : ∃ C, ∀ x, ∀ s ∈ Set.Ioo (t - 1) (t + 1), ‖u x s - u x t‖ ≤ C * |s - t|) :
    Filter.Tendsto (fun s => ∫ x, inner ℝ ((s - t)⁻¹ • (u x s - u x t)) (w x))
      (nhdsWithin t (Set.Ioi t)) (nhds (∫ x, inner ℝ (timeDeriv u x t) (w x))) := by
  obtain ⟨C, hC⟩ := hlip
  -- The `t`-slice is a.e. strongly measurable: it is the pointwise limit of the continuous slices
  -- `u · (t + η/(n+2))` along the right neighbourhood given by `hu`.
  have hmeas_t : AEStronglyMeasurable (fun x => u x t) volume := by
    rw [Filter.eventually_iff, Metric.mem_nhdsWithin_iff] at hu
    obtain ⟨δ, hδpos, hδ⟩ := hu
    set η : ℝ := min δ 1 with hη
    have hηpos : 0 < η := lt_min hδpos zero_lt_one
    have hηδ : η ≤ δ := min_le_left _ _
    have hη1 : η ≤ 1 := min_le_right _ _
    have hcont_n : ∀ n : ℕ, Continuous (fun x => u x (t + η / ((n : ℝ) + 2))) := by
      intro n
      have hpos : (0 : ℝ) < (n : ℝ) + 2 := by positivity
      have hlt : η / ((n : ℝ) + 2) < η := by
        have h1 : 1 < (n : ℝ) + 2 := by
          have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
          linarith
        exact div_lt_self hηpos h1
      have hsmall : η / ((n : ℝ) + 2) < δ := lt_of_lt_of_le hlt hηδ
      refine hδ ⟨?_, ?_⟩
      · rw [Metric.mem_ball, Real.dist_eq,
          show t + η / ((n : ℝ) + 2) - t = η / ((n : ℝ) + 2) by ring,
          abs_of_pos (div_pos hηpos hpos)]
        exact hsmall
      · exact lt_add_of_pos_right t (div_pos hηpos hpos)
    refine (measurable_of_tendsto_metrizable (f := fun n x => u x (t + η / ((n : ℝ) + 2)))
      (fun n => (hcont_n n).measurable) ?_).aestronglyMeasurable
    rw [tendsto_pi_nhds]
    intro x
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (f := fun n : ℕ => ‖u x (t + η / ((n : ℝ) + 2)) - u x t‖)
      (g := fun n : ℕ => C * (η / ((n : ℝ) + 2))) (fun n => norm_nonneg _) (fun n => ?_) ?_
    · have hpos : (0 : ℝ) < (n : ℝ) + 2 := by positivity
      have hlt1 : η / ((n : ℝ) + 2) < 1 := by
        rw [div_lt_one hpos]
        have h2 : (2 : ℝ) ≤ (n : ℝ) + 2 := by
          have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
          linarith
        linarith
      have hmem : (t + η / ((n : ℝ) + 2)) ∈ Set.Ioo (t - 1) (t + 1) := by
        have := div_pos hηpos hpos
        constructor <;> linarith
      calc ‖u x (t + η / ((n : ℝ) + 2)) - u x t‖
          ≤ C * |t + η / ((n : ℝ) + 2) - t| := hC x _ hmem
        _ = C * (η / ((n : ℝ) + 2)) := by
            rw [show t + η / ((n : ℝ) + 2) - t = η / ((n : ℝ) + 2) by ring,
              abs_of_pos (div_pos hηpos hpos)]
    · have hdiv : Tendsto (fun n : ℕ => η / ((n : ℝ) + 2)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop
          (tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop)
      simpa using hdiv.const_mul C
  -- Measurability of the integrands.
  have hmeas : ∀ᶠ s in nhdsWithin t (Set.Ioi t),
      AEStronglyMeasurable (fun x => inner ℝ ((s - t)⁻¹ • (u x s - u x t)) (w x)) volume := by
    filter_upwards [hu] with s hs
    have h1 : (fun x => inner ℝ ((s - t)⁻¹ • (u x s - u x t)) (w x))
        = (fun x => inner ℝ ((s - t)⁻¹ • u x s - (s - t)⁻¹ • u x t) (w x)) := by
      funext x; rw [smul_sub]
    rw [h1]
    exact AEStronglyMeasurable.inner
      ((hs.const_smul ((s - t)⁻¹)).aestronglyMeasurable.sub
        (hmeas_t.const_smul ((s - t)⁻¹))) hwcont.aestronglyMeasurable
  -- Domination by `C ‖w‖`.
  have hbound : ∀ᶠ s in nhdsWithin t (Set.Ioi t),
      ∀ᵐ x ∂volume, ‖inner ℝ ((s - t)⁻¹ • (u x s - u x t)) (w x)‖ ≤ C * ‖w x‖ := by
    rw [Filter.eventually_iff, Metric.mem_nhdsWithin_iff]
    refine ⟨1, one_pos, ?_⟩
    rintro s ⟨hs, hst⟩
    simp only [Set.mem_ofPred_eq]
    have hst' : t < s := hst
    have hsI : s ∈ Set.Ioo (t - 1) (t + 1) := by
      rw [Metric.mem_ball, Real.dist_eq] at hs
      constructor <;> linarith [(abs_lt.mp hs).1, (abs_lt.mp hs).2]
    have h0 : 0 < |s - t| := abs_pos.mpr (by linarith)
    filter_upwards with x
    calc ‖inner ℝ ((s - t)⁻¹ • (u x s - u x t)) (w x)‖
        ≤ ‖(s - t)⁻¹ • (u x s - u x t)‖ * ‖w x‖ := norm_inner_le_norm _ _
      _ = |s - t|⁻¹ * ‖u x s - u x t‖ * ‖w x‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_inv]
      _ ≤ |s - t|⁻¹ * (C * |s - t|) * ‖w x‖ := by
          gcongr
          exact hC x s hsI
      _ = C * ‖w x‖ := by
          rw [mul_comm C |s - t|, ← mul_assoc, inv_mul_cancel₀ (abs_ne_zero.mpr (by linarith)),
            one_mul]
  -- Pointwise convergence of the slopes to the one-sided time derivative.
  have hpt : ∀ᵐ x ∂volume, Tendsto (fun s => inner ℝ ((s - t)⁻¹ • (u x s - u x t)) (w x))
      (nhdsWithin t (Set.Ioi t)) (nhds (inner ℝ (timeDeriv u x t) (w x))) := by
    refine Filter.Eventually.of_forall (fun x => ?_)
    have hslope : Tendsto (fun s => slope (u x) t s) (nhdsWithin t (Set.Ioi t))
        (nhds (timeDeriv u x t)) := by
      have h := hasDerivWithinAt_iff_tendsto_slope.mp (hderiv x)
      rwa [show Set.Ici t \ {t} = Set.Ioi t from by
        ext y; simp [Set.mem_Ioi, lt_iff_le_and_ne]] at h
    have hc : Tendsto (fun _ : ℝ => w x) (nhdsWithin t (Set.Ioi t)) (nhds (w x)) :=
      tendsto_const_nhds
    have h2 := Filter.Tendsto.inner (𝕜 := ℝ) hslope hc
    simpa [slope, Function.comp_def] using h2
  have hbndint : Integrable (fun x => C * ‖w x‖) volume :=
    (hwcont.norm.integrable_of_hasCompactSupport hwcs.norm).const_mul C
  exact tendsto_integral_filter_of_dominated_convergence (fun x => C * ‖w x‖)
    hmeas hbound hbndint hpt

theorem weakDiv_timeDeriv {u : R3 → ℝ → R3} {t : ℝ} {φ : R3 → ℝ}
    (hφ : ∀ n : ℕ, ContDiff ℝ n φ) (hφcs : HasCompactSupport φ)
    (hnbhd : ∀ᶠ s in nhdsWithin t (Set.Ici t),
      ContDiff ℝ 1 (u · s) ∧ FiniteTimeSingularity.div (u · s) = 0)
    (hderiv : ∀ x, HasDerivWithinAt (u x) (FiniteTimeSingularity.timeDeriv u x t) (Set.Ici t) t)
    (hlip : ∃ C, ∀ x, ∀ s ∈ Set.Ioo (t - 1) (t + 1), ‖u x s - u x t‖ ≤ C * |s - t|) :
    ∫ x, inner ℝ (FiniteTimeSingularity.timeDeriv u x t) (gradient φ x) = 0 := by
  have hgradcont : Continuous (fun x => gradient φ x) := by
    have h : Continuous fun x => (InnerProductSpace.toDual ℝ R3).symm (fderiv ℝ φ x) :=
      (InnerProductSpace.toDual ℝ R3).symm.continuous.comp
        ((hφ 1).continuous_fderiv (by norm_num))
    simpa [gradient, Function.comp_def] using h
  have hgradcs : HasCompactSupport (fun x => gradient φ x) := by
    have h := (hφcs.fderiv ℝ).comp_left
      (g := fun L : R3 →L[ℝ] ℝ => (InnerProductSpace.toDual ℝ R3).symm L) (by simp)
    simpa [gradient, Function.comp_def] using h
  -- The right-neighbourhood on which the slices are `C¹` and divergence-free.
  rw [Filter.eventually_iff, Metric.mem_nhdsWithin_iff] at hnbhd
  obtain ⟨ε, hεpos, hε⟩ := hnbhd
  have hnb : ∀ s, dist s t < ε → t ≤ s →
      ContDiff ℝ 1 (fun x => u x s) ∧ div (fun x => u x s) = 0 :=
    fun s hs hts => hε ⟨hs, hts⟩
  -- The slice pairing vanishes on `[t, t+ε)`.
  have hA0 : ∀ s, t ≤ s → s < t + ε → (∫ x, inner ℝ (u x s) (gradient φ x)) = 0 := by
    intro s hts hs
    have hd : dist s t < ε := by
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hts)]
      linarith
    obtain ⟨hc, hd0⟩ := hnb s hd hts
    exact integral_inner_gradient_eq_zero hc hd0 hφ hφcs
  -- The slices stay continuous along `s ↓ t`.
  have hu : ∀ᶠ s in nhdsWithin t (Set.Ioi t), Continuous (fun x => u x s) := by
    rw [Filter.eventually_iff, Metric.mem_nhdsWithin_iff]
    refine ⟨ε, hεpos, ?_⟩
    rintro s ⟨hs, hst⟩
    exact ((hnb s hs (le_of_lt hst)).1).continuous
  have hlim := tendsto_integral_slope_self hgradcont hgradcs hu hderiv hlip
  -- Rewrite the difference quotients as integrals of the slopes.
  have hquot : ∀ᶠ s in nhdsWithin t (Set.Ioi t),
      (∫ x, inner ℝ ((s - t)⁻¹ • (u x s - u x t)) (gradient φ x))
        = ((∫ x, inner ℝ (u x s) (gradient φ x))
            - (∫ x, inner ℝ (u x t) (gradient φ x))) / (s - t) := by
    rw [Filter.eventually_iff, Metric.mem_nhdsWithin_iff]
    refine ⟨ε, hεpos, ?_⟩
    rintro s ⟨hs, hst⟩
    simp only [Set.mem_ofPred_eq]
    have hts : t ≤ s := le_of_lt hst
    obtain ⟨hc, _⟩ := hnb s hs hts
    have hct : ContDiff ℝ 1 (fun x => u x t) :=
      (hnb t (by rw [dist_self]; exact hεpos) le_rfl).1
    have hIs : Integrable (fun x => inner ℝ (u x s) (gradient φ x)) :=
      (hc.continuous.inner hgradcont).integrable_of_hasCompactSupport
        (hasCompactSupport_inner_right _ hgradcs _)
    have hIt : Integrable (fun x => inner ℝ (u x t) (gradient φ x)) :=
      (hct.continuous.inner hgradcont).integrable_of_hasCompactSupport
        (hasCompactSupport_inner_right _ hgradcs _)
    have hsub : (∫ x, inner ℝ (u x s - u x t) (gradient φ x))
        = (∫ x, inner ℝ (u x s) (gradient φ x))
          - (∫ x, inner ℝ (u x t) (gradient φ x)) := by
      rw [← integral_sub hIs hIt]
      refine integral_congr_ae ?_
      filter_upwards with x
      rw [inner_sub_left]
    have hsmul : (∫ x, inner ℝ ((s - t)⁻¹ • (u x s - u x t)) (gradient φ x))
        = (s - t)⁻¹ * (∫ x, inner ℝ (u x s - u x t) (gradient φ x)) := by
      rw [← integral_const_mul]
      refine integral_congr_ae ?_
      filter_upwards with x
      rw [real_inner_smul_left]
    rw [hsmul, hsub, div_eq_inv_mul]
  -- The difference quotients are eventually zero.
  have hQ0 : ∀ᶠ s in nhdsWithin t (Set.Ioi t),
      ((∫ x, inner ℝ (u x s) (gradient φ x))
        - (∫ x, inner ℝ (u x t) (gradient φ x))) / (s - t) = 0 := by
    rw [Filter.eventually_iff, Metric.mem_nhdsWithin_iff]
    refine ⟨ε, hεpos, ?_⟩
    rintro s ⟨hs, hst⟩
    simp only [Set.mem_ofPred_eq]
    have hts : t ≤ s := le_of_lt hst
    have hd : dist s t < ε := hs
    have hse : s < t + ε := by
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hts)] at hd
      linarith
    have h1 : (∫ x, inner ℝ (u x s) (gradient φ x)) = 0 := hA0 s hts hse
    have h2 : (∫ x, inner ℝ (u x t) (gradient φ x)) = 0 := hA0 t le_rfl (by linarith)
    rw [h1, h2, sub_zero, zero_div]
  have hQlim : Tendsto (fun s => ((∫ x, inner ℝ (u x s) (gradient φ x))
        - (∫ x, inner ℝ (u x t) (gradient φ x))) / (s - t))
      (nhdsWithin t (Set.Ioi t)) (nhds (∫ x, inner ℝ (timeDeriv u x t) (gradient φ x))) :=
    Tendsto.congr' hquot hlim
  have hQzero : Tendsto (fun s => ((∫ x, inner ℝ (u x s) (gradient φ x))
        - (∫ x, inner ℝ (u x t) (gradient φ x))) / (s - t))
      (nhdsWithin t (Set.Ioi t)) (nhds 0) :=
    Tendsto.congr' (hQ0.mono fun s hs => hs.symm) tendsto_const_nhds
  exact tendsto_nhds_unique hQlim hQzero

end Work.FTS.PressureOn
