/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsLocalPStar/JepsTraceTransferPi.lean`

Trace transfer for the log-coordinate mollifier `Jeps` at the **right end** `θ = π/2⁻`: for
`z > 0`, the angular trace at `θ = π/2` of `J_ε f` is the `s`-marginal average of the angular
trace `lam` of `f` along the `z`-shift,

  `J_ε f (z, θ) ⟶ ∫ s, (∫ t, ρ (s, t)) * lam (z e^{-ε s})`  as `θ → π/2⁻`.

This is the `θ = π/2` companion of `EpsLocalPStar/JepsTraceTransfer.lean` (which treats `θ = 0⁺`).
The two statements differ only in the filter: the `θ`-shift `thShift θ p = arctan (tan θ e^{-p})`
sends `θ → π/2⁻` to `π/2⁻` as well, because `tan θ → +∞` (`Real.tendsto_tan_pi_div_two`) and
`arctan` has limit `π/2` at `+∞` (`Real.tendsto_arctan_atTop`).

The hypotheses `hfm` (a.e. strong measurability of the profile on the quadrant) and `hlamm`
(measurability of the trace) are exactly the ones of `JepsTraceTransfer_of_measurable`; they are
*necessary* — without them the analogous assertion at `θ = 0⁺` is false by
`integral_non_aestronglyMeasurable`, and the same counterexample applies here.

## Route

`Jeps ρ ε f z θ = ∫ p, Jker ρ ε p * f (z e^{-p₁}) (thShift θ p₂)` on the quadrant, so the claim is
dominated convergence in `θ`:

* the value of the limit is identified by the change of variables `p ↦ ε⁻¹ • p` plus Fubini on the
  `s`-marginal (`integral_Jker_mul_eq_marginal`, the same statement as in the `θ = 0⁺` file, which
  does not mention the filter at all and so is re-proved here in a private copy);
* the domination is `‖Jker ρ ε p‖ * M`, where `M` bounds `f` on the box
  `(z e^{-ε}, z e^{ε}) × (0, π/2)` — obtained from the local boundedness hypothesis `hfbd` on the
  compact interval `[z e^{-ε}, z e^{ε}]` by `exists_bound_Icc`;
* the a.e. strong measurability of the integrand in the `p`-variable is transported from `hfm` by
  the fact that the shift `sPhi z θ` is quasi-measure-preserving onto the quadrant
  (`qmp_sPhi_restrict`).

The helpers are private copies of the ones proved in `EpsLocalPStar/JepsTraceTransfer.lean`; they
are reproduced here so that this module's import cone does not have to go through that file, whose
sibling statement `JepsTraceTransfer` is false as written and is therefore left unproved there.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.RingTheory.TotallySplit
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.Kernel
import Submission.Work.FTS.StrongEps.Jeps_tendsto

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsLocalPStar

open scoped Real Topology
open MeasureTheory Set Filter

/-! ## Boundedness on compact `z`-intervals -/

/-- On the support of the rescaled kernel `Jker ρ ε`, the first coordinate of `p` is bounded by
`ε`. -/
private lemma abs_fst_le_of_Jker_ne_zero {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsMollKernel ρ)
    {ε : ℝ} (hε : 0 < ε) {p : ℝ × ℝ} (hp : Work.FTS.StrongEps.Jker ρ ε p ≠ 0) :
    |p.1| ≤ ε := by
  have h := Work.FTS.StrongEps.Jker_ne_zero_support hρ hε hp
  have h1 : p.1 ^ 2 ≤ ε ^ 2 := by nlinarith [sq_nonneg p.2]
  have h2 := (sq_le_sq.mp h1 : |p.1| ≤ |ε|)
  rwa [abs_of_nonneg hε.le] at h2

/-- On the support of an admissible kernel, the first coordinate is bounded by `1`. -/
private lemma abs_fst_le_one_of_mollKernel {ρ : ℝ × ℝ → ℝ}
    (hρ : Work.FTS.StrongEps.IsMollKernel ρ) {q : ℝ × ℝ} (hq : ρ q ≠ 0) : |q.1| ≤ 1 := by
  have h := hρ.support q hq
  have h1 : q.1 ^ 2 ≤ 1 ^ 2 := by nlinarith [sq_nonneg q.2]
  have h2 := (sq_le_sq.mp h1 : |q.1| ≤ |(1 : ℝ)|)
  rwa [abs_one] at h2

/-- **A uniform bound for the profile on a closed `z`-interval.**  The hypothesis `hfbd` only
bounds `f` on the boxes `(z/2, 2z) × (0, π/2)`; finitely many of those boxes (one `z` per point of
`[a,b]`) cover any compact `z`-interval inside `(0,∞)`. -/
private lemma exists_bound_Icc {f : ℝ → ℝ → ℝ}
    (hfbd : ∀ z : ℝ, 0 < z → ∃ M : ℝ, ∀ z' ∈ Set.Ioo (z / 2) (2 * z),
      ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |f z' θ| ≤ M)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ M : ℝ, 0 < M ∧ ∀ z' ∈ Set.Icc a b, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |f z' θ| ≤ M := by
  classical
  choose M hM using fun w : {w : ℝ // 0 < w} => hfbd w.1 w.2
  have hcover : Set.Icc a b ⊆ ⋃ w : {w : ℝ // 0 < w}, Set.Ioo (w.1 / 2) (2 * w.1) := by
    intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le ha hx.1
    refine Set.mem_iUnion.mpr ⟨⟨x, hxpos⟩, ?_⟩
    exact ⟨by linarith, by linarith⟩
  obtain ⟨t, ht⟩ := isCompact_Icc.elim_finite_subcover
    (fun w : {w : ℝ // 0 < w} => Set.Ioo (w.1 / 2) (2 * w.1)) (fun _ => isOpen_Ioo) hcover
  refine ⟨(∑ w ∈ t, |M w|) + 1, by positivity, ?_⟩
  intro z' hz' θ hθ
  obtain ⟨w, hwt, hwz⟩ : ∃ w, w ∈ t ∧ z' ∈ Set.Ioo (w.1 / 2) (2 * w.1) := by
    simpa only [Set.mem_iUnion, exists_prop] using ht hz'
  have h1 : |f z' θ| ≤ M w := hM w z' hwz θ hθ
  have h2 : M w ≤ |M w| := le_abs_self _
  have h3 : |M w| ≤ ∑ w' ∈ t, |M w'| :=
    Finset.single_le_sum (f := fun w' => |M w'|) (fun i _ => abs_nonneg _) hwt
  linarith

/-- Passing to the trace at `π/2⁻`: `hfbd` bounds `lam` on every compact `z`-interval
`[a,b] ⊆ (0,∞)`. -/
private lemma exists_bound_lam_Icc_pi {f : ℝ → ℝ → ℝ} {lam : ℝ → ℝ}
    (hfbd : ∀ z : ℝ, 0 < z → ∃ M : ℝ, ∀ z' ∈ Set.Ioo (z / 2) (2 * z),
      ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |f z' θ| ≤ M)
    (hlam : ∀ z : ℝ, 0 < z →
      Filter.Tendsto (fun θ => f z θ) (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))
        (nhds (lam z)))
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ M : ℝ, 0 < M ∧ ∀ z' ∈ Set.Icc a b, |lam z'| ≤ M := by
  obtain ⟨M, hMpos, hM⟩ := exists_bound_Icc hfbd ha hab
  refine ⟨M, hMpos, fun z' hz' => ?_⟩
  have hz'pos : 0 < z' := lt_of_lt_of_le ha hz'.1
  refine le_of_tendsto_of_tendsto (hlam z' hz'pos).abs tendsto_const_nhds ?_
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < Real.pi / 2 by positivity)] with θ hθ
  exact hM z' hz' θ hθ

/-! ## Measurability of the shifted profile -/

/-- **The log-coordinate shift is quasi-measure-preserving onto the quadrant.**  The shift
`p ↦ (z e^{-p₁}, arctan (tan θ e^{-p₂}))` maps `ℝ²` into the quadrant `Ioi 0 ×ˢ Ioo 0 (π/2)`, so
(being quasi-measure-preserving for the unrestricted measure, `qmp_sPhi`) its push-forward is
absolutely continuous with respect to the Lebesgue measure *restricted to the quadrant* as well. -/
private lemma qmp_sPhi_restrict {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Measure.QuasiMeasurePreserving (Work.FTS.StrongEps.sPhi z θ) (volume : Measure (ℝ × ℝ))
      (volume.restrict (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) := by
  classical
  set S : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) with hSdef
  have hSmeas : MeasurableSet S := measurableSet_Ioi.prod measurableSet_Ioo
  have hsmem : ∀ p : ℝ × ℝ, Work.FTS.StrongEps.sPhi z θ p ∈ S := by
    intro p
    obtain ⟨h1, h2⟩ := Work.FTS.StrongEps.sPhi_mem hz hθ p
    exact ⟨h1, h2⟩
  refine ⟨(Work.FTS.StrongEps.continuous_sPhi z θ).measurable, ?_⟩
  refine Measure.AbsolutelyContinuous.mk fun s hs hs0 => ?_
  rw [Measure.map_apply (Work.FTS.StrongEps.continuous_sPhi z θ).measurable hs]
  have hpre : (Work.FTS.StrongEps.sPhi z θ) ⁻¹' s
      = (Work.FTS.StrongEps.sPhi z θ) ⁻¹' (s ∩ S) := by
    ext p
    constructor
    · intro hp
      exact ⟨hp, hsmem p⟩
    · exact fun hp => hp.1
  rw [hpre]
  rw [← Measure.map_apply (Work.FTS.StrongEps.continuous_sPhi z θ).measurable (hs.inter hSmeas)]
  have hzero : volume (s ∩ S) = 0 := by
    rw [← Measure.restrict_apply (μ := volume) (s := S) hs]
    exact hs0
  exact (Work.FTS.StrongEps.qmp_sPhi hz hθ).2 hzero

/-! ## The change of variables `p ↦ ε⁻¹ • p` and Fubini on the marginal -/

/-- **The transfer identity.**  The `p`-integral against the rescaled kernel of the `z`-marginal
trace `lam (z e^{-p₁})` equals the `s`-integral of `lam (z e^{-ε s})` against the `t`-marginal of
`ρ`:

  `∫ p, Jker ρ ε p * lam (z e^{-p₁}) = ∫ s, (∫ t, ρ (s,t)) * lam (z e^{-ε s})`.

This is independent of the endpoint at which the trace of `f` is taken, so it is the same identity
as in the `θ = 0⁺` file. -/
private lemma integral_Jker_mul_eq_marginal {ρ : ℝ × ℝ → ℝ}
    (hρ : Work.FTS.StrongEps.IsMollKernel ρ)
    {ε z : ℝ} (hε : 0 < ε) (hz : 0 < z) {lam : ℝ → ℝ} (hlamm : Measurable lam)
    {C : ℝ} (hC : ∀ q : ℝ × ℝ, ρ q ≠ 0 → |lam (z * Real.exp (-(ε * q.1)))| ≤ C) :
    ∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p * lam (z * Real.exp (-p.1))
      = ∫ s, (∫ t, ρ (s, t)) * lam (z * Real.exp (-(ε * s))) := by
  classical
  have hρint : Integrable ρ (volume : Measure (ℝ × ℝ)) := by
    refine hρ.cont.integrable_of_hasCompactSupport ?_
    refine IsCompact.of_isClosed_subset (isCompact_closedBall (0 : ℝ × ℝ) 1) isClosed_closure
      (closure_minimal ?_ Metric.isClosed_closedBall)
    intro q hq
    rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
    have h1 : q.1 ^ 2 ≤ 1 ^ 2 := by
      have := hρ.support q hq
      nlinarith [sq_nonneg q.2]
    have h2 : q.2 ^ 2 ≤ 1 ^ 2 := by
      have := hρ.support q hq
      nlinarith [sq_nonneg q.1]
    refine max_le ?_ ?_
    · have := (sq_le_sq.mp h1 : |q.1| ≤ |(1 : ℝ)|)
      simpa using this
    · have := (sq_le_sq.mp h2 : |q.2| ≤ |(1 : ℝ)|)
      simpa using this
  have haesm : AEStronglyMeasurable
      (fun q : ℝ × ℝ => ρ q * lam (z * Real.exp (-(ε * q.1)))) (volume : Measure (ℝ × ℝ)) :=
    hρ.cont.aestronglyMeasurable.mul (hlamm.comp (by fun_prop)).aestronglyMeasurable
  have hGint : Integrable (fun q : ℝ × ℝ => ρ q * lam (z * Real.exp (-(ε * q.1))))
      (volume : Measure (ℝ × ℝ)) := by
    refine Integrable.mono' (hρint.norm.const_mul (max C 0)) haesm ?_
    filter_upwards with q
    by_cases hq : ρ q = 0
    · simp [hq]
    · have h1 : |lam (z * Real.exp (-(ε * q.1)))| ≤ C := hC q hq
      have h2 : (0 : ℝ) ≤ |ρ q| := abs_nonneg _
      have h3 : C ≤ max C 0 := le_max_left _ _
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
      calc |ρ q| * |lam (z * Real.exp (-(ε * q.1)))|
          ≤ |ρ q| * max C 0 := mul_le_mul_of_nonneg_left (h1.trans h3) h2
        _ = max C 0 * |ρ q| := by ring
  -- step 1: the change of variables `p ↦ ε⁻¹ • p`
  have hstep : (∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p * lam (z * Real.exp (-p.1)))
      = ∫ q : ℝ × ℝ, ρ q * lam (z * Real.exp (-(ε * q.1))) := by
    let g : ℝ × ℝ → ℝ := fun q => ε⁻¹ ^ 2 * (ρ q * lam (z * Real.exp (-(ε * q.1))))
    have h1 : (∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p * lam (z * Real.exp (-p.1)))
        = ∫ p : ℝ × ℝ, g (ε⁻¹ • p) := by
      refine integral_congr_ae (Eventually.of_forall fun p => ?_)
      have hε1 : ε * (ε⁻¹ * p.1) = p.1 := by
        rw [← mul_assoc, mul_inv_cancel₀ hε.ne', one_mul]
      have hfst : (ε⁻¹ • p).1 = ε⁻¹ * p.1 := rfl
      simp only [Work.FTS.StrongEps.Jker, g, hfst, hε1]
      ring
    have h2 := MeasureTheory.Measure.integral_comp_inv_smul_of_nonneg
      (μ := (volume : Measure (ℝ × ℝ))) g hε.le
    rw [show Module.finrank ℝ (ℝ × ℝ) = 2 from by simp [Module.finrank_prod],
      smul_eq_mul] at h2
    rw [h1, h2]
    have h3 : (∫ q : ℝ × ℝ, g q)
        = ε⁻¹ ^ 2 * ∫ q : ℝ × ℝ, ρ q * lam (z * Real.exp (-(ε * q.1))) := by
      simp only [g]
      rw [MeasureTheory.integral_const_mul]
    rw [h3]
    have h4 : ε ^ 2 * ε⁻¹ ^ 2 = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ hε.ne', one_pow]
    rw [← mul_assoc, h4, one_mul]
  -- step 2: Fubini on the marginal
  have hGint' : Integrable (fun q : ℝ × ℝ => ρ q * lam (z * Real.exp (-(ε * q.1))))
      (volume.prod volume) := by
    simpa only [MeasureTheory.Measure.volume_eq_prod ℝ ℝ] using hGint
  have hR : (∫ s, (∫ t, ρ (s, t)) * lam (z * Real.exp (-(ε * s))))
      = ∫ q : ℝ × ℝ, ρ q * lam (z * Real.exp (-(ε * q.1))) := by
    have hinner : ∀ s : ℝ, (∫ t, ρ (s, t)) * lam (z * Real.exp (-(ε * s)))
        = ∫ t, ρ (s, t) * lam (z * Real.exp (-(ε * s))) := fun s => by
      rw [MeasureTheory.integral_mul_const]
    simp only [hinner]
    rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
    exact (MeasureTheory.integral_prod _ hGint').symm
  rw [hstep, hR]

/-! ## The trace transfer at `θ = π/2⁻` -/

theorem JepsTraceTransferPi {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {ε : ℝ} (hε : 0 < ε) {f : ℝ → ℝ → ℝ} {lam : ℝ → ℝ}
    (hfm : MeasureTheory.AEStronglyMeasurable (Function.uncurry f)
      (MeasureTheory.volume.restrict (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))))
    (hlamm : Measurable lam)
    (hlam : ∀ z : ℝ, 0 < z →
      Filter.Tendsto (fun θ => f z θ) (nhdsWithin (Real.pi/2) (Set.Iio (Real.pi/2))) (nhds (lam z)))
    (hfbd : ∀ z : ℝ, 0 < z → ∃ M : ℝ, ∀ z' ∈ Set.Ioo (z/2) (2*z),
      ∀ θ ∈ Set.Ioo 0 (Real.pi/2), |f z' θ| ≤ M) :
    ∀ z : ℝ, 0 < z →
      Filter.Tendsto (fun θ => Work.FTS.StrongEps.Jeps ρ ε f z θ)
        (nhdsWithin (Real.pi/2) (Set.Iio (Real.pi/2)))
        (nhds (∫ s, (∫ t, ρ (s, t)) * lam (z * Real.exp (-(ε * s))))) := by
  intro z hz
  have ha : 0 < z * Real.exp (-ε) := by positivity
  have hab : z * Real.exp (-ε) ≤ z * Real.exp ε :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hz.le
  obtain ⟨M, hMpos, hM⟩ := exists_bound_Icc hfbd ha hab
  obtain ⟨N, hNpos, hN⟩ := exists_bound_lam_Icc_pi hfbd hlam ha hab
  -- the value of the limit, in the `p`-coordinates
  have hCbd : ∀ q : ℝ × ℝ, ρ q ≠ 0 → |lam (z * Real.exp (-(ε * q.1)))| ≤ N := by
    intro q hq
    have hq1 : |q.1| ≤ 1 := abs_fst_le_one_of_mollKernel hρ.moll hq
    have h1 : -ε ≤ ε * q.1 := by have := (abs_le.mp hq1).1; nlinarith
    have h2 : ε * q.1 ≤ ε := by have := (abs_le.mp hq1).2; nlinarith
    exact hN _ ⟨mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hz.le,
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hz.le⟩
  rw [← integral_Jker_mul_eq_marginal hρ.moll hε hz hlamm hCbd]
  -- dominated convergence
  have hJint : Integrable (Work.FTS.StrongEps.Jker ρ ε) (volume : Measure (ℝ × ℝ)) :=
    Work.FTS.StrongEps.Jker_integrable hρ.moll hε
  have hbound_int : Integrable (fun p : ℝ × ℝ => ‖Work.FTS.StrongEps.Jker ρ ε p‖ * M)
      (volume : Measure (ℝ × ℝ)) := hJint.norm.mul_const M
  have hmem : Set.Ioo (0 : ℝ) (Real.pi / 2)
      ∈ nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)) :=
    Ioo_mem_nhdsLT (show (0 : ℝ) < Real.pi / 2 by positivity)
  have hmeas : ∀ᶠ θ in nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)), AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.FTS.StrongEps.Jker ρ ε p *
        f (z * Real.exp (-p.1)) (Real.arctan (Real.tan θ * Real.exp (-p.2))))
      (volume : Measure (ℝ × ℝ)) := by
    filter_upwards [hmem] with θ hθ
    have hcomp := hfm.comp_quasiMeasurePreserving (qmp_sPhi_restrict hz hθ)
    have hcomp' : AEStronglyMeasurable
        (fun p : ℝ × ℝ => f (z * Real.exp (-p.1))
          (Real.arctan (Real.tan θ * Real.exp (-p.2)))) (volume : Measure (ℝ × ℝ)) := by
      simpa only [Function.comp_def, Function.uncurry, Work.FTS.StrongEps.sPhi,
        Work.FTS.StrongEps.zShift, Work.FTS.StrongEps.thShift] using hcomp
    exact (Work.FTS.StrongEps.Jker_continuous hρ.moll ε).aestronglyMeasurable.mul hcomp'
  have hbound : ∀ᶠ θ in nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)),
      ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)),
      ‖Work.FTS.StrongEps.Jker ρ ε p *
        f (z * Real.exp (-p.1)) (Real.arctan (Real.tan θ * Real.exp (-p.2)))‖
      ≤ ‖Work.FTS.StrongEps.Jker ρ ε p‖ * M := by
    filter_upwards [hmem] with θ hθ
    filter_upwards with p
    by_cases hp : Work.FTS.StrongEps.Jker ρ ε p = 0
    · simp [hp]
    · have hp1 : |p.1| ≤ ε := abs_fst_le_of_Jker_ne_zero hρ.moll hε hp
      have h1 : -ε ≤ p.1 := (abs_le.mp hp1).1
      have h2 : p.1 ≤ ε := (abs_le.mp hp1).2
      have hzmem : z * Real.exp (-p.1) ∈ Set.Icc (z * Real.exp (-ε)) (z * Real.exp ε) :=
        ⟨mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hz.le,
         mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hz.le⟩
      have hJnn : 0 ≤ Work.FTS.StrongEps.Jker ρ ε p := by
        simp only [Work.FTS.StrongEps.Jker]
        exact mul_nonneg (by positivity) (hρ.moll.nonneg _)
      have hθ' : Real.arctan (Real.tan θ * Real.exp (-p.2)) ∈ Set.Ioo 0 (Real.pi / 2) :=
        Work.FTS.StrongEps.thShift_mem hθ
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hJnn]
      exact mul_le_mul_of_nonneg_left (hM _ hzmem _ hθ') hJnn
  have hlim : ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)), Tendsto
      (fun θ => Work.FTS.StrongEps.Jker ρ ε p *
        f (z * Real.exp (-p.1)) (Real.arctan (Real.tan θ * Real.exp (-p.2))))
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))
      (nhds (Work.FTS.StrongEps.Jker ρ ε p * lam (z * Real.exp (-p.1)))) := by
    filter_upwards with p
    -- the `θ`-shift sends `θ → π/2⁻` to `π/2⁻`
    have hshift : Tendsto (fun θ : ℝ => Real.arctan (Real.tan θ * Real.exp (-p.2)))
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) :=
      Real.tendsto_arctan_atTop.comp
        (Real.tendsto_tan_pi_div_two.atTop_mul_const (Real.exp_pos _))
    exact Tendsto.const_mul _ ((hlam (z * Real.exp (-p.1)) (by positivity)).comp hshift)
  have hDCT := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (μ := (volume : Measure (ℝ × ℝ)))
    (F := fun θ p => Work.FTS.StrongEps.Jker ρ ε p *
      f (z * Real.exp (-p.1)) (Real.arctan (Real.tan θ * Real.exp (-p.2))))
    (f := fun p => Work.FTS.StrongEps.Jker ρ ε p * lam (z * Real.exp (-p.1)))
    (fun p => ‖Work.FTS.StrongEps.Jker ρ ε p‖ * M) hmeas hbound hbound_int hlim
  refine hDCT.congr' ?_
  filter_upwards [hmem, self_mem_nhdsWithin] with θ hθ hθpos
  rw [Work.FTS.StrongEps.Jeps_eq_integral ρ ε f hz hθ]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  simp only [Work.FTS.StrongEps.zShift, Work.FTS.StrongEps.thShift]

end Work.FTS.StrongEps.EpsLocalPStar
