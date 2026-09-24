import Mathlib
import Submission.Work.Analysis.RiemannSurface.DivisorBasics
import Submission.Work.Analysis.RiemannSurface.weyl_surface
import Submission.Work.Analysis.Complex.PolePush.pole_push
import Submission.Work.SimplyConnected.ABS.ExtremalImports
import Submission.Work.Analysis.Complex.DbarCauchy.Defs
import Submission.Work.Analysis.Complex.Hormander.weightedMeasure
import Submission.Work.Analysis.Complex.DbarCauchy.integral_dbar_eq_zero
import Submission.Work.Analysis.Complex.DbarCauchy.integral_comp_normSq
import Submission.Work.Analysis.Complex.DbarCauchy.cauchyPompeiu
import Submission.Work.Analysis.Complex.DbarCauchy.dbar_representation
import Submission.Work.Analysis.Complex.DbarCauchy.dbar_solvable

namespace Work.Analysis.RiemannSurface

/-- **Geometric expansion of the Cauchy kernel off the disc of radius `‖z‖`.**  For `‖z‖ < ‖w‖` the
kernel `(z - w)⁻¹` is the sum of the (convergent) geometric series `Σ_m w⁻¹ (z/w)^m`.  This is the
tool the moments argument uses to turn a circle integral against `(z-w)⁻¹` into the moments
`∮ z^m f z`; the uniform bound `‖w⁻¹ (z/w)^m‖ ≤ ‖w‖⁻¹ (‖z‖/‖w‖)^m` on a circle of radius `r < ‖w‖`
makes the corresponding series of integrals summable. -/
theorem hasSum_cauchyKernel {z w : ℂ} (hzw : ‖z‖ < ‖w‖) :
    HasSum (fun m : ℕ => w⁻¹ * (z / w) ^ m) (-(z - w)⁻¹) := by
  have hw : w ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hzw
    exact absurd hzw (not_lt_of_ge (norm_nonneg z))
  have hξ : ‖z / w‖ < 1 := by
    rw [norm_div, div_lt_one (norm_pos_iff.mpr hw)]
    exact hzw
  have h1 : HasSum (fun m : ℕ => w⁻¹ * (z / w) ^ m) (w⁻¹ * (1 - z / w)⁻¹) :=
    (hasSum_geometric_of_norm_lt_one hξ).mul_left w⁻¹
  have h2 : w⁻¹ * (1 - z / w)⁻¹ = -(z - w)⁻¹ := by
    rw [show z - w = -(w - z) from by ring, inv_neg, neg_neg]
    have hA : (1 : ℂ) - z / w = (w - z) / w := by field_simp
    rw [hA, inv_div, mul_comm]
    field_simp
  rwa [h2] at h1

/-- **The outer Cauchy-kernel term bound.**  For `‖z‖ = r < ‖w‖`,
`‖(-w⁻¹) (z/w)^m f z‖ ≤ ‖f z‖ (r/‖w‖)^m ‖w‖⁻¹` — indeed equality: the `w⁻¹` contributes `‖w‖⁻¹`,
the `m`-th power contributes `(r/‖w‖)^m`, and the rest is `‖f z‖`.  This is the pointwise
domination input of the outer Cauchy-kernel expansion (no conditional `simp` needed: plain `rw`). -/
theorem norm_cauchyKernel_term_le {f : ℂ → ℂ} {r : ℝ} (hr : 0 ≤ r) {w : ℂ}
    (hwr : r < ‖w‖) {z : ℂ} (hz : ‖z‖ = r) (m : ℕ) :
    ‖(-w⁻¹) * (z / w) ^ m * f z‖ ≤ ‖f z‖ * (r / ‖w‖) ^ m * ‖w‖⁻¹ := by
  have hw : (0 : ℝ) < ‖w‖ := hr.trans_lt hwr
  rw [norm_mul, norm_mul, norm_neg, norm_inv, norm_pow, norm_div, hz, div_pow]
  exact le_of_eq (by ring)

/-- **The norm of the derivative of the circle map.**  `‖deriv (circleMap 0 r) θ‖ = |r|`; this is
the factor `r` that appears when the outer Cauchy-kernel expansion is applied to a circle integral.
(The companion identity `‖circleMap 0 r θ‖ = |r|` is Mathlib's `norm_circleMap_zero`.) -/
theorem norm_deriv_circleMap_eq (r : ℝ) (θ : ℝ) :
    ‖deriv (circleMap 0 r) θ‖ = |r| := by
  rw [show deriv (circleMap 0 r) θ = circleMap 0 r θ * Complex.I from
    (hasDerivAt_circleMap (0 : ℂ) r θ).deriv]
  rw [norm_mul, norm_circleMap_zero, Complex.norm_I, mul_one]

/-- **The outer Cauchy-kernel expansion.**  For `r < ‖w‖` the circle integral of `(z-w)⁻¹ f z`
expands as the (summable) series of moments against `-w⁻¹ (z/w)^m`.  Mathlib has the inner case
(`Complex.hasSum_two_pi_I_cauchyPowerSeries_integral`); this is the outer one, which is what the
moments argument on the punctured disc needs.  The measurability hypothesis on `f ∘ circleMap` is
automatic for `CircleIntegrable f 0 r` (divide out the nowhere-vanishing `deriv`). -/
theorem hasSum_circleIntegral_cauchyKernel {f : ℂ → ℂ} {r : ℝ} (hr : 0 < r) {w : ℂ}
    (hwr : r < ‖w‖) (hf : CircleIntegrable f 0 r)
    (hf' : MeasureTheory.AEStronglyMeasurable (fun θ : ℝ => f (circleMap 0 r θ))
      (MeasureTheory.volume.restrict (Set.uIoc 0 (2 * Real.pi)))) :
    HasSum (fun m : ℕ => ∮ z in C(0, r), (-w⁻¹) * (z / w) ^ m * f z)
      (∮ z in C(0, r), (z - w)⁻¹ * f z) := by
  have hwpos : 0 < ‖w‖ := lt_trans hr hwr
  have hrle : (0 : ℝ) ≤ r := hr.le
  have hnorm : ∀ θ : ℝ, ‖circleMap 0 r θ‖ = r := fun θ => by
    rw [norm_circleMap_zero, abs_of_pos hr]
  have hw : w ≠ 0 := norm_pos_iff.mp hwpos
  have hlt : r / ‖w‖ < 1 := (div_lt_one hwpos).mpr hwr
  have h0 : (0 : ℝ) ≤ r / ‖w‖ := div_nonneg hrle hwpos.le
  simp only [circleIntegral]
  refine intervalIntegral.hasSum_integral_of_dominated_convergence (a := 0) (b := 2 * Real.pi)
    (μ := MeasureTheory.volume)
    (F := fun (m : ℕ) (θ : ℝ) =>
      deriv (circleMap 0 r) θ • ((-w⁻¹) * (circleMap 0 r θ / w) ^ m * f (circleMap 0 r θ)))
    (f := fun θ : ℝ => deriv (circleMap 0 r) θ • ((circleMap 0 r θ - w)⁻¹ * f (circleMap 0 r θ)))
    (fun (m : ℕ) (θ : ℝ) => ‖f (circleMap 0 r θ)‖ * (r / ‖w‖) ^ m * (r * ‖w‖⁻¹)) ?_ ?_ ?_ ?_ ?_
  · intro m
    have hconst : MeasureTheory.AEStronglyMeasurable (fun _ : ℝ => (-w⁻¹ : ℂ))
        (MeasureTheory.volume.restrict (Set.uIoc 0 (2 * Real.pi))) := MeasureTheory.aestronglyMeasurable_const
    have hc : MeasureTheory.AEStronglyMeasurable (fun θ : ℝ => circleMap 0 r θ / w)
        (MeasureTheory.volume.restrict (Set.uIoc 0 (2 * Real.pi))) := by fun_prop
    have hmul : MeasureTheory.AEStronglyMeasurable
        (fun θ : ℝ => (-w⁻¹) * (circleMap 0 r θ / w) ^ m * f (circleMap 0 r θ))
        (MeasureTheory.volume.restrict (Set.uIoc 0 (2 * Real.pi))) := (hconst.mul (hc.pow m)).mul hf'
    have hd : MeasureTheory.AEStronglyMeasurable (fun θ : ℝ => deriv (circleMap 0 r) θ)
        (MeasureTheory.volume.restrict (Set.uIoc 0 (2 * Real.pi))) := by fun_prop
    exact hd.smul hmul
  · intro m
    filter_upwards with θ hθ
    rw [norm_smul, norm_deriv_circleMap_eq]
    calc |r| * ‖(-w⁻¹) * (circleMap 0 r θ / w) ^ m * f (circleMap 0 r θ)‖
        ≤ r * (‖f (circleMap 0 r θ)‖ * (r / ‖w‖) ^ m * ‖w‖⁻¹) := by
          rw [abs_of_pos hr]
          exact mul_le_mul_of_nonneg_left (norm_cauchyKernel_term_le hrle hwr (hnorm θ) m) hrle
      _ = ‖f (circleMap 0 r θ)‖ * (r / ‖w‖) ^ m * (r * ‖w‖⁻¹) := by ring
  · refine Filter.Eventually.of_forall fun t _ => ?_
    exact ((summable_geometric_of_lt_one h0 hlt).mul_left ‖f (circleMap 0 r t)‖).mul_right
      (r * ‖w‖⁻¹)
  · have hh : IntervalIntegrable (fun t : ℝ => ‖f (circleMap 0 r t)‖) MeasureTheory.volume 0 (2 * Real.pi) :=
      hf.norm
    simpa only [mul_assoc, tsum_mul_left, tsum_mul_right, tsum_geometric_of_lt_one h0 hlt] using
      hh.mul_continuousOn continuousOn_const
  · refine Filter.Eventually.of_forall fun θ _ => ?_
    have h := ((hasSum_cauchyKernel (z := circleMap 0 r θ) (w := w)
      (by rw [hnorm θ]; exact hwr)).neg.mul_right (f (circleMap 0 r θ)))
    simpa only [smul_eq_mul, neg_mul, neg_neg] using h.mul_left (deriv (circleMap 0 r) θ)

/-- **Every term of the outer Cauchy-kernel expansion vanishes when the moments do.**  For
`w ≠ 0` and a vanishing moment `∮ z^m f z = 0`, the corresponding term of
`hasSum_circleIntegral_cauchyKernel` vanishes too: the term is the constant
`(-w⁻¹) * (w⁻¹)^m` times that moment. -/
theorem circleIntegral_cauchyKernel_term_eq_zero {f : ℂ → ℂ} {r : ℝ} {w : ℂ} (hw : w ≠ 0) (m : ℕ)
    (hmom : (∮ z in C(0, r), z ^ m * f z) = 0) :
    (∮ z in C(0, r), (-w⁻¹) * (z / w) ^ m * f z) = 0 := by
  have hfun : (fun z : ℂ => (-w⁻¹) * (z / w) ^ m * f z)
      = fun z : ℂ => ((-w⁻¹) * (w⁻¹) ^ m) * (z ^ m * f z) := by
    funext z
    rw [div_eq_mul_inv, mul_pow]
    ring
  rw [hfun]
  have hpull : (∮ z in C(0, r), ((-w⁻¹) * (w⁻¹) ^ m) * (z ^ m * f z))
      = ((-w⁻¹) * (w⁻¹) ^ m) * (∮ z in C(0, r), z ^ m * f z) := by
    simp only [circleIntegral]
    rw [show (fun θ : ℝ => deriv (circleMap 0 r) θ •
          (((-w⁻¹) * (w⁻¹) ^ m) * ((circleMap 0 r θ) ^ m * f (circleMap 0 r θ))))
        = fun θ : ℝ => ((-w⁻¹) * (w⁻¹) ^ m) *
            (deriv (circleMap 0 r) θ * ((circleMap 0 r θ) ^ m * f (circleMap 0 r θ))) from by
      funext θ
      simp only [smul_eq_mul]
      ring]
    simp only [smul_eq_mul]
    rw [intervalIntegral.integral_const_mul]
  rw [hpull, hmom, mul_zero]

/-- **Step 3 of the moments plan.**  If every moment `∮ z^m f z` vanishes and `r < ‖w‖`, then the
outer Cauchy-kernel integral `∮ (z-w)⁻¹ f z` over the circle of radius `r` vanishes: it is the sum of
the expansion terms, all of which are constants times the vanishing moments. -/
theorem circleIntegral_cauchyKernel_eq_zero {f : ℂ → ℂ} {r : ℝ} (hr : 0 < r) {w : ℂ}
    (hwr : r < ‖w‖) (hf : CircleIntegrable f 0 r)
    (hf' : MeasureTheory.AEStronglyMeasurable (fun θ : ℝ => f (circleMap 0 r θ))
      (MeasureTheory.volume.restrict (Set.uIoc 0 (2 * Real.pi))))
    (hmom : ∀ m : ℕ, (∮ z in C(0, r), z ^ m * f z) = 0) :
    (∮ z in C(0, r), (z - w)⁻¹ * f z) = 0 := by
  have hw : w ≠ 0 := norm_pos_iff.mp (lt_trans hr hwr)
  have hsum := hasSum_circleIntegral_cauchyKernel hr hwr hf hf'
  have hzero : ∀ m : ℕ, (∮ z in C(0, r), (-w⁻¹) * (z / w) ^ m * f z) = 0 :=
    fun m => circleIntegral_cauchyKernel_term_eq_zero hw m (hmom m)
  rw [← hsum.tsum_eq]
  simp only [hzero, tsum_zero]

/-- Existence of a holomorphic function with a single simple zero at a prescribed point of a
non-compact connected Riemann surface (Weierstrass/Cousin; Behnke--Stein: a non-compact Riemann
surface is Stein, so every divisor is principal). The module `SimplyConnected/ABS/extremal_maximizer_proper`
contains a sorried declaration of the same content, `exists_holomorphic_single_zero`; do not use it
(that would be circular).

**State of the reduction (see `NOTES_divisor_chapter_plan.md` §24).**  The whole theorem is now
reduced, by a *machine-checked* one-step reduction, to the single approximation-theoretic input
`Work.Analysis.RiemannSurface.MeromorphicRunge`:

```
Work.Analysis.RiemannSurface.exists_singleZero_of_meromorphicRunge x₀ hX h : <this statement>
```

(`h : MeromorphicRunge x₀`), in `Submission/Work/Analysis/RiemannSurface/runge_meromorphic.lean`.
That file also contains the tools a proof of the input needs at each step
(`unit_approx_of_log`, `weighted_approx_of_chart_model`, `exists_taylor_one`) and the *chart-local*
base case of the input (`meromorphicRunge_chart_of_log'`).  What is still missing is the global
step, i.e. the Cousin/`H¹(X,𝒪*) = 0` bookkeeping; see §24.9 of the notes.

**Session L5xx: the potential-theoretic reformulation (see §25 of the notes).**  The statement is
*also* equivalent to a statement of potential theory on the open surface `X ∖ {x₀}`: there is a
harmonic function `E` on `X ∖ {x₀}` with a logarithmic pole of coefficient one at `x₀`
(`Work.Analysis.RiemannSurface.HasUnitLogPoleAt`) whose harmonic conjugate has all periods in `2πℤ`
(the conjugate-period homomorphism `Work.Analysis.RiemannSurface.logPeriodHom` takes values in
`2πℤ`).  The direction *datum ⟹ this statement* is machine-checked in
`Submission/Work/Analysis/RiemannSurface/target_of_harmonicLogDatum_periods.lean`
(`Work.Analysis.RiemannSurface.target_of_harmonicLogDatum_periods`, no `sorry`, axioms
`propext, Classical.choice, Quot.sound`), using the tree's `Work.Modulus` monodromy machinery with
the positivity and compact-superlevel hypotheses of `IsUnitGreenFunctionAt` removed; the converse
(there is such a datum as soon as the statement holds, with `E = -log ‖g‖`) is a one-step
computation whose machinery (`Submission.harmonicOnXAt_neg_log_norm`, the winding numbers of `g`) is
in the tree.  No Runge/Behnke--Stein approximation, no sheaf cohomology of `𝒪` and no `∂̄`
solvability appears in this formulation: the difficulty is the *period condition* (the flux of `E`
through the handle cycles of `X ∖ {x₀}`), which §25.2 of the notes identifies with the classical
Hodge-theoretic statement that the periods of the holomorphic `1`-forms on `X ∖ {x₀}` fill
`Hom (H₁ (X ∖ {x₀}), ℂ)` — equivalently that every closed `1`-form there is cohomologous to a
holomorphic one.

**Session 6: the "good" cases are now closed, and the crux is isolated.**  A new sorry-free module
`Submission.Work.Analysis.RiemannSurface.single_simple_zero_of_unitGreen` (importable on its own,
*x*unlike this one while the target is open) records two reductions that turn the workspace's modulus
chapter into this statement verbatim:

* `Work.Analysis.RiemannSurface.singleSimpleZero_of_unitGreen_loopsTrivial` — the target follows
  from a unit-pole Green function at `x₀` plus the *purely topological* loop condition
  `Work.Modulus.AllLoopsOfPuncturedTrivialInX x₀`; no simple connectivity of `X` is assumed.  The
  passage is: `Work.SimplyConnected.ABS.unitGreen_modulus_of_loopsTrivial` produces the holomorphic
  modulus `Φ` with `‖Φ x‖ = exp (-(E x))`, and a modulus is *nowhere zero* off the pole;
* `Work.Analysis.RiemannSurface.singleSimpleZero_of_unitGreen_simplyConnected` — the same with
  `SimplyConnectedSpace X` in place of the loop condition.

Both are axiom-clean.  Note the *asymmetry* of these reductions: they need `E > 0`, i.e. a genuine
unit-pole *Green* function, and (in the second) `X` simply connected; the missing cases are exactly
those in which `X` has no unit Green function (the parabolic case) and those in which the periods of
`*dE` are not multiples of `2π`.  The harmonic-level reformulation of §25 (`HarmonicLogDatum`, which
*does* hold in the parabolic case, e.g. `E = -log ‖c · - c x₀‖` on a plane domain) together with
`Work.Analysis.RiemannSurface.target_of_harmonicLogDatum_periods` reduces the whole statement to the
period/flux condition alone.  A *logarithmic* pole, and hence (`∂̄` of it) a Cauchy kernel
`ω_z` holomorphic off `z` with a simple pole at `z`, exists — but its periods (equivalently the
fluxes of the harmonic functions on `X`) are the obstructing datum. 
**SESSION 20 (status).**  `NOTES_divisor_chapter_plan.md` §39 records the *corrected* endgame of
this chapter, which replaces the multivalued-log argument of §37.2 (dead: the log model has a cut and
does not extend out of its chart) by a **smooth trivializer**: if `φ : X → ℂ` is `C^∞`, has zero set
exactly `{x₀}`, is holomorphic with a simple zero at `x₀` (`Submission.HasLogPoleAt x₀ φ`) and its
logarithmic derivative `α = ∂̄φ/φ` is presented by a compactly supported chartwise datum, then a
global solution `u` of the classical equation `∂̄u = α` (the analytic half, `H¹(X,𝒪) = 0`) gives the
target through `g := φ · exp (-u)`, because `∂̄(g ∘ e.symm) = 0` pointwise in every chart by the
product rule and `Work.Analysis.RiemannSurface.dbar_exp`.  The two halves are independent: `(SM)` is
the smooth/topological half, whose winding/degree analysis is in §39.3 and whose two good cases are
the landed `single_simple_zero_of_unitGreen` results.

Landed for this reduction (axiom-clean, `Submission/Work/Analysis/RiemannSurface/smooth_model_at.lean`):
`dbar_comp_hasDerivAt` (`∂̄(F ∘ v) = c · ∂̄v` for `HasDerivAt F c (v z)`),
`dbar_comp_analyticAt_outer` (the holomorphic-outer chain rule `∂̄(F ∘ v) = F′(v)·∂̄v`), `dbar_exp`
(`∂̄(exp ∘ v) = exp v · ∂̄v`) and the definition `SmoothModelAt x₀` of the second input.

Fire-ready delegations (statements reviewed 2/2 "looks correct as stated"; the fleet was saturated at
every attempt of this session): `Analysis/RiemannSurface/exists_dbar_weight` and
`Analysis/RiemannSurface/single_simple_zero_of_smoothModel_dbar`.

-/
theorem single_simple_zero_at {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] (x₀ : X) (hX : ¬ CompactSpace X) :
    ∃ g : X → ℂ, Submission.HolomorphicOnX g Set.univ ∧ (∀ z : X, z ≠ x₀ → g z ≠ 0) ∧
      Submission.HasLogPoleAt x₀ g := by
  sorry

end Work.Analysis.RiemannSurface
