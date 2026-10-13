/-
# The Green-function identity for the Gaussian scale of the Laplacian

`Work.FTS.PressureOn.Green.integral_gauss_smul_laplaceTraceVec`:

  `∫ z, (∫ s in 0..T, exp (-(s²‖z‖²))) • ΔG z = -(2T³) • ∫ z, exp (-(T²‖z‖²)) • G z`

for `G : ℝ³ → ℝ³` of class `C²` with compact support, where `Δ = laplaceTrace` is the trace of
the Hessian (the Euclidean Laplacian).

## The mathematics

For a fixed `z` the whole `s`-integral has a clean antiderivative: with
`Δ_z exp (-(s²‖z‖²)) = (4s⁴‖z‖² - 6s²) exp (-(s²‖z‖²)) = -2 ∂_s (s³ exp (-(s²‖z‖²)))`
one gets `∫_0^T Δ_z exp (-(s²‖z‖²)) ds = -2T³ exp (-(T²‖z‖²))` (the three-dimensional
coefficient `-6` is exactly what makes this an exact `s`-derivative).  Moving `Δ` from `G` onto
the Gaussian weight by Green's identity (two integrations by parts, legitimate because `G` is
`C²` with compact support) gives the stated identity.

## The formal route

Everything is reduced to scalars first.

* `scalar_core` proves the identity for a scalar `φ` from two ingredients: Fubini's theorem for
  interval integrals (`MeasureTheory.intervalIntegral_integral_swap`) to interchange the `s`- and
  `z`-integrals, the Green identity `integral_mul_laplaceTrace_comm` slice by slice, the explicit
  Laplacian of the Gaussian (`laplaceTrace_exp_neg_mul_normSq`) and the `s`-antiderivative
  `integral_quartic_exp_neg_mul_sq`.  The integrability hypotheses of the two Fubini steps are
  discharged by `integrable_uncurry_of_bound`, a majorant argument on the measure
  `(volume.restrict (uIoc 0 T)).prod volume`.
* `integral_gauss_smul_laplaceTraceVec` is then obtained coordinatewise: `PiLp.ext` together with
  `MeasureTheory.eval_integral_piLp` moves the coordinates out of the Bochner integrals, and
  `laplaceTraceVec_coord` identifies the `j`-th coordinate of the vector Laplacian with the
  Laplacian of the `j`-th coordinate.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Work.FTS.PressureOn.Defs
import Submission.Work.FTS.PressureOn.Green.laplaceTrace_exp_neg_mul_normSq
import Submission.Work.FTS.PressureOn.Green.integral_quartic_exp_neg_mul_sq
import Submission.Work.FTS.PressureOn.Green.integral_mul_laplaceTrace_comm

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set MeasureTheory
open scoped Topology

noncomputable section

namespace Work.FTS.PressureOn.Green

open Work.FTS.PressureOn

namespace IgslvAux

/-- The `j`-th coordinate of a derivative is the derivative of the `j`-th coordinate. -/
lemma fderiv_coord (H : R3 → R3) (z : R3) (hH : DifferentiableAt ℝ H z) (j : Fin 3) (v : R3) :
    fderiv ℝ (fun w => H w j) z v = (fderiv ℝ H z v) j := by
  have hproj : HasFDerivAt (fun f : R3 => f.ofLp j)
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) j) (H z) :=
    PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 (H z) j
  have hc := hproj.comp z hH.hasFDerivAt
  change HasFDerivAt (fun w : R3 => (H w).ofLp j) _ z at hc
  rw [hc.fderiv]
  simp [PiLp.proj_apply]

/-- The `j`-th component of `laplaceTraceVec` is the `laplaceTrace` of the `j`-th component. -/
lemma laplaceTraceVec_coord (G : R3 → R3) (hG : ContDiff ℝ 2 G) (z : R3) (j : Fin 3) :
    laplaceTraceVec G z j = laplaceTrace (fun z => G z j) z := by
  simp only [laplaceTraceVec, laplaceTrace]
  rw [show ((∑ i : Fin 3, (fderiv ℝ (fun w => (fderiv ℝ G w) (FiniteTimeSingularity.e i)) z)
        (FiniteTimeSingularity.e i)) : R3).ofLp j
      = ∑ i : Fin 3, ((fderiv ℝ (fun w => (fderiv ℝ G w) (FiniteTimeSingularity.e i)) z)
        (FiniteTimeSingularity.e i)).ofLp j from by
    rw [show ((∑ i : Fin 3, (fderiv ℝ (fun w => (fderiv ℝ G w) (FiniteTimeSingularity.e i)) z)
        (FiniteTimeSingularity.e i)) : R3).ofLp j
        = (EuclideanSpace.proj j) (∑ i : Fin 3, (fderiv ℝ (fun w => (fderiv ℝ G w)
          (FiniteTimeSingularity.e i)) z) (FiniteTimeSingularity.e i)) from by
      rw [EuclideanSpace.proj, PiLp.proj_apply]]
    rw [map_sum]
    rfl]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← fderiv_coord (fun w => (fderiv ℝ G w) (FiniteTimeSingularity.e i)) z ?_ j
    (FiniteTimeSingularity.e i)]
  · have hfun : (fun w : R3 => ((fderiv ℝ G w) (FiniteTimeSingularity.e i)).ofLp j)
        = fun w : R3 => (fderiv ℝ (fun z => G z j) w) (FiniteTimeSingularity.e i) := by
      funext w
      exact (fderiv_coord G w (hG.differentiable (by norm_num) w) j
        (FiniteTimeSingularity.e i)).symm
    rw [hfun]
  · fun_prop

/-- The `j`-th component of a `C²` field is `C²`. -/
lemma contDiff_coord (G : R3 → R3) (hG : ContDiff ℝ 2 G) (j : Fin 3) :
    ContDiff ℝ 2 (fun z => G z j) := by
  have := (EuclideanSpace.proj j).contDiff.comp hG
  simpa [Function.comp_def, EuclideanSpace.proj, PiLp.proj_apply] using this

/-- The `j`-th component of a compactly supported field is compactly supported. -/
lemma hasCompactSupport_coord (G : R3 → R3) (hcs : HasCompactSupport G) (j : Fin 3) :
    HasCompactSupport (fun z => G z j) := by
  have := hcs.comp_left (g := fun w : R3 => w j) (by simp)
  simpa [Function.comp_def] using this

/-- The measure `volume.restrict (uIoc 0 T)` on `ℝ` is finite. -/
lemma isFiniteMeasure_restrict_uIoc (T : ℝ) :
    IsFiniteMeasure (volume.restrict (uIoc (0 : ℝ) T)) := by
  constructor
  rw [Measure.restrict_apply_univ, Real.volume_uIoc]
  exact ENNReal.ofReal_lt_top

/-- `laplaceTrace` is supported in the support of the function. -/
lemma support_laplaceTrace_subset (φ : R3 → ℝ) :
    Function.support (laplaceTrace φ) ⊆ tsupport φ := by
  intro z hz
  by_contra hzt
  apply hz
  have hopen : IsOpen (tsupport φ)ᶜ := (isClosed_tsupport φ).isOpen_compl
  rw [laplaceTrace]
  refine Finset.sum_eq_zero fun i _ => ?_
  have hderiv0 : (fun w => fderiv ℝ φ w) =ᶠ[𝓝 z] 0 := by
    filter_upwards [hopen.mem_nhds hzt] with w hw
    have h0 : φ =ᶠ[𝓝 w] 0 := by
      filter_upwards [hopen.mem_nhds hw] with v hv
      exact image_eq_zero_of_notMem_tsupport hv
    rw [h0.fderiv_eq]
    simp
  have h1 : (fun w => fderiv ℝ φ w (FiniteTimeSingularity.e i)) =ᶠ[𝓝 z] 0 := by
    filter_upwards [hderiv0] with w hw
    rw [hw]
    simp
  have h2 : fderiv ℝ (fun w => fderiv ℝ φ w (FiniteTimeSingularity.e i)) z = 0 := by
    rw [h1.fderiv_eq]
    simp
  rw [h2]
  simp

lemma hasCompactSupport_laplaceTrace (φ : R3 → ℝ) (hcs : HasCompactSupport φ) :
    HasCompactSupport (laplaceTrace φ) :=
  HasCompactSupport.of_support_subset_isCompact hcs (support_laplaceTrace_subset φ)

lemma continuous_laplaceTrace (φ : R3 → ℝ) (hφ : ContDiff ℝ 2 φ) :
    Continuous (laplaceTrace φ) := by
  unfold laplaceTrace
  refine continuous_finsetSum _ fun i _ => ?_
  have hψ : ContDiff ℝ 1 (fun w => fderiv ℝ φ w (FiniteTimeSingularity.e i)) := by fun_prop
  have hcont := hψ.continuous_fderiv (by norm_num)
  exact (ContinuousLinearMap.apply ℝ ℝ (FiniteTimeSingularity.e i)).continuous.comp hcont

lemma integrable_laplaceTrace (φ : R3 → ℝ) (hφ : ContDiff ℝ 2 φ) (hcs : HasCompactSupport φ) :
    Integrable (laplaceTrace φ) :=
  (continuous_laplaceTrace φ hφ).integrable_of_hasCompactSupport
    (hasCompactSupport_laplaceTrace φ hcs)

/-- Majorant integrability on `(volume.restrict (uIoc 0 T)).prod volume`: a continuous function
bounded on the `s ∈ uIoc 0 T`-range by `K * ‖ψ z‖` with `ψ` integrable is integrable. -/
lemma integrable_uncurry_of_bound {T K : ℝ} {ψ : R3 → ℝ} {F : ℝ → R3 → ℝ}
    (hψ : Integrable ψ) (hcont : Continuous (Function.uncurry F))
    (hbound : ∀ s ∈ uIoc (0 : ℝ) T, ∀ z, ‖F s z‖ ≤ K * ‖ψ z‖) :
    Integrable (Function.uncurry F) ((volume.restrict (uIoc (0 : ℝ) T)).prod volume) := by
  have hfin : IsFiniteMeasure (volume.restrict (uIoc (0 : ℝ) T)) :=
    isFiniteMeasure_restrict_uIoc T
  have hmaj : Integrable (fun p : ℝ × R3 => |K| * ‖ψ p.2‖)
      ((volume.restrict (uIoc (0 : ℝ) T)).prod volume) := by
    have h := Integrable.mul_prod (μ := volume.restrict (uIoc (0 : ℝ) T)) (ν := volume)
      (f := fun _ : ℝ => |K|) (g := fun z => ‖ψ z‖) (integrable_const |K|) hψ.norm
    simpa using h
  refine Integrable.mono' hmaj hcont.aestronglyMeasurable ?_
  have hnull : ((volume.restrict (uIoc (0 : ℝ) T)).prod volume)
      {p : ℝ × R3 | p.1 ∉ uIoc (0 : ℝ) T} = 0 := by
    rw [show {p : ℝ × R3 | p.1 ∉ uIoc (0 : ℝ) T}
        = (uIoc (0 : ℝ) T)ᶜ ×ˢ (Set.univ : Set R3) from by ext p; simp]
    rw [Measure.prod_prod]
    have hz : (volume.restrict (uIoc (0 : ℝ) T)) ((uIoc (0 : ℝ) T)ᶜ) = 0 := by
      rw [Measure.restrict_apply measurableSet_uIoc.compl, Set.compl_inter_self, measure_empty]
    rw [hz, zero_mul]
  filter_upwards [MeasureTheory.ae_iff.mpr hnull] with p hp
  exact le_trans (hbound p.1 hp p.2) (mul_le_mul_of_nonneg_right (le_abs_self K) (norm_nonneg _))

/-- The Laplacian of the Gaussian profile, in the variable `s = √c`. -/
lemma laplaceTrace_gauss (s : ℝ) (z : R3) :
    laplaceTrace (fun y : R3 => Real.exp (-(s ^ 2 * ‖y‖ ^ 2))) z
      = (4 * s ^ 4 * ‖z‖ ^ 2 - 6 * s ^ 2) * Real.exp (-(s ^ 2 * ‖z‖ ^ 2)) := by
  rw [laplaceTrace_exp_neg_mul_normSq (s ^ 2) z]
  ring_nf

/-- The Gaussian profile `s ↦ exp (-(s²‖z‖²))` is bounded by one. -/
lemma exp_neg_sq_le_one (s : ℝ) (z : R3) : ‖Real.exp (-(s ^ 2 * ‖z‖ ^ 2))‖ ≤ 1 := by
  rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
  exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg (sq_nonneg s) (sq_nonneg _)))

/-- The Gaussian profile is `C²`. -/
lemma contDiff_gauss (s : ℝ) :
    ContDiff ℝ 2 (fun y : R3 => Real.exp (-(s ^ 2 * ‖y‖ ^ 2))) := by
  have h1 : ContDiff ℝ 2 (fun y : R3 => ‖y‖ ^ 2) := contDiff_norm_sq ℝ
  have h2 : ContDiff ℝ 2 (fun y : R3 => s ^ 2 * ‖y‖ ^ 2) :=
    ContDiff.const_smul (s ^ 2) h1
  have h3 : ContDiff ℝ 2 (fun y : R3 => -(s ^ 2 * ‖y‖ ^ 2)) := ContDiff.neg h2
  exact ContDiff.exp h3

/-- On `uIoc 0 T` one has `s² ≤ T²`. -/
lemma sq_le_sq_of_mem_uIoc {s T : ℝ} (hs : s ∈ uIoc (0 : ℝ) T) : s ^ 2 ≤ T ^ 2 := by
  rcases le_total 0 T with hT | hT
  · rw [Set.uIoc_of_le hT] at hs
    have h := mul_self_le_mul_self hs.1.le hs.2
    simpa [sq] using h
  · rw [Set.uIoc_of_ge hT] at hs
    have h1 : -s ≤ -T := by linarith [hs.1]
    have h2 : (0 : ℝ) ≤ -s := by linarith [hs.2]
    have h := mul_self_le_mul_self h2 h1
    nlinarith [h]

/-- The pointwise bound on the Laplacian of the Gaussian profile used for the majorant of the
second Fubini step: for `s² ≤ T²`, `‖Δ(exp(-s²‖·‖²)) z‖ ≤ 10 T²`. -/
lemma norm_laplaceTrace_gauss_le {s T : ℝ} (hT : s ^ 2 ≤ T ^ 2) (z : R3) :
    ‖laplaceTrace (fun y : R3 => Real.exp (-(s ^ 2 * ‖y‖ ^ 2))) z‖ ≤ 10 * T ^ 2 := by
  have hr : (0 : ℝ) ≤ ‖z‖ ^ 2 := sq_nonneg _
  have hpos : (0 : ℝ) ≤ Real.exp (-(s ^ 2 * ‖z‖ ^ 2)) := Real.exp_nonneg _
  have he : Real.exp (-(s ^ 2 * ‖z‖ ^ 2)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg (sq_nonneg s) hr))
  have hu : (s ^ 2 * ‖z‖ ^ 2) * Real.exp (-(s ^ 2 * ‖z‖ ^ 2)) ≤ 1 := by
    have h := Real.mul_exp_neg_le_exp_neg_one (s ^ 2 * ‖z‖ ^ 2)
    have h2 : Real.exp (-1 : ℝ) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
    linarith
  have h4 : 4 * s ^ 4 * ‖z‖ ^ 2 * Real.exp (-(s ^ 2 * ‖z‖ ^ 2)) ≤ 4 * T ^ 2 := by
    have hkey : 4 * s ^ 4 * ‖z‖ ^ 2 * Real.exp (-(s ^ 2 * ‖z‖ ^ 2))
        = 4 * (s ^ 2 * ((s ^ 2 * ‖z‖ ^ 2) * Real.exp (-(s ^ 2 * ‖z‖ ^ 2)))) := by ring
    rw [hkey]
    calc 4 * (s ^ 2 * ((s ^ 2 * ‖z‖ ^ 2) * Real.exp (-(s ^ 2 * ‖z‖ ^ 2))))
        ≤ 4 * (s ^ 2 * 1) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          exact mul_le_mul_of_nonneg_left hu (sq_nonneg s)
      _ = 4 * s ^ 2 := by ring
      _ ≤ 4 * T ^ 2 := by linarith
  have h6 : 6 * s ^ 2 * Real.exp (-(s ^ 2 * ‖z‖ ^ 2)) ≤ 6 * T ^ 2 := by
    calc 6 * s ^ 2 * Real.exp (-(s ^ 2 * ‖z‖ ^ 2)) ≤ 6 * s ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left he (by positivity)
      _ ≤ 6 * T ^ 2 := by linarith
  rw [laplaceTrace_gauss, Real.norm_eq_abs, abs_mul, abs_of_nonneg hpos]
  calc |4 * s ^ 4 * ‖z‖ ^ 2 - 6 * s ^ 2| * Real.exp (-(s ^ 2 * ‖z‖ ^ 2))
      ≤ (4 * s ^ 4 * ‖z‖ ^ 2 + 6 * s ^ 2) * Real.exp (-(s ^ 2 * ‖z‖ ^ 2)) := by
        refine mul_le_mul_of_nonneg_right ?_ hpos
        calc |4 * s ^ 4 * ‖z‖ ^ 2 - 6 * s ^ 2|
            ≤ |4 * s ^ 4 * ‖z‖ ^ 2| + |6 * s ^ 2| := abs_sub _ _
          _ = 4 * s ^ 4 * ‖z‖ ^ 2 + 6 * s ^ 2 := by
              rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    _ = 4 * s ^ 4 * ‖z‖ ^ 2 * Real.exp (-(s ^ 2 * ‖z‖ ^ 2))
        + 6 * s ^ 2 * Real.exp (-(s ^ 2 * ‖z‖ ^ 2)) := by ring
    _ ≤ 4 * T ^ 2 + 6 * T ^ 2 := add_le_add h4 h6
    _ = 10 * T ^ 2 := by ring

/-- The parametric `s`-integral of the Gaussian weights is continuous in `z`. -/
lemma continuous_parametric_gauss (T : ℝ) :
    Continuous (fun z : R3 => ∫ s in (0 : ℝ)..T, Real.exp (-(s ^ 2 * ‖z‖ ^ 2))) := by
  fun_prop

/-- The parametric `s`-integral of the Gaussian weights is bounded by `|T|`. -/
lemma norm_parametric_gauss_le (T : ℝ) (z : R3) :
    ‖∫ s in (0 : ℝ)..T, Real.exp (-(s ^ 2 * ‖z‖ ^ 2))‖ ≤ |T| := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := T) (C := 1) (f := fun s : ℝ => Real.exp (-(s ^ 2 * ‖z‖ ^ 2)))
    (fun s _ => exp_neg_sq_le_one s z)
  simpa using h

/-- The parametric Gaussian weight against `laplaceTrace ψ` is integrable. -/
lemma integrable_gauss_mul_laplaceTrace (T : ℝ) (ψ : R3 → ℝ) (hψ : ContDiff ℝ 2 ψ)
    (hcs : HasCompactSupport ψ) :
    Integrable (fun z : R3 =>
      (∫ s in (0 : ℝ)..T, Real.exp (-(s ^ 2 * ‖z‖ ^ 2))) * laplaceTrace ψ z) := by
  have hψ' := integrable_laplaceTrace ψ hψ hcs
  have hmaj : Integrable (fun z : R3 => |T| * ‖laplaceTrace ψ z‖) := hψ'.norm.const_mul |T|
  refine Integrable.mono' hmaj ?_ ?_
  · exact ((continuous_parametric_gauss T).mul (continuous_laplaceTrace ψ hψ)).aestronglyMeasurable
  · filter_upwards with z
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_right (norm_parametric_gauss_le T z) (norm_nonneg _)

end IgslvAux

open IgslvAux

/-- **The scalar core**: for a `C²` compactly supported `φ`, the `s`-integral of the Gaussian
weights against `Δφ` equals `-2T³` times the Gaussian at `T` integrated against `φ`, given the
Green identity that moves `Δ` off `φ` and onto the Gaussian weights. -/
theorem scalar_core (T : ℝ) (φ : R3 → ℝ) (hφ : ContDiff ℝ 2 φ) (hcs : HasCompactSupport φ)
    (hgreen : ∀ s : ℝ, ∫ z, Real.exp (-(s ^ 2 * ‖z‖ ^ 2)) * laplaceTrace φ z
      = ∫ z, laplaceTrace (fun y : R3 => Real.exp (-(s ^ 2 * ‖y‖ ^ 2))) z * φ z) :
    ∫ z, (∫ s in (0 : ℝ)..T, Real.exp (-(s ^ 2 * ‖z‖ ^ 2))) * laplaceTrace φ z
      = -(2 * T ^ 3) * ∫ z, Real.exp (-(T ^ 2 * ‖z‖ ^ 2)) * φ z := by
  have hΔint : Integrable (laplaceTrace φ) := integrable_laplaceTrace φ hφ hcs
  have hφint : Integrable φ := hφ.continuous.integrable_of_hasCompactSupport hcs
  -- Step 1: the product of the `s`-integral with `Δφ` is the `s`-integral of the product.
  have h1 : ∫ z, (∫ s in (0 : ℝ)..T, Real.exp (-(s ^ 2 * ‖z‖ ^ 2))) * laplaceTrace φ z
      = ∫ z, ∫ s in (0 : ℝ)..T, Real.exp (-(s ^ 2 * ‖z‖ ^ 2)) * laplaceTrace φ z := by
    refine integral_congr_ae ?_
    filter_upwards with z
    rw [intervalIntegral.integral_mul_const]
  rw [h1]
  -- Step 2: Fubini.
  have hInt1 : Integrable
      (Function.uncurry (fun s z => Real.exp (-(s ^ 2 * ‖z‖ ^ 2)) * laplaceTrace φ z))
      ((volume.restrict (uIoc (0 : ℝ) T)).prod volume) := by
    refine integrable_uncurry_of_bound (K := 1) hΔint ?_ ?_
    · have h2 : Continuous (fun p : ℝ × R3 => Real.exp (-(p.1 ^ 2 * ‖p.2‖ ^ 2))) := by fun_prop
      have h3 : Continuous (fun p : ℝ × R3 => laplaceTrace φ p.2) :=
        (continuous_laplaceTrace φ hφ).comp continuous_snd
      exact h2.mul h3
    · intro s hs z
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (exp_neg_sq_le_one s z) (norm_nonneg _)
  rw [← intervalIntegral_integral_swap hInt1]
  -- Step 3: Green's identity, one slice at a time.
  have h2 : ∫ s in (0 : ℝ)..T, ∫ z, Real.exp (-(s ^ 2 * ‖z‖ ^ 2)) * laplaceTrace φ z
      = ∫ s in (0 : ℝ)..T,
          ∫ z, laplaceTrace (fun y : R3 => Real.exp (-(s ^ 2 * ‖y‖ ^ 2))) z * φ z := by
    refine intervalIntegral.integral_congr fun s _ => hgreen s
  rw [h2]
  -- Step 4: Fubini back.
  have hInt2 : Integrable
      (Function.uncurry (fun s z =>
        laplaceTrace (fun y : R3 => Real.exp (-(s ^ 2 * ‖y‖ ^ 2))) z * φ z))
      ((volume.restrict (uIoc (0 : ℝ) T)).prod volume) := by
    refine integrable_uncurry_of_bound (K := 10 * T ^ 2) hφint ?_ ?_
    · have h2 : Continuous (fun p : ℝ × R3 => laplaceTrace
          (fun y : R3 => Real.exp (-(p.1 ^ 2 * ‖y‖ ^ 2))) p.2) := by
        have hfun : (fun p : ℝ × R3 => laplaceTrace
              (fun y : R3 => Real.exp (-(p.1 ^ 2 * ‖y‖ ^ 2))) p.2)
            = fun p : ℝ × R3 => (4 * p.1 ^ 4 * ‖p.2‖ ^ 2 - 6 * p.1 ^ 2)
                * Real.exp (-(p.1 ^ 2 * ‖p.2‖ ^ 2)) := by
          funext p
          exact laplaceTrace_gauss p.1 p.2
        rw [hfun]
        fun_prop
      have h3 : Continuous (fun p : ℝ × R3 => φ p.2) := hφ.continuous.comp continuous_snd
      exact h2.mul h3
    · intro s hs z
      rw [norm_mul]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      exact norm_laplaceTrace_gauss_le (sq_le_sq_of_mem_uIoc hs) z
  rw [intervalIntegral_integral_swap hInt2]
  -- Step 5: the pointwise `s`-integral.
  have h3 : ∫ z, (∫ s in (0 : ℝ)..T,
        laplaceTrace (fun y : R3 => Real.exp (-(s ^ 2 * ‖y‖ ^ 2))) z * φ z)
      = ∫ z, -(2 * T ^ 3) * (Real.exp (-(T ^ 2 * ‖z‖ ^ 2)) * φ z) := by
    refine integral_congr_ae ?_
    filter_upwards with z
    rw [intervalIntegral.integral_mul_const]
    have hpt : (∫ s in (0 : ℝ)..T,
          laplaceTrace (fun y : R3 => Real.exp (-(s ^ 2 * ‖y‖ ^ 2))) z)
        = -2 * T ^ 3 * Real.exp (-(T ^ 2 * ‖z‖ ^ 2)) := by
      rw [show (∫ s in (0 : ℝ)..T,
            laplaceTrace (fun y : R3 => Real.exp (-(s ^ 2 * ‖y‖ ^ 2))) z)
          = ∫ s in (0 : ℝ)..T,
              (4 * s ^ 4 * ‖z‖ ^ 2 - 6 * s ^ 2) * Real.exp (-(s ^ 2 * ‖z‖ ^ 2)) from
        intervalIntegral.integral_congr fun s _ => laplaceTrace_gauss s z]
      exact integral_quartic_exp_neg_mul_sq T (‖z‖ ^ 2)
    rw [hpt]
    ring
  rw [h3, integral_const_mul]

/-- **The vector statement, given the scalar Green identity.** -/
theorem integral_gauss_smul_laplaceTraceVec_of_scalar (T : ℝ) (G : R3 → R3)
    (hG : ContDiff ℝ 2 G) (hcs : HasCompactSupport G)
    (hgreen : ∀ (s : ℝ) (j : Fin 3),
      ∫ z, Real.exp (-(s ^ 2 * ‖z‖ ^ 2)) * laplaceTrace (fun z => G z j) z
        = ∫ z, laplaceTrace (fun y : R3 => Real.exp (-(s ^ 2 * ‖y‖ ^ 2))) z
            * (fun z => G z j) z) :
    ∫ z, (∫ s in (0 : ℝ)..T, Real.exp (-(s ^ 2 * ‖z‖ ^ 2))) • laplaceTraceVec G z
      = -(2 * T ^ 3) • ∫ z, Real.exp (-(T ^ 2 * ‖z‖ ^ 2)) • G z := by
  -- integrability of the two vector integrands
  have hintL : ∀ i : Fin 3, Integrable (fun z : R3 =>
      ((∫ s in (0 : ℝ)..T, Real.exp (-(s ^ 2 * ‖z‖ ^ 2))) • laplaceTraceVec G z) i) := by
    intro i
    have h := integrable_gauss_mul_laplaceTrace T (fun z => G z i) (contDiff_coord G hG i)
      (hasCompactSupport_coord G hcs i)
    refine h.congr ?_
    filter_upwards with z
    rw [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, laplaceTraceVec_coord G hG z i]
  have hintR : Integrable (fun z : R3 => Real.exp (-(T ^ 2 * ‖z‖ ^ 2)) • G z) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · fun_prop
    · refine HasCompactSupport.of_support_subset_isCompact hcs ?_
      intro z hz
      rw [Function.mem_support] at hz
      exact subset_tsupport _ (by
        rw [Function.mem_support]
        intro h0
        exact hz (by simp [h0]))
  refine PiLp.ext fun j => ?_
  have hLHS : (∫ z, (∫ s in (0 : ℝ)..T, Real.exp (-(s ^ 2 * ‖z‖ ^ 2))) • laplaceTraceVec G z).ofLp j
      = ∫ z, (∫ s in (0 : ℝ)..T, Real.exp (-(s ^ 2 * ‖z‖ ^ 2)))
          * laplaceTrace (fun z => G z j) z := by
    rw [MeasureTheory.eval_integral_piLp hintL j]
    refine integral_congr_ae ?_
    filter_upwards with z
    rw [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, laplaceTraceVec_coord G hG z j]
  have hRHS : (-(2 * T ^ 3) • ∫ z, Real.exp (-(T ^ 2 * ‖z‖ ^ 2)) • G z).ofLp j
      = -(2 * T ^ 3) * ∫ z, Real.exp (-(T ^ 2 * ‖z‖ ^ 2)) * (G z).ofLp j := by
    rw [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
    rw [MeasureTheory.eval_integral_piLp (fun i => hintR.eval_piLp i) j]
    have hfun : (fun x : R3 => (Real.exp (-(T ^ 2 * ‖x‖ ^ 2)) • G x).ofLp j)
        = fun x : R3 => Real.exp (-(T ^ 2 * ‖x‖ ^ 2)) * (G x).ofLp j := by
      funext x
      rw [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
    rw [hfun]
  rw [hLHS, hRHS]
  exact scalar_core T (fun z => G z j) (contDiff_coord G hG j)
    (hasCompactSupport_coord G hcs j) (fun s => hgreen s j)

/-- **The Green-function identity for the Gaussian scale of the Laplacian.**

For `G : ℝ³ → ℝ³` of class `C²` with compact support and any real `T`,
`∫ z, (∫ s in 0..T, exp (-(s²‖z‖²))) • ΔG z = -(2T³) • ∫ z, exp (-(T²‖z‖²)) • G z`. -/
theorem integral_gauss_smul_laplaceTraceVec
    (T : ℝ) (G : Work.FTS.PressureOn.R3 → Work.FTS.PressureOn.R3)
    (hG : ContDiff ℝ 2 G) (hcs : HasCompactSupport G) :
    ∫ z, (∫ s in (0 : ℝ)..T, Real.exp (-(s ^ 2 * ‖z‖ ^ 2)))
        • Work.FTS.PressureOn.laplaceTraceVec G z
      = -(2 * T ^ 3) • ∫ z, Real.exp (-(T ^ 2 * ‖z‖ ^ 2)) • G z :=
  integral_gauss_smul_laplaceTraceVec_of_scalar T G hG hcs fun s j =>
    integral_mul_laplaceTrace_comm (fun y : R3 => Real.exp (-(s ^ 2 * ‖y‖ ^ 2)))
      (fun z => G z j) (contDiff_gauss s) (contDiff_coord G hG j)
      (hasCompactSupport_coord G hcs j)

end Work.FTS.PressureOn.Green
