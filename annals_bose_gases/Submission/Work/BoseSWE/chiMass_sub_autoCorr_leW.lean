import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Submission.Work.BoseFixB1.SectorAux.chiSmallB_lipschitz
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END


/-!
# `Work.BoseSWE.chiMass_sub_autoCorr_leW` -- a `devFTCDefs`-free copy of
# `Work.BoseB1Cube.chiMass_sub_autoCorr_le`

The corpus declares `Work.BoseB1Cube.sq_integral_le_integral_sq` **twice** (in
`Submission/Work/BoseB1Cube/sq_integral_le_integral_sq.lean` and in
`Submission/Work/BoseB1Cube/devFTCDefs.lean`), so no import cone may contain both
`Submission.Work.BoseB1Cube.devFTCDefs` and `Submission.Work.BoseB1Cube.sq_integral_le_integral_sq`.
`Work.BoseRoot.Assembly`'s cone contains the latter, hence this module must avoid the former.

This module is a **verbatim transcription** of the six corpus files

* `Submission/Work/BoseB1Cube/devFTCDefs.lean`
* `Submission/Work/BoseB1Cube/aeShiftDifferentiable.lean`
* `Submission/Work/BoseB1Cube/integrableIntegralShiftGrad.lean`
* `Submission/Work/BoseB1Cube/integralIntegralShiftGrad.lean`
* `Submission/Work/BoseB1Cube/devFTC.lean`
* `Submission/Work/BoseB1Cube/chiMass_sub_autoCorr_le.lean`

into the single namespace `Work.BoseSWE.CopyDev` (the internal imports between them are dropped
since they now live in one file).  The final result is re-exported, outside that namespace, as
`Work.BoseSWE.chiMass_sub_autoCorr_leW`, whose statement is byte-identical to the corpus's
`Work.BoseB1Cube.chiMass_sub_autoCorr_le`.
-/

noncomputable section

open MeasureTheory Filter Metric
open scoped Topology Real ENNReal NNReal

namespace Work.BoseSWE.CopyDev

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-!
# Support definitions for `Work.BoseB1Cube.devFTC`

This module holds the definitions and elementary lemmas that the proof of
`Work.BoseB1Cube.devFTC` (and its delegated sub-lemmas) need.  It is deliberately sorry-free and
contains no analysis beyond the elementary.

* `devNu` is the probability measure `volume ↾ (0,1]` on the parameter of the segment from `x` to
  `x + s`; the fundamental theorem of calculus represents the increment as an integral against it.
* `sq_integral_le_integral_sq` is Cauchy–Schwarz `(∫ h ∂μ)² ≤ ∫ h² ∂μ` for a probability measure.
* `norm_gradient_eq_norm_fderiv` identifies the norm of the gradient with the operator norm of the
  Fréchet derivative (the Riesz map is an isometry).
* `lipschitzWith_of_abs_sub_le` converts the `|g x - g y| ≤ L ‖x - y‖` form to `LipschitzWith`.
* `deriv_shift_eq_lineDeriv` identifies the one-dimensional derivative of the shifted function
  with the line derivative of `g` in the direction `s`.
-/


open MeasureTheory Filter Metric
open scoped Topology Real ENNReal NNReal



/-- The probability measure carried by the unit interval `(0,1]`: the parameter measure of the
fundamental-theorem-of-calculus representation of the segment from `x` to `x + s`. -/
def devNu : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1)

theorem devNu_univ : devNu Set.univ = 1 := by
  rw [devNu, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Ioc]
  norm_num

instance instIsProbabilityMeasureDevNu : IsProbabilityMeasure devNu := ⟨devNu_univ⟩

/-- **Cauchy–Schwarz** for a probability measure `μ` on `ℝ`: `(∫ h ∂μ)² ≤ ∫ h² ∂μ`. -/
theorem sq_integral_le_integral_sq {μ : Measure ℝ} [IsProbabilityMeasure μ] {h : ℝ → ℝ}
    (h1 : Integrable h μ) (h2 : Integrable (fun t => h t ^ 2) μ) :
    (∫ t, h t ∂μ) ^ 2 ≤ ∫ t, h t ^ 2 ∂μ := by
  have h1' : Integrable (fun t => |h t|) μ := by simpa [Real.norm_eq_abs] using h1.norm
  have h2' : Integrable (fun t => |h t| ^ 2) μ := by simpa [sq_abs] using h2
  have hJ : (∫ t, |h t| ∂μ) ^ 2 ≤ ∫ t, |h t| ^ 2 ∂μ :=
    (convexOn_pow (𝕜 := ℝ) 2).map_integral_le (continuous_pow 2).continuousOn isClosed_Ici
      (Filter.Eventually.of_forall fun t => by simpa using abs_nonneg (h t)) h1' h2'
  have habs : |∫ t, h t ∂μ| ≤ ∫ t, |h t| ∂μ := abs_integral_le_integral_abs
  refine le_trans ?_ (le_trans hJ (le_of_eq ?_))
  · obtain ⟨ha, hb⟩ := abs_le.mp habs
    exact sq_le_sq' ha hb
  · exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => sq_abs (h t))

/-- The norm of the gradient is the operator norm of the Fréchet derivative. -/
theorem norm_gradient_eq_norm_fderiv (g : E3 → ℝ) (x : E3) :
    ‖gradient g x‖ = ‖fderiv ℝ g x‖ := by
  rw [← LinearIsometryEquiv.norm_map (InnerProductSpace.toDual ℝ E3) (gradient g x),
    toDual_gradient]

/-- The `|g x - g y| ≤ L ‖x - y‖` form of a Lipschitz bound, as a `LipschitzWith`. -/
theorem lipschitzWith_of_abs_sub_le {g : E3 → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ x y : E3, |g x - g y| ≤ L * ‖x - y‖) :
    LipschitzWith (Real.toNNReal L) g := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.dist_eq, Real.coe_toNNReal L hL, dist_eq_norm]
  exact hlip x y

/-- The one-dimensional derivative of `u ↦ g (y + u • s)` at `t` is the line derivative of `g` at
`y + t • s` in the direction `s`. -/
theorem deriv_shift_eq_lineDeriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : E → ℝ) (y s : E) (t : ℝ) :
    deriv (fun u : ℝ => g (y + u • s)) t = lineDeriv ℝ g (y + t • s) s := by
  rw [lineDeriv]
  have h := deriv_comp_const_add (fun u : ℝ => g (y + u • s)) t 0
  rw [add_zero] at h
  rw [← h]
  congr 1
  ext u
  rw [add_smul, add_assoc]

/-- The derivative of the shifted function is bounded by the Lipschitz constant times `‖s‖`. -/
theorem abs_deriv_shift_le {g : E3 → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g) (y s : E3) (t : ℝ) :
    |deriv (fun u : ℝ => g (y + u • s)) t| ≤ (K : ℝ) * ‖s‖ := by
  rw [deriv_shift_eq_lineDeriv, ← Real.norm_eq_abs]
  exact norm_lineDeriv_le_of_lipschitz ℝ hg
open MeasureTheory


/-- **A Lipschitz function is differentiable along almost every translate of the segment
`y ↦ y + t • s`.**  For almost every `y` and almost every `t ∈ (0,1]`, the point `y + t • s` is a
point of differentiability of `g`.

This is Rademacher's theorem (`LipschitzWith.ae_differentiableAt`) combined with the fact that the
parametrisation `(y,t) ↦ y + t • s` is non-singular: each of its slices `y ↦ y + t • s` is a
translation, hence preserves Lebesgue measure, and `MeasureTheory.Measure.prod_of_left` +
`MeasureTheory.Measure.ae_ae_of_ae_prod` turn the parametrised a.e. statement into an iterated one.
No measurability of the differentiability set is needed. -/
theorem aeShiftDifferentiable {g : EuclideanSpace ℝ (Fin 3) → ℝ} {K : NNReal} (hg : LipschitzWith K g)
    (s : EuclideanSpace ℝ (Fin 3)) :
    ∀ᵐ y ∂(volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))),
      ∀ᵐ t ∂devNu, DifferentiableAt ℝ g (y + t • s) := by
  -- Rademacher: `g` is differentiable almost everywhere.
  have hrad : ∀ᵐ z ∂(volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))),
      DifferentiableAt ℝ g z := hg.ae_differentiableAt
  -- The parametrisation `p ↦ p.1 + p.2 • s` is quasi-measure-preserving, i.e. it does not send
  -- a null set of parameters to a set of positive measure: each slice `y ↦ y + r • s` is a
  -- translation of `E3`, hence measure preserving.
  have hF : MeasureTheory.Measure.QuasiMeasurePreserving
      (fun p : EuclideanSpace ℝ (Fin 3) × ℝ => p.1 + p.2 • s)
      ((volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
        (volume : MeasureTheory.Measure ℝ))
      (volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) := by
    refine MeasureTheory.QuasiMeasurePreserving.prod_of_left ?_ ?_
    · fun_prop
    · exact Filter.Eventually.of_forall fun r => (measurePreserving_add_right
        (volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) (r • s)).quasiMeasurePreserving
  -- Pull the a.e. differentiability back along the parametrisation.
  have hae : ∀ᵐ p ∂((volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
      (volume : MeasureTheory.Measure ℝ)), DifferentiableAt ℝ g (p.1 + p.2 • s) := hF.ae hrad
  -- Uncurry the product-a.e. statement (valid for arbitrary predicates).
  have h2 : ∀ᵐ y ∂(volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))),
      ∀ᵐ t ∂(volume : MeasureTheory.Measure ℝ), DifferentiableAt ℝ g (y + t • s) :=
    MeasureTheory.Measure.ae_ae_of_ae_prod hae
  filter_upwards [h2] with y hy
  -- Restrict the parameter to the unit interval `(0,1]`, i.e. to `devNu`.
  exact MeasureTheory.ae_restrict_of_ae hy
/-!
# Integrability of the shifted, parameter-averaged squared gradient

`devNu` is the probability measure carried by the unit interval `(0,1]`.  For a Lipschitz function
`g` with compact support and a shift vector `s`, the function

    y ↦ ∫ t, ‖∇g (y + t • s)‖² ∂devNu

is integrable: it is measurable, bounded by `K²`, and vanishes off the compact set of points whose
forward segment towards `s` meets `tsupport g`.
-/


open MeasureTheory Filter Metric
open scoped Topology Real ENNReal NNReal



/-- The Fréchet derivative of a function with compact support vanishes outside the (compact)
topological support of the function. -/
private lemma fderiv_eq_zero_of_notMem_tsupport {g : E3 → ℝ} {z : E3}
    (hz : z ∉ tsupport g) : fderiv ℝ g z = 0 := by
  have hU : (tsupport g)ᶜ ∈ 𝓝 z := (isClosed_tsupport g).isOpen_compl.mem_nhds hz
  have hev : g =ᶠ[𝓝 z] (fun _ : E3 => (0 : ℝ)) := by
    filter_upwards [hU] with w hw
    exact image_eq_zero_of_notMem_tsupport hw
  rw [hev.fderiv_eq]
  simp

/-- The parametrised integral of the squared Fréchet derivative is a.e.-strongly-measurable. -/
private lemma aestronglyMeasurable_integral_fderiv_sq (g : E3 → ℝ) (s : E3) :
    AEStronglyMeasurable (fun y : E3 => ∫ t, ‖fderiv ℝ g (y + t • s)‖ ^ 2 ∂devNu) volume := by
  have hcont : Continuous fun p : E3 × ℝ => p.1 + p.2 • s :=
    continuous_fst.add (continuous_snd.smul continuous_const)
  have hG : Measurable (fun p : E3 × ℝ => ‖fderiv ℝ g (p.1 + p.2 • s)‖ ^ 2) :=
    ((measurable_fderiv ℝ g).norm.pow_const 2).comp hcont.measurable
  exact hG.aestronglyMeasurable.integral_prod_right'

/-- Pointwise bound of the parametrised integral by the square of the Lipschitz constant. -/
private lemma norm_integral_fderiv_sq_le {g : E3 → ℝ} {K : NNReal} (hg : LipschitzWith K g)
    (s y : E3) : ‖∫ t, ‖fderiv ℝ g (y + t • s)‖ ^ 2 ∂devNu‖ ≤ (K : ℝ) ^ 2 := by
  have hbound : ∀ z : E3, ‖fderiv ℝ g z‖ ^ 2 ≤ (K : ℝ) ^ 2 := by
    intro z
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_fderiv_le_of_lipschitz (𝕜 := ℝ) hg (x₀ := z)) 2
  have hnn : 0 ≤ ∫ t, ‖fderiv ℝ g (y + t • s)‖ ^ 2 ∂devNu :=
    integral_nonneg fun t => by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  have hmono : ∫ t, ‖fderiv ℝ g (y + t • s)‖ ^ 2 ∂devNu ≤ ∫ t, (K : ℝ) ^ 2 ∂devNu :=
    integral_mono_of_nonneg (Eventually.of_forall fun t => by positivity) (integrable_const _)
      (Eventually.of_forall fun t => hbound (y + t • s))
  have hconst : (∫ t, (K : ℝ) ^ 2 ∂devNu) = (K : ℝ) ^ 2 := by
    simp [MeasureTheory.probReal_univ]
  exact hmono.trans hconst.le

/-- The parametrised integral vanishes off the compact set of points whose forward segment
towards `s` meets `tsupport g`. -/
private lemma integral_fderiv_sq_eq_zero_of_notMem {g : E3 → ℝ} {s y : E3}
    (hy : y ∉ (fun p : E3 × ℝ => p.1 - p.2 • s) '' (tsupport g ×ˢ Set.Icc (0 : ℝ) 1)) :
    (∫ t, ‖fderiv ℝ g (y + t • s)‖ ^ 2 ∂devNu) = 0 := by
  refine integral_eq_zero_of_ae ?_
  filter_upwards [MeasureTheory.self_mem_ae_restrict
    (μ := volume) (s := Set.Ioc (0 : ℝ) 1) measurableSet_Ioc] with t ht
  have hts : t ∈ Set.Icc (0 : ℝ) 1 := Set.Ioc_subset_Icc_self ht
  have hmem : y + t • s ∉ tsupport g := by
    intro hcon
    apply hy
    exact ⟨(y + t • s, t), ⟨hcon, hts⟩, by simp⟩
  rw [fderiv_eq_zero_of_notMem_tsupport hmem]
  simp

theorem integrableIntegralShiftGrad {g : EuclideanSpace ℝ (Fin 3) → ℝ} {K : NNReal}
    (hg : LipschitzWith K g) (hsupp : HasCompactSupport g) (s : EuclideanSpace ℝ (Fin 3)) :
    MeasureTheory.Integrable (fun y => ∫ t, ‖gradient g (y + t • s)‖ ^ 2 ∂devNu) := by
  set S : Set E3 := (fun p : E3 × ℝ => p.1 - p.2 • s) '' (tsupport g ×ˢ Set.Icc (0 : ℝ) 1)
    with hSdef
  have hScomp : IsCompact S := by
    rw [hSdef]
    exact (hsupp.isCompact.prod isCompact_Icc).image
      (continuous_fst.sub (continuous_snd.smul continuous_const))
  have hmeas := aestronglyMeasurable_integral_fderiv_sq g s
  have hzero : ∀ y : E3, y ∉ S →
      (fun y : E3 => ∫ t, ‖fderiv ℝ g (y + t • s)‖ ^ 2 ∂devNu) y = 0 := by
    intro y hy
    refine integral_fderiv_sq_eq_zero_of_notMem (g := g) (s := s) ?_
    rwa [hSdef] at hy
  have hIntOn : IntegrableOn (fun y : E3 => ∫ t, ‖fderiv ℝ g (y + t • s)‖ ^ 2 ∂devNu) S volume :=
    IntegrableOn.of_bound hScomp.measure_lt_top (hmeas.mono_measure Measure.restrict_le_self)
      ((K : ℝ) ^ 2) (Eventually.of_forall fun y => norm_integral_fderiv_sq_le hg s y)
  have hres : Integrable (fun y : E3 => ∫ t, ‖fderiv ℝ g (y + t • s)‖ ^ 2 ∂devNu) volume :=
    hIntOn.integrable_of_forall_notMem_eq_zero hzero
  refine hres.congr (Eventually.of_forall fun y => ?_)
  exact integral_congr_ae
    (Eventually.of_forall fun t => by simp [norm_gradient_eq_norm_fderiv])
/-!
# Averaging the squared gradient over a segment

This module proves `integralIntegralShiftGrad`: for a Lipschitz function `g` with compact support
on `ℝ³` and any direction `s`,

  `∫_y ∫_t ‖∇g (y + t • s)‖² dν(t) dy = ∫_z ‖∇g z‖² dz`,

where `ν = devNu = volume ↾ (0,1]` is the probability measure carried by the unit interval.

The mathematical content is translation invariance of Lebesgue measure: for every `t` the inner
integral over `y` is `∫_z ‖∇g z‖² dz`, and then the outer integral against the probability measure
`ν` leaves that value unchanged.  Formally the two `y`/`t` integrals are interchanged with Fubini
(`MeasureTheory.integral_integral_swap`), which requires joint integrability of
`(y,t) ↦ ‖∇g (y + t • s)‖²` with respect to `volume.prod devNu`.  That integrability is obtained by
dominating the integrand by the indicator of a compact box together with the global Lipschitz bound
`‖∇g‖ ≤ K` and the fact that `∇g` vanishes off `tsupport g`.

The auxiliary facts used are the elementary ones from `devFTCDefs`
(`norm_gradient_eq_norm_fderiv`), plus the support calculus for `fderiv`.
-/


open MeasureTheory Filter Metric
open scoped Topology



/-- The gradient of a `K`-Lipschitz function is bounded by `K` everywhere. -/
private lemma norm_gradient_le_of_lipschitz {g : E3 → ℝ} {K : NNReal} (hg : LipschitzWith K g)
    (z : E3) : ‖gradient g z‖ ≤ (K : ℝ) := by
  rw [norm_gradient_eq_norm_fderiv]
  exact norm_fderiv_le_of_lipschitz ℝ hg

/-- The gradient of a function vanishes off the (closed) topological support of the function:
on the open complement of `tsupport g` the function is eventually `0`, so its derivative is `0`. -/
private lemma gradient_eq_zero_of_notMem_tsupport {g : E3 → ℝ} {z : E3}
    (hz : z ∉ tsupport g) : gradient g z = 0 := by
  have hfd : fderiv ℝ g z = 0 := by
    have hU : (tsupport g)ᶜ ∈ 𝓝 z := (isClosed_tsupport g).isOpen_compl.mem_nhds hz
    have hev : g =ᶠ[𝓝 z] (fun _ : E3 => (0 : ℝ)) := by
      filter_upwards [hU] with y hy
      exact image_eq_zero_of_notMem_tsupport hy
    rw [hev.fderiv_eq]
    simp
  have h1 : (InnerProductSpace.toDual ℝ E3) (gradient g z) = (InnerProductSpace.toDual ℝ E3) 0 := by
    rw [toDual_gradient, hfd, map_zero]
  exact (InnerProductSpace.toDual ℝ E3).injective h1

/-- The squared norm of the gradient of a Lipschitz function with compact support is integrable:
it is bounded by `K²` and vanishes off the compact set `tsupport g`. -/
private lemma integrable_gradient_norm_sq {g : E3 → ℝ} {K : NNReal} (hg : LipschitzWith K g)
    (hsupp : HasCompactSupport g) :
    Integrable (fun z : E3 => ‖gradient g z‖ ^ 2) volume := by
  have hmeas : Measurable (fun z : E3 => ‖gradient g z‖ ^ 2) := by
    have heq : (fun z : E3 => ‖gradient g z‖ ^ 2) = fun z : E3 => ‖fderiv ℝ g z‖ ^ 2 := by
      funext z; rw [norm_gradient_eq_norm_fderiv]
    rw [heq]
    exact (measurable_fderiv ℝ g).norm.pow_const 2
  have hzero : ∀ z : E3, z ∉ tsupport g → ‖gradient g z‖ ^ 2 = 0 := by
    intro z hz
    rw [gradient_eq_zero_of_notMem_tsupport hz]
    simp
  have hbound : ∀ z : E3, ‖‖gradient g z‖ ^ 2‖ ≤ ((K : ℝ) ^ 2) := by
    intro z
    rw [Real.norm_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_gradient_le_of_lipschitz hg z) 2
  have hfin : volume (tsupport g) < ⊤ := hsupp.isCompact.measure_lt_top
  have hIntOn : IntegrableOn (fun z : E3 => ‖gradient g z‖ ^ 2) (tsupport g) volume :=
    IntegrableOn.of_bound hfin
      (hmeas.aestronglyMeasurable.mono_measure Measure.restrict_le_self)
      ((K : ℝ) ^ 2) (ae_of_all _ hbound)
  exact hIntOn.integrable_of_forall_notMem_eq_zero hzero

/-- Joint integrability of `(y,t) ↦ ‖∇g (y + t • s)‖²` with respect to `volume.prod devNu`.

The integrand is measurable, vanishes as soon as `y + t • s ∉ tsupport g`, is bounded by `K²`, and
`devNu` is supported on `(0,1]`.  Hence it is dominated by `K²` times the indicator of the compact
box `closedBall 0 (R + ‖s‖) × (0,1]`, where `R` is any radius with `tsupport g ⊆ closedBall 0 R`. -/
private lemma integrable_shiftGrad {g : E3 → ℝ} {K : NNReal} (hg : LipschitzWith K g)
    (hsupp : HasCompactSupport g) (s : E3) :
    Integrable (fun p : E3 × ℝ => ‖gradient g (p.1 + p.2 • s)‖ ^ 2)
      ((volume : Measure E3).prod devNu) := by
  have hcont : Continuous fun p : E3 × ℝ => p.1 + p.2 • s := by fun_prop
  have hmeas : Measurable (fun p : E3 × ℝ => ‖gradient g (p.1 + p.2 • s)‖ ^ 2) := by
    have heq : (fun p : E3 × ℝ => ‖gradient g (p.1 + p.2 • s)‖ ^ 2)
        = fun p : E3 × ℝ => ‖fderiv ℝ g (p.1 + p.2 • s)‖ ^ 2 := by
      funext p; rw [norm_gradient_eq_norm_fderiv]
    rw [heq]
    exact ((measurable_fderiv ℝ g).comp hcont.measurable).norm.pow_const 2
  obtain ⟨R, hR⟩ := hsupp.isCompact.isBounded.subset_closedBall (0 : E3)
  set S : Set (E3 × ℝ) := Metric.closedBall 0 (R + ‖s‖) ×ˢ Set.Ioc (0 : ℝ) 1 with hSdef
  have hSmeas : MeasurableSet S :=
    (Metric.isClosed_closedBall).measurableSet.prod measurableSet_Ioc
  have hSfin : ((volume : Measure E3).prod devNu) S < ⊤ := by
    rw [hSdef, Measure.prod_prod]
    refine ENNReal.mul_lt_top (isCompact_closedBall 0 (R + ‖s‖)).measure_lt_top ?_
    simp [devNu]
  have hGint : Integrable (S.indicator fun _ : E3 × ℝ => (K : ℝ) ^ 2)
      ((volume : Measure E3).prod devNu) := by
    rw [MeasureTheory.integrable_indicator_iff hSmeas]
    refine integrableOn_const ?_ ?_
    · exact hSfin.ne
    · simp
  refine hGint.mono' hmeas.aestronglyMeasurable ?_
  -- almost everywhere the parameter lies in the support `(0,1]` of `devNu`
  have haeIoc : ∀ᵐ p ∂((volume : Measure E3).prod devNu), p.2 ∈ Set.Ioc (0 : ℝ) 1 := by
    rw [MeasureTheory.ae_iff]
    have hset : {p : E3 × ℝ | ¬ p.2 ∈ Set.Ioc (0 : ℝ) 1}
        = Set.univ ×ˢ (Set.Ioc (0 : ℝ) 1)ᶜ := by
      ext p; simp
    rw [hset, Measure.prod_prod]
    have : devNu (Set.Ioc (0 : ℝ) 1)ᶜ = 0 := by simp [devNu]
    rw [this, mul_zero]
  filter_upwards [haeIoc] with p hp
  by_cases hpS : p ∈ S
  · -- inside the box the global Lipschitz bound applies
    rw [Set.indicator_of_mem hpS, Real.norm_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_gradient_le_of_lipschitz hg _) 2
  · -- outside the box (with `p.2 ∈ (0,1]`) the argument of `g` leaves `tsupport g`
    rw [Set.indicator_of_notMem hpS]
    have hnotball : p.1 ∉ Metric.closedBall (0 : E3) (R + ‖s‖) := by
      intro hmem
      exact hpS (by rw [hSdef]; exact ⟨hmem, hp⟩)
    have hlt : R + ‖s‖ < ‖p.1‖ := by
      have h1 : ¬ (dist p.1 (0 : E3) ≤ R + ‖s‖) :=
        fun h => hnotball (Metric.mem_closedBall.mpr h)
      have h2 := not_le.mp h1
      rwa [dist_zero_right] at h2
    have hnorm : R < ‖p.1 + p.2 • s‖ := by
      have h2 : ‖p.2 • s‖ ≤ ‖s‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hp.1]
        exact mul_le_of_le_one_left (norm_nonneg s) hp.2
      have h3 : ‖p.1‖ - ‖p.2 • s‖ ≤ ‖p.1 + p.2 • s‖ :=
        norm_sub_le_norm_add p.1 (p.2 • s)
      linarith
    have hnotsupp : p.1 + p.2 • s ∉ tsupport g := by
      intro hmem
      have h4 := hR hmem
      rw [Metric.mem_closedBall, dist_zero_right] at h4
      linarith
    rw [gradient_eq_zero_of_notMem_tsupport hnotsupp]
    simp

theorem integralIntegralShiftGrad {g : EuclideanSpace ℝ (Fin 3) → ℝ} {K : NNReal}
    (hg : LipschitzWith K g) (hsupp : HasCompactSupport g) (s : EuclideanSpace ℝ (Fin 3)) :
    (∫ y, (∫ t, ‖gradient g (y + t • s)‖ ^ 2 ∂devNu)) = ∫ z, ‖gradient g z‖ ^ 2 := by
  have hjoint := integrable_shiftGrad hg hsupp s
  have hswap := MeasureTheory.integral_integral_swap
    (f := fun y t => ‖gradient g (y + t • s)‖ ^ 2) hjoint
  calc (∫ y, (∫ t, ‖gradient g (y + t • s)‖ ^ 2 ∂devNu))
      = ∫ t, (∫ y, ‖gradient g (y + t • s)‖ ^ 2 ∂volume) ∂devNu := hswap
    _ = ∫ t, (∫ z, ‖gradient g z‖ ^ 2 ∂volume) ∂devNu := by
          refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
          exact MeasureTheory.integral_add_right_eq_self (fun z : E3 => ‖gradient g z‖ ^ 2) (t • s)
    _ = ∫ z, ‖gradient g z‖ ^ 2 ∂volume := by
          rw [MeasureTheory.integral_const]
          simp
/-!
# `Work.BoseB1Cube.devFTC` — the finite-difference Poincaré bound for Lipschitz functions

The target is the classical estimate

    ∫ x, (g (x + s) - g x)² ≤ ‖s‖² · ∫ x, ‖∇g x‖²

for a Lipschitz, compactly supported `g : ℝ³ → ℝ`.  For a `C¹` function this is the fundamental
theorem of calculus along the segment, Cauchy–Schwarz in the segment parameter, Fubini and the
translation invariance of Lebesgue measure.  Under the present (merely Lipschitz) hypotheses the
only new ingredient is Rademacher's theorem (Mathlib's `LipschitzWith.ae_differentiableAt`): the
Fréchet derivative exists almost everywhere, and the one-dimensional fundamental theorem of
calculus holds for the absolutely continuous function `t ↦ g (y + t • s)`.

The proof is split as

* `devFTC_pointwise_of_ae` — the pointwise estimate for a fixed `y` at which `g` is differentiable
  along the segment, and
* the assembly, which integrates it in `y` (delegated Fubini/translation lemmas
  `Work.BoseB1Cube.integrableIntegralShiftGrad`, `Work.BoseB1Cube.integralIntegralShiftGrad` and
  the a.e. differentiability along segments `Work.BoseB1Cube.aeShiftDifferentiable`).
-/


open MeasureTheory Filter Metric
open scoped Topology Real ENNReal NNReal



set_option maxHeartbeats 1000000

/-- Pointwise form of the finite-difference bound: if `g` is differentiable almost everywhere along
the segment `t ↦ y + t • s` (`t ∈ (0,1]`), then

    (g (y + s) - g y)² ≤ ‖s‖² ∫ t, ‖∇g (y + t • s)‖² .

The proof is the fundamental theorem of calculus for the absolutely continuous function
`t ↦ g (y + t • s)` (it is Lipschitz), Cauchy–Schwarz in the segment variable, and the bound
`‖fderiv g z s‖ ≤ ‖s‖ ‖∇g z‖`. -/
theorem devFTC_pointwise_of_ae {g : E3 → ℝ} {K : NNReal} (hg : LipschitzWith K g) (s y : E3)
    (hy : ∀ᵐ t ∂devNu, DifferentiableAt ℝ g (y + t • s)) :
    (g (y + s) - g y) ^ 2 ≤ ‖s‖ ^ 2 * ∫ t, ‖gradient g (y + t • s)‖ ^ 2 ∂devNu := by
  have hψlip : LipschitzWith (Real.toNNReal ((K : ℝ) * ‖s‖)) (fun t : ℝ => g (y + t • s)) := by
    refine LipschitzWith.of_dist_le' (K := (K : ℝ) * ‖s‖) fun a b => ?_
    calc dist (g (y + a • s)) (g (y + b • s))
        ≤ (K : ℝ) * dist (y + a • s) (y + b • s) := hg.dist_le_mul _ _
      _ = (K : ℝ) * ‖s‖ * dist a b := by
          have hdist : dist (y + a • s) (y + b • s) = ‖s‖ * dist a b := by
            rw [dist_eq_norm, Real.dist_eq]
            have h' : y + a • s - (y + b • s) = (a - b) • s := by rw [sub_smul]; abel
            rw [h', norm_smul, Real.norm_eq_abs]
            ring
          rw [hdist]
          ring
  have hac : AbsolutelyContinuousOnInterval (fun t : ℝ => g (y + t • s)) 0 1 :=
    hψlip.lipschitzOnWith.absolutelyContinuousOnInterval
  have hFTC : ∫ t in (0 : ℝ)..1, deriv (fun t : ℝ => g (y + t • s)) t = g (y + s) - g y := by
    have h := AbsolutelyContinuousOnInterval.integral_deriv_eq_sub hac
    simpa using h
  have hFTC' : (∫ t, deriv (fun t : ℝ => g (y + t • s)) t ∂devNu) = g (y + s) - g y := by
    rw [devNu, ← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
    exact hFTC
  have h1 : Integrable (fun t : ℝ => deriv (fun t : ℝ => g (y + t • s)) t) devNu := by
    refine Integrable.of_bound (aestronglyMeasurable_deriv _ _) ((K : ℝ) * ‖s‖) ?_
    filter_upwards with t
    rw [Real.norm_eq_abs]
    exact abs_deriv_shift_le hg y s t
  have h2 : Integrable (fun t : ℝ => (deriv (fun t : ℝ => g (y + t • s)) t) ^ 2) devNu := by
    refine Integrable.of_bound
      ((MeasureTheory.Integrable.aestronglyMeasurable h1).pow 2) (((K : ℝ) * ‖s‖) ^ 2) ?_
    filter_upwards with t
    have hb := abs_deriv_shift_le hg y s t
    have := pow_le_pow_left₀ (abs_nonneg _) hb 2
    simpa [Real.norm_of_nonneg (sq_nonneg _), sq_abs] using this
  have hCS : (∫ t, deriv (fun t : ℝ => g (y + t • s)) t ∂devNu) ^ 2
      ≤ ∫ t, (deriv (fun t : ℝ => g (y + t • s)) t) ^ 2 ∂devNu :=
    sq_integral_le_integral_sq h1 h2
  have hgrad : Measurable (fun z : E3 => ‖gradient g z‖ ^ 2) := by
    have h : Measurable (fun z : E3 => ‖gradient g z‖) :=
      (InnerProductSpace.toDual ℝ E3).symm.continuous.measurable.comp
        (measurable_fderiv ℝ g) |>.norm
    exact h.pow_const 2
  have hup_int : Integrable (fun t : ℝ => ‖s‖ ^ 2 * ‖gradient g (y + t • s)‖ ^ 2) devNu := by
    refine Integrable.of_bound ?_ (‖s‖ ^ 2 * (K : ℝ) ^ 2) ?_
    · have hmeas : Measurable (fun t : ℝ => ‖s‖ ^ 2 * ‖gradient g (y + t • s)‖ ^ 2) :=
        (hgrad.comp (by fun_prop)).const_mul _
      exact hmeas.aestronglyMeasurable
    · filter_upwards with t
      rw [Real.norm_of_nonneg (by positivity)]
      have hb : ‖gradient g (y + t • s)‖ ≤ (K : ℝ) := by
        rw [norm_gradient_eq_norm_fderiv]
        exact norm_fderiv_le_of_lipschitz ℝ hg
      have hb' : 0 ≤ ‖gradient g (y + t • s)‖ := norm_nonneg _
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hb' hb 2) (sq_nonneg _)
  have hcmp : ∫ t, (deriv (fun t : ℝ => g (y + t • s)) t) ^ 2 ∂devNu
      ≤ ∫ t, ‖s‖ ^ 2 * ‖gradient g (y + t • s)‖ ^ 2 ∂devNu := by
    refine integral_mono_of_nonneg (Eventually.of_forall fun t => sq_nonneg _) hup_int ?_
    filter_upwards [hy] with t ht
    have hderiv : deriv (fun t : ℝ => g (y + t • s)) t = fderiv ℝ g (y + t • s) s := by
      rw [deriv_shift_eq_lineDeriv, ht.lineDeriv_eq_fderiv]
    have hle : |deriv (fun t : ℝ => g (y + t • s)) t| ≤ ‖s‖ * ‖gradient g (y + t • s)‖ := by
      rw [hderiv, norm_gradient_eq_norm_fderiv]
      calc ‖fderiv ℝ g (y + t • s) s‖ ≤ ‖fderiv ℝ g (y + t • s)‖ * ‖s‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ = ‖s‖ * ‖fderiv ℝ g (y + t • s)‖ := by ring
    obtain ⟨hlo, hhi⟩ := abs_le.mp hle
    calc (deriv (fun t : ℝ => g (y + t • s)) t) ^ 2
        ≤ (‖s‖ * ‖gradient g (y + t • s)‖) ^ 2 := sq_le_sq' hlo hhi
      _ = ‖s‖ ^ 2 * ‖gradient g (y + t • s)‖ ^ 2 := by ring
  calc (g (y + s) - g y) ^ 2
      = (∫ t, deriv (fun t : ℝ => g (y + t • s)) t ∂devNu) ^ 2 := by rw [hFTC']
    _ ≤ ∫ t, (deriv (fun t : ℝ => g (y + t • s)) t) ^ 2 ∂devNu := hCS
    _ ≤ ∫ t, ‖s‖ ^ 2 * ‖gradient g (y + t • s)‖ ^ 2 ∂devNu := hcmp
    _ = ‖s‖ ^ 2 * ∫ t, ‖gradient g (y + t • s)‖ ^ 2 ∂devNu := integral_const_mul _ _

/-- The assembly of `devFTC` from its three analytic inputs: a.e. differentiability along the
segments, integrability of the segment-averaged gradient energy, and the Fubini/translation
identity for that average. -/
theorem devFTC_of_pieces (g : E3 → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ x y : E3, |g x - g y| ≤ L * ‖x - y‖) (_hsupp : HasCompactSupport g) (s : E3)
    (hae : ∀ᵐ y ∂(volume : Measure E3), ∀ᵐ t ∂devNu, DifferentiableAt ℝ g (y + t • s))
    (hint : Integrable (fun y => ∫ t, ‖gradient g (y + t • s)‖ ^ 2 ∂devNu))
    (hfub : (∫ y, (∫ t, ‖gradient g (y + t • s)‖ ^ 2 ∂devNu)) = ∫ z, ‖gradient g z‖ ^ 2) :
    ∫ x, (g (x + s) - g x) ^ 2 ≤ ‖s‖ ^ 2 * ∫ x, ‖gradient g x‖ ^ 2 := by
  have hg : LipschitzWith (Real.toNNReal L) g := lipschitzWith_of_abs_sub_le hL hlip
  have hpt : ∀ᵐ y ∂(volume : Measure E3),
      (g (y + s) - g y) ^ 2 ≤ ‖s‖ ^ 2 * ∫ t, ‖gradient g (y + t • s)‖ ^ 2 ∂devNu := by
    filter_upwards [hae] with y hy
    exact devFTC_pointwise_of_ae hg s y hy
  have hU : Integrable (fun y => ‖s‖ ^ 2 * ∫ t, ‖gradient g (y + t • s)‖ ^ 2 ∂devNu) := by
    simpa [mul_comm] using hint.const_mul (‖s‖ ^ 2)
  have hmono : ∫ y, (g (y + s) - g y) ^ 2
      ≤ ∫ y, ‖s‖ ^ 2 * (∫ t, ‖gradient g (y + t • s)‖ ^ 2 ∂devNu) :=
    integral_mono_of_nonneg (Eventually.of_forall fun y => sq_nonneg _) hU hpt
  calc ∫ x, (g (x + s) - g x) ^ 2
      ≤ ∫ y, ‖s‖ ^ 2 * (∫ t, ‖gradient g (y + t • s)‖ ^ 2 ∂devNu) := hmono
    _ = ‖s‖ ^ 2 * ∫ y, (∫ t, ‖gradient g (y + t • s)‖ ^ 2 ∂devNu) := integral_const_mul _ _
    _ = ‖s‖ ^ 2 * ∫ z, ‖gradient g z‖ ^ 2 := by rw [hfub]

theorem devFTC (g : EuclideanSpace ℝ (Fin 3) → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ x y : EuclideanSpace ℝ (Fin 3), |g x - g y| ≤ L * ‖x - y‖)
    (hsupp : HasCompactSupport g) (s : EuclideanSpace ℝ (Fin 3)) :
    ∫ x, (g (x + s) - g x) ^ 2
      ≤ ‖s‖ ^ 2 * ∫ x, ‖gradient g x‖ ^ 2 := by
  have hg : LipschitzWith (Real.toNNReal L) g := lipschitzWith_of_abs_sub_le hL hlip
  exact devFTC_of_pieces g L hL hlip hsupp s (aeShiftDifferentiable hg s)
    (integrableIntegralShiftGrad hg hsupp s) (integralIntegralShiftGrad hg hsupp s)
/-!
# `Work.BoseB1Cube.chiMass_sub_autoCorr_le`

The autocorrelation (`χ`-mass minus the autocorrelation integral) bound for the two-factor
sliding cutoff `χ_{B(u)} = chiSmallB M ℓ d u`:

    ∫ χ² − ∫ χ(z+y) χ(y) ≤ ½ ‖z‖² ∫ ‖∇χ‖² .

This is the `L²`-translation bound for the bump: the identity
`∫ (χ(z+·) − χ)² = 2 ∫ χ² − 2 ∫ χ(z+·)χ` (translation invariance of Lebesgue measure) turns the
left-hand side into one half of the squared `L²` distance between `χ` and its `z`-translate, and
the finite-difference Poincaré bound `Work.BoseB1Cube.devFTC`
(`∫ (g(·+s) − g)² ≤ ‖s‖² ∫ ‖∇g‖²` for a Lipschitz, compactly supported `g`) finishes the job.
The Lipschitz property of `chiSmallB` is the already-proved
`Work.BoseFixB1.SectorAux.chiSmallB_lipschitz`.
-/


open MeasureTheory Filter Metric
open scoped Topology Real ENNReal NNReal



set_option linter.unusedVariables false
set_option maxHeartbeats 800000

/-- The autocorrelation identity: for an integrable `g` with integrable square and integrable
cross term,

    `2 ∫ g² − 2 ∫ g(z+·) g = ∫ (g(z+·) − g)²`.

Expanding the square pointwise and using the translation invariance of Lebesgue measure gives
the claim. -/
private lemma autoCorr_identity_aux {g : E3 → ℝ} (z : E3)
    (h1 : Integrable (fun x : E3 => (g x) ^ 2))
    (h2 : Integrable (fun x : E3 => g (z + x) * g x)) :
    2 * (∫ x : E3, (g x) ^ 2) - 2 * (∫ x : E3, g (z + x) * g x)
      = ∫ x : E3, (g (z + x) - g x) ^ 2 := by
  have h2' : Integrable (fun x : E3 => 2 * (g (z + x) * g x)) := h2.const_mul 2
  have h1z : Integrable (fun x : E3 => (g (z + x)) ^ 2) := h1.comp_add_left z
  have hP : Integrable (fun x : E3 => (g (z + x)) ^ 2 - 2 * (g (z + x) * g x)) :=
    h1z.sub h2'
  have hexp : (fun x : E3 => (g (z + x) - g x) ^ 2)
      = fun x : E3 => ((g (z + x)) ^ 2 - 2 * (g (z + x) * g x)) + (g x) ^ 2 := by
    funext x
    ring
  have htrans : (∫ x : E3, (g (z + x)) ^ 2) = ∫ x : E3, (g x) ^ 2 :=
    integral_add_left_eq_self (fun x : E3 => (g x) ^ 2) z
  rw [hexp, integral_add hP h1, integral_sub h1z h2', integral_const_mul, htrans]
  ring

/-- The `L²`-translation (mean-square displacement) bound for a Lipschitz, compactly supported
function: `∫ (g(x+z) − g x)² ≤ ‖z‖² ∫ ‖∇g‖²`, in the `z + x` orientation. -/
private lemma shift_sq_le_grad {g : E3 → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ x y : E3, |g x - g y| ≤ L * ‖x - y‖) (hcs : HasCompactSupport g) (z : E3) :
    (∫ x : E3, (g (z + x) - g x) ^ 2) ≤ ‖z‖ ^ 2 * ∫ x : E3, ‖gradient g x‖ ^ 2 := by
  have hdev := devFTC g L hL hlip hcs z
  have hcongr : (∫ x : E3, (g (z + x) - g x) ^ 2) = ∫ x : E3, (g (x + z) - g x) ^ 2 := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    show (g (z + x) - g x) ^ 2 = (g (x + z) - g x) ^ 2
    rw [add_comm]
  rw [hcongr]
  exact hdev

theorem chiMass_sub_autoCorr_le {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u z : EuclideanSpace ℝ (Fin 3)) :
    (∫ x : EuclideanSpace ℝ (Fin 3), (Submission.BoseGases.chiSmallB M ℓ d u x) ^ 2)
        - (∫ y : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.chiSmallB M ℓ d u (z + y)
            * Submission.BoseGases.chiSmallB M ℓ d u y)
      ≤ (1 / 2) * ‖z‖ ^ 2
          * (∫ x : EuclideanSpace ℝ (Fin 3),
              ‖gradient (fun w : EuclideanSpace ℝ (Fin 3) =>
                Submission.BoseGases.chiSmallB M ℓ d u w) x‖ ^ 2) := by
  obtain ⟨L, hL0, hlip⟩ := Work.BoseFixB1.SectorAux.chiSmallB_lipschitz hM hℓ hd u
  -- the bump as a single function
  set f : E3 → ℝ := fun w => Submission.BoseGases.chiSmallB M ℓ d u w with hf
  have hbump : (fun w : E3 => f w)
      = fun w : E3 => Submission.BoseGases.chiScale ℓ w
          * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • w - u) := by
    funext w
    rw [hf]
    rfl
  have hcont : Continuous f := by
    rw [hf]
    simp only [Submission.BoseGases.chiSmallB]
    exact (Submission.BoseGases.chiScale_continuous ℓ).mul
      ((Submission.BoseGases.chiSmall_continuous hM).comp
        ((continuous_id.const_smul ((ℓ * d)⁻¹)).sub continuous_const))
  have hcs : HasCompactSupport f := by
    rw [hf]
    simp only [Submission.BoseGases.chiSmallB]
    have hA : HasCompactSupport
        (fun w : E3 => Submission.BoseGases.chiScale ℓ w) :=
      Submission.BoseGases.chiScale_hasCompactSupport hℓ.ne'
    have h0 : HasCompactSupport (Submission.BoseGases.chiSmall M) :=
      Submission.BoseGases.chiSmall_hasCompactSupport hM
    have hφ : HasCompactSupport
        (fun w : E3 => Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • w - u)) := by
      have hc : (ℓ * d) ≠ 0 := ne_of_gt (mul_pos hℓ hd)
      have h1 : HasCompactSupport
          (fun x : E3 => Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x)) :=
        h0.comp_smul (c := (ℓ * d)⁻¹) (inv_ne_zero hc)
      have h2 := h1.comp_homeomorph (Homeomorph.addRight (-((ℓ * d) • u)))
      convert h2 using 1
      ext w
      simp only [Function.comp_apply, Homeomorph.coe_addRight, smul_add, smul_neg, smul_smul,
        inv_mul_cancel₀ hc, one_smul, sub_eq_add_neg]
    exact hA.mul_right
  have hlip' : ∀ x y : E3, |f x - f y| ≤ L * ‖x - y‖ := by
    intro x y
    rw [hf]
    exact hlip x y
  have hint1 : Integrable (fun x : E3 => (f x) ^ 2) :=
    (hcont.memLp_of_hasCompactSupport hcs).integrable_sq
  have hcont' : Continuous (fun x : E3 => f (z + x)) :=
    hcont.comp (continuous_const.add continuous_id)
  have hcs' : HasCompactSupport (fun x : E3 => f (z + x)) :=
    hcs.comp_homeomorph (Homeomorph.addLeft z)
  have hint2 : Integrable (fun x : E3 => f (z + x) * f x) :=
    (hcont'.mul hcont).integrable_of_hasCompactSupport hcs'.mul_right
  have hid := autoCorr_identity_aux (g := f) z hint1 hint2
  have hdev := shift_sq_le_grad hL0 hlip' hcs z
  have hmain : (∫ x : E3, (f x) ^ 2) - (∫ y : E3, f (z + y) * f y)
      ≤ (1 / 2) * ‖z‖ ^ 2 * (∫ x : E3, ‖gradient f x‖ ^ 2) := by
    have hkey : (∫ x : E3, (f x) ^ 2) - (∫ y : E3, f (z + y) * f y)
        = (1 / 2) * ∫ x : E3, (f (z + x) - f x) ^ 2 := by
      linarith [hid]
    calc (∫ x : E3, (f x) ^ 2) - (∫ y : E3, f (z + y) * f y)
        = (1 / 2) * ∫ x : E3, (f (z + x) - f x) ^ 2 := hkey
      _ ≤ (1 / 2) * (‖z‖ ^ 2 * ∫ x : E3, ‖gradient f x‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hdev (by norm_num)
      _ = (1 / 2) * ‖z‖ ^ 2 * (∫ x : E3, ‖gradient f x‖ ^ 2) := by ring
  rw [hf]
  exact hmain

end Work.BoseSWE.CopyDev


namespace Work.BoseSWE

/-- **`Work.BoseSWE.chiMass_sub_autoCorr_leW`** -- a *renamed, `devFTCDefs`-free copy* of the
corpus's `Work.BoseB1Cube.chiMass_sub_autoCorr_le`, needed because the corpus declares
`Work.BoseB1Cube.sq_integral_le_integral_sq` **twice** (in `BoseB1Cube/sq_integral_le_integral_sq.lean`
and in `BoseB1Cube/devFTCDefs.lean`), so any import cone containing both is unbuildable.
`Work.BoseRoot.Assembly`'s cone contains the first; the `BoseSWE` cone must therefore avoid the
second. -/
theorem chiMass_sub_autoCorr_leW {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u z : EuclideanSpace ℝ (Fin 3)) :
    (∫ x : EuclideanSpace ℝ (Fin 3), (Submission.BoseGases.chiSmallB M ℓ d u x) ^ 2)
        - (∫ y : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.chiSmallB M ℓ d u (z + y)
            * Submission.BoseGases.chiSmallB M ℓ d u y)
      ≤ (1 / 2) * ‖z‖ ^ 2
          * (∫ x : EuclideanSpace ℝ (Fin 3),
              ‖gradient (fun w : EuclideanSpace ℝ (Fin 3) =>
                Submission.BoseGases.chiSmallB M ℓ d u w) x‖ ^ 2) :=
  CopyDev.chiMass_sub_autoCorr_le hM hℓ hd u z

end Work.BoseSWE
