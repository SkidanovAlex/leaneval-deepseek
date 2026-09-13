/-
# Chaudhuri--Trudinger: the Hessian of a `2`-convex function is a measure

This module proves `Submission.HessianMeasureInput`.

Following the paper (and `[CT]`), we use the positive functionals

* `Λ(φ) = ∫ u Δφ` (positive for `2`-convex `u`, by `Submission.twoConvex_laplacian_nonneg`),
* `Λ_e(φ) = ∫ u (Δφ - D²φ(e,e))` for a unit vector `e` (positive for `2`-convex `u`, by
  `Submission.hyperplane_laplacian_nonneg_of_twoConvex_e`),

represent them by positive Radon measures `μ`, `μ_e` (Riesz representation,
`Commons.Measure.Distribution.exists_measure_of_positive_functional`), and observe
`∫ u D²φ(e,e) = Λ φ - Λ_e φ = ∫ φ dμ - ∫ φ dμ_e`.  Polarising,
`D_ij u = (1/2)(D_{e₊e₊}u - D_{e₋e₋}u)` for `e± = (e_i ± e_j)/√2` gives every entry of the weak
Hessian as a difference of two positive Radon measures.  The Lebesgue decomposition for measures
then produces the locally integrable density `M` and the singular signed measure `σ`.
-/
import Mathlib
import Submission.AlexandrovInputs
import Submission.ViscosityMVP
import Submission.SliceDistribution
import Submission.HessianMeasureInput
import Submission.Commons.Measure.Distribution.exists_measure_of_positive_functional
import Submission.Commons.Measure.Distribution.exists_measure_of_positive_functional_compact
import Submission.Commons.Measure.VectorMeasure.integral_toSignedMeasure_smul
import Submission.Commons.Analysis.InnerProductSpace.exists_orthonormalBasis_head
import Submission.Commons.Analysis.Calculus.BumpFunction.contDiff_eq_one_on_isCompact_tsupport_subset
import Submission.Commons.Analysis.Calculus.FDeriv.iteratedFDeriv_apply_congr_of_eventuallyEq

open HessianEstimates
open MeasureTheory Metric Set Filter Function
open scoped BigOperators ENNReal Topology RealInnerProductSpace InnerProductSpace ContDiff

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Submission

local notation "ℝ⁴" => EuclideanSpace ℝ (Fin 4)
local notation "bFun" => EuclideanSpace.basisFun (Fin 4) ℝ

/-! ## Elementary integrability and continuity lemmas -/

/-- The product of a function continuous on the open set `s` with a continuous function whose
compact support lies in `s` is integrable. -/
private theorem integrable_mul_of_continuousOn {u g : ℝ⁴ → ℝ} {s : Set ℝ⁴} (hu : ContinuousOn u s)
    (hg : Continuous g) (hgcs : HasCompactSupport g) (hgs : tsupport g ⊆ s) :
    Integrable (fun x => u x * g x) volume := by
  have hK : IntegrableOn (fun x => u x * g x) (tsupport g) volume :=
    ((hu.mono hgs).mul hg.continuousOn).integrableOn_compact hgcs
  have heq : (fun x => u x * g x) = (tsupport g).indicator (fun x => u x * g x) := by
    funext x
    by_cases hx : x ∈ tsupport g
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx,
        image_eq_zero_of_notMem_tsupport (fun h => hx h), mul_zero]
  rw [heq]
  exact (integrable_indicator_iff (hgcs.isClosed).measurableSet).mpr hK

/-- The Laplacian in terms of second derivatives in the standard basis. -/
private theorem laplacian_eq_sum_second {φ : ℝ⁴ → ℝ} (x : ℝ⁴) :
    Laplacian.laplacian φ x = ∑ j : Fin 4, (fderiv ℝ (fderiv ℝ φ) x) (bFun j) (bFun j) := by
  rw [Commons.Analysis.Calculus.FDeriv.laplacian_eq_sum_second_partials (bFun) φ x]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [bilinearIteratedFDerivTwo_eq_iteratedFDeriv, iteratedFDeriv_two_apply]
  simp

/-- The second derivative of a `C²` function in two fixed directions is continuous. -/
private theorem continuous_second_deriv {φ : ℝ⁴ → ℝ} (hφ : ContDiff ℝ 2 φ) (v w : ℝ⁴) :
    Continuous (fun x : ℝ⁴ => (fderiv ℝ (fderiv ℝ φ) x) v w) := by
  have h3 : Continuous (fun x : ℝ⁴ => (iteratedFDeriv ℝ 2 φ x) ![v, w]) :=
    ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => ℝ⁴) ℝ ![v, w]).continuous).comp
      (hφ.continuous_iteratedFDeriv (m := 2) (by norm_num))
  have h4 : (fun x : ℝ⁴ => (fderiv ℝ (fderiv ℝ φ) x) v w)
      = fun x => (iteratedFDeriv ℝ 2 φ x) ![v, w] := by
    funext x
    rw [iteratedFDeriv_two_apply φ x ![v, w]]
    simp
  rw [h4]
  exact h3

/-- The Laplacian of a `C²` function is continuous. -/
private theorem continuous_laplacian' {φ : ℝ⁴ → ℝ} (hφ : ContDiff ℝ 2 φ) :
    Continuous (Laplacian.laplacian φ) := by
  have h : Laplacian.laplacian φ
      = fun x => ∑ j : Fin 4, (fderiv ℝ (fderiv ℝ φ) x) (bFun j) (bFun j) :=
    funext fun x => laplacian_eq_sum_second x
  rw [h]
  exact continuous_finsetSum _ fun j _ => continuous_second_deriv hφ _ _

/-- For a function vanishing near `x`, so does its second derivative in two fixed directions. -/
private theorem notMem_tsupport_second_deriv {φ : ℝ⁴ → ℝ} {x : ℝ⁴} (e : ℝ⁴)
    (hx : x ∉ tsupport φ) :
    x ∉ tsupport (fun y : ℝ⁴ => (fderiv ℝ (fderiv ℝ φ) y) e e) := by
  rw [notMem_tsupport_iff_eventuallyEq]
  filter_upwards [(isClosed_tsupport φ).isOpen_compl.mem_nhds hx] with y hy
  have h2 : φ =ᶠ[𝓝 y] (0 : ℝ⁴ → ℝ) :=
    Filter.eventually_of_mem ((isClosed_tsupport φ).isOpen_compl.mem_nhds hy)
      (fun z hz => image_eq_zero_of_notMem_tsupport hz)
  have hkey : ∀ (f : ℝ⁴ → ℝ),
      (fderiv ℝ (fderiv ℝ f) y) e e = (iteratedFDeriv ℝ 2 f y) ![e, e] := by
    intro f
    rw [iteratedFDeriv_two_apply f y ![e, e]]
    simp
  show (fderiv ℝ (fderiv ℝ φ) y) e e = 0
  rw [hkey φ]
  rw [Commons.Analysis.Calculus.FDeriv.iteratedFDeriv_apply_congr_of_eventuallyEq (n := 2) h2 ![e, e]]
  simp

/-- The second derivative in two fixed directions is supported in the support of the function. -/
private theorem tsupport_second_deriv_subset {φ : ℝ⁴ → ℝ} (e : ℝ⁴) :
    tsupport (fun y : ℝ⁴ => (fderiv ℝ (fderiv ℝ φ) y) e e) ⊆ tsupport φ :=
  closure_minimal (fun x hx => by
    rw [Function.mem_support] at hx
    by_contra hc
    exact hx (image_eq_zero_of_notMem_tsupport
      (f := fun y : ℝ⁴ => (fderiv ℝ (fderiv ℝ φ) y) e e)
      (notMem_tsupport_second_deriv (φ := φ) e hc)))
    (isClosed_tsupport φ)

/-- The Laplacian is supported in the support of the function. -/
private theorem tsupport_laplacian_subset {φ : ℝ⁴ → ℝ} :
    tsupport (Laplacian.laplacian φ) ⊆ tsupport φ := by
  refine closure_minimal (fun x hx => ?_) (isClosed_tsupport φ)
  rw [Function.mem_support] at hx
  by_contra hc
  exact hx (by
    rw [laplacian_eq_sum_second]
    refine Finset.sum_eq_zero fun j _ => ?_
    exact image_eq_zero_of_notMem_tsupport
      (f := fun y : ℝ⁴ => (fderiv ℝ (fderiv ℝ φ) y) (bFun j) (bFun j))
      (notMem_tsupport_second_deriv (φ := φ) (bFun j) hc))

/-- The Laplacian piece of a compactly supported function has compact support. -/
private theorem hasCompactSupport_laplacian {φ : ℝ⁴ → ℝ} (hcs : HasCompactSupport φ) :
    HasCompactSupport (Laplacian.laplacian φ) :=
  hcs.of_isClosed_subset (isClosed_tsupport _) tsupport_laplacian_subset

/-- The second-derivative piece of a compactly supported function has compact support. -/
private theorem hasCompactSupport_second_deriv {φ : ℝ⁴ → ℝ} (hcs : HasCompactSupport φ) (e : ℝ⁴) :
    HasCompactSupport (fun y : ℝ⁴ => (fderiv ℝ (fderiv ℝ φ) y) e e) :=
  hcs.of_isClosed_subset (isClosed_tsupport _) (tsupport_second_deriv_subset e)


/-- The second derivative in two fixed directions is additive in the function. -/
private theorem second_deriv_add {φ ψ : ℝ⁴ → ℝ} {x e : ℝ⁴} (hφ : ContDiffAt ℝ 2 φ x)
    (hψ : ContDiffAt ℝ 2 ψ x) :
    (fderiv ℝ (fderiv ℝ (φ + ψ)) x) e e
      = (fderiv ℝ (fderiv ℝ φ) x) e e + (fderiv ℝ (fderiv ℝ ψ) x) e e := by
  have key : ∀ (f : ℝ⁴ → ℝ),
      (fderiv ℝ (fderiv ℝ f) x) e e = (iteratedFDeriv ℝ 2 f x) ![e, e] := by
    intro f
    rw [iteratedFDeriv_two_apply f x ![e, e]]
    simp
  rw [key (φ + ψ), key φ, key ψ]
  exact Commons.Analysis.Calculus.FDeriv.iteratedFDeriv_two_apply_add hφ hψ

/-- The second derivative in two fixed directions is homogeneous. -/
private theorem second_deriv_smul (a : ℝ) {φ : ℝ⁴ → ℝ} {x e : ℝ⁴} (hφ : ContDiffAt ℝ 2 φ x) :
    (fderiv ℝ (fderiv ℝ (a • φ)) x) e e = a * ((fderiv ℝ (fderiv ℝ φ) x) e e) := by
  have key : ∀ (f : ℝ⁴ → ℝ),
      (fderiv ℝ (fderiv ℝ f) x) e e = (iteratedFDeriv ℝ 2 f x) ![e, e] := by
    intro f
    rw [iteratedFDeriv_two_apply f x ![e, e]]
    simp
  rw [key (a • φ), key φ]
  rw [iteratedFDeriv_const_smul_apply hφ]
  simp [smul_eq_mul]

/-- A `C^∞` function is `C²`. -/
private theorem contDiff_two_of_infty {φ : ℝ⁴ → ℝ} (h : ContDiff ℝ ∞ φ) : ContDiff ℝ 2 φ :=
  h.of_le (by decide)

/-- Integrability of `u` times the Laplacian of a compactly supported function. -/
private theorem integrable_mul_laplacian {u φ : ℝ⁴ → ℝ} {s : Set ℝ⁴} (hu : ContinuousOn u s)
    (hφ : ContDiff ℝ ∞ φ) (hcs : HasCompactSupport φ) (hs : tsupport φ ⊆ s) :
    Integrable (fun x => u x * Laplacian.laplacian φ x) :=
  integrable_mul_of_continuousOn hu (continuous_laplacian' (contDiff_two_of_infty hφ))
    (hasCompactSupport_laplacian hcs) (tsupport_laplacian_subset.trans hs)

/-- Integrability of `u` times a second derivative of a compactly supported function. -/
private theorem integrable_mul_second_deriv {u φ : ℝ⁴ → ℝ} {s : Set ℝ⁴} (hu : ContinuousOn u s)
    (e : ℝ⁴) (hφ : ContDiff ℝ ∞ φ) (hcs : HasCompactSupport φ) (hs : tsupport φ ⊆ s) :
    Integrable (fun x => u x * (fderiv ℝ (fderiv ℝ φ) x) e e) :=
  integrable_mul_of_continuousOn hu (continuous_second_deriv (contDiff_two_of_infty hφ) e e)
    (hasCompactSupport_second_deriv hcs e) ((tsupport_second_deriv_subset e).trans hs)

/-- The functional `φ ↦ ∫ x, u x * Δφ x` of a function `u`. -/
private noncomputable def lapFun (u : ℝ⁴ → ℝ) (φ : ℝ⁴ → ℝ) : ℝ :=
  ∫ x, u x * Laplacian.laplacian φ x

/-- The functional `φ ↦ ∫ x, u x * (Δφ x - D²φ(x)(e,e))`. -/
private noncomputable def dirFun (u : ℝ⁴ → ℝ) (e : ℝ⁴) (φ : ℝ⁴ → ℝ) : ℝ :=
  ∫ x, u x * (Laplacian.laplacian φ x - (fderiv ℝ (fderiv ℝ φ) x) e e)

private theorem lapFun_add {u : ℝ⁴ → ℝ} {s : Set ℝ⁴} (hu : ContinuousOn u s)
    {φ ψ : ℝ⁴ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφcs : HasCompactSupport φ) (hφs : tsupport φ ⊆ s)
    (hψ : ContDiff ℝ ∞ ψ) (hψcs : HasCompactSupport ψ) (hψs : tsupport ψ ⊆ s) :
    lapFun u (φ + ψ) = lapFun u φ + lapFun u ψ := by
  have hpt : ∀ x : ℝ⁴, Laplacian.laplacian (φ + ψ) x
      = Laplacian.laplacian φ x + Laplacian.laplacian ψ x := fun x =>
    ContDiffAt.laplacian_add ((hφ.of_le (by decide)).contDiffAt)
      ((hψ.of_le (by decide)).contDiffAt)
  have hfun : (fun x : ℝ⁴ => u x * Laplacian.laplacian (φ + ψ) x)
      = fun x => u x * Laplacian.laplacian φ x + u x * Laplacian.laplacian ψ x := by
    funext x
    rw [hpt x]
    ring
  rw [lapFun, lapFun, lapFun, hfun,
    integral_add (integrable_mul_laplacian hu hφ hφcs hφs)
      (integrable_mul_laplacian hu hψ hψcs hψs)]

private theorem lapFun_smul {u : ℝ⁴ → ℝ} {s : Set ℝ⁴} (hu : ContinuousOn u s) (a : ℝ)
    {φ : ℝ⁴ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφcs : HasCompactSupport φ) (hφs : tsupport φ ⊆ s) :
    lapFun u (a • φ) = a * lapFun u φ := by
  have hpt : ∀ x : ℝ⁴, Laplacian.laplacian (a • φ) x = a * Laplacian.laplacian φ x := fun x =>
    InnerProductSpace.laplacian_smul a ((hφ.of_le (by decide)).contDiffAt)
  have hfun : (fun x : ℝ⁴ => u x * Laplacian.laplacian (a • φ) x)
      = fun x => a * (u x * Laplacian.laplacian φ x) := by
    funext x
    rw [hpt x]
    ring
  rw [lapFun, lapFun, hfun, MeasureTheory.integral_const_mul]

private theorem lapFun_pos {u : ℝ⁴ → ℝ} {s : Set ℝ⁴} (hs : IsOpen s) (hu : ContinuousOn u s)
    (h2 : IsTwoConvexOn u s) {φ : ℝ⁴ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφcs : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ s) (hφnn : 0 ≤ φ) : 0 ≤ lapFun u φ :=
  twoConvex_laplacian_nonneg hs hu h2 φ hφ hφcs hφs hφnn

private theorem dirFun_add {u : ℝ⁴ → ℝ} {s : Set ℝ⁴} (hu : ContinuousOn u s) (e : ℝ⁴)
    {φ ψ : ℝ⁴ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφcs : HasCompactSupport φ) (hφs : tsupport φ ⊆ s)
    (hψ : ContDiff ℝ ∞ ψ) (hψcs : HasCompactSupport ψ) (hψs : tsupport ψ ⊆ s) :
    dirFun u e (φ + ψ) = dirFun u e φ + dirFun u e ψ := by
  have hpt : ∀ x : ℝ⁴,
      Laplacian.laplacian (φ + ψ) x - (fderiv ℝ (fderiv ℝ (φ + ψ)) x) e e
        = (Laplacian.laplacian φ x - (fderiv ℝ (fderiv ℝ φ) x) e e)
          + (Laplacian.laplacian ψ x - (fderiv ℝ (fderiv ℝ ψ) x) e e) := fun x => by
    rw [ContDiffAt.laplacian_add ((hφ.of_le (by decide)).contDiffAt)
        ((hψ.of_le (by decide)).contDiffAt),
      second_deriv_add ((hφ.of_le (by decide)).contDiffAt) ((hψ.of_le (by decide)).contDiffAt)]
    ring
  have hfun : (fun x : ℝ⁴ => u x * (Laplacian.laplacian (φ + ψ) x
        - (fderiv ℝ (fderiv ℝ (φ + ψ)) x) e e))
      = fun x => u x * (Laplacian.laplacian φ x - (fderiv ℝ (fderiv ℝ φ) x) e e)
          + u x * (Laplacian.laplacian ψ x - (fderiv ℝ (fderiv ℝ ψ) x) e e) := by
    funext x
    rw [hpt x]
    ring
  have hint : ∀ (η : ℝ⁴ → ℝ), ContDiff ℝ ∞ η → HasCompactSupport η → tsupport η ⊆ s →
      Integrable (fun x : ℝ⁴ => u x * (Laplacian.laplacian η x - (fderiv ℝ (fderiv ℝ η) x) e e)) :=
    fun η hη hηcs hηs => by
      have h1 : (fun x : ℝ⁴ => u x * (Laplacian.laplacian η x - (fderiv ℝ (fderiv ℝ η) x) e e))
          = fun x => u x * Laplacian.laplacian η x - u x * (fderiv ℝ (fderiv ℝ η) x) e e := by
        funext x; ring
      rw [h1]
      exact (integrable_mul_laplacian hu hη hηcs hηs).sub
        (integrable_mul_second_deriv hu e hη hηcs hηs)
  rw [dirFun, dirFun, dirFun, hfun, integral_add (hint φ hφ hφcs hφs) (hint ψ hψ hψcs hψs)]

private theorem dirFun_smul {u : ℝ⁴ → ℝ} {s : Set ℝ⁴} (hu : ContinuousOn u s) (e : ℝ⁴) (a : ℝ)
    {φ : ℝ⁴ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφcs : HasCompactSupport φ) (hφs : tsupport φ ⊆ s) :
    dirFun u e (a • φ) = a * dirFun u e φ := by
  have hpt : ∀ x : ℝ⁴,
      Laplacian.laplacian (a • φ) x - (fderiv ℝ (fderiv ℝ (a • φ)) x) e e
        = a * (Laplacian.laplacian φ x - (fderiv ℝ (fderiv ℝ φ) x) e e) := fun x => by
    rw [InnerProductSpace.laplacian_smul a ((hφ.of_le (by decide)).contDiffAt),
      second_deriv_smul a ((hφ.of_le (by decide)).contDiffAt)]
    ring
  have hfun : (fun x : ℝ⁴ => u x * (Laplacian.laplacian (a • φ) x
        - (fderiv ℝ (fderiv ℝ (a • φ)) x) e e))
      = fun x => a * (u x * (Laplacian.laplacian φ x - (fderiv ℝ (fderiv ℝ φ) x) e e)) := by
    funext x
    rw [hpt x]
    ring
  rw [dirFun, dirFun, hfun, MeasureTheory.integral_const_mul]

private theorem dirFun_pos {u : ℝ⁴ → ℝ} {s : Set ℝ⁴} (hs : IsOpen s) (hu : ContinuousOn u s)
    (h2 : IsTwoConvexOn u s) (b : OrthonormalBasis (Fin 4) ℝ ℝ⁴) (e : ℝ⁴) (hb : b 0 = e)
    {φ : ℝ⁴ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφcs : HasCompactSupport φ) (hφs : tsupport φ ⊆ s)
    (hφnn : 0 ≤ φ) : 0 ≤ dirFun u e φ :=
  hyperplane_laplacian_nonneg_of_twoConvex_e hs hu h2 b e hb φ hφ hφcs hφs hφnn


/-! ## Auxiliary measure facts -/

/-- The `1/2`-multiple of a measure finite on `closure t` is finite on `closure t`. -/
private theorem half_smul_apply_lt_top {t : Set ℝ⁴} {ν : Measure ℝ⁴}
    (h : ν (closure t) < ⊤) : ((1/2 : NNReal) • ν) (closure t) < ⊤ := by
  rw [Measure.smul_apply]
  exact ENNReal.mul_lt_top ENNReal.coe_lt_top h

/-! ## Polarisation -/

/-- Polarisation of the second derivative in the orthonormal pair
`e± = (e_i ± e_j)/√2`. -/
private theorem polarisation {φ : ℝ⁴ → ℝ} {x : ℝ⁴} (hφ : ContDiffAt ℝ 2 φ x) (i j : Fin 4) :
    (fderiv ℝ (fderiv ℝ φ) x) (stdE i) (stdE j)
      = (1/2) * ((fderiv ℝ (fderiv ℝ φ) x) ((Real.sqrt 2)⁻¹ • (stdE i + stdE j))
            ((Real.sqrt 2)⁻¹ • (stdE i + stdE j))
          - (fderiv ℝ (fderiv ℝ φ) x) ((Real.sqrt 2)⁻¹ • (stdE i - stdE j))
            ((Real.sqrt 2)⁻¹ • (stdE i - stdE j))) := by
  have hsymm := (ContDiffAt.isSymmSndFDerivAt (𝕜 := ℝ) (n := 2) hφ (by simp)).eq
  have h1 : (fderiv ℝ (fderiv ℝ φ) x) ((Real.sqrt 2)⁻¹ • (stdE i + stdE j))
      ((Real.sqrt 2)⁻¹ • (stdE i + stdE j))
      = (1/2) * ((fderiv ℝ (fderiv ℝ φ) x) (stdE i) (stdE i)
          + (fderiv ℝ (fderiv ℝ φ) x) (stdE i) (stdE j)
          + (fderiv ℝ (fderiv ℝ φ) x) (stdE j) (stdE i)
          + (fderiv ℝ (fderiv ℝ φ) x) (stdE j) (stdE j)) := by
    simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
    field_simp
    rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    ring
  have h3 : (fderiv ℝ (fderiv ℝ φ) x) ((Real.sqrt 2)⁻¹ • (stdE i - stdE j))
      ((Real.sqrt 2)⁻¹ • (stdE i - stdE j))
      = (1/2) * ((fderiv ℝ (fderiv ℝ φ) x) (stdE i) (stdE i)
          - (fderiv ℝ (fderiv ℝ φ) x) (stdE i) (stdE j)
          - (fderiv ℝ (fderiv ℝ φ) x) (stdE j) (stdE i)
          + (fderiv ℝ (fderiv ℝ φ) x) (stdE j) (stdE j)) := by
    simp only [map_sub, map_smul, sub_apply, smul_apply, smul_eq_mul]
    field_simp
    rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    ring
  rw [h1, h3, hsymm (stdE j) (stdE i)]
  ring

/-! ## The norm of the polarised directions -/

private theorem norm_stdE (i : Fin 4) : ‖stdE i‖ = 1 := by
  rw [stdE]; simp

private theorem norm_add_stdE {i j : Fin 4} (hij : i ≠ j) : ‖stdE i + stdE j‖ = Real.sqrt 2 := by
  have hsq : ‖stdE i + stdE j‖ ^ 2 = 2 := by
    rw [norm_add_sq_real]
    rw [show ⟪stdE i, stdE j⟫_ℝ = 0 from by
      rw [stdE, stdE]; simp [PiLp.inner_apply, EuclideanSpace.single, hij]]
    rw [norm_stdE i, norm_stdE j]
    norm_num
  have hnn := norm_nonneg (stdE i + stdE j)
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]

private theorem norm_sub_stdE {i j : Fin 4} (hij : i ≠ j) : ‖stdE i - stdE j‖ = Real.sqrt 2 := by
  have hsq : ‖stdE i - stdE j‖ ^ 2 = 2 := by
    rw [norm_sub_sq_real]
    rw [show ⟪stdE i, stdE j⟫_ℝ = 0 from by
      rw [stdE, stdE]; simp [PiLp.inner_apply, EuclideanSpace.single, hij]]
    rw [norm_stdE i, norm_stdE j]
    norm_num
  have hnn := norm_nonneg (stdE i - stdE j)
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]

private theorem norm_smul_sqrt_inv {v : ℝ⁴} (hv : ‖v‖ = Real.sqrt 2) :
    ‖(Real.sqrt 2)⁻¹ • v‖ = 1 := by
  have h2 : Real.sqrt 2 ≠ 0 := by positivity
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (Real.sqrt_nonneg 2), hv,
    inv_mul_cancel₀ h2]


/-- A continuous function with compact support is bounded. -/
private theorem exists_bound_of_hasCompactSupport {f : ℝ⁴ → ℝ} (hf : Continuous f)
    (hcs : HasCompactSupport f) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖f x‖ ≤ C := by
  obtain ⟨C, hC⟩ := hcs.exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
  by_cases hx : x ∈ tsupport f
  · exact le_trans (hC x hx) (le_max_left _ _)
  · rw [image_eq_zero_of_notMem_tsupport (fun h => hx h), norm_zero]
    exact le_max_right _ _

/-! ## The main theorem -/

theorem hessianMeasureInput_holds : HessianMeasureInput := by
  intro u s hs hb hu h2 t ht hct
  -- ## the compact set and the support of test functions
  have hKc : IsCompact (closure t) :=
    Metric.isCompact_iff_isClosed_bounded.mpr
      ⟨isClosed_closure, Bornology.IsBounded.subset hb hct⟩
  have hKmeas : MeasurableSet (closure t) := hKc.isClosed.measurableSet
  have hcpt : ∀ φ : ℝ⁴ → ℝ, tsupport φ ⊆ s → HasCompactSupport φ := by
    intro φ hφs
    rw [HasCompactSupport]
    exact Metric.isCompact_iff_isClosed_bounded.mpr
      ⟨isClosed_tsupport φ, Bornology.IsBounded.subset hb hφs⟩
  -- ## the Laplacian functional and its measure
  obtain ⟨μ, hμs, hμfin, hμ⟩ :=
    Commons.Measure.Distribution.exists_measure_of_positive_functional_compact hs (lapFun u)
      (fun φ ψ hφ hφs hψ hψs => lapFun_add hu hφ (hcpt φ hφs) hφs hψ (hcpt ψ hψs) hψs)
      (fun a φ hφ hφs => lapFun_smul hu a hφ (hcpt φ hφs) hφs)
      (fun φ hφ hφs hφnn => lapFun_pos hs hu h2 hφ (hcpt φ hφs) hφs hφnn)
  -- ## the direction measures
  have hdir : ∀ e : ℝ⁴, ‖e‖ = 1 → ∃ μe : Measure ℝ⁴,
      (μe sᶜ = 0 ∧ (∀ K : Set ℝ⁴, IsCompact K → K ⊆ s → μe K < ⊤) ∧
        ∀ φ : ℝ⁴ → ℝ, ContDiff ℝ ∞ φ → tsupport φ ⊆ s →
          ∫ x, φ x ∂μe = dirFun u e φ) := by
    intro e he
    obtain ⟨b, hb'⟩ := Commons.Analysis.InnerProductSpace.exists_orthonormalBasis_head
      (E := ℝ⁴) (n := 3) (by simp [finrank_euclideanSpace]) e he
    exact Commons.Measure.Distribution.exists_measure_of_positive_functional_compact hs (dirFun u e)
      (fun φ ψ hφ hφs hψ hψs => dirFun_add hu e hφ (hcpt φ hφs) hφs hψ (hcpt ψ hψs) hψs)
      (fun a φ hφ hφs => dirFun_smul hu e a hφ (hcpt φ hφs) hφs)
      (fun φ hφ hφs hφnn => dirFun_pos hs hu h2 b e hb' hφ (hcpt φ hφs) hφs hφnn)
  choose μD hμD using hdir
  -- ## the second derivative tested against `u`
  have hsecond : ∀ (e : ℝ⁴) (φ : ℝ⁴ → ℝ), ContDiff ℝ ∞ φ → tsupport φ ⊆ s →
      ∫ x, u x * (fderiv ℝ (fderiv ℝ φ) x) e e = lapFun u φ - dirFun u e φ := by
    intro e φ hφ hφs
    have hcs := hcpt φ hφs
    rw [lapFun, dirFun]
    have hpt : (fun x : ℝ⁴ => u x * (Laplacian.laplacian φ x - (fderiv ℝ (fderiv ℝ φ) x) e e))
        = fun x => u x * Laplacian.laplacian φ x - u x * (fderiv ℝ (fderiv ℝ φ) x) e e := by
      funext x; ring
    rw [hpt, integral_sub (integrable_mul_laplacian hu hφ hcs hφs)
      (integrable_mul_second_deriv hu e hφ hcs hφs)]
    ring
  -- ## the pair of measures representing each second derivative
  have hpair : ∀ i j : Fin 4, ∃ ν₁ ν₂ : Measure ℝ⁴,
      ((ν₁ (closure t) < ⊤ ∧ ν₂ (closure t) < ⊤) ∧
      (∀ φ : ℝ⁴ → ℝ, ContDiff ℝ ∞ φ → tsupport φ ⊆ t →
        ∫ x, u x * (fderiv ℝ (fderiv ℝ φ) x) (stdE i) (stdE j)
          = ∫ x, φ x ∂ν₁ - ∫ x, φ x ∂ν₂)) := by
    intro i j
    by_cases hij : i = j
    · subst hij
      refine ⟨μ, μD (stdE i) (norm_stdE i), ⟨hμfin _ hKc hct, (hμD _ _).2.1 _ hKc hct⟩, ?_⟩
      intro φ hφ hφs
      have hφs' : tsupport φ ⊆ s := hφs.trans (subset_closure.trans hct)
      rw [hsecond (stdE i) φ hφ hφs', ← hμ φ hφ hφs',
        ← (hμD (stdE i) (norm_stdE i)).2.2 φ hφ hφs']
    · have hem : ‖(Real.sqrt 2)⁻¹ • (stdE i - stdE j)‖ = 1 :=
        norm_smul_sqrt_inv (norm_sub_stdE hij)
      have hep : ‖(Real.sqrt 2)⁻¹ • (stdE i + stdE j)‖ = 1 :=
        norm_smul_sqrt_inv (norm_add_stdE hij)
      refine ⟨(1/2 : NNReal) • μD ((Real.sqrt 2)⁻¹ • (stdE i - stdE j)) hem,
        (1/2 : NNReal) • μD ((Real.sqrt 2)⁻¹ • (stdE i + stdE j)) hep, ⟨?_, ?_⟩, ?_⟩
      · exact half_smul_apply_lt_top ((hμD _ hem).2.1 _ hKc hct)
      · exact half_smul_apply_lt_top ((hμD _ hep).2.1 _ hKc hct)
      · intro φ hφ hφs
        have hφs' : tsupport φ ⊆ s := hφs.trans (subset_closure.trans hct)
        have hcs := hcpt φ hφs'
        have h2φ : ContDiff ℝ 2 φ := hφ.of_le (by decide)
        have hpt : ∀ x : ℝ⁴, u x * (fderiv ℝ (fderiv ℝ φ) x) (stdE i) (stdE j)
            = (1/2) * (u x * (fderiv ℝ (fderiv ℝ φ) x)
                ((Real.sqrt 2)⁻¹ • (stdE i + stdE j)) ((Real.sqrt 2)⁻¹ • (stdE i + stdE j))
              - u x * (fderiv ℝ (fderiv ℝ φ) x)
                ((Real.sqrt 2)⁻¹ • (stdE i - stdE j)) ((Real.sqrt 2)⁻¹ • (stdE i - stdE j))) := by
          intro x
          rw [polarisation (h2φ.contDiffAt)]
          ring
        rw [show (∫ x, u x * (fderiv ℝ (fderiv ℝ φ) x) (stdE i) (stdE j))
            = ∫ x, (1/2) * (u x * (fderiv ℝ (fderiv ℝ φ) x)
                ((Real.sqrt 2)⁻¹ • (stdE i + stdE j))
                ((Real.sqrt 2)⁻¹ • (stdE i + stdE j))
              - u x * (fderiv ℝ (fderiv ℝ φ) x)
                ((Real.sqrt 2)⁻¹ • (stdE i - stdE j))
                ((Real.sqrt 2)⁻¹ • (stdE i - stdE j))) from
          integral_congr_ae (Filter.Eventually.of_forall hpt)]
        rw [MeasureTheory.integral_const_mul,
          integral_sub
            (integrable_mul_second_deriv hu ((Real.sqrt 2)⁻¹ • (stdE i + stdE j)) hφ hcs hφs')
            (integrable_mul_second_deriv hu ((Real.sqrt 2)⁻¹ • (stdE i - stdE j)) hφ hcs hφs'),
          hsecond ((Real.sqrt 2)⁻¹ • (stdE i + stdE j)) φ hφ hφs',
          hsecond ((Real.sqrt 2)⁻¹ • (stdE i - stdE j)) φ hφ hφs',
          ← (hμD _ hem).2.2 φ hφ hφs', ← (hμD _ hep).2.2 φ hφ hφs',
          MeasureTheory.integral_smul_nnreal_measure, MeasureTheory.integral_smul_nnreal_measure,
          NNReal.smul_def, NNReal.smul_def]
        push_cast
        ring
  choose ν₁ ν₂ hνpair hνid using hpair
  -- ## finiteness of the restricted measures
  have hfin₁ : ∀ i j, IsFiniteMeasure ((ν₁ i j).restrict (closure t)) := fun i j =>
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
        exact (hνpair i j).1⟩
  have hfin₂ : ∀ i j, IsFiniteMeasure ((ν₂ i j).restrict (closure t)) := fun i j =>
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
        exact (hνpair i j).2⟩
  -- ## the density and the singular part
  refine ⟨fun i j x => (((ν₁ i j).restrict (closure t)).rnDeriv volume x).toReal
      - (((ν₂ i j).restrict (closure t)).rnDeriv volume x).toReal,
    fun i j => (((ν₁ i j).restrict (closure t)).singularPart volume).toSignedMeasure
      - (((ν₂ i j).restrict (closure t)).singularPart volume).toSignedMeasure,
    ?_, ?_, ?_⟩
  · intro i j
    haveI := hfin₁ i j
    haveI := hfin₂ i j
    exact ((Measure.integrable_toReal_rnDeriv (μ := (ν₁ i j).restrict (closure t))
        (ν := volume)).locallyIntegrable).sub
      ((Measure.integrable_toReal_rnDeriv (μ := (ν₂ i j).restrict (closure t))
        (ν := volume)).locallyIntegrable)
  · intro i j
    haveI := hfin₁ i j
    haveI := hfin₂ i j
    have h1 : ((((ν₁ i j).restrict (closure t)).singularPart volume).toSignedMeasure
          - (((ν₂ i j).restrict (closure t)).singularPart volume).toSignedMeasure).totalVariation
        ≤ ((ν₁ i j).restrict (closure t)).singularPart volume
          + ((ν₂ i j).restrict (closure t)).singularPart volume := by
      rw [SignedMeasure.totalVariation_eq_variation]
      refine VectorMeasure.variation_sub_le.trans (le_of_eq ?_)
      rw [Measure.variation_toSignedMeasure, Measure.variation_toSignedMeasure]
    refine Measure.MutuallySingular.mono ?_ h1 le_rfl
    exact (Measure.mutuallySingular_singularPart _ volume).add_left
      (Measure.mutuallySingular_singularPart _ volume)
  · intro φ hφ hφs i j
    have hφs' : tsupport φ ⊆ s := hφs.trans (subset_closure.trans hct)
    have hcs : HasCompactSupport φ := hcpt φ hφs'
    obtain ⟨Cφ, hCφ0, hCφ⟩ := exists_bound_of_hasCompactSupport hφ.continuous hcs
    have hφK : tsupport φ ⊆ closure t := hφs.trans subset_closure
    -- the restricted measure agrees with the original one on test functions supported in `t`
    have hres : ∀ (ν : Measure ℝ⁴), (∫ x, φ x ∂(ν.restrict (closure t))) = ∫ x, φ x ∂ν := by
      intro ν
      rw [← MeasureTheory.integral_indicator (μ := ν) (s := closure t) hKmeas]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      by_cases hx : x ∈ closure t
      · rw [Set.indicator_of_mem hx]
      · rw [Set.indicator_of_notMem hx,
          image_eq_zero_of_notMem_tsupport (fun h => hx (hφK h))]
    -- bounded functions are integrable for finite measures
    have hInt : ∀ (μ : Measure ℝ⁴), IsFiniteMeasure μ → Integrable φ μ :=
      fun μ _ => Integrable.of_bound hφ.continuous.aestronglyMeasurable Cφ
        (Filter.Eventually.of_forall hCφ)
    -- the Lebesgue decomposition of a finite measure
    have hsplit : ∀ (ν' : Measure ℝ⁴), IsFiniteMeasure ν' →
        (∫ x, φ x ∂ν') = (∫ x, φ x ∂ν'.singularPart volume)
          + ∫ x, φ x * ((ν'.rnDeriv volume x).toReal) ∂volume := by
      intro ν' hν'
      haveI := hν'
      have hsp_fin : (ν'.singularPart volume) univ < ⊤ :=
        lt_of_le_of_lt
          ((Measure.le_iff.mp (Measure.singularPart_le ν' volume)) univ MeasurableSet.univ)
          (measure_lt_top ν' univ)
      have hsp_inst : IsFiniteMeasure (ν'.singularPart volume) := ⟨hsp_fin⟩
      have hwd_inst : IsFiniteMeasure (volume.withDensity (ν'.rnDeriv volume)) :=
        isFiniteMeasure_withDensity (Measure.lintegral_rnDeriv_lt_top ν' volume).ne
      haveI := hsp_inst
      haveI := hwd_inst
      have hwd : (∫ x, φ x ∂(volume.withDensity (ν'.rnDeriv volume)))
          = ∫ x, φ x * ((ν'.rnDeriv volume x).toReal) ∂volume := by
        rw [integral_withDensity_eq_integral_toReal_smul (Measure.measurable_rnDeriv _ _)
          (Measure.rnDeriv_lt_top ν' volume) φ]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp [smul_eq_mul, mul_comm]
      have hdec := Measure.singularPart_add_rnDeriv ν' volume
      conv_lhs => rw [← hdec]
      rw [MeasureTheory.integral_add_measure (hInt _ hsp_inst) (hInt _ hwd_inst), hwd]
    -- abbreviations for the singular parts and the signed measure
    set a₁ : Measure ℝ⁴ := ((ν₁ i j).restrict (closure t)).singularPart volume with ha₁
    set a₂ : Measure ℝ⁴ := ((ν₂ i j).restrict (closure t)).singularPart volume with ha₂
    have hsing₁ : IsFiniteMeasure a₁ := ⟨by
      rw [ha₁]
      exact lt_of_le_of_lt
        ((Measure.le_iff.mp (Measure.singularPart_le ((ν₁ i j).restrict (closure t)) volume))
          univ MeasurableSet.univ)
        (measure_lt_top ((ν₁ i j).restrict (closure t)) univ)⟩
    have hsing₂ : IsFiniteMeasure a₂ := ⟨by
      rw [ha₂]
      exact lt_of_le_of_lt
        ((Measure.le_iff.mp (Measure.singularPart_le ((ν₂ i j).restrict (closure t)) volume))
          univ MeasurableSet.univ)
        (measure_lt_top ((ν₂ i j).restrict (closure t)) univ)⟩
    have hσval : (∫ᵛ x, φ x ∂•(a₁.toSignedMeasure - a₂.toSignedMeasure))
        = (∫ x, φ x ∂a₁) - (∫ x, φ x ∂a₂) := by
      haveI := hsing₁
      haveI := hsing₂
      have hint₁ : (a₁.toSignedMeasure).Integrable φ := by
        rw [VectorMeasure.Integrable, Measure.variation_toSignedMeasure]
        exact hInt a₁ hsing₁
      have hint₂ : (a₂.toSignedMeasure).Integrable φ := by
        rw [VectorMeasure.Integrable, Measure.variation_toSignedMeasure]
        exact hInt a₂ hsing₂
      rw [VectorMeasure.integral_sub_vectorMeasure hint₁ hint₂,
        Commons.Measure.VectorMeasure.integral_toSignedMeasure_smul,
        Commons.Measure.VectorMeasure.integral_toSignedMeasure_smul]
    rw [show (∫ᵛ x, φ x ∂•(a₁.toSignedMeasure - a₂.toSignedMeasure)) = _ from hσval]
    rw [hνid i j φ hφ hφs, ← hres (ν₁ i j), ← hres (ν₂ i j),
      hsplit _ (hfin₁ i j), hsplit _ (hfin₂ i j)]
    have hMval : (∫ x, φ x * ((((ν₁ i j).restrict (closure t)).rnDeriv volume x).toReal
          - (((ν₂ i j).restrict (closure t)).rnDeriv volume x).toReal) ∂volume)
        = (∫ x, φ x * (((ν₁ i j).restrict (closure t)).rnDeriv volume x).toReal ∂volume)
          - (∫ x, φ x * (((ν₂ i j).restrict (closure t)).rnDeriv volume x).toReal ∂volume) := by
      haveI := hfin₁ i j
      haveI := hfin₂ i j
      have hint₁ : Integrable (fun x : ℝ⁴ =>
          φ x * (((ν₁ i j).restrict (closure t)).rnDeriv volume x).toReal) volume := by
        refine Integrable.mono' ((Measure.integrable_toReal_rnDeriv
            (μ := (ν₁ i j).restrict (closure t)) (ν := volume)).const_mul Cφ)
          (hφ.continuous.aestronglyMeasurable.mul
            (Measure.measurable_rnDeriv _ _).aemeasurable.ennreal_toReal.aestronglyMeasurable) ?_
        filter_upwards with x
        have h1 : ‖(((ν₁ i j).restrict (closure t)).rnDeriv volume x).toReal‖
            = (((ν₁ i j).restrict (closure t)).rnDeriv volume x).toReal :=
          Real.norm_of_nonneg ENNReal.toReal_nonneg
        rw [norm_mul, h1]
        exact mul_le_mul_of_nonneg_right (hCφ x) ENNReal.toReal_nonneg
      have hint₂ : Integrable (fun x : ℝ⁴ =>
          φ x * (((ν₂ i j).restrict (closure t)).rnDeriv volume x).toReal) volume := by
        refine Integrable.mono' ((Measure.integrable_toReal_rnDeriv
            (μ := (ν₂ i j).restrict (closure t)) (ν := volume)).const_mul Cφ)
          (hφ.continuous.aestronglyMeasurable.mul
            (Measure.measurable_rnDeriv _ _).aemeasurable.ennreal_toReal.aestronglyMeasurable) ?_
        filter_upwards with x
        have h1 : ‖(((ν₂ i j).restrict (closure t)).rnDeriv volume x).toReal‖
            = (((ν₂ i j).restrict (closure t)).rnDeriv volume x).toReal :=
          Real.norm_of_nonneg ENNReal.toReal_nonneg
        rw [norm_mul, h1]
        exact mul_le_mul_of_nonneg_right (hCφ x) ENNReal.toReal_nonneg
      rw [show (fun x : ℝ⁴ => φ x * ((((ν₁ i j).restrict (closure t)).rnDeriv volume x).toReal
            - (((ν₂ i j).restrict (closure t)).rnDeriv volume x).toReal))
          = fun x => φ x * (((ν₁ i j).restrict (closure t)).rnDeriv volume x).toReal
            - φ x * (((ν₂ i j).restrict (closure t)).rnDeriv volume x).toReal from by
        funext x; ring]
      rw [integral_sub hint₁ hint₂]
    rw [hMval]
    ring

end Submission
