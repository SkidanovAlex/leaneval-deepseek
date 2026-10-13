/-
# Symmetry of the trace-of-Hessian pairing

`Work.FTS.PressureOn.Green.integral_mul_laplaceTrace_comm`:

  `∫ x, f x * laplaceTrace u x = ∫ x, laplaceTrace f x * u x`

for `f, u : ℝ³ → ℝ` of class `C²` with `u` compactly supported.  This is the
integration-by-parts (Green) symmetry of the Laplacian, written with the trace of the Hessian
`laplaceTrace`; it is the entry that lets a Newtonian potential be paired against a test
function in either order.

## The route

The difference of the two integrands is a divergence.  With
`G := f • ∇u − u • ∇f` (both `f` and `u` are `C²`),

  `div G = f · Δu + ⟪∇f, ∇u⟫ − (u · Δf + ⟪∇u, ∇f⟫) = f · Δu − u · Δf`,

because `div (a • ∇v) = a · div (∇v) + (fderiv a) (∇v)` (product rule for the trace of the
derivative), `div (∇v) = laplaceTrace v` (the definition of the trace in the standard basis),
and `(fderiv f x) (∇u x) = ⟪∇f x, ∇u x⟫ = ⟪∇u x, ∇f x⟫`.

`G` is `C¹`, and it is supported on `tsupport u` (`u ≡ 0` on the open set `(tsupport u)ᶜ`,
hence `∇u ≡ 0` there as well), so it is compactly supported, continuous and its divergence is
integrable.  The divergence theorem for compactly supported `C¹` fields,
`Work.FTS.PressureOn.integral_div_eq_zero_of_hasFDerivAt`, then gives `∫ div G = 0`, i.e.

  `∫ x, (f x * Δu x − Δf x * u x) = 0`,

and since both `f · Δu` and `Δf · u` are continuous with support in the compact set
`tsupport u`, they are integrable and the linearity of the integral finishes the proof.
-/
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Trace
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Work.FTS.PressureOn.Defs
import Submission.Work.FTS.PressureOn.integral_div_eq_zero_of_hasFDerivAt

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set MeasureTheory Filter
open scoped Topology

namespace Work.FTS.PressureOn.Green

/-! ## Elementary facts about the standard basis -/

/-- The `i`-th coordinate of a vector of `ℝ³` is the inner product with `e i`. -/
lemma inner_e_eq (v : R3) (i : Fin 3) : inner ℝ v (FiniteTimeSingularity.e i) = v i := by
  rw [PiLp.inner_apply]
  simp only [FiniteTimeSingularity.e]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj]
    simp
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- The `i`-th coordinate of a vector of `ℝ³` is the inner product with `e i` (other order). -/
lemma inner_e_eq' (v : R3) (i : Fin 3) : inner ℝ (FiniteTimeSingularity.e i) v = v i := by
  rw [real_inner_comm, inner_e_eq]

/-! ## The product rule for the divergence, and the divergence of a gradient -/

/-- **The product rule for `div`.**  For `a : ℝ³ → ℝ` and `V : ℝ³ → ℝ³` differentiable at `x`,
`div (a • V) x = a x * div V x + (fderiv ℝ a x) (V x)`. -/
theorem div_smul_eq (a : R3 → ℝ) (V : R3 → R3) (x : R3)
    (ha : DifferentiableAt ℝ a x) (hV : DifferentiableAt ℝ V x) :
    div (fun y => a y • V y) x = a x * div V x + (fderiv ℝ a x) (V x) := by
  rw [div, fderiv_fun_smul ha hV]
  rw [show (↑(a x • fderiv ℝ V x + (fderiv ℝ a x).smulRight (V x)) : R3 →ₗ[ℝ] R3)
        = (a x • (fderiv ℝ V x : R3 →ₗ[ℝ] R3)) + ((fderiv ℝ a x).smulRight (V x) : R3 →ₗ[ℝ] R3)
      from rfl]
  rw [map_add, map_smul]
  rw [show ((fderiv ℝ a x).smulRight (V x) : R3 →ₗ[ℝ] R3)
        = ((fderiv ℝ a x : R3 →ₗ[ℝ] ℝ)).smulRight (V x) from rfl]
  rw [LinearMap.trace_smulRight]
  rw [div]
  rw [show ((fderiv ℝ a x : R3 →ₗ[ℝ] ℝ)) (V x) = (fderiv ℝ a x) (V x) from rfl, smul_eq_mul]

/-- **Linearity of `div` in its argument.** -/
theorem div_sub_eq (A B : R3 → R3) (x : R3)
    (hA : DifferentiableAt ℝ A x) (hB : DifferentiableAt ℝ B x) :
    div (fun y => A y - B y) x = div A x - div B x := by
  rw [div, div, div, fderiv_fun_sub hA hB]
  rw [show (↑(fderiv ℝ A x - fderiv ℝ B x) : R3 →ₗ[ℝ] R3)
        = (fderiv ℝ A x : R3 →ₗ[ℝ] R3) - (fderiv ℝ B x : R3 →ₗ[ℝ] R3) from rfl]
  rw [map_sub]

/-- The gradient of a `C²` function is `C¹`. -/
theorem contDiff_gradient (u : R3 → ℝ) (hu : ContDiff ℝ 2 u) :
    ContDiff ℝ 1 (fun z => gradient u z) := by
  have hfd : ContDiff ℝ 1 (fderiv ℝ u) := hu.fderiv_right (m := 1) (n := 2) (by norm_num)
  have := ((InnerProductSpace.toDual ℝ R3).symm.toContinuousLinearMap).contDiff.comp hfd
  simpa [gradient, Function.comp_def] using this

/-- **`div (∇u) = laplaceTrace u`**, coordinate by coordinate: the diagonal entries of the
Jacobian of the gradient are the second derivatives of `u` along the coordinate lines. -/
theorem fderiv_gradient_apply_diag (u : R3 → ℝ) (hu : ContDiff ℝ 2 u) (x : R3) (i : Fin 3) :
    (fderiv ℝ (fun z => gradient u z) x (FiniteTimeSingularity.e i)) i
      = fderiv ℝ (fun w => fderiv ℝ u w (FiniteTimeSingularity.e i)) x
          (FiniteTimeSingularity.e i) := by
  have h1 : ContDiff ℝ 1 (fun z => gradient u z) := contDiff_gradient u hu
  have hG : HasFDerivAt (fun z => gradient u z) (fderiv ℝ (fun z => gradient u z) x) x :=
    ((h1.differentiable (by norm_num)).differentiableAt).hasFDerivAt
  have hφ : (fun w => fderiv ℝ u w (FiniteTimeSingularity.e i))
      = (innerSL ℝ (FiniteTimeSingularity.e i)) ∘ (fun z => gradient u z) := by
    funext w
    simp only [Function.comp_apply]
    show fderiv ℝ u w (FiniteTimeSingularity.e i)
      = (innerSL ℝ (FiniteTimeSingularity.e i)) (gradient u w)
    rw [show (innerSL ℝ (FiniteTimeSingularity.e i)) (gradient u w)
        = inner ℝ (FiniteTimeSingularity.e i) (gradient u w) from rfl, real_inner_comm]
    exact (inner_gradient_left (f := u) (x := w) (y := FiniteTimeSingularity.e i)).symm
  have hcomp : HasFDerivAt ((innerSL ℝ (FiniteTimeSingularity.e i)) ∘ (fun z => gradient u z))
      ((innerSL ℝ (FiniteTimeSingularity.e i)) ∘SL fderiv ℝ (fun z => gradient u z) x) x :=
    (ContinuousLinearMap.hasFDerivAt (innerSL ℝ (FiniteTimeSingularity.e i))).comp x hG
  have hfφ : fderiv ℝ (fun w => fderiv ℝ u w (FiniteTimeSingularity.e i)) x
      = (innerSL ℝ (FiniteTimeSingularity.e i)) ∘SL fderiv ℝ (fun z => gradient u z) x := by
    rw [hφ]; exact hcomp.fderiv
  rw [hfφ, ContinuousLinearMap.comp_apply]
  rw [show (innerSL ℝ (FiniteTimeSingularity.e i))
        (fderiv ℝ (fun z => gradient u z) x (FiniteTimeSingularity.e i))
      = inner ℝ (FiniteTimeSingularity.e i)
        (fderiv ℝ (fun z => gradient u z) x (FiniteTimeSingularity.e i)) from rfl]
  rw [real_inner_comm, inner_e_eq]

/-- **The divergence of the gradient is the trace of the Hessian.** -/
theorem div_gradient_eq_laplaceTrace (u : R3 → ℝ) (hu : ContDiff ℝ 2 u) :
    div (fun z => gradient u z) = laplaceTrace u := by
  funext x
  rw [Work.FTS.PressureOn.div_eq_sum_single]
  rw [laplaceTrace]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact fderiv_gradient_apply_diag u hu x i

/-- **The product rule for `div` applied to `a • ∇u`**, using `div (∇u) = laplaceTrace u`. -/
theorem div_smul_gradient (a u : R3 → ℝ) (hu : ContDiff ℝ 2 u) (x : R3)
    (ha : DifferentiableAt ℝ a x) :
    div (fun y => a y • gradient u y) x
      = a x * laplaceTrace u x + (fderiv ℝ a x) (gradient u x) := by
  rw [div_smul_eq a (fun y => gradient u y) x ha
        (((contDiff_gradient u hu).differentiable (by norm_num)).differentiableAt)]
  rw [congrFun (div_gradient_eq_laplaceTrace u hu) x]

/-- **The divergence of `f • ∇u - u • ∇f`** is `f · Δu - u · Δf`: the two mixed terms
`(fderiv f x) (∇u x)` and `(fderiv u x) (∇f x)` are both `⟪∇f x, ∇u x⟫` and cancel. -/
theorem div_gradient_sub (f u : R3 → ℝ) (hf : ContDiff ℝ 2 f) (hu : ContDiff ℝ 2 u) :
    div (fun y => f y • gradient u y - u y • gradient f y)
      = fun x => f x * laplaceTrace u x - laplaceTrace f x * u x := by
  funext x
  have hcf : DifferentiableAt ℝ f x := (hf.differentiable (by norm_num)).differentiableAt
  have hcu : DifferentiableAt ℝ u x := (hu.differentiable (by norm_num)).differentiableAt
  have h1 : DifferentiableAt ℝ (fun y => f y • gradient u y) x :=
    hcf.smul (((contDiff_gradient u hu).differentiable (by norm_num)).differentiableAt)
  have h2 : DifferentiableAt ℝ (fun y => u y • gradient f y) x :=
    hcu.smul (((contDiff_gradient f hf).differentiable (by norm_num)).differentiableAt)
  rw [div_sub_eq (fun y => f y • gradient u y) (fun y => u y • gradient f y) x h1 h2,
    div_smul_gradient f u hu x hcf, div_smul_gradient u f hf x hcu]
  have hcancel : (fderiv ℝ f x) (gradient u x) = (fderiv ℝ u x) (gradient f x) := by
    rw [← inner_gradient_left (f := f) (x := x) (y := gradient u x),
      ← inner_gradient_left (f := u) (x := x) (y := gradient f x)]
    exact real_inner_comm _ _
  rw [hcancel]
  ring

/-! ## Vanishing off the support, and continuity -/

/-- Off the topological support of `u`, the gradient of `u` vanishes. -/
lemma gradient_eq_zero_of_notMem_tsupport {u : R3 → ℝ} {x : R3} (hx : x ∉ tsupport u) :
    gradient u x = 0 := by
  have hopen : IsOpen (tsupport u)ᶜ := (isClosed_tsupport u).isOpen_compl
  have h2 : u =ᶠ[𝓝 x] 0 := by
    filter_upwards [hopen.mem_nhds hx] with y hy
    exact image_eq_zero_of_notMem_tsupport hy
  have h3 : fderiv ℝ u x = 0 := by
    rw [h2.fderiv_eq]
    simp
  simp only [gradient, h3, map_zero]

/-- Off the topological support of `u`, the trace of the Hessian of `u` vanishes. -/
lemma laplaceTrace_eq_zero_of_notMem_tsupport {u : R3 → ℝ} {x : R3}
    (hx : x ∉ tsupport u) : laplaceTrace u x = 0 := by
  have hopen : IsOpen (tsupport u)ᶜ := (isClosed_tsupport u).isOpen_compl
  have h3 : fderiv ℝ u =ᶠ[𝓝 x] 0 := by
    filter_upwards [hopen.mem_nhds hx] with y hy
    have hy' : u =ᶠ[𝓝 y] 0 := by
      filter_upwards [hopen.mem_nhds hy] with z hz
      exact image_eq_zero_of_notMem_tsupport hz
    rw [hy'.fderiv_eq]
    simp
  rw [laplaceTrace]
  refine Finset.sum_eq_zero fun i _ => ?_
  have hφ : (fun w => fderiv ℝ u w (FiniteTimeSingularity.e i)) =ᶠ[𝓝 x] 0 := by
    filter_upwards [h3] with y hy
    simp [hy]
  have h4 : fderiv ℝ (fun w => fderiv ℝ u w (FiniteTimeSingularity.e i)) x = 0 := by
    rw [hφ.fderiv_eq]
    simp
  simp [h4]

/-- The trace of the Hessian of a `C²` function is continuous. -/
theorem continuous_laplaceTrace (u : R3 → ℝ) (hu : ContDiff ℝ 2 u) :
    Continuous (laplaceTrace u) := by
  rw [← div_gradient_eq_laplaceTrace u hu]
  have hfd : Continuous (fderiv ℝ (fun z => gradient u z)) :=
    (contDiff_gradient u hu).continuous_fderiv (by norm_num)
  rw [funext (Work.FTS.PressureOn.div_eq_sum_single (fun z => gradient u z))]
  fun_prop

/-! ## The main theorem -/

theorem integral_mul_laplaceTrace_comm (f u : Work.FTS.PressureOn.R3 → ℝ)
    (hf : ContDiff ℝ 2 f) (hu : ContDiff ℝ 2 u) (hcs : HasCompactSupport u) :
    ∫ x, f x * Work.FTS.PressureOn.laplaceTrace u x
      = ∫ x, Work.FTS.PressureOn.laplaceTrace f x * u x := by
  -- the vector field whose divergence is the difference of the two integrands
  set G : R3 → R3 := fun x => f x • gradient u x - u x • gradient f x with hGdef
  have hdiv : ∀ x, div G x = f x * laplaceTrace u x - laplaceTrace f x * u x := by
    intro x
    rw [hGdef]
    exact congrFun (div_gradient_sub f u hf hu) x
  -- the smoothness of `G`
  have hGcd : ContDiff ℝ 1 G := by
    rw [hGdef]
    exact ((hf.of_le (by norm_num)).smul (contDiff_gradient u hu)).sub
      ((hu.of_le (by norm_num)).smul (contDiff_gradient f hf))
  have hcontG : Continuous G := hGcd.continuous
  have hdiffG : ∀ x, HasFDerivAt G (fderiv ℝ G x) x := fun x =>
    ((hGcd.differentiable (by norm_num)).differentiableAt).hasFDerivAt
  -- compact support of `G`
  have hcsG : HasCompactSupport G := by
    refine HasCompactSupport.intro hcs fun x hx => ?_
    simp only [hGdef]
    rw [gradient_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hx]
    simp
  -- integrability of the two summands (continuous, supported in `tsupport u`)
  have hcs1 : HasCompactSupport (fun x => f x * laplaceTrace u x) := by
    refine HasCompactSupport.intro hcs fun x hx => ?_
    simp [laplaceTrace_eq_zero_of_notMem_tsupport hx]
  have hcs2 : HasCompactSupport (fun x => laplaceTrace f x * u x) := by
    refine HasCompactSupport.intro hcs fun x hx => ?_
    simp [image_eq_zero_of_notMem_tsupport hx]
  have hI1 : Integrable (fun x => f x * laplaceTrace u x) :=
    (hf.continuous.mul (continuous_laplaceTrace u hu)).integrable_of_hasCompactSupport hcs1
  have hI2 : Integrable (fun x => laplaceTrace f x * u x) :=
    ((continuous_laplaceTrace f hf).mul hu.continuous).integrable_of_hasCompactSupport hcs2
  have hintG : Integrable (div G) :=
    (hI1.sub hI2).congr (Eventually.of_forall fun x => (hdiv x).symm)
  -- the divergence theorem
  have hzero : ∫ x, div G x = 0 :=
    Work.FTS.PressureOn.integral_div_eq_zero_of_hasFDerivAt G hcsG hcontG hdiffG hintG
  have hfinal : ∫ x, (f x * laplaceTrace u x - laplaceTrace f x * u x) = 0 := by
    rw [show (∫ x, (f x * laplaceTrace u x - laplaceTrace f x * u x)) = ∫ x, div G x from
      integral_congr_ae (Eventually.of_forall fun x => (hdiv x).symm)]
    exact hzero
  rw [integral_sub hI1 hI2] at hfinal
  linarith [hfinal]

end Work.FTS.PressureOn.Green
