import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.LinearAlgebra.Trace
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Work.FTS.PressureOn.Green.integral_mul_laplaceTrace_comm
import Submission.Work.FTS.PressureOn.integral_div_eq_zero_of_hasFDerivAt
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.conv_shift_sq_integral_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `∫ f · div V = −∫ ⟪∇f, V⟫` (integration by parts in `ℝ³`)

`Work.FTS.PressureOn.Auxiliary.integral_mul_div_eq_neg_inner_gradient`: for `f : ℝ³ → ℝ` and
`V : ℝ³ → ℝ³` of class `C^∞`, with `V` compactly supported,

  `∫ x, f x * div V x = −∫ x, ⟪∇f x, V x⟫`.

## The route

Put `G := f • V`.  The product rule for the trace of the Jacobian
(`Work.FTS.PressureOn.Green.div_smul_eq`) gives, pointwise,

  `div G x = f x * div V x + (fderiv ℝ f x) (V x) = f x * div V x + ⟪∇f x, V x⟫`.

`G` is `C¹` (`f` and `V` are `C^∞`), compactly supported (its support is contained in that of
`V`), and its divergence is integrable (both summands are continuous with support in `tsupport V`;
off `tsupport V` the field `V` — and hence its Jacobian, hence `div V` — vanishes).  The divergence
theorem for compactly supported `C¹` fields on `ℝ³`,
`Work.FTS.PressureOn.integral_div_eq_zero_of_hasFDerivAt`, then gives `∫ div G = 0`, and the
linearity of the integral finishes the proof.
-/

open MeasureTheory Filter Set
open scoped Topology

namespace Work.FTS.PressureOn.Auxiliary

/-- Off the topological support of `V`, the divergence of `V` vanishes: `V` is *locally* zero
there, hence so is its Fréchet derivative, hence so is the trace. -/
lemma div_eq_zero_of_notMem_tsupport {V : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∉ tsupport V) :
    FiniteTimeSingularity.div V x = 0 := by
  have hopen : IsOpen (tsupport V)ᶜ := (isClosed_tsupport V).isOpen_compl
  have h2 : V =ᶠ[𝓝 x] 0 := by
    filter_upwards [hopen.mem_nhds hx] with y hy
    exact image_eq_zero_of_notMem_tsupport hy
  rw [FiniteTimeSingularity.div, h2.fderiv_eq]
  simp

theorem integral_mul_div_eq_neg_inner_gradient (f : EuclideanSpace ℝ (Fin 3) → ℝ)
    (V : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (hf : ∀ n : ℕ, ContDiff ℝ n f) (hV : ∀ n : ℕ, ContDiff ℝ n V) (hVc : HasCompactSupport V) :
    ∫ x, f x * FiniteTimeSingularity.div V x
      = -∫ x, inner ℝ (gradient f x) (V x) := by
  -- the vector field whose divergence is the difference of the two integrands
  set G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) := fun x => f x • V x with hGdef
  have hdiv : ∀ x, FiniteTimeSingularity.div G x
      = f x * FiniteTimeSingularity.div V x + inner ℝ (gradient f x) (V x) := by
    intro x
    rw [hGdef, Work.FTS.PressureOn.Green.div_smul_eq f V x
      ((hf 1).differentiable (by norm_num)).differentiableAt
      ((hV 1).differentiable (by norm_num)).differentiableAt, inner_gradient_left]
  -- `G` is compactly supported, continuous, differentiable everywhere
  have hcsG : HasCompactSupport G := by
    rw [hGdef]
    exact HasCompactSupport.intro hVc (fun x hx => by
      simp [image_eq_zero_of_notMem_tsupport hx])
  have hcontG : Continuous G := by
    rw [hGdef]
    exact (hf 0).continuous.smul (hV 0).continuous
  have hGcd : ContDiff ℝ 1 G := by
    rw [hGdef]
    exact (hf 1).smul (hV 1)
  have hdiffG : ∀ x, HasFDerivAt G (fderiv ℝ G x) x := fun x =>
    ((hGcd.differentiable (by norm_num)).differentiableAt).hasFDerivAt
  -- continuity of `div V` (it is a finite sum of components of `fderiv ℝ V`)
  have hdivVcont : Continuous (fun x => FiniteTimeSingularity.div V x) := by
    rw [funext (Work.FTS.PressureOn.div_eq_sum_single V)]
    fun_prop
  -- integrability of the two summands of `div G`
  have hI1 : MeasureTheory.Integrable (fun x => f x * FiniteTimeSingularity.div V x) := by
    refine Continuous.integrable_of_hasCompactSupport ((hf 0).continuous.mul hdivVcont) ?_
    exact HasCompactSupport.intro hVc (fun x hx => by
      rw [div_eq_zero_of_notMem_tsupport hx, mul_zero])
  have hI2 : MeasureTheory.Integrable (fun x => inner ℝ (gradient f x) (V x)) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · have h : Continuous (fun x => (fderiv ℝ f x) (V x)) :=
        ((hf 1).continuous_fderiv_apply (by norm_num)).comp
          (continuous_id.prodMk (hV 0).continuous)
      refine h.congr ?_
      intro x
      rw [inner_gradient_left]
    · exact HasCompactSupport.intro hVc (fun x hx => by
        rw [inner_gradient_left, image_eq_zero_of_notMem_tsupport hx, map_zero])
  have hintG : MeasureTheory.Integrable (FiniteTimeSingularity.div G) :=
    (hI1.add hI2).congr (Eventually.of_forall fun x => (hdiv x).symm)
  -- the divergence theorem
  have hzero : ∫ x, FiniteTimeSingularity.div G x = 0 :=
    Work.FTS.PressureOn.integral_div_eq_zero_of_hasFDerivAt G hcsG hcontG hdiffG hintG
  have hfinal :
      ∫ x, (f x * FiniteTimeSingularity.div V x + inner ℝ (gradient f x) (V x)) = 0 := by
    rw [show (∫ x, (f x * FiniteTimeSingularity.div V x + inner ℝ (gradient f x) (V x)))
        = ∫ x, FiniteTimeSingularity.div G x from
      integral_congr_ae (Eventually.of_forall fun x => (hdiv x).symm)]
    exact hzero
  rw [MeasureTheory.integral_add hI1 hI2] at hfinal
  linarith

end Work.FTS.PressureOn.Auxiliary
