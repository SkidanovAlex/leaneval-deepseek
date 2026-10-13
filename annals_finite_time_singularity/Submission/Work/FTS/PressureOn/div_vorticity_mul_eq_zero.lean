import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Work.FTS.PressureOn.Defs
import Submission.Work.FTS.PressureOn.integral_div_eq_zero_of_hasFDerivAt
import Submission.Work.FTS.PressureOn.PoissonAux.Ibp
import Submission.Work.FTS.PressureOn.PoissonAux.Ibp2
import Submission.Work.FTS.PressureOn.OffPlanes.offPlanes_ibp
import Submission.Work.FTS.PressureOn.CurlGrad.vorticity_gradient_integral_eq_zero

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `∫ x, div ω x * ψ x = 0` for `ω = ∇ × u` (the divergence of a curl integrates to zero)

The main result `Work.FTS.PressureOn.div_vorticity_mul_eq_zero` is assembled here from two
ingredients:

* `Work.FTS.PressureOn.OffPlanes.offPlanes_ibp` — the per-coordinate integration by parts for a
  function `g` that is differentiable only off the two coordinate planes `x 0 = 0` and `x 2 = 0`
  (the standing hypothesis on `ω = ∇ × u`), applied to the coordinate functions `x ↦ ω x i`;
* `Work.FTS.PressureOn.CurlGrad.vorticity_gradient_integral_eq_zero` — the vanishing of the
  pairing `∫ x, ⟪∇ × u x, ∇ψ x⟫`, which is the step in which the curl structure of `ω` is used.

The plumbing in between is developped in this file: the coordinate functions and their
differentiability, the trace identity `div ω = ∑ i, ∂ᵢωᵢ` (almost everywhere, which is what makes
the identity available in the integral), the identity `⟪ω x, ∇ψ x⟫ = ∑ i, ω x i * ∂ᵢψ x`, and the
nullity of the two coordinate planes.
-/

open FiniteTimeSingularity MeasureTheory Set Filter
open scoped Topology

set_option autoImplicit false

namespace Work.FTS.PressureOn

noncomputable section

/-! ## The coordinate functions of a vector field -/

/-- The `i`-th coordinate function of a vector field. -/
def coord (i : Fin 3) (ω : R3 → R3) : R3 → ℝ := fun x => WithLp.ofLp (ω x) i

@[simp] theorem coord_apply (i : Fin 3) (ω : R3 → R3) (x : R3) : coord i ω x = ω x i := rfl

theorem continuous_coord (i : Fin 3) {ω : R3 → R3} (hω : Continuous ω) :
    Continuous (coord i ω) :=
  (continuous_apply i).comp (ofLpCLM.continuous.comp hω)

theorem hasCompactSupport_coord (i : Fin 3) {ω : R3 → R3} (hω : HasCompactSupport ω) :
    HasCompactSupport (coord i ω) :=
  hω.mono (fun x hx => by
    rw [Function.mem_support] at hx ⊢
    intro h
    exact hx (by simp [coord, h]))

/-- A vector field with bounded support (given as a pointwise norm bound on the nonzero values)
has compact support. -/
theorem hasCompactSupport_of_norm_bound {ω : R3 → R3} {R : ℝ}
    (h : ∀ x, ω x ≠ 0 → ‖x‖ ≤ R) : HasCompactSupport ω :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : R3) R)
    (fun x hx => by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact h x hx)

/-- **The derivative of a coordinate function** is the composition of the derivative of the field
with the projection onto that coordinate. -/
theorem fderiv_coord (i : Fin 3) {ω : R3 → R3} {x : R3} (hx : DifferentiableAt ℝ ω x) :
    fderiv ℝ (coord i ω) x
      = (ContinuousLinearMap.proj i).comp (ofLpCLM.comp (fderiv ℝ ω x)) := by
  have h1 : HasFDerivAt (fun y : R3 => WithLp.ofLp (ω y))
      (ofLpCLM.comp (fderiv ℝ ω x)) x :=
    (ContinuousLinearMap.hasFDerivAt ofLpCLM).comp x hx.hasFDerivAt
  have h3 := (ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.proj i)).comp x h1
  exact h3.fderiv

/-- The evaluation form of `fderiv_coord`: the `i`-th coordinate of the partial derivative is
the partial derivative of the `i`-th coordinate function. -/
theorem fderiv_coord_apply (i j : Fin 3) {ω : R3 → R3} {x : R3} (hx : DifferentiableAt ℝ ω x) :
    fderiv ℝ (coord i ω) x (e j) = (fderiv ℝ ω x (e j)) i := by
  rw [fderiv_coord i hx]
  simp [ContinuousLinearMap.comp_apply, ofLpCLM_apply, ContinuousLinearMap.proj_apply]

/-- A coordinate function of a field differentiable off the two planes is differentiable off the
two planes. -/
theorem hasFDerivAt_coord_of_off_planes (i : Fin 3) {ω : R3 → R3}
    (hωdiff : ∀ x, x 0 ≠ 0 → x 2 ≠ 0 → HasFDerivAt ω (fderiv ℝ ω x) x)
    {x : R3} (h0 : x 0 ≠ 0) (h2 : x 2 ≠ 0) :
    HasFDerivAt (coord i ω)
      ((ContinuousLinearMap.proj i).comp (ofLpCLM.comp (fderiv ℝ ω x))) x := by
  have hx := hωdiff x h0 h2
  have h1 : HasFDerivAt (fun y : R3 => WithLp.ofLp (ω y))
      (ofLpCLM.comp (fderiv ℝ ω x)) x :=
    (ContinuousLinearMap.hasFDerivAt ofLpCLM).comp x hx
  have h3 := (ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.proj i)).comp x h1
  exact h3

/-! ## The nullity of the coordinate planes -/

/-- A coordinate hyperplane in `Fin 3 → ℝ` is Lebesgue-null. -/
theorem volume_fin3_coord_eq_zero (i : Fin 3) (c : ℝ) :
    volume {p : Fin 3 → ℝ | p i = c} = 0 := by
  rw [MeasureTheory.volume_pi]
  exact MeasureTheory.Measure.pi_hyperplane (fun _ : Fin 3 => (volume : Measure ℝ)) i c

/-- A coordinate hyperplane in `ℝ³` is Lebesgue-null. -/
theorem volume_coord_eq_zero (i : Fin 3) (c : ℝ) : volume {x : R3 | x i = c} = 0 := by
  have hset : {x : R3 | x i = c} = toLpCLE '' {p : Fin 3 → ℝ | p i = c} := by
    ext x
    constructor
    · intro hx
      exact ⟨WithLp.ofLp x, by simpa [toLpCLE_apply] using hx, toLpCLE_apply (WithLp.ofLp x)⟩
    · rintro ⟨p, hp, rfl⟩
      simpa [toLpCLE_apply] using hp
  rw [hset, ← toLpCLE_measurePreserving.measure_preimage_emb toLpCLE_measurableEmbedding]
  rw [Set.preimage_image_eq _ toLpCLE.injective]
  exact volume_fin3_coord_eq_zero i c

/-- Almost every point of `ℝ³` satisfies `x 0 ≠ 0` and `x 2 ≠ 0`. -/
theorem ae_coord_ne_zero : ∀ᵐ x : R3 ∂volume, x 0 ≠ 0 ∧ x 2 ≠ 0 := by
  rw [MeasureTheory.ae_iff]
  have hset : {x : R3 | ¬(x 0 ≠ 0 ∧ x 2 ≠ 0)}
      = {x : R3 | x 0 = 0} ∪ {x : R3 | x 2 = 0} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_union]
    tauto
  rw [hset]
  exact measure_union_null (volume_coord_eq_zero 0 0) (volume_coord_eq_zero 2 0)

/-- Almost every point of `ℝ³` is a point of differentiability of a field that is differentiable
off the two coordinate planes. -/
theorem ae_differentiableAt_of_off_planes {ω : R3 → R3}
    (hωdiff : ∀ x, x 0 ≠ 0 → x 2 ≠ 0 → HasFDerivAt ω (fderiv ℝ ω x) x) :
    ∀ᵐ x ∂volume, DifferentiableAt ℝ ω x := by
  filter_upwards [ae_coord_ne_zero] with x hx
  exact (hωdiff x hx.1 hx.2).differentiableAt

/-! ## The trace identity and the gradient identity -/

/-- **The trace identity, almost everywhere.**  Off the two coordinate planes `div ω` is the sum
of the coordinatewise partial derivatives. -/
theorem div_ae_eq_sum_fderiv_coord {ω : R3 → R3}
    (hωdiff : ∀ x, x 0 ≠ 0 → x 2 ≠ 0 → HasFDerivAt ω (fderiv ℝ ω x) x) :
    div ω =ᵐ[volume] fun x => ∑ i, fderiv ℝ (coord i ω) x (e i) := by
  filter_upwards [ae_differentiableAt_of_off_planes hωdiff] with x hx
  rw [div_eq_sum_single]
  exact Finset.sum_congr rfl fun i _ => (fderiv_coord_apply i i hx).symm

/-- **The gradient identity.**  The inner product of `ω x` with `∇ψ x` is the sum of the
coordinatewise products. -/
theorem inner_gradient_eq_sum_fderiv (ω : R3 → R3) (ψ : R3 → ℝ) (x : R3) :
    inner ℝ (ω x) (gradient ψ x) = ∑ i, ω x i * fderiv ℝ ψ x (e i) := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : (gradient ψ x) i = fderiv ℝ ψ x (e i) := by
    rw [← inner_e_eq_apply (gradient ψ x) i, inner_gradient_left]
  rw [h1, RCLike.inner_apply]
  simp [mul_comm]

/-- The basis vector `e i` has norm one. -/
theorem norm_e (i : Fin 3) : ‖(e i : R3)‖ = 1 := by
  have h : (e i : R3) = EuclideanSpace.single i (1 : ℝ) := rfl
  rw [h, EuclideanSpace.norm_single, norm_one]

/-- **The `i`-th coordinate of a vector is bounded by its norm.** -/
theorem norm_coord_le (w : R3) (i : Fin 3) : ‖w i‖ ≤ ‖w‖ := by
  calc ‖w i‖ = |inner ℝ w (e i)| := by rw [Real.norm_eq_abs, inner_e_eq_apply]
    _ ≤ ‖w‖ * ‖(e i : R3)‖ := abs_real_inner_le_norm _ _
    _ = ‖w‖ := by rw [norm_e i, mul_one]

/-- **The derivative of a coordinate function is locally integrable.** -/
theorem locallyIntegrable_fderiv_coord (i : Fin 3) {ω : R3 → R3}
    (hωdiff : ∀ x, x 0 ≠ 0 → x 2 ≠ 0 → HasFDerivAt ω (fderiv ℝ ω x) x)
    (hωint : MeasureTheory.LocallyIntegrable (fun x => fderiv ℝ ω x)) :
    MeasureTheory.LocallyIntegrable (fun x => fderiv ℝ (coord i ω) x) := by
  have hae : (fun x => fderiv ℝ (coord i ω) x)
      =ᵐ[volume] fun x => (ContinuousLinearMap.proj i).comp (ofLpCLM.comp (fderiv ℝ ω x)) := by
    filter_upwards [ae_differentiableAt_of_off_planes hωdiff] with x hx
    exact fderiv_coord i hx
  have hcont : Continuous fun L : R3 →L[ℝ] R3 =>
      (ContinuousLinearMap.proj i).comp (ofLpCLM.comp L) := by fun_prop
  have hmeas : AEStronglyMeasurable (fun x => fderiv ℝ (coord i ω) x) volume :=
    ((hcont.measurable.comp_aemeasurable
      hωint.aestronglyMeasurable.aemeasurable).aestronglyMeasurable).congr hae.symm
  refine hωint.mono hmeas ?_
  filter_upwards [hae] with x hx
  rw [hx]
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun (v : R3) => ?_
  have h1 : ((ContinuousLinearMap.proj i).comp (ofLpCLM.comp (fderiv ℝ ω x))) v
      = (fderiv ℝ ω x v) i := by
    simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, ofLpCLM_apply]
  rw [h1]
  exact le_trans (norm_coord_le (fderiv ℝ ω x v) i) (ContinuousLinearMap.le_opNorm _ v)

/-- **Integrability of the coordinatewise product.**  The product of `ψ` with the `i`-th partial
derivative of a field differentiable off the two coordinate planes is integrable. -/
theorem integrable_mul_fderiv_coord_self {ω : R3 → R3} {ψ : R3 → ℝ} (i : Fin 3)
    (hωdiff : ∀ x, x 0 ≠ 0 → x 2 ≠ 0 → HasFDerivAt ω (fderiv ℝ ω x) x)
    (hωint : MeasureTheory.LocallyIntegrable (fun x => fderiv ℝ ω x))
    (hψ : ContDiff ℝ 1 ψ) (hψcs : HasCompactSupport ψ) :
    Integrable (fun x => ψ x * fderiv ℝ (coord i ω) x (e i)) := by
  have hae : (fun x => fderiv ℝ (coord i ω) x (e i))
      =ᵐ[volume] fun x => (fderiv ℝ ω x (e i)) i := by
    filter_upwards [ae_differentiableAt_of_off_planes hωdiff] with x hx
    exact fderiv_coord_apply i i hx
  have hcont : Continuous (fun L : R3 →L[ℝ] R3 => (L (e i)) i) := by fun_prop
  have hne : ‖(e i : R3)‖ = 1 := by
    have h : (e i : R3) = EuclideanSpace.single i (1 : ℝ) := rfl
    rw [h, EuclideanSpace.norm_single, norm_one]
  have hloc : LocallyIntegrable (fun x => (fderiv ℝ ω x (e i)) i) :=
    hωint.mono
      (hcont.measurable.comp_aemeasurable hωint.aestronglyMeasurable.aemeasurable).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        refine le_trans (norm_coord_le _ i) ?_
        have h1 : ‖(fderiv ℝ ω x) (e i)‖ ≤ ‖fderiv ℝ ω x‖ * ‖(e i : R3)‖ :=
          ContinuousLinearMap.le_opNorm _ _
        rw [hne, mul_one] at h1
        exact h1)
  have hloc' : LocallyIntegrable (fun x => fderiv ℝ (coord i ω) x (e i)) := hloc.congr hae.symm
  obtain ⟨C, hC⟩ := (hψcs.isCompact).exists_bound_of_continuousOn
    hψ.continuous.continuousOn
  have hK : IntegrableOn (fun x => fderiv ℝ (coord i ω) x (e i)) (tsupport ψ) :=
    hloc'.integrableOn_isCompact hψcs.isCompact
  refine Integrable.mono' (IntegrableOn.integrable_indicator
    (hK.norm.const_mul C) hψcs.isCompact.measurableSet) ?_ ?_
  · exact hψ.continuous.aestronglyMeasurable.mul hloc'.aestronglyMeasurable
  · filter_upwards with x
    by_cases hx : x ∈ tsupport ψ
    · rw [Set.indicator_of_mem hx, norm_mul]
      gcongr
      exact hC x hx
    · rw [Set.indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport hx, zero_mul, norm_zero]

/-- **The pairing of `div ω` with `ψ` as a sum of coordinate pairings.** -/
theorem integral_div_mul_eq_sum_fderiv_coord {ω : R3 → R3} {ψ : R3 → ℝ}
    (hωdiff : ∀ x, x 0 ≠ 0 → x 2 ≠ 0 → HasFDerivAt ω (fderiv ℝ ω x) x)
    (hωint : MeasureTheory.LocallyIntegrable (fun x => fderiv ℝ ω x))
    (hψ : ContDiff ℝ 1 ψ) (hψcs : HasCompactSupport ψ) :
    ∫ x, div ω x * ψ x = ∑ i, ∫ x, ψ x * fderiv ℝ (coord i ω) x (e i) := by
  have hB : ∀ i : Fin 3, Integrable (fun x => ψ x * fderiv ℝ (coord i ω) x (e i)) :=
    fun i => integrable_mul_fderiv_coord_self i hωdiff hωint hψ hψcs
  have hsplit := div_ae_eq_sum_fderiv_coord hωdiff
  calc ∫ x, div ω x * ψ x
      = ∫ x, (∑ i, fderiv ℝ (coord i ω) x (e i)) * ψ x := by
        refine integral_congr_ae ?_
        filter_upwards [hsplit] with x hx
        rw [hx]
      _ = ∑ i, ∫ x, ψ x * fderiv ℝ (coord i ω) x (e i) := by
        rw [show (fun x : R3 => (∑ i, fderiv ℝ (coord i ω) x (e i)) * ψ x)
            = fun x => ∑ i, fderiv ℝ (coord i ω) x (e i) * ψ x from
          funext fun x => Finset.sum_mul Finset.univ (fun i => fderiv ℝ (coord i ω) x (e i)) (ψ x)]
        rw [integral_finsetSum]
        · refine Finset.sum_congr rfl fun i _ => ?_
          exact integral_congr_ae (Filter.Eventually.of_forall fun x => by simp [mul_comm])
        · intro i _
          exact (hB i).congr (Filter.Eventually.of_forall fun x => by simp [mul_comm])

/-- **The pairing of `ω` with `∇ψ` as a sum of coordinate pairings.** -/
theorem integral_inner_gradient_eq_sum_fderiv_psi {ω : R3 → R3} {ψ : R3 → ℝ}
    (hωcont : Continuous ω) (hψ : ContDiff ℝ 1 ψ) (hψcs : HasCompactSupport ψ) :
    ∫ x, inner ℝ (ω x) (gradient ψ x) = ∑ i, ∫ x, ω x i * fderiv ℝ ψ x (e i) := by
  have hB : ∀ i : Fin 3, Integrable (fun x => ω x i * fderiv ℝ ψ x (e i)) := by
    intro i
    have hcont1 : Continuous (fun x : R3 => fderiv ℝ ψ x (e i)) :=
      (hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const
    have hcs1 : HasCompactSupport (fun x : R3 => fderiv ℝ ψ x (e i)) :=
      hasCompactSupport_fderiv_apply_e hψcs i
    have hcont : Continuous (fun x : R3 => ω x i * fderiv ℝ ψ x (e i)) :=
      ((continuous_apply i).comp (ofLpCLM.continuous.comp hωcont)).mul hcont1
    exact hcont.integrable_of_hasCompactSupport (hcs1.mul_left (f := fun x => ω x i))
  rw [← integral_finsetSum]
  · refine integral_congr_ae ?_
    filter_upwards with x
    rw [inner_gradient_eq_sum_fderiv]
  · intro i _
    exact hB i

theorem div_vorticity_mul_eq_zero {u ω : R3 → R3}
    (hu : ContDiff ℝ 1 u) (hcurl : ∀ x, FiniteTimeSingularity.vorticity u x = ω x)
    (hωcont : Continuous ω) (hsuppω : ∃ R, ∀ x, ω x ≠ 0 → ‖x‖ ≤ R)
    (hωdiff : ∀ x, x 0 ≠ 0 → x 2 ≠ 0 → HasFDerivAt ω (fderiv ℝ ω x) x)
    (hωint : MeasureTheory.LocallyIntegrable (fun x => fderiv ℝ ω x))
    {ψ : R3 → ℝ} (hψ : ContDiff ℝ 1 ψ) (hψcs : HasCompactSupport ψ) :
    ∫ x, FiniteTimeSingularity.div ω x * ψ x = 0 := by
  obtain ⟨R, hR⟩ := hsuppω
  have hcs : HasCompactSupport ω := hasCompactSupport_of_norm_bound hR
  -- Step 1: the per-coordinate integration by parts (differentiability off the planes)
  have hIBP : ∀ i : Fin 3, ∫ x, ψ x * fderiv ℝ (coord i ω) x (e i)
      = -∫ x, coord i ω x * fderiv ℝ ψ x (e i) := by
    intro i
    refine OffPlanes.offPlanes_ibp i (continuous_coord i hωcont)
      (hasCompactSupport_coord i hcs) ?_ (locallyIntegrable_fderiv_coord i hωdiff hωint) hψ hψcs
    intro x h0 h2
    simpa [fderiv_coord i ((hωdiff x h0 h2).differentiableAt)]
      using hasFDerivAt_coord_of_off_planes i hωdiff h0 h2
  -- Step 2: the two summation identities
  have hsum1 := integral_div_mul_eq_sum_fderiv_coord hωdiff hωint hψ hψcs
  have hsum2 := integral_inner_gradient_eq_sum_fderiv_psi hωcont hψ hψcs
  have hsum3 : (∑ i, ∫ x, ψ x * fderiv ℝ (coord i ω) x (e i))
      = -∑ i, ∫ x, coord i ω x * fderiv ℝ ψ x (e i) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => hIBP i
  have hfin : ∑ i, ∫ x, coord i ω x * fderiv ℝ ψ x (e i)
      = ∫ x, inner ℝ (ω x) (gradient ψ x) := by
    rw [hsum2]
    exact Finset.sum_congr rfl fun i _ =>
      integral_congr_ae (Filter.Eventually.of_forall fun x => by simp [coord])
  -- Step 3: the pairing of `∇ψ` with the curl vanishes (the curl structure enters here)
  have hcurl0 : ∫ x, inner ℝ (ω x) (gradient ψ x) = 0 := by
    simpa only [hcurl] using CurlGrad.vorticity_gradient_integral_eq_zero hu hψ hψcs
  rw [hsum1, hsum3, hfin, hcurl0, neg_zero]

end

end Work.FTS.PressureOn
